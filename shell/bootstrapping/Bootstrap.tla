---- MODULE Bootstrap ----

EXTENDS FiniteSets, Naturals, Sequences, TLC, Hash, Samples

CONSTANTS
    NODES,              \* set of node ids
    MIN_PEERS,          \* minimum number of peers
    MAX_PEERS,          \* maximum number of peers
    MAX_OPS,            \* maximum number of operations per block
    MAX_LEVEL,          \* 
    MAX_FITNESS,        \* 
    MAX_HASH,           \* 
    INIT_CHAIN,         \* initial chain
    INIT_HEAD,          \* initial head
    INIT_CONNECTIONS,   \* initial connections
    NONE                \* null value

VARIABLES
    greylist,           \* the node's set of greylisted peers
    messages,           \* the node's set of messages
    chain,              \* the node's local chain
    connections,        \* the node's set of connections
    current_head,       \* the node's current head (header with hash)
    peer_head,          \* the node's peers' current heads
    earliest_hashes,    \* the earliest non-fetched hashes supplied by peers' current branches
    target,             \* the block hash and level we build our segment up to
    pending_headers,    \* the segment of headers retrieved up to the current checkpoint
    pending_operations, \* the corresponding operations for the pending headers
    sent_get_branch,    \* the node's set of peers to whom they have sent a Get_current_branch message
    sent_get_headers,   \* the node's function from peers to whom they have sent a Get_block_headers message to the requested headers
    sent_get_ops,       \* the node's function from peers to whom they have sent a Get_operations message to the requested operations
    recv_branch,        \* the node's set of peers from whom they have received a Current_branch message
    recv_head,          \* the node's set of received peer heads
    recv_header,        \* the node's function from peers to the set of headers with hashes received
    recv_operation      \* the node's function from peers to set of operations received

\* inclusive variables
sent_vars    == <<sent_get_branch, sent_get_headers, sent_get_ops>>
recv_vars    == <<recv_branch, recv_head, recv_header, recv_operation>>
local_vars   == <<greylist, messages, chain, connections, current_head>>
pending_vars == <<pending_headers, pending_operations>>
target_vars  == <<target, earliest_hashes>>
peer_vars    == <<peer_head, target_vars>>

\* exclusive variables
non_conn_vars     == <<greylist, messages, chain, current_head, peer_vars, pending_vars, sent_vars, recv_vars>>
non_msg_vars      == <<greylist, connections, chain, current_head, peer_vars, pending_vars, sent_vars, recv_vars>>
non_branch_vars   == <<local_vars, peer_vars, pending_vars, sent_get_headers, sent_get_ops, recv_head, recv_header, recv_operation>>
non_header_vars   == <<local_vars, peer_vars, pending_vars, sent_get_branch, sent_get_ops, recv_head, recv_branch, recv_operation>>
non_op_vars       == <<local_vars, peer_vars, pending_vars, sent_get_branch, sent_get_headers, recv_branch, recv_header>>
non_recv_vars     == <<local_vars, peer_vars, pending_vars, sent_vars>>
non_pending_vars  == <<local_vars, peer_vars, sent_vars, recv_vars>>
non_target_vars   == <<local_vars, peer_head, pending_vars, sent_vars, recv_vars>>
non_greylist_vars == <<connections, messages, chain, current_head, peer_vars, pending_vars, sent_vars, recv_vars>>

\* all variables
vars == <<local_vars, peer_vars, pending_vars, sent_vars, recv_vars>>

----

(***********)
(* Helpers *)
(***********)

\* [1] General helpers

INSTANCE Utils

\* [2] Spec-specific helpers

N == Card(NODES)

\* block levels
Levels  == Nat \ {0}
Levels0 == Nat

\* fitness
Fitness == Nat

\* context hashes
ContextHashes == Int

\* hash types
Hashes   == Int
OpHashes == Int

header(l, pred, ctx, fit, op) ==
    [ level |-> l, predecessor |-> pred, context |-> ctx, fitness |-> fit, ops_hash |-> op ]

header_with_hash(hd, h) == [ header |-> hd, hash |-> h ]

operation(bh, op) == [ block_hash |-> bh, op |-> op ]
operations(bh, ops) == [ block_hash : {bh}, op : ops ]
block(hdr, ops) == [ header |-> hdr, ops |-> { op.op : op \in ops } ]
hash(hd) == Hash(hd)

gen_header == header(0, 0, hash({}), 0, hash({}))
gen_operations == operations(hash(gen_header), {})
genesis == block(gen_header, gen_operations)

\* headers
Headers  == [
    level       : Levels0,
    context     : ContextHashes,
    fitness     : Fitness,
    predecessor : Hashes,
    ops_hash    : OpHashes
]

HashLevels == [ hash : Hashes, level : Levels ]
HeadersWithHash == [ header : Headers, hash : Hashes ]
Headers_of_hash(h) == { hd \in Headers : hash(hd) = h }

BoundedHeaders == [
    level       : 0..MAX_LEVEL,
    context     : 0..MAX_HASH,
    fitness     : 0..MAX_FITNESS,
    predecessor : 0..MAX_HASH,
    ops_hash    : 0..MAX_HASH
]

BoundedHeadersWithHash == [ header : BoundedHeaders, hash : Hashes ]

\* operations
Ops == Nat
Operations == [ block_hash : Hashes, op : SUBSET Ops ]
OperationHashes == Int

BoundedOperations == [ block_hash : 0..MAX_HASH, op : 0..MAX_OPS ]

\* blocks
Blocks == [ header : Headers, ops : SUBSET Ops ]
BlockOpHashes == [ block_hash : Hashes, op_hash : OperationHashes ]

BoundedBlocks == [ header : BoundedHeaders, ops : SUBSET 0..MAX_OPS ]

\* history
History == Seq(Levels \X Hashes)
Locators == [ current_head : Headers, history : History ]

BoundedHistory == Seq_n(MAX_LEVEL, {})

locator(hd, hist) == [ current_head |-> hd, history |-> hist ]

received_operations_block_hash(n, bh) == { op \in recv_operation[n] : op.block_hash = bh }

all_recv_operations_block_hash(bh) == UNION { received_operations_block_hash(n, bh) : n \in NODES }

\* all fetched data
fetched_hashes_node(n)  == { h.hash : h \in recv_header[n] }
fetched_headers_node(n) == { h.header : h \in recv_header[n] }

all_header_data    == UNION ToSet(pending_headers)
fetched_hashes     == UNION { fetched_hashes_node(n) : n \in NODES }
fetched_headers    == UNION { fetched_headers_node(n) : n \in NODES }
fetched_operations == UNION { recv_operation[n] : n \in NODES }

fetched_ops_block_hash(bh)     == { op \in fetched_operations : op.block_hash = bh }
num_fetched_ops_block_hash(bh) == Card(fetched_ops_block_hash(bh))

\* peer data

chain_levels(n) == peer_head[n].level

num_peers == Card(connections \cup greylist)

peers_at_level(l) == { n \in NODES : chain_levels(n) = l }

peers_at_or_above_level(l) == { n \in NODES : chain_levels(n) >= l }

headers_with_hash(bh) == { p \in all_header_data : p.header = bh }

\* only applied to sequences of headers and sets of operations of the same length
\* checks that hash of header matches the block hash in the operations and
\* that the hash of the operations matches the operations hash in the header
RECURSIVE Check(_, _)
Check(hds, ops) ==
    IF hds = <<>> THEN TRUE
    ELSE
        LET hd == Head(hds)
            op == Head(ops)
            check(h, o) ==
                \* header ops_hash matches hash of ops
                /\ h.ops_hash = hash(o.op)
                \* operations block_hash matches hash of block
                /\ hash(h) = o.block_hash
        IN
        /\ check(hd, op)
        /\ Check(Tail(hds), Tail(ops))

----

(************)
(* Messages *)
(************)

\* [1] Requests
\* [1.1] Good requests
GetCurrentBranchMessages == [ type : {"Get_current_branch"} ]
GetBlockHeadersMessages  == [ type : {"Get_block_headers"}, hashes : NESet(HashLevels) ]
GetOperationsMessages    == [ type : {"Get_operations"},    op_hashes : NESet(OperationHashes) ]

GetMessages == GetCurrentBranchMessages \cup GetBlockHeadersMessages \cup GetOperationsMessages

\* [1.2] Request constructors
get_current_branch_msg    == [ type |-> "Get_current_branch" ]
get_block_headers_msg(hs) == [ type |-> "Get_block_headers", hashes    |-> hs ]
get_operations_msg(ohs)   == [ type |-> "Get_operations",    op_hashes |-> ohs ]

\* [1.3] Sets of request types
current_branch_msgs(n) == { msg \in messages[n] : msg.type = "Current_branch" }
block_header_msgs(n)   == { msg \in messages[n] : msg.type = "Block_header" }
operation_msgs(n)      == { msg \in messages[n] : msg.type = "Operation" }

\* [1.4] Request predicates
has_requested_branch_from(n)  == n \in sent_get_branch
has_requested_headers_from(n) == sent_get_headers[n] /= {}
has_requested_ops_from(n)     == sent_get_ops[n] /= {}

requested_branch_from  == { n \in connections : has_requested_branch_from(n) }
requested_headers_from == { n \in connections : has_requested_headers_from(n) }
requested_ops_from     == { n \in connections : has_requested_ops_from(n) }

has_received_branch(n)    == recv_branch[n] /= {}
has_received_header(n)    == recv_header[n] /= {}
has_received_operation(n) == recv_operation[n] /= {}

received_branch_from == { n \in NODES : has_received_branch(n) }
received_header_from == { n \in NODES : has_received_header(n) }
received_op_from     == { n \in NODES : has_received_operation(n) }

\* [2] Responses
CurrentBranchMessages == [ type : {"Current_branch"}, from : NODES, locator : Locators ]
BlockHeaderMessages   == [ type : {"Block_header"},   from : NODES, header : Headers ]
OperationsMessages    == [ type : {"Operation"},      from : NODES, operation : Operations ]

ResponseMessages == CurrentBranchMessages \cup BlockHeaderMessages \cup OperationsMessages

current_branch_msg(n, l) == [ type |-> "Current_branch", from |-> n, locator   |-> l ]
block_header_msg(n, hd)  == [ type |-> "Block_header",   from |-> n, header    |-> hd ]
operation_msg(n, op)     == [ type |-> "Operation",      from |-> n, operation |-> op ]

\* [3] P2p messages
AdvertiseMessages   == [ type : {"Advertise"},  from : NODES, peers : NESet(NODES) ]
DisconnectMessages  == [ type : {"Disconnect"}, from : NODES ]

P2pMessages == AdvertiseMessages \cup DisconnectMessages

\* node p2p messages

NodeAdvertiseMessages  == [ type : {"Advertise"}, peers : NESet(NODES) ]
NodeDisconnectMessages == [ type : {"Disconnect"} ]

NodeP2pMessages == NodeAdvertiseMessages \cup NodeDisconnectMessages

advertise_msgs(n)  == { msg \in messages[n] : msg.type = "Advertise" }
disconnect_msgs(n) == { msg \in messages[n] : msg.type = "Disconnect" }

advertise_msg(n, ps) == [ type |-> "Advertise",  from |-> n, peers |-> ps ]
disconnect_msg(n)    == [ type |-> "Disconnect", from |-> n ]

\* [4] All messages
Messages          == GetMessages \cup ResponseMessages \cup P2pMessages \cup NodeP2pMessages
BranchMessages    == { msg \in Messages : msg.type = "Current_branch" }
HeaderMessages    == { msg \in Messages : msg.type = "Block_header" }
OperationMessages == { msg \in Messages : msg.type = "Operation" }

----

(***********)
(* Actions *)
(***********)

\* [0] Action helpers

Send(n, msg) ==
    messages' = [ messages EXCEPT ![n] = @ \cup {msg} ]

Drop(msg) ==
    LET n == msg.from IN
    messages' = [ messages EXCEPT ![n] = @ \ {msg} ]

update_connections(ps)    == connections' = ps
update_current_head(hdwh) == current_head' = hdwh

\* [1] Request actions

\* request a current branch from a peer
SendGetCurrentBranch == \E n \in connections \ greylist :
    /\ ~has_requested_branch_from(n)
    /\ sent_get_branch' = sent_get_branch \cup {n}
    /\ UNCHANGED <<messages, greylist, non_branch_vars, recv_branch>>

\* request headers from a peer up to the target hash/level
SendGetBlockHeaders == \E n \in connections \ greylist :
    /\ target.hash /= NONE
    /\ current_head.header.level < target.level
    /\ sent_get_headers' = [ sent_get_headers EXCEPT ![n] = @ \cup fetched_hashes_node(n) ]
    /\ UNCHANGED <<messages, greylist, non_header_vars, recv_header>>

\* request operations for a known header from a peer
SendGetOperations == \E n \in connections \ greylist, hdwh \in fetched_headers :
    LET bh  == hdwh.hash
        ops == operations(bh, 1..hdwh.header.ops_hash)
        req == ops \ all_recv_operations_block_hash(bh)
        ohs == { <<bh, hash(op)>> : op \in req }
    IN
    /\ target.hash /= NONE
    /\ current_head.header.level < target.level
    /\ req /= {}
    /\ sent_get_ops' = [ sent_get_ops EXCEPT ![n] = @ \cup ohs ]
    /\ UNCHANGED <<messages, greylist, non_op_vars, recv_operation>>

\* [2] Responding to the bootstrapping node

Advertise == \E n \in connections \ greylist, ps \in NESet(NODES) :
    LET msg == advertise_msg(n, ps) IN
    /\ Send(n, msg)
    /\ UNCHANGED non_msg_vars

Disconnect == \E n \in connections \ greylist :
    LET msg == disconnect_msg(n) IN
    /\ Send(n, msg)
    /\ UNCHANGED non_msg_vars

CurrentBranch == \E n \in (sent_get_branch \cap connections) \ greylist :
    \E blk \in Blocks, l \in Locators :
        LET data == locator(blk, l)
            msg  == current_branch_msg(n, data)
        IN
        /\ recv_branch[n] = {}
        /\ Send(n, msg)
        /\ UNCHANGED non_msg_vars

BlockHeader == \E n \in connections \ greylist, hd \in BoundedHeaders :
    LET msg  == block_header_msg(n, hd)
        req  == { hl.hash : hl \in sent_get_headers[n] }
        recv == { hdwh.hash : hdwh \in recv_header[n] }
    IN
    /\ hash(hd) \in req \ recv
    /\ Send(n, msg)
    /\ UNCHANGED non_msg_vars

Operation == \E n \in connections \ greylist :
    \E op \in BoundedOperations :
        LET msg == operation_msg(n, op) IN
        /\ op.block_hash \in { hdwh.hash : hdwh \in recv_header[n] }
        /\ hash(op) \in sent_get_ops[n]
        /\ Send(n, msg)
        /\ UNCHANGED non_msg_vars

\* [3] Bootstrapping node handles responses

\* bootstrapping node handles an Advertise message
HandleAdvertise == \E n \in connections \ greylist :
    \E msg \in advertise_msgs(n) :
        \E ps \in NESet(msg.peers) :
            /\ connections' = connections \cup ps
            /\ UNCHANGED non_conn_vars

\* bootstrapping node handles a Disconnect message
HandleDisconnect == \E n \in connections \ greylist :
    \E msg \in disconnect_msgs(n) :
        /\ connections' = connections \ {msg.from}
        /\ UNCHANGED non_conn_vars
        \* TODO Drop n from each functions' domain

\* bootstrapping node handles a CurrentBranch message
HandleCurrentBranch == \E n \in connections \ greylist :
    \E msg \in current_branch_msgs(n) :
        LET hist    == msg.locator.history
            curr_hd == msg.locator.current_head
        IN
        /\ Drop(msg)
        /\ peer_head' = [ peer_head EXCEPT ![n] =
                CASE curr_hd.level < @.level -> @
                  [] curr_hd.level > @.level -> curr_hd
                  \* curr_hd.level = @.level
                  [] curr_hd.fitness < @.fitness -> @
                  [] curr_hd.fitness < @.fitness -> curr_hd ]
        /\ earliest_hashes' = earliest_hashes \cup {Min_level_seq(hist)}
        /\ recv_header'     = [ recv_header  EXCEPT ![n] = @ \cup {header_with_hash(curr_hd, hash(curr_hd))} ]
        /\ recv_branch'     = [ recv_branch  EXCEPT ![n] = @ \cup ToSet(hist) ]
        /\ UNCHANGED <<greylist, connections, current_head, sent_vars, recv_header, recv_operation>>

\* bootstrapping node handles a BlockHeader message
HandleBlockHeader == \E n \in connections \ greylist :
    \E msg \in block_header_msgs(n) :
        LET hd == msg.header
            h  == hash(hd)
        IN
        /\ target.hash /= NONE
        /\ current_head.header.level < target.level
        /\ h \in sent_get_headers[n]
        /\ hd \notin fetched_headers
        /\ Drop(msg)
        /\ recv_header' = [ recv_header EXCEPT ![n] = @ \cup {header_with_hash(hd, h)} ]
        /\ recv_branch' = [ recv_branch EXCEPT ![n] = @ \cup {h} ]
        /\ UNCHANGED <<greylist, non_recv_vars, recv_operation>>

\* bootstrapping node handles an Operation message
HandleOperation == \E n \in connections \ greylist :
    \E msg \in operation_msgs(n) :
        \E hd \in fetched_headers :
            LET op == msg.operation
                bh == op.block_hash
            IN
            /\ target.hash /= NONE
            /\ current_head.header.level < target.level
            /\ bh = hash(hd)
            /\ op \notin recv_operation[n]
            /\ Drop(msg)
            /\ recv_operation' = [ recv_operation EXCEPT ![n] = @ \cup {op} ]
            /\ UNCHANGED <<greylist, non_recv_vars, recv_branch, recv_header>>

\* bootstrapping node computes the next target hash/level and earliest_hashes
ComputeNextTarget ==
    LET lh == Max_level_set(earliest_hashes)
        l  == lh[1]
        h  == lh[2]
    IN
    /\ \/ target.hash = NONE
       \/ target.level = NONE
    /\ 3 * Card(earliest_hashes) > 2 * Card(connections)
    /\ target'          = [ hash |-> h, level |-> l ]
    /\ earliest_hashes' = { Max_level_set_above(recv_branch[n], l) : n \in connections }
    /\ UNCHANGED non_target_vars

\* [4] Block validation

\* node applies a block formed from fetched headers and operations
apply_block(hd, ops) ==
    LET b == block(hd, ops) IN
    /\ pending_headers'    = Tail(pending_headers)
    /\ pending_operations' = Tail(pending_operations)
    /\ chain'              = Cons(b, chain)
    /\ IF pending_headers' = <<>>
       THEN /\ target' = [ hash |-> NONE, level |-> NONE ]
            /\ UNCHANGED <<local_vars, peer_head, sent_vars, recv_vars>>
       ELSE UNCHANGED non_pending_vars

ApplyBlock ==
    LET hds == pending_headers
        ops == pending_operations
    IN
    /\ hds /= <<>>
    /\ ops /= <<>>
    /\ Check(hds, ops)
    /\ LET hd == Head(hds)
           op == Head(ops)
        IN
        /\ op.block_hash = hash(hd)
        /\ apply_block(hd, ops)

\* [5] undesirable actions

\* [5.1] Timeout actions

greylist_node(n) == greylist' = greylist \cup {n}

filter_msgs_from(n) == messages' = [ messages EXCEPT ![n] = {} ]

remove_connection(n) == connections' = connections \ {n}

remove_data(n) ==
    /\ recv_branch'    = [ recv_branch    EXCEPT ![n] = {} ]
    /\ recv_header'    = [ recv_header    EXCEPT ![n] = {} ]
    /\ recv_operation' = [ recv_operation EXCEPT ![n] = {} ]

greylist_timeout(n) ==
    /\ greylist_node(n)
    /\ filter_msgs_from(n)
    /\ UNCHANGED <<chain, connections, current_head, peer_vars, pending_vars, sent_vars, recv_vars>>

\* timeout => greylist but keep data
Timeout ==
    \/ \E n \in requested_branch_from :
        /\ ~has_received_branch(n)
        /\ greylist_timeout(n)
    \/ \E n \in requested_headers_from :
        /\ Card(recv_header[n]) /= Card(sent_get_headers[n])
        /\ greylist_timeout(n)
    \/ \E n \in requested_ops_from :
        /\ ~has_received_operation(n)
        /\ greylist_timeout(n)

\* [5.2] Punative actions

Greylist ==
    \E n \in connections \ greylist :
        \E msg \in messages[n] :
            LET t == msg.type IN
            /\ n = msg.from
            /\ CASE t = "Block_header" ->
                        LET hd == msg.header IN
                        \* send multiple headers at the same level
                        \/ \E hdwh \in recv_header[n] : hdwh.header.level = hd.level
                        \* never requested header with that hash
                        \/ hash(hd) \notin sent_get_headers[n]
                [] t = "Operation" ->
                        LET op == msg.operation
                            h  == op.block_hash
                        IN
                        \* never requested operation
                        \/ h \notin sent_get_ops[n]
                        \* invalid operation
                        \/ \E hdwh \in fetched_headers :
                            /\ hdwh.hash = h
                            /\ hdwh.header.ops_hash < op.op
                [] OTHER -> FALSE
            /\ greylist_node(n)

Ungreylist == \E n \in greylist :
    /\ greylist' = greylist \ {n}
    /\ UNCHANGED non_greylist_vars

----

(*********************)
(* Initial predicate *)
(*********************)

Init ==
    /\ greylist           = {}
    /\ connections        = INIT_CONNECTIONS
    /\ messages           = [ n \in connections |-> {} ]
    /\ chain              = INIT_CHAIN
    /\ current_head       = INIT_HEAD
    /\ peer_head          = [ n \in connections |-> INIT_HEAD ]
    /\ earliest_hashes    = {}
    /\ target             = [ hash |-> NONE, level |-> NONE ]
    /\ pending_headers    = <<>>
    /\ pending_operations = <<>>
    /\ sent_get_branch    = {}
    /\ sent_get_headers   = [ n \in NODES |-> {} ]
    /\ sent_get_ops       = [ n \in NODES |-> {} ]
    /\ recv_branch        = [ n \in NODES |-> {} ]
    /\ recv_head          = [ n \in NODES |-> {} ]
    /\ recv_header        = [ n \in NODES |-> {} ]
    /\ recv_operation     = [ n \in NODES |-> {} ]

(****************)
(* Next actions *)
(****************)

Next ==
    \* Message passing
    \/ SendGetCurrentBranch
    \/ SendGetBlockHeaders
    \/ SendGetOperations
    \/ Advertise
    \/ Disconnect
    \/ CurrentBranch
    \/ BlockHeader
    \/ Operation
    \/ HandleAdvertise
    \/ HandleDisconnect
    \/ HandleCurrentBranch
    \/ HandleBlockHeader
    \/ HandleOperation
    \* Block application
    \/ ApplyBlock
    \* Timeouts
    \/ Timeout
    \* Disciplinary actions
    \/ Greylist
    \/ Ungreylist

(*****************)
(* Specification *)
(*****************)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----

(**************)
(* Invariants *)
(**************)

\* [1] TypeOK - type safety

TypeOK ==
    /\ connections        \in SUBSET NODES
    /\ greylist           \in SUBSET connections
    /\ messages           \in [ connections -> SUBSET (ResponseMessages \cup P2pMessages) ]
    /\ chain              \in Seq(Blocks)
    /\ current_head       \in Headers
    /\ peer_head          \in [ connections -> Headers ]
    /\ earliest_hashes    \in SUBSET (Levels \X Hashes)
    /\ target             \in [ hash : Option(Hashes), level : Option(Levels) ]
    /\ pending_headers    \in Seq(HeadersWithHash)
    /\ pending_operations \in Seq(Operations)
    /\ sent_get_branch    \in SUBSET connections
    /\ sent_get_headers   \in [ connections -> SUBSET HashLevels ]
    /\ sent_get_ops       \in [ connections -> SUBSET BlockOpHashes ]
    /\ recv_branch        \in [ connections -> SUBSET HashLevels ]
    /\ recv_head          \in [ connections -> SUBSET Headers ]
    /\ recv_header        \in [ connections -> SUBSET HeadersWithHash ]
    /\ recv_operation     \in [ connections -> SUBSET Operations ]

\* [2] General safety properties

ConnectionSafety == num_peers <= MAX_PEERS

MessageSafety == \A n \in NODES :
    \/ n \in connections
    \/ messages[n] = {}

\* The node has seen a quorum of support for their current head
CurrentHeadIsAlwaysMajor ==
    \/ current_head = INIT_HEAD
    \/ 3 * Card({ n \in connections : current_head \in recv_header[n] }) > 2 * Card(connections)

\* TODO properties

Safety ==
    /\ TypeOK
    /\ ConnectionSafety
    /\ CurrentHeadIsAlwaysMajor

(**************)
(* Properties *)
(**************)

\* PeerConservation ==
\*     [][ IF \/ connections /= {}
\*            \/ greylist /= {}
\*         THEN connections \cup greylist = connections' \cup greylist'
\*         ELSE connections \cup greylist \subseteq connections' \cup greylist' ]_vars

\* fitness always increases
MonotonicFitness ==
    LET old_head  == current_head
        new_head  == current_head'
    IN
    [][ old_head /= new_head => old_head.header.fitness < new_head.header.fitness ]_vars

\* Liveness

\* Bootstrapping node always learns about local major branches
\* IfLocalMajorBranchExistsThenBootstrapppingWillHearAboutIt ==
\*     LET curr_hd == current_head IN
\*     \E hd \in major_headers :
\*         <>( \/ hd = curr_hd
\*             \/ hd.fitness < curr_hd.fitness )

\* Liveness ==
\*     /\ IfLocalMajorBranchExistsThenBootstrapppingWillHearAboutIt

==========================
