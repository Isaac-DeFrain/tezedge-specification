---- MODULE Messages ----

CONSTANT NONE, MAX_OPS

VARIABLES messages, connections, peers, peer_head, recv_branch, recv_head, recv_header, recv_operation, pending_headers, sent_get_headers, sent_get_ops

----

INSTANCE Utils

(************)
(* Messages *)
(************)

\* [1] Requests
\* [1.1] Good requests
GetCurrentBranchMessages == [ type : {"Get_current_branch"} ]
GetBlockHeadersMessages  == [ type : {"Get_block_headers"}, hashes : NESet(HashLevels) ]
GetOperationsMessages    == [ type : {"Get_operations"},    op_hashes : NESet(OperationHashes) ]
\* GetCheckpointMessages    == [ type : {"Get_checkpoint"} ]
\* GetPredHeaderMessages    == [ type : {"Get_predecessor_header"}, hash : Hashes, offset : Nat ]

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
has_branch_from(n)            == recv_branch[n] /= {}
has_requested_headers_from(n) == sent_get_headers[n] /= {}
has_requested_ops_from(n)     == sent_get_ops[n] /= {}

requested_branch_from  == { n \in connections : has_branch_from(n) }
requested_headers_from == { n \in connections : has_requested_headers_from(n) }
requested_ops_from     == { n \in connections : has_requested_ops_from(n) }

has_received_branch(n)    == recv_branch[n] /= {}
has_received_header(n)    == recv_header[n] /= {}
has_received_operation(n) == recv_operation[n] /= {}

received_branch_from == { n \in Nodes : has_received_branch(n) }
received_header_from == { n \in Nodes : has_received_header(n) }
received_op_from     == { n \in Nodes : has_received_operation(n) }

\* [2] Responses
CurrentBranchMessages == [ type : {"Current_branch"}, from : Nodes, locator : Locators ]
BlockHeaderMessages   == [ type : {"Block_header"},   from : Nodes, header : Headers ]
OperationsMessages    == [ type : {"Operation"},      from : Nodes, operation : Operations ]
\* CheckpointMessages    == [ type : {"Checkpoint"},    from : Nodes, hash : Hashes ]
\* PredHeaderMessages    == [ type : {"Pred_header"},   from : Nodes, hash : Hashes, offset : Nat, header : Headers ]

ResponseMessages == CurrentBranchMessages \cup BlockHeaderMessages \cup OperationsMessages

current_branch_msg(n, l) == [ type |-> "Current_branch", from |-> n, locator   |-> l ]
block_header_msg(n, hd)  == [ type |-> "Block_header",   from |-> n, header    |-> hd ]
operation_msg(n, op)     == [ type |-> "Operation",      from |-> n, operation |-> op ]

\* [3] P2p messages
AdvertiseMessages   == [ type : {"Advertise"},  from : Nodes, peers : NESet(Nodes) ]
DisconnectMessages  == [ type : {"Disconnect"}, from : Nodes ]
SwapAckMessages     == [ type : {"Swap_ack"},   from : Nodes ]
SwapRequestMessages == [ type : {"Swap_req"},   from : Nodes, peer : Nodes ]

P2pMessages == AdvertiseMessages \cup DisconnectMessages \cup SwapRequestMessages \cup SwapAckMessages

\* node p2p messages

NodeAdvertiseMessages  == [ type : {"Advertise"}, peers : NESet(Nodes) ]
NodeDisconnectMessages == [ type : {"Disconnect"} ]
NodeSwapAckMessages    == [ type : {"Swap_ack"},  peer : Nodes ]
NodeSwapReqMessages    == [ type : {"Swap_req"},  peer : Nodes ]

NodeP2pMessages == NodeAdvertiseMessages \cup NodeDisconnectMessages \cup NodeSwapAckMessages \cup NodeSwapReqMessages

advertise_msgs(n)  == { msg \in messages[n] : msg.type = "Advertise" }
disconnect_msgs(n) == { msg \in messages[n] : msg.type = "Disconnect" }
swap_req_msgs(n)   == { msg \in messages[n] : msg.type = "Swap_request" }
swap_ack_msgs(n)   == { msg \in messages[n] : msg.type = "Swap_ack" }

advertise_msg(n, ps) == [ type |-> "Advertise",    from |-> n, peers |-> ps ]
disconnect_msg(n)    == [ type |-> "Disconnect",   from |-> n ]
swap_req_msg(n, p)   == [ type |-> "Swap_request", from |-> n, peer |-> p ]
swap_ack_msg(n)      == [ type |-> "Swap_ack",     from |-> n ]

\* [4] All messages
Messages          == GetMessages \cup ResponseMessages \cup P2pMessages \cup NodeP2pMessages
BranchMessages    == { msg \in Messages : msg.type = "Current_branch" }
HeaderMessages    == { msg \in Messages : msg.type = "Block_header" }
OperationMessages == { msg \in Messages : msg.type = "Operation" }

=========================
