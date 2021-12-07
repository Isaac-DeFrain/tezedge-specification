---- MODULE Utils ----

EXTENDS FiniteSets, Integers, Sequences, TLC, Hash

CONSTANTS MAX_OPS, NONE

Card(s) == Cardinality(s)

Set_op(s) == { ss \in SUBSET s : Card(ss) <= MAX_OPS }

NESet(s) == SUBSET s \ {{}}

NESeq(s) == Seq(s) \ {<<>>}

Pick(s) == CHOOSE x \in s : TRUE

Option(s) == s \cup {NONE}

Cons(x, seq) == <<x>> \o seq

RECURSIVE map(_, _, _)
map(f(_), seq, acc) ==
    IF seq = <<>> THEN acc
    ELSE
        LET x == Head(seq) IN
        map(f, Tail(seq), Append(acc, f(x)))

Map(f(_), seq) == map(f, seq, <<>>)

RECURSIVE Forall(_, _)
Forall(p(_), seq) ==
    \/ seq = <<>>
    \/ /\ p(Head(seq))
       /\ Forall(p, Tail(seq))

ToSet(seq) == { seq[i] : i \in DOMAIN seq }

RECURSIVE AppendAll(_, _)
AppendAll(seq1, seq2) ==
    IF seq2 = <<>> THEN seq1
    ELSE AppendAll(Append(seq1, Head(seq2)), Tail(seq2))

\* remove the first occurence of [elem] from [seq]
\* [seq] is a sequence of sets
RECURSIVE remove(_, _, _)
remove(elem, seq, acc) ==
    IF seq = <<>> THEN acc
    ELSE
        LET s == Head(seq) IN
        IF elem \notin s THEN remove(elem, Tail(seq), Append(acc, s))
        ELSE AppendAll(Append(acc, s \ {elem}), Tail(seq))

Remove(elem, seq) == remove(elem, seq, <<>>)

RECURSIVE seq_of_set(_, _)
seq_of_set(s, acc) ==
    IF s = {} THEN acc
    ELSE
        LET x == Pick(s)
            t == s \ {x}
        IN seq_of_set(t, Append(acc, x))

SetToSeq(s) == seq_of_set(s, <<>>)

\* header level comparison
min_level_cmp(p1, p2) == p1[1] <= p2[2]

max_level_cmp(p1, p2) == min_level_cmp(p2, p1)

Min_level_seq(seq) ==
    CASE seq /= <<>> -> Head(SortSeq(seq, min_level_cmp))

Min_level_set(s) == Min_level_seq(SetToSeq(s))

Max_level_seq(seq) ==
    CASE seq /= <<>> -> Head(SortSeq(seq, max_level_cmp))

Max_level_set(s) == Max_level_seq(SetToSeq(s))

Max_level_set_above(s, l) ==
    LET above_l == { p \in s : p[1] > l } IN
    Max_level_set(above_l)

Max_set(s) == Pick({ x \in s : \A y \in s : x >= y })

Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

======================
