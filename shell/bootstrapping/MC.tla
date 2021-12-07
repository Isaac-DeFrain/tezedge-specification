---- MODULE MC ----

EXTENDS ActionTraceChecker

Nodes == {"a", "b"}
Min_peers == 0
Max_peers == 2
Max_ops == 2
Init_chain == <<genesis>>
Init_head == gen_header
Init_connections == {}

===================
