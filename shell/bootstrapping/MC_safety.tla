---- MODULE MC_safety ----

EXTENDS Bootstrap

Nodes == {"a", "b"}
Min_peers == 0
Max_peers == 2
Max_ops == 2
Max_level == 3
Max_fitness == 10
Max_hash == 10
Init_chain == <<genesis>>
Init_head == gen_header
Init_connections == {"a", "b"}

==========================
