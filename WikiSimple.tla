---- MODULE WikiSimple ----
EXTENDS Naturals, Sequences, TLC

CONSTANT Users, Pages

VARIABLE pages, history, depth

TypeOK ==
    /\ pages \in [Pages -> Pages]
    /\ history \in Seq([op: {"read", "write"}, user: Users, page: Pages])

Init ==
    /\ pages = [x \in Pages |-> ""]
    /\ history = <<>>
    /\ depth = 0

Read(user, page) ==
    /\ page \in DOMAIN pages
    /\ history' = Append(history, [op |-> "read", user |-> user, page |-> page])
    /\ UNCHANGED pages
    /\ depth' = depth + 1

Write(user, page, content) ==
    /\ pages' = [pages EXCEPT ![page] = content]
    /\ history' = Append(history, [op |-> "write", user |-> user, page |-> page])
    /\ depth' = depth + 1

Next ==
    /\ depth < 5
    /\ \E user \in Users, page \in Pages, content \in Pages:
        Read(user, page) \/ Write(user, page, content)

Spec == Init /\ [][Next]_<<pages, history, depth>>

====
