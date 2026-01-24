---- MODULE WikiSync ----
EXTENDS Naturals, Sequences, TLC

CONSTANT Users, Pages

VARIABLE pages, remote, synced, history, depth

WS == INSTANCE WikiSimple

TypeOK ==
    /\ pages \in [Pages -> Pages]
    /\ remote \in [Pages -> Pages]
    /\ synced \in [Pages -> BOOLEAN]
    /\ history \in Seq([op: {"sync"}, user: {"system"}, page: Pages])
    /\ depth \in 0..10

Init ==
    /\ pages = [x \in Pages |-> ""]
    /\ remote = [x \in Pages |-> ""]
    /\ synced = [x \in Pages |-> FALSE]
    /\ history = <<>>
    /\ depth = 0

PushSync(page) ==
    /\ page \in DOMAIN pages
    /\ remote' = [remote EXCEPT ![page] = pages[page]]
    /\ synced' = [synced EXCEPT ![page] = TRUE]
    /\ history' = Append(history, [op |-> "sync", user |-> "system", page |-> page])
    /\ UNCHANGED pages
    /\ depth' = depth + 1

PullSync(page) ==
    /\ page \in DOMAIN remote
    /\ pages' = [pages EXCEPT ![page] = remote[page]]
    /\ synced' = [synced EXCEPT ![page] = TRUE]
    /\ history' = Append(history, [op |-> "sync", user |-> "system", page |-> page])
    /\ UNCHANGED remote
    /\ depth' = depth + 1

Next ==
    /\ depth < 5
    /\ \E page \in Pages:
        PushSync(page) \/ PullSync(page)

\* WikiSync's next-state relation includes sync operations plus WikiSimple's read/write operations
CombinedNext == \/ Next \/ (WS!Next /\ UNCHANGED <<remote, synced>>)

Spec == Init /\ [][CombinedNext]_<<pages, remote, synced, history, depth>>

====
