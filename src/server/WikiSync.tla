---- MODULE WikiSync ----
EXTENDS Naturals, Sequences, TLC

CONSTANT Users, Pages

VARIABLE pages, remote, synced, history, depth

WS == INSTANCE WikiSimple

TypeOK ==
    /\ pages \in [Pages -> Pages]
    /\ remote \in [Pages -> Pages]
    /\ synced \in [Pages -> BOOLEAN]
    /\ history \in Seq([op: {"read", "write", "sync"}, user: Users \cup {"system"}, page: Pages])
    /\ depth \in 0..10

\* Synced pages have matching local and remote content (when not modified)
\* If pages differ from remote, the page must be marked as unsynced
PagesSyncConsistent ==
    \A page \in Pages: pages[page] = remote[page] \/ ~synced[page]

\* Sync operations come from system, read/write from users
OperationConsistent ==
    \A i \in DOMAIN history: 
        (history[i].op = "sync" => history[i].user = "system") /\
        (history[i].op \in {"read", "write"} => history[i].user \in Users)

\* All pages are always accessible
PagesComplete ==
    \A page \in Pages: page \in DOMAIN pages /\ page \in DOMAIN remote

\* Liveness: all pages eventually get synced
\* Note: In a system without depth limits and with fair scheduling, this would hold
AllPagesSyncEventually ==
    \A page \in Pages: []<> synced[page]

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
\* When pages change, mark affected pages as unsynced
CombinedNext == 
    \/ Next 
    \/ (\E user \in Users, page \in Pages, content \in Pages:
          WS!Write(user, page, content) /\ 
          synced' = [synced EXCEPT ![page] = FALSE] /\
          UNCHANGED remote) 
    \/ (\E user \in Users, page \in Pages:
          WS!Read(user, page) /\ UNCHANGED <<remote, synced>>)

Spec == Init /\ [][CombinedNext]_<<pages, remote, synced, history, depth>>

\* ============================================================================
\* INVARIANTS AND THEOREMS FOR TLAPS
\* ============================================================================

\* Invariant: All invariants that should hold for every reachable state
Invariants == /\ TypeOK
              /\ PagesSyncConsistent
              /\ OperationConsistent
              /\ PagesComplete

\* THEOREM InitInvariant: Init => Invariants
\* <1>1. SUFFICES ASSUME NEW page \in Pages PROVE Init => Invariants
\*       BY DEF Invariants
\* <1> QED BY DEF Init, TypeOK, PagesSyncConsistent, OperationConsistent, PagesComplete

\* THEOREM PagesSyncInvariant: Spec => []PagesSyncConsistent
\* <1> USE DEF Spec, Init, CombinedNext, Next, PushSync, PullSync, 
\*           WS!Write, WS!Read, PagesSyncConsistent, Invariants, TypeOK
\* <1> QED OMITTED

\* THEOREM OperationConsistentInvariant: Spec => []OperationConsistent
\* <1> USE DEF Spec, Init, CombinedNext, Next, PushSync, PullSync,
\*           WS!Write, WS!Read, OperationConsistent, Invariants, TypeOK
\* <1> QED OMITTED

====
