---- MODULE WikiSync ----
EXTENDS Naturals, Sequences, TLC

CONSTANT Users, Pages

\* WikiSync extends WikiSimple with synchronization tracking
\* Variables from WikiSimple: pages, history, depth
\* New variables for WikiSync: remote, synced
VARIABLE pages, remote, synced, history, depth

WS == INSTANCE WikiSimple

\* ============================================================================
\* TYPE INVARIANT
\* ============================================================================

TypeOK ==
    /\ pages \in [Pages -> Pages]
    /\ remote \in [Pages -> Pages]
    /\ synced \in [Pages -> BOOLEAN]
    /\ history \in Seq([op: {"read", "write", "sync"}, user: Users \cup {"system"}, page: Pages])
    /\ depth \in 0..10

\* ============================================================================
\* SYNC CONSISTENCY INVARIANTS
\* ============================================================================

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

\* ============================================================================
\* LIVENESS PROPERTIES
\* ============================================================================

\* Liveness: all pages eventually get synced
\* Note: In a system without depth limits and with fair scheduling, this would hold
AllPagesSyncEventually ==
    \A page \in Pages: []<> synced[page]

\* ============================================================================
\* INITIALIZATION
\* ============================================================================

Init ==
    /\ pages = [x \in Pages |-> ""]
    /\ remote = [x \in Pages |-> ""]
    /\ synced = [x \in Pages |-> FALSE]
    /\ history = <<>>
    /\ depth = 0

\* ============================================================================
\* SYNCHRONIZATION ACTIONS
\* ============================================================================

\* PushSync: Local changes are synchronized to remote
PushSync(page) ==
    /\ page \in DOMAIN pages
    /\ remote' = [remote EXCEPT ![page] = pages[page]]
    /\ synced' = [synced EXCEPT ![page] = TRUE]
    /\ history' = Append(history, [op |-> "sync", user |-> "system", page |-> page])
    /\ UNCHANGED pages
    /\ depth' = depth + 1

\* PullSync: Remote changes are pulled to local
PullSync(page) ==
    /\ page \in DOMAIN remote
    /\ pages' = [pages EXCEPT ![page] = remote[page]]
    /\ synced' = [synced EXCEPT ![page] = TRUE]
    /\ history' = Append(history, [op |-> "sync", user |-> "system", page |-> page])
    /\ UNCHANGED remote
    /\ depth' = depth + 1

\* Local sync operations
SyncNext ==
    /\ depth < 5
    /\ \E page \in Pages:
        PushSync(page) \/ PullSync(page)

\* ============================================================================
\* REFINEMENT OF WikiSimple
\* ============================================================================

\* WikiSync refines WikiSimple by tracking additional sync state.
\* We compose WikiSimple's spec with our sync operations and update sync flags.
\*
\* When WikiSimple operations happen, update the sync tracking:
\* - Read operations: no change to sync state
\* - Write operations: mark page as unsynced
\*
\* Additionally, our own sync operations can happen.

Next ==
    \/ SyncNext
    \/ (\E user \in Users, page \in Pages, content \in Pages:
          WS!Write(user, page, content) /\ 
          synced' = [synced EXCEPT ![page] = FALSE] /\
          UNCHANGED remote) 
    \/ (\E user \in Users, page \in Pages:
          WS!Read(user, page) /\ UNCHANGED <<remote, synced>>)

\* Full specification: initialize and then repeatedly apply Next
Spec == Init /\ [][Next]_<<pages, remote, synced, history, depth>>

\* Refinement claim: WikiSync refines WikiSimple
\* This would require a refinement mapping, but is expressed implicitly:
\* WikiSync!Spec restricted to WikiSimple variables should satisfy WS!Spec
Refinement == WS!Spec /\ [][SyncNext]_<<remote, synced>>

\* ============================================================================
\* INVARIANTS AND THEOREMS FOR TLAPS
\* ============================================================================

\* Combined invariant: All invariants that should hold for every reachable state
Invariants == /\ TypeOK
              /\ PagesSyncConsistent
              /\ OperationConsistent
              /\ PagesComplete

\* THEOREM Spec => []TypeOK
\*   PROOF OMITTED

\* THEOREM Spec => []PagesSyncConsistent
\*   PROOF OMITTED

\* THEOREM Spec => []OperationConsistent
\*   PROOF OMITTED

\* THEOREM Spec => []PagesComplete
\*   PROOF OMITTED

\* THEOREM RefinementCorrectness: 
\*   The set of states reachable by WikiSync on (pages, history, depth) 
\*   is a subset of states reachable by WikiSimple
\*   PROOF OMITTED

====
