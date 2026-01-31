---- MODULE WikiSimple ----
EXTENDS Naturals, Sequences, TLC

CONSTANT Users, Pages

VARIABLE pages,        \* Local wiki pages: Pages -> STRING
         remotePages,  \* Remote wiki pages: Pages -> STRING
         syncState,    \* Sync state: "idle" | "syncing" | "conflict" | "error"
         pendingSync,  \* Set of pages waiting to sync
         lastError     \* Last sync error type, or "none"

TypeOK ==
    /\ pages \in [Pages -> STRING]
    /\ remotePages \in [Pages -> STRING]
    /\ syncState \in {"idle", "syncing", "conflict", "error"}
    /\ pendingSync \subseteq Pages
    /\ lastError \in {"none", "network", "merge"}

Init ==
    /\ pages = [x \in Pages |-> ""]
    /\ remotePages = [x \in Pages |-> ""]
    /\ syncState = "idle"
    /\ pendingSync = {}
    /\ lastError = "none"

\* Read local wiki page
Read(user, page) ==
    /\ page \in DOMAIN pages
    /\ UNCHANGED <<pages, remotePages, syncState, pendingSync, lastError>>

\* Write local wiki page
Write(user, page, content) ==
    /\ pages' = [pages EXCEPT ![page] = content]
    /\ pendingSync' = pendingSync \cup {page}
    /\ UNCHANGED <<remotePages, syncState, lastError>>

\* Initiate synchronization
InitiateSync ==
    /\ syncState = "idle"
    /\ pendingSync # {}
    /\ syncState' = "syncing"
    /\ lastError' = "none"
    /\ UNCHANGED <<pages, remotePages, pendingSync>>

\* Successful sync: both sides match, sync clears pending  
SyncSuccess ==
    /\ syncState = "syncing"
    /\ \A page \in pendingSync: pages[page] = remotePages[page]
    /\ syncState' = "idle"
    /\ pendingSync' = {}
    /\ lastError' = "none"
    /\ UNCHANGED <<pages, remotePages>>

\* Detect conflict during sync (when both sides differ)
SyncConflict ==
    /\ syncState = "syncing"
    /\ \E page \in pendingSync: pages[page] # remotePages[page]
    /\ syncState' = "conflict"
    /\ lastError' = "merge"
    /\ UNCHANGED <<pages, remotePages, pendingSync>>

\* Resolve conflict by forcing local version to remote
ResolveLocal ==
    /\ syncState = "conflict"
    /\ remotePages' = pages
    /\ syncState' = "idle"
    /\ pendingSync' = {}
    /\ lastError' = "none"
    /\ UNCHANGED <<pages>>

\* External update to remote (simulating another client)
RemoteUpdate(page, content) ==
    /\ remotePages' = [remotePages EXCEPT ![page] = content]
    /\ UNCHANGED <<pages, syncState, pendingSync, lastError>>

\* Network error during sync
SyncNetworkError ==
    /\ syncState = "syncing"
    /\ syncState' = "error"
    /\ lastError' = "network"
    /\ UNCHANGED <<pages, remotePages, pendingSync>>

\* Retry after network error
RetrySyncAfterError ==
    /\ syncState = "error"
    /\ lastError = "network"
    /\ syncState' = "idle"
    /\ lastError' = "none"
    /\ UNCHANGED <<pages, remotePages, pendingSync>>

Next ==
    \/ \E user \in Users, page \in Pages: Read(user, page)
    \/ \E user \in Users, page \in Pages: Write(user, page, "v1")
    \/ InitiateSync
    \/ SyncSuccess
    \/ SyncConflict
    \/ SyncNetworkError
    \/ ResolveLocal
    \/ RetrySyncAfterError
    \/ \E page \in Pages: RemoteUpdate(page, "remote")

Spec == Init /\ [][Next]_<<pages, remotePages, syncState, pendingSync, lastError>>

\* Invariant: no pending sync while syncing or conflicted
NoPendingSyncWhileBusy ==
    syncState \in {"syncing", "conflict"} => pendingSync # {}

\* Invariant: pending pages reflect local changes
\* (for pages in pendingSync, local must differ from remote, unless we haven't synced yet)
LocalModified ==
    \A page \in pendingSync: 
        pages[page] # "" \/ remotePages[page] # ""

\* Invariant: error state only with network/merge errors
ErrorStateCorrect ==
    syncState = "error" => lastError = "network"

\* Invariant: conflict state only with merge error
ConflictStateCorrect ==
    syncState = "conflict" => lastError = "merge"

====
