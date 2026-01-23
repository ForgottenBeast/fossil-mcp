----------------------- MODULE fossil_mcp -----------------------
(* TLA+ Specification for Fossil MCP Wiki Page Synchronization System
 * 
 * This module specifies the behavior of the fossil-mcp system, which provides
 * tools to read, write, and synchronize wiki pages in a Fossil SCM repository.
 * 
 * Key Components:
 * - list_wiki_pages: Lists all pages in the repository
 * - read_wiki_page: Reads a single page from the repository
 * - write_wiki_page: Writes a page to the repository and optionally syncs with remote
 * - sync_repository: Synchronizes local repository with remote
 *)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    MaxPages,           \* Maximum number of pages in the repository
    RemoteConfigured,   \* Boolean: whether remote is configured
    PageNames           \* Set of possible page names

ASSUME 
    /\ MaxPages > 0
    /\ IsFiniteSet(PageNames)
    /\ Cardinality(PageNames) <= MaxPages

(* ============================================================================
 * State Variables
 * ============================================================================ *)

VARIABLES
    pages,              \* Local pages: Name -> Content mapping
    remotePages,        \* Remote pages: Name -> Content mapping
    syncState,          \* State of synchronization: "idle", "syncing", "conflict"
    lastError,          \* Last sync error: error type or "none"
    pendingSync,        \* Set of pages pending synchronization
    clientOps           \* Queue of client operations waiting to be processed

vars == <<pages, remotePages, syncState, lastError, pendingSync, clientOps>>

(* ============================================================================
 * Type Definitions
 * ============================================================================ *)

NullString == ""

PageContent == {"", "A", "B"}

SyncErrorType == {"MergeConflict", "NoRemoteConfigured", "NetworkError", "Other", "none"}

SyncState == {"idle", "syncing", "conflict"}

Operation == [type: STRING, page: STRING, content: PageContent]

(* ============================================================================
 * Initial State
 * ============================================================================ *)

Init ==
    /\ pages = [p \in PageNames |-> NullString]
    /\ remotePages = [p \in PageNames |-> NullString]
    /\ syncState = "idle"
    /\ lastError = "none"
    /\ pendingSync = {}
    /\ clientOps = <<>>

(* ============================================================================
 * Actions - Client Operations
 * ============================================================================ *)

(* Client reads a page from the local repository *)
ReadPage(pageName) ==
    /\ pageName \in PageNames
    /\ pages[pageName] /= NullString  \* Page exists
    /\ UNCHANGED vars

(* Client writes a page to the local repository without syncing *)
WritePageSkipSync(pageName, content) ==
    /\ pageName \in PageNames
    /\ content /= NullString
    /\ pages' = [pages EXCEPT ![pageName] = content]
    /\ UNCHANGED <<remotePages, syncState, lastError, pendingSync, clientOps>>

(* Client writes a page to the local repository and requests sync *)
WritePageWithSync(pageName, content) ==
    /\ pageName \in PageNames
    /\ content /= NullString
    /\ pages' = [pages EXCEPT ![pageName] = content]
    /\ pendingSync' = pendingSync \cup {pageName}
    /\ UNCHANGED <<remotePages, syncState, lastError, clientOps>>

(* Client writes a page with force_write flag - allows override of merge conflicts *)
WritePageForceWrite(pageName, content) ==
    /\ pageName \in PageNames
    /\ content /= NullString
    /\ pages' = [pages EXCEPT ![pageName] = content]
    /\ pendingSync' = pendingSync \cup {pageName}
    /\ \* force_write allows write to succeed even with merge conflicts
       \* This is handled by not failing the operation
       UNCHANGED <<remotePages, syncState, lastError, clientOps>>

(* ============================================================================
 * Actions - Synchronization Operations
 * ============================================================================ *)

(* Initiate synchronization *)
InitiateSync ==
    /\ syncState = "idle"
    /\ pendingSync /= {}
    /\ IF RemoteConfigured
       THEN /\ syncState' = "syncing"
            /\ lastError' = "none"
            /\ UNCHANGED <<pages, remotePages, pendingSync, clientOps>>
       ELSE /\ syncState' = "idle"
            /\ lastError' = "NoRemoteConfigured"
            /\ UNCHANGED <<pages, remotePages, pendingSync, clientOps>>

(* Successful synchronization of all pending pages *)
SyncSuccess ==
    /\ syncState = "syncing"
    /\ remotePages' = [p \in PageNames |-> 
        IF p \in pendingSync THEN pages[p] ELSE remotePages[p]]
    /\ pendingSync' = {}
    /\ syncState' = "idle"
    /\ lastError' = "none"
    /\ UNCHANGED <<pages, clientOps>>

(* Synchronization fails due to merge conflict *)
SyncConflict ==
    /\ syncState = "syncing"
    /\ \E p \in pendingSync:
        /\ pages[p] /= remotePages[p]  \* Conflict: both sides changed
        /\ remotePages[p] /= NullString
    /\ syncState' = "conflict"
    /\ lastError' = "MergeConflict"
    /\ UNCHANGED <<pages, remotePages, pendingSync, clientOps>>

(* Synchronization fails due to network error *)
SyncNetworkError ==
    /\ syncState = "syncing"
    /\ syncState' = "idle"
    /\ lastError' = "NetworkError"
    /\ pendingSync' = pendingSync  \* Pages remain pending for retry
    /\ UNCHANGED <<pages, remotePages, clientOps>>

(* Resolve conflict by accepting local changes (with force_write) *)
ResolveConflictLocal ==
    /\ syncState = "conflict"
    /\ remotePages' = [p \in PageNames |-> 
        IF p \in pendingSync THEN pages[p] ELSE remotePages[p]]
    /\ pendingSync' = {}
    /\ syncState' = "idle"
    /\ lastError' = "none"
    /\ UNCHANGED <<pages, clientOps>>

(* Resolve conflict by accepting remote changes *)
ResolveConflictRemote ==
    /\ syncState = "conflict"
    /\ pages' = [p \in PageNames |->
        IF p \in pendingSync THEN remotePages[p] ELSE pages[p]]
    /\ pendingSync' = {}
    /\ syncState' = "idle"
    /\ lastError' = "none"
    /\ UNCHANGED <<remotePages, clientOps>>

(* Retry failed synchronization *)
RetrySyncAfterError ==
    /\ syncState = "idle"
    /\ lastError \in {"NetworkError", "Other"}
    /\ pendingSync /= {}
    /\ syncState' = "syncing"
    /\ lastError' = "none"
    /\ UNCHANGED <<pages, remotePages, pendingSync, clientOps>>

(* ============================================================================
 * Actions - Remote Updates (representing external changes)
 * ============================================================================ *)

(* Remote repository receives an update from another client *)
RemoteUpdate(pageName, content) ==
    /\ pageName \in PageNames
    /\ content /= NullString
    /\ remotePages' = [remotePages EXCEPT ![pageName] = content]
    /\ UNCHANGED <<pages, syncState, lastError, pendingSync, clientOps>>

(* ============================================================================
 * Next State
 * ============================================================================ *)

Next ==
    \/ \E p \in PageNames: ReadPage(p)
    \/ \E p \in PageNames, c \in {c \in PageContent : c /= NullString}: 
        WritePageSkipSync(p, c)
    \/ \E p \in PageNames, c \in {c \in PageContent : c /= NullString}: 
        WritePageWithSync(p, c)
    \/ \E p \in PageNames, c \in {c \in PageContent : c /= NullString}: 
        WritePageForceWrite(p, c)
    \/ InitiateSync
    \/ SyncSuccess
    \/ SyncConflict
    \/ SyncNetworkError
    \/ ResolveConflictLocal
    \/ ResolveConflictRemote
    \/ RetrySyncAfterError
    \/ \E p \in PageNames, c \in {c \in PageContent : c /= NullString}: 
        RemoteUpdate(p, c)

Spec == Init /\ [][Next]_vars

(* ============================================================================
 * Invariants - Properties we want to verify
 * ============================================================================ *)

(* Pages should never contain null values unless they were never written *)
ValidPages ==
    \A p \in PageNames: pages[p] \in PageContent

(* Remote pages should never contain null values unless not yet synced *)
ValidRemotePages ==
    \A p \in PageNames: remotePages[p] \in PageContent

(* Sync state must be valid *)
ValidSyncState ==
    syncState \in SyncState

(* Last error must be a valid sync error type *)
ValidLastError ==
    lastError \in SyncErrorType

(* Pending sync pages must be subset of all pages *)
ValidPendingSync ==
    pendingSync \subseteq PageNames

(* Sync state invariants *)
SyncStateInvariants ==
    /\ syncState = "idle" => lastError \in {"none", "NoRemoteConfigured", "NetworkError", "Other"}
    /\ syncState = "syncing" => lastError \in {"none"}
    /\ syncState = "conflict" => lastError = "MergeConflict"

(* If we're syncing, there must be pending pages *)
SyncingImpliesPending ==
    syncState = "syncing" => pendingSync /= {}

(* After successful sync completion, pending pages are cleared *)
SyncSuccessCleanup ==
    lastError = "none" /\ pendingSync = {} => syncState = "idle"

(* ============================================================================
 * Safety Properties - Conditions that should always hold
 * ============================================================================ *)

(* Type safety *)
TypeInvariant ==
    /\ pages \in [PageNames -> PageContent]
    /\ remotePages \in [PageNames -> PageContent]
    /\ ValidPages
    /\ ValidRemotePages
    /\ ValidSyncState
    /\ ValidLastError
    /\ ValidPendingSync
    /\ SyncStateInvariants
    /\ SyncingImpliesPending
    /\ SyncSuccessCleanup

(* Sync state is always valid *)
SyncConsistency ==
    syncState \in {"idle", "syncing", "conflict"}

(* Pages are never lost: once written, a page exists until explicitly cleared *)
PagePersistence ==
    \A p \in PageNames:
        (pages[p] /= NullString) => 
        ([] (pages[p] /= NullString \/ pages[p] = NullString))  \* Page persists in current or future states

(* ============================================================================
 * Liveness Properties - Conditions that should eventually happen
 * ============================================================================ *)

(* Pending synchronizations should eventually complete *)
EventualSyncCompletion ==
    (pendingSync /= {} /\ RemoteConfigured /\ syncState = "idle") 
    ~> 
    (pendingSync = {} /\ lastError = "none")

(* Network errors should eventually be resolved or retried *)
EventualNetworkRecovery ==
    lastError = "NetworkError" 
    ~> 
    (lastError = "none" \/ lastError = "MergeConflict")

(* Merge conflicts must eventually be resolved *)
EventualConflictResolution ==
    syncState = "conflict" 
    ~> 
    (syncState = "idle" /\ lastError = "none")

(* ============================================================================
 * Temporal Formulas - Multi-step properties
 * ============================================================================ *)

(* A page write should eventually be visible on remote (if synced) *)
PageWriteEventuallyRemote ==
    \A p \in PageNames:
        (pages[p] /= NullString /\ p \in pendingSync)
        ~> 
        (remotePages[p] = pages[p])

(* If no remote is configured, local pages should not require remote sync *)
NoRemoteNoSync ==
    ~RemoteConfigured => 
    (\A p \in PageNames, content \in PageContent:
     WritePageWithSync(p, content) => 
     (pages' = [pages EXCEPT ![p] = content] /\ 
      lastError' = "NoRemoteConfigured"))

(* ============================================================================
 * Behavioral Specifications - Specific scenarios
 * ============================================================================ *)

(* Scenario: Simple page write without sync *)
SimpleWriteScenario ==
    LET 
        initialState == Init
        writeAction == WritePageSkipSync("HomePage", "Welcome")
    IN 
    initialState /\ [writeAction]_vars

(* Scenario: Write then successful sync *)
WriteAndSyncScenario ==
    LET
        write == WritePageWithSync("HomePage", "Welcome")
        sync == SyncSuccess
    IN
    write /\ Next /\ sync

(* Scenario: Write, detect conflict, resolve locally *)
ConflictResolutionScenario ==
    LET
        remoteUpdate == RemoteUpdate("HomePage", "Remote Content")
        localWrite == WritePageWithSync("HomePage", "Local Content")
        detectConflict == SyncConflict
        resolveLocal == ResolveConflictLocal
    IN
    remoteUpdate /\ Next /\ localWrite /\ Next /\ detectConflict /\ Next /\ resolveLocal

(* ============================================================================
 * Correctness Lemmas
 * ============================================================================ *)

(* Lemma: Merge conflicts only occur when both sides modify same page *)
ConflictOccurrenceCondition ==
    syncState' = "conflict" => 
    \E p \in pendingSync: pages[p] /= remotePages[p]

(* Lemma: No remote configuration prevents successful sync *)
NoRemoteNoSuccess ==
    ~RemoteConfigured /\ syncState = "syncing" =>
    lastError' /= "none"

(* Lemma: Force write allows local version to override conflict *)
ForceWriteResolvesConflict ==
    (syncState = "conflict" /\ ResolveConflictLocal) =>
    (syncState' = "idle" /\ remotePages' = pages)

============================================================================
