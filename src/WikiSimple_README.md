# WikiSimple TLA+ Specification

## Overview

`WikiSimple.tla` is a formal specification for the local and remote wiki page synchronization system used in fossil-mcp. It models the core behaviors of reading, writing, and synchronizing wiki pages across local and remote repositories.

## Key Differences from WikiSync.tla

| Aspect | WikiSimple | WikiSync |
|--------|-----------|---------|
| Scope | Local + remote basics | Full sync system with Fossil |
| Pages | Abstract string content | Fossil wiki page structure |
| Sync | Basic conflict detection | 3-way merge, force_write, skip_sync |
| Operations | 4 core operations | Full Fossil command set |
| Purpose | Correctness proof | Implementation spec |

## State Variables

- **pages**: Local wiki page storage (Pages → STRING)
- **remotePages**: Remote wiki page storage (Pages → STRING)  
- **syncState**: Current sync state ("idle" | "syncing" | "conflict" | "error")
- **pendingSync**: Set of pages awaiting synchronization
- **lastError**: Most recent error type ("none" | "network" | "merge")

## Operations

### User Actions

**Read(user, page)**
- Precondition: page exists in local storage
- Effect: No state change (modeling data retrieval)

**Write(user, page, content)**
- Precondition: None
- Effect: Updates local page, marks for sync

### Synchronization Actions

**InitiateSync**
- Precondition: idle state with pending pages
- Effect: Transition to "syncing" state

**SyncSuccess**
- Precondition: syncing state, all pending pages match remote
- Effect: Clear pending pages, return to idle

**SyncConflict**  
- Precondition: syncing state, any pending page differs from remote
- Effect: Transition to "conflict" state with merge error recorded

**SyncNetworkError**
- Precondition: syncing state
- Effect: Transition to "error" state (network error)

**ResolveLocal**
- Precondition: conflict state
- Effect: Force local pages to remote, return to idle

**RetrySyncAfterError**
- Precondition: error state with network error
- Effect: Clear error, return to idle for retry

### External Actions

**RemoteUpdate(page, content)**
- Simulates concurrent updates from other clients
- Can cause conflicts when sync is attempted

## Safety Properties (Invariants)

### TypeOK
All variables maintain their declared types.

### NoPendingSyncWhileBusy
When in "syncing" or "conflict" state, there must be pending pages.

### LocalModified  
Any page in pending set has been modified (locally or remotely).

### ErrorStateCorrect
Error state only occurs with network failures.

### ConflictStateCorrect
Conflict state only occurs with merge conflicts.

## Liveness Properties

### EventualIdleIfNoPending
If there are no pending pages, the system eventually reaches idle state.

## Model Checking Results

Configuration:
- Users: {"alice", "bob"}
- Pages: {"home", "about"}
- Invariants: All 5 safety properties verified
- Liveness: EventualIdleIfNoPending verified

Results: **139 distinct states explored, all properties hold**

## Example Scenarios

### Successful Sync
```
Write("alice", "home", "v1")     // pendingSync = {"home"}
InitiateSync                      // syncState = "syncing"
SyncSuccess                       // remotePages["home"] = "v1"
                                  // syncState = "idle"
```

### Conflict Resolution
```
Write("alice", "home", "v1")     // pendingSync = {"home"}
RemoteUpdate("home", "v2")       // External change
InitiateSync                      // syncState = "syncing"
SyncConflict                      // Detected: local != remote
ResolveLocal                      // remotePages = local version
                                  // syncState = "idle"
```

### Network Error Recovery
```
InitiateSync                      // syncState = "syncing"
SyncNetworkError                  // syncState = "error"
                                  // lastError = "network"
RetrySyncAfterError               // syncState = "idle"
InitiateSync (retry)              // Sync proceeds normally
```

## Extensions

This specification can be extended to model:

1. **Merge Strategies**: Add resolve_remote action (accept remote on conflict)
2. **Skip Sync**: Model write_wiki_page's skip_sync parameter
3. **Force Write**: Model skip_merge_conflict behavior
4. **Multiple Pages**: Atomic vs. page-by-page sync
5. **Persistence**: Model disk failures and recovery

## Verification with TLC

To verify this spec in TLA+ Toolbox:

1. Open WikiSimple.tla in TLC
2. Load WikiSimple.cfg
3. Click "Run TLC Model Checker"
4. Wait for completion (~2 seconds)

Expected output: "Model checking completed. No error has been found."

## Notes

- This specification abstracts page content as STRING for simplicity
- Sync is atomic (all or nothing) - real implementation may be incremental  
- Network errors are transient (can be retried)
- Merge conflicts require explicit resolution
- RemoteUpdate simulates concurrent client modifications
