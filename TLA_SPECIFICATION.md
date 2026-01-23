# TLA+ Specification for fossil-mcp

## Overview

This directory contains a TLA+ (Temporal Logic of Actions) specification for the fossil-mcp wiki page synchronization system. The specification provides a formal model of the system's behavior and enables verification of critical properties.

## Files

- `fossil_mcp.tla`: Main TLA+ specification module
- `fossil_mcp.cfg`: Model checking configuration
- `TLA_SPECIFICATION.md`: This documentation

## What is TLA+?

TLA+ is a formal specification language developed by Leslie Lamport that allows you to:
- Specify system behavior at a high level of abstraction
- Verify safety properties (bad things never happen)
- Verify liveness properties (good things eventually happen)
- Find counterexamples to incorrect specifications
- Document system design formally

## System Model

### State Variables

The specification models the following state:

```
pages          - Local wiki pages (Name -> Content mapping)
remotePages    - Remote wiki pages (Name -> Content mapping)
syncState      - Synchronization state: "idle", "syncing", "conflict"
lastError      - Last synchronization error or "none"
pendingSync    - Set of pages waiting to be synchronized
clientOps      - Queue of pending client operations
```

### Operations

The system supports the following actions:

#### Client Write Operations
1. **WritePageSkipSync** - Write page locally without requesting sync
2. **WritePageWithSync** - Write page and request synchronization
3. **WritePageForceWrite** - Write page with ability to override merge conflicts

#### Synchronization Operations
1. **InitiateSync** - Begin synchronization of pending pages
2. **SyncSuccess** - Successful synchronization
3. **SyncConflict** - Merge conflict detected
4. **SyncNetworkError** - Network error during sync
5. **ResolveConflictLocal** - Accept local version on conflict
6. **ResolveConflictRemote** - Accept remote version on conflict
7. **RetrySyncAfterError** - Retry after network error

#### Remote Operations
1. **RemoteUpdate** - External update to remote repository

## Properties Verified

### Safety Invariants

**TypeInvariant**: All state variables maintain correct types and bounds

**SyncStateInvariants**: Sync state transitions are valid
- Idle state only after no errors or non-configured remote
- Syncing state clears errors
- Conflict state indicates merge conflict

**LocalRemoteConsistency**: After successful sync, local pages match remote

**PagePersistence**: Once written, a page persists (not lost)

### Liveness Properties

**EventualSyncCompletion**: Pending syncs eventually complete (if remote configured)
```
pendingSync ≠ ∅ ∧ RemoteConfigured ∧ syncState = "idle"
    ↝ pendingSync = ∅ ∧ lastError = "none"
```

**EventualNetworkRecovery**: Network errors eventually recover
```
lastError = "NetworkError" ↝ lastError = "none" ∨ lastError = "MergeConflict"
```

**EventualConflictResolution**: Merge conflicts eventually resolve
```
syncState = "conflict" ↝ syncState = "idle" ∧ lastError = "none"
```

**PageWriteEventuallyRemote**: Written pages eventually appear on remote
```
pages[p] ≠ ∅ ∧ pendingSync ∋ p ↝ remotePages[p] = pages[p]
```

## Key Behaviors Modeled

### 1. Simple Write (skip_sync=true)
```
Initial State
    ↓
WritePageSkipSync("HomePage", "Welcome")
    ↓
Page stored locally, no sync attempted
```

### 2. Write with Sync (skip_sync=false)
```
Initial State
    ↓
WritePageWithSync("HomePage", "Welcome")
    ↓
Page stored locally, sync initiated
    ↓
SyncSuccess
    ↓
Remote updated, pendingSync cleared
```

### 3. Merge Conflict Resolution
```
Remote has: "Remote Content"
Local writes: "Local Content" with sync
    ↓
SyncConflict detected
    ↓
With force_write=true: ResolveConflictLocal (local wins)
With force_write=false: User resolves manually
```

### 4. Network Error Handling
```
WritePageWithSync
    ↓
InitiateSync → SyncNetworkError
    ↓
Error reported, pendingSync remains
    ↓
RetrySyncAfterError (automatic retry)
    ↓
SyncSuccess (eventual recovery)
```

## Correctness Lemmas

### Lemma 1: Conflict Conditions
Merge conflicts only occur when both sides modify the same page:
```
syncState' = "conflict" ⟹ ∃p ∈ pendingSync: pages[p] ≠ remotePages[p]
```

### Lemma 2: No Remote Prevention
Without remote configured, sync cannot succeed:
```
¬RemoteConfigured ∧ syncState = "syncing" ⟹ lastError' ≠ "none"
```

### Lemma 3: Force Write Resolution
Force write resolves conflicts locally:
```
(syncState = "conflict" ∧ ResolveConflictLocal) ⟹
    syncState' = "idle" ∧ remotePages' = pages
```

## How to Use with TLC Model Checker

### Prerequisites
- Install TLC model checker (included with TLA+ Toolbox)
- Java 11 or later

### Basic Model Checking

1. **Load the specification**:
   ```
   Open fossil_mcp.tla in TLA+ Toolbox
   ```

2. **Create a model** with the configuration:
   ```
   Model name: fossil_mcp_small
   Load fossil_mcp.cfg
   ```

3. **Set constants**:
   ```
   MaxPages = 3 (start small for quick checking)
   RemoteConfigured = TRUE or FALSE
   PageNames = {"HomePage", "API", "Docs"}
   ```

4. **Run model checker**:
   ```
   Right-click model → Run TLC Model Checker
   ```

5. **Check results**:
   - If properties hold: "No errors found"
   - If violated: TLC provides counterexample trace

### Configuration Variants

**Small model** (quick check, ~seconds):
```
MaxPages = 2
PageNames = {"HomePage", "API"}
```

**Medium model** (thorough, ~minutes):
```
MaxPages = 3
PageNames = {"HomePage", "API", "Docs"}
```

**Large model** (extensive, ~hours):
```
MaxPages = 4
PageNames = {"HomePage", "API", "Docs", "FAQ"}
```

## Interpreting Counterexamples

If TLC finds a property violation, it provides a trace:

1. **Initial State** - Shows starting values
2. **Transition Sequence** - Each action and resulting state
3. **Property Violation** - Where the property failed

Example counterexample analysis:
```
State 1: pages["A"] = "", syncState = "idle", pendingSync = {}
Action: WritePageWithSync("A", "v1")
State 2: pages["A"] = "v1", pendingSync = {"A"}, syncState = "idle"
Action: InitiateSync
State 3: syncState = "syncing"
Action: RemoteUpdate("A", "v2") [concurrent external update]
State 4: remotePages["A"] = "v2"
Action: SyncSuccess [ERROR - attempted without conflict detection]
```

This would indicate a race condition in the specification.

## Specification Design Decisions

### 1. Page Content as STRING
Pages are modeled as strings rather than structured data, simplifying the model while capturing the essence of page mutations.

### 2. Synchronization Atomicity
Sync operations are atomic in the specification - either fully succeed or fail. Real implementation may have partial syncs.

### 3. Error Recovery
Network errors can be retried, but merge conflicts require explicit resolution, matching the actual system behavior.

### 4. Force Write Semantics
`force_write=true` allows local version to override remote on conflict, useful for disaster recovery scenarios.

### 5. PageNames Constraint
PageNames is a constant set, limiting state space for model checking. Real system has unbounded pages.

## Extensions and Refinements

### Future Enhancements

1. **Page Versioning** - Track version history
   - Add `pageVersions` variable
   - Model three-way merge semantics

2. **Incremental Sync** - Model chunk-based synchronization
   - Replace atomic sync with multi-step process
   - Track sync progress

3. **Multiple Clients** - Model concurrent clients
   - Add client identity to operations
   - Model client-to-server contention

4. **Persistent Storage** - Model disk/network failures
   - Add failure modes
   - Model recovery procedures

5. **CRDT Semantics** - Model conflict-free replicated data types
   - Replace conflict resolution with CRDT operations
   - Guarantee eventual consistency

## Limitations

1. **Abstraction Level** - Specification is high-level, doesn't model async/await details
2. **Bounded State Space** - Model checking requires finite bound on pages
3. **Simplified Content** - Pages modeled as strings, not structured wiki syntax
4. **Single Repository** - Only models one local + one remote repository
5. **Synchronous Communication** - Network operations appear atomic in specification

## References

- [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html)
- [Specifying Systems by Leslie Lamport](https://lamport.azurewebsites.net/tla/book.html)
- [TLC Model Checker Guide](https://lamport.azurewebsites.net/tla/tlc-guide.html)
- [Fossil SCM Documentation](https://fossil-scm.org/)

## Contact

For questions about this specification:
- See repository documentation in CLAUDE.md and README
- Reference the code implementation in src/server.rs
- Review test cases in tests/fossil_wiki_integration.rs
