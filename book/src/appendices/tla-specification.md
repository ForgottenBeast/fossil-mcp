# tla specification

> **RETIRED - NOT A CERTIFICATION OF THE CURRENT RUST CODE.**
> The TLA+ models in this repository (`src/WikiSimple.tla`, `src/server/WikiSync.tla`)
> describe an earlier `success`/`sync_status`/`force_write` design that no longer
> exists. Bounded model checking is not a proof of the Rust implementation, and no
> state count below describes it. At this snapshot `WikiSync.tla` instantiates a
> module whose variables differ (it is broken/unvalidated); `WikiSimple` has
> `SyncSuccess` requiring equality while transferring no content, `ResolveLocal`
> copying remote to local, an `EventualIdleIfNoPending` that starts with nothing
> pending, and fairness on the whole `Next` rather than on each recovery action.
> The Rust server makes **no** automatic-retry, force-overwrite or compare-and-swap
> guarantee; remote CAS is a separate gate. What is actually asserted today is
> listed in [Current invariant-to-test correspondence](../../../TLA_SPECIFICATION.md#current-invariant-to-test-correspondence).
> No current TLA model covers receipts or idempotency.
