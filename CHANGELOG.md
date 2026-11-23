# Changelog

All notable changes to this project are documented here. The project follows
[Semantic Versioning](https://semver.org/); the contract below is proposed for
`0.2.0` and is not yet released.

## [Unreleased]

### Breaking
- `--repo-id` and `-R` are mandatory; the repository is fixed at startup. The
  `FOSSIL_REPO` environment fallback and the `configure_repository` tool are removed.
- `authenticate_wiki` and `search_wiki` are removed, with all model-facing
  password / api_key / session_token fields and the HTTP client (`reqwest`).
- `write_wiki_page` now takes `{operation_id, page_name, content, mimetype?, publication?}`
  and returns a typed receipt. `skip_sync`, `force_write`, `success` and `sync_status`
  are gone; unknown request fields are rejected.
- `read_wiki_page` returns the page `revision` and exact content (no trailing-newline trim).
- Writes are disabled unless `--allow-local-writes --state-dir` is given; sync needs
  `--allow-repository-sync`.
- Library: `FossilWiki::new(Option<PathBuf>)` is replaced by `FossilWiki::bind(WikiConfig)`.

### Added
- `wiki_operation_status`, `wiki_reconcile_operation`, private receipt journal.
- Bounded subprocess runner; tests with throwaway repositories, fake-fossil fault
  injection, property tests, black-box stdio tests; `doCheck = true` and `checks.slice1`.

### Fixed
- Page content no longer passes through a predictable shared `/tmp` file.
- Sync is no longer reported as success when fossil exits 0 against an unreachable or
  wrong-project peer.

- Receipts are bound to the repository, not only the alias: each journal record keeps
  the Fossil project code and canonical path and is replayed or reconciled only against
  that repository (`journal_repository_mismatch` otherwise). Replay and sync-only
  reconcile also verify the recorded artifact exists in the bound repository.
  The state-directory `LOCK` serialises writers sharing that directory only; it does
  not coordinate two processes using different state directories on one repository.

### Security
- Child output, paths and content never reach tool errors.

### Documentation
- TLA+ reports are retired; `TLA_SPECIFICATION.md` carries the invariant-to-test table.

### Known gaps
- No lost-update protection (revision is observed, not enforced); remote authority is a
  separate gate. Semantic search is unavailable until its own gate.
