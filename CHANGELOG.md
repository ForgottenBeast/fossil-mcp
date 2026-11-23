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
- `wiki_backlinks`: read-only, paginated list of the pages that link to a page, served by
  the repository's backlinks sidecar. The tool exists only when the whole flag group is
  given (`--backlinks-url`, `--backlinks-issuer`, `--backlinks-key-file`, at least one
  `--backlinks-audience-scope`; optional `--backlinks-timeout-ms`, default 10000, 1000-60000).
  The sidecar origin and issuer are fixed at startup (https; plain http only for `127.0.0.1`
  and `[::1]`). Authentication is a Zitadel JWT-profile machine-user token: the RSA key is read
  from the key file on every refresh (regular file, no symlink, at most 16 KiB, no access for
  others), the token is cached in memory, a sidecar 401 triggers exactly one refresh and one
  retry, and neither the token, the key nor the path appears in tool output, errors or logs.
  New error codes: `cursor_stale`, `backlinks_unavailable`, `backlinks_forbidden`,
  `backlinks_repo_mismatch`, `backlinks_auth_failed`, `backlinks_unreachable`,
  `credential_unavailable`. The server gains an HTTP client again (`ureq` with rustls and
  WebPKI roots, no OpenSSL), `ring` (RS256 signing of the assertion, so the `rsa` crate and
  RUSTSEC-2023-0071 are not in the lockfile), `rustls-pki-types` (PEM), `zeroize` and `log`.
  The key file is checked once at startup (a missing, unsafe or unparseable file stops the
  server with a pathless message) and still read again on every refresh. Token responses
  with `expires_in` of 60 s or less are `backlinks_auth_failed`. `checked_at` must be a valid
  RFC 3339 timestamp. `timeout` and `bad_response` from the backlinks path carry
  backlinks-specific fixed messages (codes unchanged). The assertion, the form body and token
  response bodies are held in wiping buffers. Dependency TRACE/DEBUG logging (ureq-proto
  writes raw request bytes, including the bearer, at TRACE) is compiled out through `log`'s
  `max_level_info`, independent of the logger an embedding application installs; this also
  silences other `log`-crate DEBUG/TRACE output in the same build. The test RSA key under
  `tests/fixtures` is a labelled throwaway.
  Library: `WikiConfig::backlinks: Option<BacklinksConfig>`.
- `wiki_operation_status`, `wiki_reconcile_operation`, private receipt journal.
- Bounded subprocess runner; tests with throwaway repositories, fake-fossil fault
  injection, property tests, black-box stdio tests; `doCheck = true` and `checks.slice1`.
- MCP tool annotations: reads and status are read-only; write and reconcile are
  destructive (visible page content is replaced), idempotent and open-world.

### Fixed
- Page content no longer passes through a predictable shared `/tmp` file.
- Sync is no longer reported as success when fossil exits 0 against an unreachable or
  wrong-project peer.

- Receipts are bound to the repository, not only the alias: each journal record keeps
  the Fossil project code and canonical path and is replayed or reconciled only against
  that repository (`journal_repository_mismatch` otherwise). Replay, status and
  every reconcile also verify the recorded artifact exists in the bound repository, so a
  restore from an older snapshot yields `journal_repository_mismatch`, never `committed`.
  The state-directory `LOCK` serialises writers sharing that directory only; it does
  not coordinate two processes using different state directories on one repository.
- Publication reconcile combines the retry with the prior receipt: an inconclusive retry
  (no remote, zero round trips, spawn failure) keeps `unknown`; only a confirmed sync
  resolves it. Remote presence of the artifact is not checked.
- The committed revision is attributed by content among every revision of the page
  created after a blob-id baseline read just before the commit (neither `fossil wiki
  create` nor `commit` prints the new artifact id on 2.27 or 2.28): the single one whose
  wiki body equals the written bytes wins, provided every candidate was read and parsed.
  A candidate whose read fails (nonzero exit, timeout, output cap) or whose W card does
  not parse gives `revision_unresolved`, never a skip, as do zero or several matches
  (including a same-bytes writer racing our commit). Another writer's revision can be
  returned only if it is the sole readable same-bytes revision after the baseline, and
  only if blob ids stay monotonic (a purge or restore mid-write can break that). No baseline means no commit (`preflight_failed`).
- Every `fossil` child runs in its own process group and the whole group is killed when the
  call ends (exit, deadline, output overflow, cancellation), so forked descendants no longer
  outlive it. The leader is watched through a pidfd and reaped only after the group was
  signalled, so a recycled pid is never signalled (Linux 5.3+).

### Security
- Child output, paths and content never reach tool errors.
- Revision attribution runs one constant SQL query; page names are never interpolated into
  SQL (the page is matched in Rust against the hex-decoded tag name).

### Documentation
- `CLAUDE.md` documents the receipt API instead of `skip_sync` / `force_write`.
- TLA+ reports are retired; `TLA_SPECIFICATION.md` carries the invariant-to-test table.

### Known gaps
- No lost-update protection (revision is observed, not enforced); remote authority is a
  separate gate. Semantic search is unavailable until its own gate.
