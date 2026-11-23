# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is an MCP (Model Context Protocol) server that provides programmatic access to Fossil SCM wiki pages. It exposes five tools: list, read and write wiki pages, plus operation status and reconcile for write receipts. A sixth, read-only `wiki_backlinks`, exists only when the backlinks flag group is supplied.

## Build and Development Commands

### Building with Nix (Recommended)
```bash
# Enter development shell (provides Rust toolchain and dependencies)
nix develop

# Build in release mode
nix develop --command cargo build --release

# Build debug version
cargo build
```

### Building without Nix
Requires: Rust toolchain, gcc/build-essential, cmake

```bash
# Debug build
cargo build

# Release build
cargo build --release
```

### Running the Server
The server requires a path to a Fossil repository file:

```bash
# Using short flag
./target/release/fossil-mcp --repo-id notes -R /path/to/repo.fossil

# Using long flag
./target/release/fossil-mcp --repo-id notes --repository /path/to/repo.fossil
```

## Architecture

### Core Design
- **Transport**: stdio MCP server, one process per bound repository.
- **Binding**: `--repo-id <alias> -R <repo.fossil>` are mandatory and fixed at startup
  (`src/server/binding.rs`). No runtime reconfiguration, no `FOSSIL_REPO` fallback,
  symlink/empty/non-repository files are rejected before the MCP service starts.
- **Authority**: owner-local OS authority only. `repo_id` is an identifier, not a credential.
  Writes need `--allow-local-writes --state-dir <0700 dir>`; `publication: sync_repository`
  also needs `--allow-repository-sync` (sync may publish every sharable artifact).
- **Processes**: every `fossil` child goes through `src/server/process.rs` (stdin piping,
  capped concurrent stdout/stderr drains, one deadline, kill-on-drop). Page bytes travel over
  stdin; there is no temporary content file.
- **Receipts**: `write_wiki_page` returns `receipt{commit_state, publication_state, revision,
  previous_revision, error_code, retry_action}` (`types.rs`, mapping in `outcome.rs`).
  `unknown` is never reported as failure. Errors carry fixed codes only, no child output,
  paths or content.
- **Journal**: `operations.rs` keeps one private record per `operation_id` (reserve before
  spawn, atomic replace). Same key + same request replays the receipt; unknown survives restart;
  `wiki_reconcile_operation(retry_publication=true)` re-runs only sync, never commit.
- **Not implemented**: lost-update protection / remote authority (separate gate). The receipt's
  `previous_revision`/`revision` are where it plugs in. Semantic search was removed.

### Tools (stable catalog of five)
`list_wiki_pages`, `read_wiki_page` (returns `revision`), `write_wiki_page`,
`wiki_operation_status`, `wiki_reconcile_operation`. Read-only servers answer write/status/
reconcile with `write_disabled`; the catalog does not change at runtime.

### wiki_backlinks (optional, flag-gated)
Present in the catalog only when `--backlinks-url`, `--backlinks-issuer`, `--backlinks-key-file`
and at least one `--backlinks-audience-scope` are all given (`--backlinks-timeout-ms` optional).
Code: `src/server/secret.rs` (opaque `Secret`, `FileSecretSource`, `ZitadelKey`),
`src/server/backlinks/{mod,token,client}.rs`. The key file is read per token refresh and never
from the environment; the token never leaves the process. Tests: `tests/backlinks_token.rs`,
`tests/backlinks_tool.rs`, `tests/backlinks_stdio.rs` (fake issuer and sidecar on loopback).

### Testing
`cargo test --locked --all-targets && cargo test --locked --doc`. Integration tests use the
real `fossil` binary on throwaway repositories (isolated HOME) and a scripted fake fossil for
fault injection; they never touch a real wiki. `nix build .#checks.<system>.slice1` runs the
same suite. The TLA+ models are retired (see `TLA_SPECIFICATION.md`).

## MCP Integration

### Adding to Claude Code
```bash
claude mcp add --transport stdio fossil-mcp "/path/to/fossil-mcp --repo-id notes -R /path/to/repo.fossil"
```

### Adding to Claude Desktop
Configuration file location: `~/Library/Application Support/Claude/claude_desktop_config.json` (macOS) or equivalent on other platforms.

```json
{
  "mcpServers": {
    "fossil": {
      "command": "/path/to/fossil_mcp/target/release/fossil-mcp",
      "args": ["--repo-id", "notes", "-R", "/path/to/your/repo.fossil"]
    }
  }
}
```

## Tool Interface

### list_wiki_pages
No parameters. Returns all wiki page names in the repository.

**Response**: `{pages: string[]}`

### read_wiki_page
Reads the exact content and current revision of a page.

**Parameters**:
- `page_name` (string, required): Name of the page to read

**Response**: `{page_name, content, revision}`. `revision` is the Fossil artifact id of the version read.

### write_wiki_page
Creates or updates a page and returns a typed receipt. Requires the server to be started with
`--allow-local-writes --state-dir <private dir>`; `publication: "sync_repository"` also needs
`--allow-repository-sync`.

**Parameters** (unknown fields are rejected):
- `operation_id` (string, required): caller-generated idempotency key, 1-64 ASCII letters, digits, `_` or `-`
- `page_name` (string, required): non-empty, at most 256 bytes, no NUL/CR/LF, not starting with `-`
- `content` (string, required): at most 1 MiB, sent over stdin (no temporary file)
- `mimetype` (string, optional): `"text/x-fossil-wiki"`, `"text/x-markdown"` or `"text/plain"`
- `publication` (string, optional, default `"local_only"`): `"local_only"` or `"sync_repository"`.
  A sync may publish **all** sharable repository artifacts, not just this page.

**Response**: `{receipt, error_code, message}`. The receipt:

```json
{
  "receipt_version": 1,
  "repo_id": "notes",
  "operation_id": "op-1",
  "page_name": "API/v2/Reference",
  "previous_revision": "<artifact id or null>",
  "revision": "<artifact id, null unless attributed>",
  "commit_state": "committed",
  "publication_state": "confirmed",
  "error_code": null,
  "retry_action": "none"
}
```

- `commit_state`: `not_committed` (provably nothing happened), `committed`, `unknown`
- `publication_state`: `not_requested`, `pending` (provably not yet performed), `confirmed`, `unknown`
- `retry_action`: `none`, `retry_same_operation`, `reconcile`, `operator_required`
- `error_code` is a fixed snake_case code (for example `timeout`, `commit_unconfirmed`,
  `publication_unconfirmed`, `no_remote`, `revision_unresolved`, `idempotency_conflict`,
  `journal_repository_mismatch`); messages never contain child output, paths or content.

**Semantics**:
- Repeating an `operation_id` with the same request replays the stored receipt and never commits
  twice; the same id with a different request is `idempotency_conflict`.
- `unknown` is never reported as failure and is never downgraded by an inconclusive retry.
- `revision` is attributed by content (the single artifact parented on the pre-write head whose body
  equals the bytes written); otherwise the commit is `committed` with `revision_unresolved`.
- Receipts are bound to the repository (project code and path); a journal used with another
  repository fails closed with `journal_repository_mismatch`.
- There is no lost-update protection: `previous_revision` is observed, not enforced.

### wiki_operation_status
`{operation_id}` -> the stored receipt, read-only. `unknown_operation` if there is none.

### wiki_reconcile_operation
`{operation_id, retry_publication?}` -> the stored receipt. With `retry_publication: true` it re-runs
only `fossil sync` for an already committed revision whose publication is `pending` or `unknown`
(needs `--allow-repository-sync`); it never creates a wiki artifact, and first verifies the recorded
artifact exists in the bound repository.

### wiki_backlinks
Only listed when the backlinks flag group is supplied. Read-only, idempotent, open-world.

**Parameters** (unknown fields are rejected):
- `page` (string, required): 1-256 bytes, no NUL/CR/LF, not starting with `-`
- `cursor` (string, optional): the previous response's `next_cursor` (`<generation>:<offset>`)
- `limit` (integer, optional, 1-200, default 100)

**Response**: `{schema_version: "backlinks.v1", repo_id, page, status: "current", checked_at,
generation, inbound: [{source_page}], total_inbound, next_cursor}`. A cursor from an older index
generation is `cursor_stale` (restart from the first page). Errors are fixed codes:
`page_not_found`, `invalid_argument`, `backlinks_unavailable` (index `updating`/`unavailable`;
retry shortly), `backlinks_auth_failed` and `backlinks_forbidden` (operator: key, allowlist,
audience), `backlinks_unreachable`, `timeout`, `bad_response`, `backlinks_repo_mismatch` (the URL
points at another wiki's sidecar), `credential_unavailable` (key file unreadable or unsafe).

**Annotations**: reads and status are `readOnlyHint`; write and reconcile are not read-only,
destructive (the visible page content is replaced, although Fossil history is append-only),
idempotent and open-world (they may sync).

## Nix Flake Configuration

The flake.nix configures a cross-compilation setup targeting `aarch64-unknown-linux-musl` with fenix for Rust toolchain management. The dev shell provides rustfmt, clippy, and sets up CARGO_HOME in `.cargo/` (git-ignored).
