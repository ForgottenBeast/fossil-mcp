# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is an MCP (Model Context Protocol) server that provides programmatic access to Fossil SCM wiki pages. It exposes three tools for listing, reading, and writing wiki pages in a Fossil repository.

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
Reads the content of a wiki page.

**Parameters**:
- `page_name` (string, required): Name of the page to read

**Response**: `{page_name: string, content: string}`

### write_wiki_page
Creates or updates a wiki page with optional repository synchronization.

**Parameters**:
- `page_name` (string, required): Name of the page to write
- `content` (string, required): Content for the page
- `mimetype` (string, optional): MIME type for the page (e.g., `"text/x-fossil-wiki"`, `"text/x-markdown"`, `"text/plain"`)
- `skip_sync` (boolean, optional, default: `false`): If `true`, skip repository synchronization after writing
- `force_write` (boolean, optional, default: `false`): If `true`, allow write to succeed even if sync fails with a merge conflict

**Sync Behavior**:
- When `skip_sync` is `false`, the repository will synchronize with remote after the page is written
- Merge conflicts are blocking errors that prevent the operation unless `force_write` is `true`
- Network errors and missing remote configuration are non-blocking and don't prevent the page write
- The response includes a `sync_status` field describing the synchronization outcome

**Response**:
```json
{
  "success": bool,
  "page_name": string,
  "message": string,
  "sync_status": {
    "attempted": bool,
    "succeeded": bool,
    "error_type": string | null,
    "error_message": string | null,
    "can_force_write": bool
  } | null
}
```

**Sync Error Types**:
- `MergeConflict`: Merge conflict occurred (blocking, can retry with `force_write: true`)
- `NoRemoteConfigured`: No remote repository is configured (non-blocking)
- `NetworkError`: Network connectivity issue (non-blocking)
- `Other`: Other synchronization error (non-blocking)

**Example Usage**:

```json
// Simple write without sync
{
  "page_name": "LocalDraft",
  "content": "# Draft Page\n\nWork in progress...",
  "skip_sync": true
}

// Write with sync (default behavior)
{
  "page_name": "API/v2/Reference",
  "content": "# API Documentation\n\nVersion 2.0 changes...",
  "mimetype": "text/x-markdown",
  "skip_sync": false
}

// Force write despite potential conflicts
{
  "page_name": "HotFix",
  "content": "# Emergency Update\n\nCritical fix applied.",
  "skip_sync": false,
  "force_write": true
}
```

**Sync Workflow Examples**:

```json
// Success: Page written and synced
{
  "success": true,
  "page_name": "UpdatedPage",
  "message": "Wiki page written successfully",
  "sync_status": {
    "attempted": true,
    "succeeded": true,
    "error_type": null,
    "error_message": null,
    "can_force_write": false
  }
}

// Non-blocking: No remote configured (page still written)
{
  "success": true,
  "page_name": "LocalPage",
  "message": "Wiki page written successfully",
  "sync_status": {
    "attempted": true,
    "succeeded": false,
    "error_type": "NoRemoteConfigured",
    "error_message": "No remote URL configured for this repository.",
    "can_force_write": false
  }
}

// Blocking: Merge conflict without force_write
{
  "error": "Sync failed: Merge conflict occurred during synchronization. Use force_write flag to override."
}

// Override: With force_write=true, page writes despite conflict
{
  "success": true,
  "page_name": "ConflictedPage",
  "message": "Wiki page written successfully",
  "sync_status": {
    "attempted": true,
    "succeeded": false,
    "error_type": "MergeConflict",
    "error_message": "Merge conflict occurred during synchronization. Use force_write to override.",
    "can_force_write": true
  }
}
```

## Nix Flake Configuration

The flake.nix configures a cross-compilation setup targeting `aarch64-unknown-linux-musl` with fenix for Rust toolchain management. The dev shell provides rustfmt, clippy, and sets up CARGO_HOME in `.cargo/` (git-ignored).
