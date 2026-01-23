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
./target/release/fossil-mcp -R /path/to/repo.fossil

# Using long flag
./target/release/fossil-mcp --repository /path/to/repo.fossil
```

## Architecture

### Core Design
- **Transport**: Stdio-based MCP server (runs as a subprocess, communicates via stdin/stdout)
- **State Management**: Uses `AppState` with `Arc<PathBuf>` to share the repository path across async handlers
- **Command Execution**: All operations execute `fossil -R <repo_path>` commands, allowing interaction with any Fossil repository without requiring a checkout directory

### Key Components

**Handler Functions** (src/main.rs:41-120):
- `list_wiki_pages`: Executes `fossil -R <repo> wiki list`
- `read_wiki_page`: Executes `fossil -R <repo> wiki export <page_name>`
- `write_wiki_page`: Writes content to temp file, then executes `fossil -R <repo> wiki commit`

**State Pattern**:
The server uses clap for CLI parsing and passes `AppState` to all handlers via `.with_handler_and_state()`. This allows the repository path to be specified at launch and used consistently across all operations.

## MCP Integration

### Adding to Claude Code
```bash
claude mcp add --transport stdio fossil-mcp "/path/to/fossil-mcp -R /path/to/repo.fossil"
```

### Adding to Claude Desktop
Configuration file location: `~/Library/Application Support/Claude/claude_desktop_config.json` (macOS) or equivalent on other platforms.

```json
{
  "mcpServers": {
    "fossil": {
      "command": "/path/to/fossil_mcp/target/release/fossil-mcp",
      "args": ["-R", "/path/to/your/repo.fossil"]
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
{
  "page_name": "API/v2/Reference",
  "content": "# API Documentation\n\n...",
  "mimetype": "text/x-markdown",
  "skip_sync": false,
  "force_write": false
}
```

## Nix Flake Configuration

The flake.nix configures a cross-compilation setup targeting `aarch64-unknown-linux-musl` with fenix for Rust toolchain management. The dev shell provides rustfmt, clippy, and sets up CARGO_HOME in `.cargo/` (git-ignored).
