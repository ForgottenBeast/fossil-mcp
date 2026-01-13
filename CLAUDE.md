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

**list_wiki_pages** - No parameters. Returns `{pages: string[], count: number}`

**read_wiki_page** - Requires `page_name: string`. Returns `{page_name: string, content: string}`

**write_wiki_page** - Requires `page_name: string`, `content: string`. Optional: `mimetype: "text/x-fossil-wiki" | "text/x-markdown" | "text/plain"`. Returns `{success: bool, page_name: string, message: string}`

## Nix Flake Configuration

The flake.nix configures a cross-compilation setup targeting `aarch64-unknown-linux-musl` with fenix for Rust toolchain management. The dev shell provides rustfmt, clippy, and sets up CARGO_HOME in `.cargo/` (git-ignored).
