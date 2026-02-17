# Getting Started

This guide will help you get the Fossil MCP server up and running.

## Prerequisites

Before you begin, ensure you have:

1. **Fossil SCM** installed and available in your PATH
   ```bash
   fossil version
   ```

2. **A Fossil repository** with wiki pages
   ```bash
   fossil new myproject.fossil
   ```

3. **An MCP client** such as:
   - [Claude Desktop](https://claude.ai/download)
   - [MCP CLI](https://github.com/modelcontextprotocol/cli)
   - Custom MCP client implementation

## Installation Methods

Choose the installation method that works best for you:

### Option 1: Using Nix (Recommended)

If you have [Nix](https://nixos.org) installed with flakes enabled:

```bash
# Build and run directly
nix run github:yourusername/fossil-mcp -- -R /path/to/repo.fossil

# Install to your profile
nix profile install github:yourusername/fossil-mcp
fossil-mcp -R /path/to/repo.fossil
```

### Option 2: Build from Source

```bash
# Clone the repository
git clone https://github.com/yourusername/fossil-mcp.git
cd fossil-mcp

# Build with Cargo
cargo build --release

# Run the server
./target/release/fossil-mcp -R /path/to/repo.fossil
```

### Option 3: Download Binary

Download pre-built binaries from the [releases page](https://github.com/yourusername/fossil-mcp/releases).

## Quick Verification

Test that the server starts correctly:

```bash
# Start the server (it will wait for stdin)
fossil-mcp -R /path/to/repo.fossil

# Send an initialize request (in another terminal or via echo)
echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{},"clientInfo":{"name":"test","version":"1.0"}}}' | fossil-mcp -R /path/to/repo.fossil
```

You should see a JSON response with server capabilities.

## Next Steps

- [Quick Start Guide](./quick-start.md) - Run your first commands
- [MCP Client Integration](./mcp-integration.md) - Connect to Claude Desktop
- [Configuration](./configuration.md) - Advanced setup options
