# Installation

## System Requirements

- **Operating System**: Linux, macOS, or Windows (WSL)
- **Fossil SCM**: Version 2.x or later
- **Rust** (for building from source): 1.70+

## Installation Options

### Using Nix Flakes (Recommended)

The easiest way to install fossil-mcp is using Nix with flakes:

```bash
# Run directly without installing
nix run github:yourusername/fossil-mcp -- -R repo.fossil

# Install to your user profile
nix profile install github:yourusername/fossil-mcp

# Use in a development shell
nix develop github:yourusername/fossil-mcp
```

### Building from Source

#### Prerequisites

Install Rust and Cargo:
```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

Install Fossil:
```bash
# On Debian/Ubuntu
sudo apt-get install fossil

# On macOS
brew install fossil

# On Arch Linux
sudo pacman -S fossil
```

#### Build Steps

```bash
# Clone the repository
git clone https://github.com/yourusername/fossil-mcp.git
cd fossil-mcp

# Build in release mode
cargo build --release

# The binary will be at target/release/fossil-mcp
./target/release/fossil-mcp --help
```

### Using Pre-built Binaries

Download pre-compiled binaries from the [GitHub Releases](https://github.com/yourusername/fossil-mcp/releases) page.

1. Download the appropriate binary for your platform
2. Make it executable: `chmod +x fossil-mcp`
3. Move to your PATH: `sudo mv fossil-mcp /usr/local/bin/`

## Verifying Installation

Check that the server runs:

```bash
fossil-mcp --version
# Output: fossil-mcp 0.1.0

fossil-mcp --help
# Shows usage information
```

Test with a repository:

```bash
# Create a test repository
fossil new test.fossil

# Start the server
fossil-mcp -R test.fossil
# Should start and wait for stdin input
```

## Next Steps

- [Quick Start](./quick-start.md) - Run your first commands
- [MCP Integration](./mcp-integration.md) - Connect to clients
