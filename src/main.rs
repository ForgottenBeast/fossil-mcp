//! # Fossil MCP Server Binary
//!
//! This is the main entry point for the Fossil MCP server. It creates a stdio-based
//! MCP server that exposes Fossil SCM wiki operations.
//!
//! ## Usage
//!
//! Start the server by specifying a repository file:
//!
//! ```bash
//! fossil-mcp -R /path/to/repo.fossil
//! ```
//!
//! The server communicates via JSON-RPC 2.0 over stdin/stdout, following the
//! [Model Context Protocol](https://modelcontextprotocol.io).
//!
//! ## Integration
//!
//! ### Claude Desktop
//!
//! Add to `claude_desktop_config.json`:
//!
//! ```json
//! {
//!   "mcpServers": {
//!     "fossil": {
//!       "command": "/usr/local/bin/fossil-mcp",
//!       "args": ["-R", "/path/to/repo.fossil"]
//!     }
//!   }
//! }
//! ```
//!
//! ### Custom MCP Client
//!
//! ```javascript
//! const server = spawn('fossil-mcp', ['-R', '/path/to/repo.fossil']);
//!
//! // Send initialize request
//! server.stdin.write(JSON.stringify({
//!   jsonrpc: '2.0',
//!   id: 1,
//!   method: 'initialize',
//!   params: { protocolVersion: '2024-11-05', ... }
//! }) + '\n');
//! ```
//!
//! ## Logging
//!
//! Logs are written to stderr to avoid interfering with JSON-RPC on stdout.
//! Set `RUST_LOG` environment variable to control log level:
//!
//! ```bash
//! RUST_LOG=debug fossil-mcp -R repo.fossil
//! ```

use anyhow::Result;
use clap::Parser;
use rmcp::ServiceExt;
use std::path::PathBuf;
use tokio::io::{stdin, stdout};

use fossil_mcp::FossilWiki;

/// Command-line arguments for the Fossil MCP server.
///
/// The server requires a path to a Fossil repository file and communicates
/// via stdio using the Model Context Protocol.
///
/// # Example
///
/// ```bash
/// fossil-mcp --repository /path/to/repo.fossil
/// fossil-mcp -R /path/to/repo.fossil  # Short form
/// ```
#[derive(Parser, Debug)]
#[command(author, version, about = "MCP server for Fossil SCM wiki operations", long_about = None)]
struct Args {
    /// Path to the Fossil repository file (e.g., /path/to/project.fossil)
    #[arg(short = 'R', long = "repository", value_name = "FILE")]
    repository: PathBuf,
}

#[tokio::main]
async fn main() -> Result<()> {
    // Initialize tracing subscriber for logging
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_writer(std::io::stderr) // Write logs to stderr to avoid interfering with JSON-RPC on stdout
        .init();

    // Parse command-line arguments
    let args = Args::parse();

    // Validate that the repository file exists
    if !args.repository.exists() {
        anyhow::bail!("Repository file does not exist: {:?}", args.repository);
    }

    // Create the wiki handler
    let wiki = FossilWiki::new(args.repository);

    // Create transport from stdin/stdout
    let transport = (stdin(), stdout());

    // Serve the MCP server
    let server = wiki.serve(transport).await?;

    // Wait for the server to complete
    server.waiting().await?;

    Ok(())
}
