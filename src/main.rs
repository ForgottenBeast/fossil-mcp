use anyhow::Result;
use clap::Parser;
use mcp_server::router::RouterService;
use mcp_server::{ByteTransport, Server};
use std::path::PathBuf;
use tokio::io::{stdin, stdout};

use fossil_mcp::{AppState, FossilRouter};

/// Command-line arguments for the MCP server
#[derive(Parser, Debug)]
#[command(author, version, about = "MCP server for Fossil SCM wiki operations", long_about = None)]
struct Args {
    /// Path to the Fossil repository file
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

    // Create shared state
    let state = AppState::new(args.repository);

    // Create the router
    let router = FossilRouter::new(state);

    // Wrap in RouterService
    let service = RouterService(router);

    // Create the server
    let server = Server::new(service);

    // Create transport from stdin/stdout
    let transport = ByteTransport::new(stdin(), stdout());

    // Run the server
    server.run(transport).await?;

    Ok(())
}
