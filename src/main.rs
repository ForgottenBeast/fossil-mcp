use anyhow::Result;
use clap::Parser;
use rmcp::ServiceExt;
use std::path::PathBuf;
use tokio::io::{stdin, stdout};

use fossil_mcp::FossilWiki;

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
