use anyhow::{Context, Result};
use clap::Parser;
use mcp_server::{
    router::RouterService, serve, ByteTransport, Server, Tool,
};
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::path::PathBuf;
use std::process::Command;
use std::sync::Arc;

#[derive(Parser, Debug)]
#[command(author, version, about = "MCP server for Fossil SCM wiki operations", long_about = None)]
struct Args {
    /// Path to the Fossil repository file
    #[arg(short = 'R', long = "repository", value_name = "FILE")]
    repository: PathBuf,
}

#[derive(Clone)]
struct AppState {
    repository_path: Arc<PathBuf>,
}

#[derive(Debug, Serialize, Deserialize)]
struct ListWikiPagesArgs {}

#[derive(Debug, Serialize, Deserialize)]
struct ReadWikiPageArgs {
    page_name: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct WriteWikiPageArgs {
    page_name: String,
    content: String,
    #[serde(default)]
    mimetype: Option<String>,
}

async fn list_wiki_pages(_args: ListWikiPagesArgs, state: AppState) -> Result<serde_json::Value> {
    let output = Command::new("fossil")
        .arg("-R")
        .arg(state.repository_path.as_ref())
        .args(["wiki", "list"])
        .output()
        .context("Failed to execute fossil wiki list")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        anyhow::bail!("fossil wiki list failed: {}", stderr);
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let pages: Vec<String> = stdout
        .lines()
        .map(|line| line.trim().to_string())
        .filter(|line| !line.is_empty())
        .collect();

    Ok(json!({
        "pages": pages,
        "count": pages.len()
    }))
}

async fn read_wiki_page(args: ReadWikiPageArgs, state: AppState) -> Result<serde_json::Value> {
    let output = Command::new("fossil")
        .arg("-R")
        .arg(state.repository_path.as_ref())
        .args(["wiki", "export", &args.page_name])
        .output()
        .context("Failed to execute fossil wiki export")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        anyhow::bail!("fossil wiki export failed: {}", stderr);
    }

    let content = String::from_utf8_lossy(&output.stdout).to_string();

    Ok(json!({
        "page_name": args.page_name,
        "content": content
    }))
}

async fn write_wiki_page(args: WriteWikiPageArgs, state: AppState) -> Result<serde_json::Value> {
    // Write content to a temporary file
    let temp_file = format!("/tmp/fossil_wiki_{}.txt", args.page_name.replace("/", "_"));
    std::fs::write(&temp_file, &args.content)
        .context("Failed to write temporary file")?;

    // Build the command
    let mut cmd = Command::new("fossil");
    cmd.arg("-R")
        .arg(state.repository_path.as_ref())
        .args(["wiki", "commit", &args.page_name, &temp_file]);

    if let Some(ref mt) = args.mimetype {
        cmd.arg(format!("--mimetype={}", mt));
    }

    let output = cmd.output()
        .context("Failed to execute fossil wiki commit")?;

    // Clean up temp file
    let _ = std::fs::remove_file(&temp_file);

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        anyhow::bail!("fossil wiki commit failed: {}", stderr);
    }

    Ok(json!({
        "success": true,
        "page_name": args.page_name,
        "message": "Wiki page written successfully"
    }))
}

#[tokio::main]
async fn main() -> Result<()> {
    // Parse command-line arguments
    let args = Args::parse();

    // Validate that the repository file exists
    if !args.repository.exists() {
        anyhow::bail!("Repository file does not exist: {:?}", args.repository);
    }

    // Create shared state
    let state = AppState {
        repository_path: Arc::new(args.repository),
    };

    let list_pages_tool = Tool::new(
        "list_wiki_pages",
        "List all wiki pages in the Fossil repository",
        json!({
            "type": "object",
            "properties": {},
            "required": []
        }),
    )
    .with_handler_and_state(state.clone(), list_wiki_pages);

    let read_page_tool = Tool::new(
        "read_wiki_page",
        "Read the content of a wiki page",
        json!({
            "type": "object",
            "properties": {
                "page_name": {
                    "type": "string",
                    "description": "The name of the wiki page to read"
                }
            },
            "required": ["page_name"]
        }),
    )
    .with_handler_and_state(state.clone(), read_wiki_page);

    let write_page_tool = Tool::new(
        "write_wiki_page",
        "Create or update a wiki page",
        json!({
            "type": "object",
            "properties": {
                "page_name": {
                    "type": "string",
                    "description": "The name of the wiki page to create or update"
                },
                "content": {
                    "type": "string",
                    "description": "The content to write to the wiki page"
                },
                "mimetype": {
                    "type": "string",
                    "description": "The MIME type of the content (text/x-fossil-wiki, text/x-markdown, or text/plain)",
                    "enum": ["text/x-fossil-wiki", "text/x-markdown", "text/plain"]
                }
            },
            "required": ["page_name", "content"]
        }),
    )
    .with_handler_and_state(state.clone(), write_wiki_page);

    let server = Server::new("fossil-mcp")
        .with_tool(list_pages_tool)
        .with_tool(read_page_tool)
        .with_tool(write_page_tool);

    let service = RouterService::new(server);
    let transport = ByteTransport::from_stdio();

    serve(service, transport).await?;

    Ok(())
}
