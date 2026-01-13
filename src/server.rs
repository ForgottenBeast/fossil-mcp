use anyhow::Result;
use rmcp::{
    handler::server::{wrapper::Parameters, ServerHandler},
    model::{ServerCapabilities, ServerInfo},
    tool, tool_router, Json,
};

use std::sync::Arc;
use std::path::PathBuf;
use tokio::process::Command;
use crate::server::types::{ReadWikiPageArgs, WriteWikiPageArgs};

pub mod types;

pub fn parse_wiki_list(output: &str) -> Vec<String> {
    output
        .lines()
        .map(|line| line.trim().to_string())
        .filter(|line| !line.is_empty())
        .collect()
}


#[derive(Clone)]
pub struct FossilWiki(#[allow(dead_code)] Arc<PathBuf>);

#[tool_router]
impl FossilWiki {
    pub fn new(path: PathBuf) -> Self {
        Self(Arc::new(path))
    }

    fn repository_path(&self) -> &PathBuf {
        &self.0
    }

    /// List all wiki pages in the Fossil repository
    #[tool(description = "List all wiki pages in the Fossil repository")]
    async fn list_wiki_pages(&self) -> Result<Json<types::ListWikiPagesResponse>, String> {
        let output = Command::new("fossil")
            .arg("-R")
            .arg(self.repository_path())
            .args(["wiki", "list"])
            .output()
            .await
            .map_err(|e| e.to_string())?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("fossil wiki list failed: {}", stderr));
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        let pages = parse_wiki_list(&stdout);

        Ok(Json(types::ListWikiPagesResponse { pages }))
    }

    /// Read the content of a wiki page
    #[tool(description = "Read the content of a wiki page")]
    async fn read_wiki_page(
        &self,
        args: Parameters<ReadWikiPageArgs>,
    ) -> Result<Json<types::ReadWikiPageResponse>, String> {
        let output = Command::new("fossil")
            .arg("-R")
            .arg(self.repository_path())
            .args(["wiki", "export", &args.0.page_name])
            .output()
            .await
            .map_err(|e| e.to_string())?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("fossil wiki export failed: {}", stderr));
        }

        let content = String::from_utf8_lossy(&output.stdout).to_string();

        Ok(Json(types::ReadWikiPageResponse {
            page_name: args.0.page_name,
            content,
        }))
    }

    /// Create or update a wiki page
    #[tool(description = "Create or update a wiki page")]
    async fn write_wiki_page(
        &self,
        args: Parameters<WriteWikiPageArgs>,
    ) -> Result<Json<types::WriteWikiPageResponse>, String> {
        // Write content to a temporary file
        let temp_file = format!("/tmp/fossil_wiki_{}.txt", args.0.page_name.replace("/", "_"));
        tokio::fs::write(&temp_file, &args.0.content)
            .await
            .map_err(|e| format!("Failed to write temporary file: {}", e))?;

        // Build the command
        let mut cmd = Command::new("fossil");
        cmd.arg("-R")
            .arg(self.repository_path())
            .args(["wiki", "commit", &args.0.page_name, &temp_file]);

        if let Some(ref mt) = args.0.mimetype {
            cmd.arg(format!("--mimetype={}", mt));
        }

        let output = cmd
            .output()
            .await
            .map_err(|e| format!("Failed to execute fossil wiki commit: {}", e))?;

        // Clean up temp file
        let _ = tokio::fs::remove_file(&temp_file).await;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("fossil wiki commit failed: {}", stderr));
        }

        Ok(Json(types::WriteWikiPageResponse {
            success: true,
            page_name: args.0.page_name,
            message: "Wiki page written successfully".to_string(),
        }))
    }
}

impl ServerHandler for FossilWiki {
    fn get_info(&self) -> ServerInfo {
        ServerInfo {
            protocol_version: Default::default(),
            capabilities: ServerCapabilities::builder().enable_tools().build(),
            server_info: Default::default(),
            instructions: Some("MCP server for accessing Fossil SCM wiki pages".to_string()),
        }
    }
}
