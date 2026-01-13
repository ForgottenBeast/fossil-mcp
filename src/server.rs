use anyhow::{Context, Result};
use rmcp::{
    handler::server::{tool::ToolRouter, wrapper::Parameters, ServerHandler},
    model::{ServerCapabilities, ServerInfo},
    tool, tool_router, Json,
};

use tokio::process::Command;
use crate::types::{ListWikiPagesArgs, ReadWikiPageArgs, WriteWikiPageArgs};

pub mod types;

pub fn parse_wiki_list(output: &str) -> Vec<String> {
    output
        .lines()
        .map(|line| line.trim().to_string())
        .filter(|line| !line.is_empty())
        .collect()
}


#[derive(Clone)]
pub struct FossilWiki(Arc<PathBuf>),

#[tool_router]
impl FossilWiki {
    pub fn new(path: PathBuf) -> Self {
        Self(Arc::new(path))
    }

    /// List all wiki pages in the Fossil repository
    #[tool(description = "List all wiki pages in the Fossil repository")]
    async fn list_wiki_pages(
        &self,
    ) -> Result<Json<types::ListWikiPagesResponse>, String> {
        let output = Command::new("fossil")
            .arg("-R")
            .arg(state.repository_path.as_ref())
            .args(["wiki", "list"])
            .output()
            .await
            .map_err(|e| e.to_string())?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        anyhow::bail!("fossil wiki list failed: {}", stderr);
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let pages = parse_wiki_list(&stdout);

        Ok(Json(result))
    }

    /// Read the content of a wiki page
    #[tool(description = "Read the content of a wiki page")]
    async fn read_wiki_page(
        &self,
        args: Parameters<ReadWikiPageArgs>,
    ) -> Result<Json<types::ReadWikiPageResponse>, String> {
        let result = handlers::read_wiki_page(args.0, self.state.clone())
            .await
            .map_err(|e| e.to_string())?;
        Ok(Json(result))
    }

    /// Create or update a wiki page
    #[tool(description = "Create or update a wiki page")]
    async fn write_wiki_page(
        &self,
        args: Parameters<WriteWikiPageArgs>,
    ) -> Result<Json<types::WriteWikiPageResponse>, String> {
        let result = handlers::write_wiki_page(args.0, self.state.clone())
            .await
            .map_err(|e| e.to_string())?;
        Ok(Json(result))
    }
}

impl ServerHandler for FossilRouter {
    fn get_info(&self) -> ServerInfo {
        ServerInfo {
            protocol_version: Default::default(),
            capabilities: ServerCapabilities::builder().enable_tools().build(),
            server_info: Default::default(),
            instructions: Some("MCP server for accessing Fossil SCM wiki pages".to_string()),
        }
    }
}
