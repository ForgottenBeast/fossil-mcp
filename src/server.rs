use anyhow::Result;
use rmcp::{
    Json,
    handler::server::{ServerHandler, tool::ToolRouter, wrapper::Parameters},
    model::{ServerCapabilities, ServerInfo},
    tool, tool_handler, tool_router,
};

use crate::server::types::{ReadWikiPageArgs, WriteWikiPageArgs};
use std::path::PathBuf;
use std::sync::Arc;
use tokio::process::Command;

pub mod types;

pub fn parse_wiki_list(output: &str) -> Vec<String> {
    output
        .lines()
        .map(|line| line.trim().to_string())
        .filter(|line| !line.is_empty())
        .collect()
}

#[derive(Clone)]
pub struct FossilWiki {
    repository: Arc<PathBuf>,
    tool_router: ToolRouter<Self>,
}

#[tool_router]
impl FossilWiki {
    pub fn new(path: PathBuf) -> Self {
        Self {
            repository: Arc::new(path),
            tool_router: Self::tool_router(),
        }
    }

    fn repository_path(&self) -> &PathBuf {
        &self.repository
    }

    /// List all wiki pages in the Fossil repository
    #[tool(description = "List all wiki pages in the Fossil repository")]
    pub async fn list_wiki_pages(&self) -> Result<Json<types::ListWikiPagesResponse>, String> {
        let output = Command::new("fossil")
            .args(["wiki", "-R", &self.repository_path().to_string_lossy(), "list"])
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
    pub async fn read_wiki_page(
        &self,
        args: Parameters<ReadWikiPageArgs>,
    ) -> Result<Json<types::ReadWikiPageResponse>, String> {
        let output = Command::new("fossil")
            .args(["wiki", "-R", &self.repository_path().to_string_lossy(), "export", &args.0.page_name])
            .output()
            .await
            .map_err(|e| e.to_string())?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("fossil wiki export failed: {}", stderr));
        }

        let content = String::from_utf8_lossy(&output.stdout);
        let content = content.trim_end_matches('\n').to_string();

        Ok(Json(types::ReadWikiPageResponse {
            page_name: args.0.page_name,
            content,
        }))
    }

    /// Create or update a wiki page
    #[tool(description = "Create or update a wiki page")]
    pub async fn write_wiki_page(
        &self,
        args: Parameters<WriteWikiPageArgs>,
    ) -> Result<Json<types::WriteWikiPageResponse>, String> {
        // Write content to a temporary file
        let temp_file = format!(
            "/tmp/fossil_wiki_{}.txt",
            args.0.page_name.replace("/", "_")
        );
        tokio::fs::write(&temp_file, &args.0.content)
            .await
            .map_err(|e| format!("Failed to write temporary file: {}", e))?;

        // Try "create" first, then "commit" if it fails (for existing pages)
        let mut cmd = Command::new("fossil");
        cmd.args(["wiki", "-R", &self.repository_path().to_string_lossy(), "create", &args.0.page_name, &temp_file]);

        if let Some(ref mt) = args.0.mimetype {
            cmd.arg(format!("--mimetype={}", mt));
        }

        let output = cmd
            .output()
            .await
            .map_err(|e| format!("Failed to execute fossil wiki create: {}", e))?;

        // If create failed with "already exists" or similar, try commit
        let mut final_output = output;
        if !final_output.status.success() {
            let stderr_str = String::from_utf8_lossy(&final_output.stderr);
            if stderr_str.contains("already exists") || stderr_str.contains("exists") {
                let mut cmd = Command::new("fossil");
                cmd.args(["wiki", "-R", &self.repository_path().to_string_lossy(), "commit", &args.0.page_name, &temp_file]);

                if let Some(ref mt) = args.0.mimetype {
                    cmd.arg(format!("--mimetype={}", mt));
                }

                final_output = cmd
                    .output()
                    .await
                    .map_err(|e| format!("Failed to execute fossil wiki commit: {}", e))?;
            }
        }

        // Clean up temp file
        let _ = tokio::fs::remove_file(&temp_file).await;

        if !final_output.status.success() {
            let stderr = String::from_utf8_lossy(&final_output.stderr);
            return Err(format!("fossil wiki operation failed: {}", stderr));
        }

        Ok(Json(types::WriteWikiPageResponse {
            success: true,
            page_name: args.0.page_name,
            message: "Wiki page written successfully".to_string(),
        }))
    }
}

#[tool_handler]
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_wiki_list_empty() {
        let output = "";
        let pages = parse_wiki_list(output);
        assert_eq!(pages, Vec::<String>::new());
    }

    #[test]
    fn test_parse_wiki_list_single_page() {
        let output = "HomePage";
        let pages = parse_wiki_list(output);
        assert_eq!(pages, vec!["HomePage"]);
    }

    #[test]
    fn test_parse_wiki_list_multiple_pages() {
        let output = "HomePage\nAbout\nDocumentation";
        let pages = parse_wiki_list(output);
        assert_eq!(pages, vec!["HomePage", "About", "Documentation"]);
    }

    #[test]
    fn test_parse_wiki_list_with_whitespace() {
        let output = "  HomePage  \n  About  \n  Documentation  ";
        let pages = parse_wiki_list(output);
        assert_eq!(pages, vec!["HomePage", "About", "Documentation"]);
    }

    #[test]
    fn test_parse_wiki_list_with_empty_lines() {
        let output = "HomePage\n\nAbout\n\n\nDocumentation\n";
        let pages = parse_wiki_list(output);
        assert_eq!(pages, vec!["HomePage", "About", "Documentation"]);
    }

    #[test]
    fn test_parse_wiki_list_with_special_characters() {
        let output = "HomePage\nAbout-Us\nUser_Guide\nFAQ";
        let pages = parse_wiki_list(output);
        assert_eq!(pages, vec!["HomePage", "About-Us", "User_Guide", "FAQ"]);
    }

    #[test]
    fn test_parse_wiki_list_with_slashes() {
        let output = "HomePage\nDocs/API\nDocs/CLI\nDocs/Web-UI";
        let pages = parse_wiki_list(output);
        assert_eq!(pages, vec!["HomePage", "Docs/API", "Docs/CLI", "Docs/Web-UI"]);
    }

    #[test]
    fn test_fossil_wiki_creation() {
        let path = std::path::PathBuf::from("/tmp/test.fossil");
        let wiki = FossilWiki::new(path.clone());
        assert_eq!(wiki.repository_path(), &path);
    }
}
