use rmcp::{
    handler::server::{tool::ToolRouter, wrapper::Parameters, ServerHandler},
    model::{ServerCapabilities, ServerInfo},
    tool, tool_router, Json,
};

use crate::handlers;
use crate::state::AppState;
use crate::types::{ListWikiPagesArgs, ReadWikiPageArgs, WriteWikiPageArgs};

#[derive(Clone)]
pub struct FossilRouter {
    state: AppState,
    tool_router: ToolRouter<Self>,
}

#[tool_router]
impl FossilRouter {
    pub fn new(state: AppState) -> Self {
        Self {
            state,
            tool_router: ToolRouter::new(),
        }
    }

    /// List all wiki pages in the Fossil repository
    #[tool(description = "List all wiki pages in the Fossil repository")]
    async fn list_wiki_pages(
        &self,
        _args: Parameters<ListWikiPagesArgs>,
    ) -> Result<Json<crate::types::ListWikiPagesResponse>, String> {
        let result = handlers::list_wiki_pages(ListWikiPagesArgs {}, self.state.clone())
            .await
            .map_err(|e| e.to_string())?;
        Ok(Json(result))
    }

    /// Read the content of a wiki page
    #[tool(description = "Read the content of a wiki page")]
    async fn read_wiki_page(
        &self,
        args: Parameters<ReadWikiPageArgs>,
    ) -> Result<Json<crate::types::ReadWikiPageResponse>, String> {
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
    ) -> Result<Json<crate::types::WriteWikiPageResponse>, String> {
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
