use std::{future::Future, pin::Pin};

use mcp_server::router::{CapabilitiesBuilder, Router};
use mcp_spec::{
    content::Content,
    handler::{PromptError, ResourceError, ToolError},
    prompt::Prompt,
    protocol::ServerCapabilities,
    tool::Tool,
};
use serde_json::Value;

use crate::handlers;
use crate::state::AppState;

#[derive(Clone)]
pub struct FossilRouter {
    state: AppState,
}

impl FossilRouter {
    pub fn new(state: AppState) -> Self {
        Self { state }
    }
}

impl Router for FossilRouter {
    fn name(&self) -> String {
        "fossil-mcp".to_string()
    }

    fn instructions(&self) -> String {
        "MCP server for accessing Fossil SCM wiki pages".to_string()
    }

    fn capabilities(&self) -> ServerCapabilities {
        CapabilitiesBuilder::new()
            .with_tools(false)
            .build()
    }

    fn list_tools(&self) -> Vec<Tool> {
        vec![
            Tool {
                name: "list_wiki_pages".to_string(),
                description: "List all wiki pages in the Fossil repository".to_string(),
                input_schema: serde_json::json!({
                    "type": "object",
                    "properties": {},
                    "required": []
                }),
            },
            Tool {
                name: "read_wiki_page".to_string(),
                description: "Read the content of a wiki page".to_string(),
                input_schema: serde_json::json!({
                    "type": "object",
                    "properties": {
                        "page_name": {
                            "type": "string",
                            "description": "The name of the wiki page to read"
                        }
                    },
                    "required": ["page_name"]
                }),
            },
            Tool {
                name: "write_wiki_page".to_string(),
                description: "Create or update a wiki page".to_string(),
                input_schema: serde_json::json!({
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
            },
        ]
    }

    fn call_tool(
        &self,
        tool_name: &str,
        arguments: Value,
    ) -> Pin<Box<dyn Future<Output = Result<Vec<Content>, ToolError>> + Send + 'static>> {
        let state = self.state.clone();
        let tool_name = tool_name.to_string();

        Box::pin(async move {
            match tool_name.as_str() {
                "list_wiki_pages" => {
                    let args = serde_json::from_value(arguments)
                        .map_err(|e| ToolError::InvalidParameters(e.to_string()))?;

                    let result = handlers::list_wiki_pages(args, state)
                        .await
                        .map_err(|e| ToolError::ExecutionError(e.to_string()))?;

                    Ok(vec![Content::text(result.to_string())])
                }
                "read_wiki_page" => {
                    let args = serde_json::from_value(arguments)
                        .map_err(|e| ToolError::InvalidParameters(e.to_string()))?;

                    let result = handlers::read_wiki_page(args, state)
                        .await
                        .map_err(|e| ToolError::ExecutionError(e.to_string()))?;

                    Ok(vec![Content::text(result.to_string())])
                }
                "write_wiki_page" => {
                    let args = serde_json::from_value(arguments)
                        .map_err(|e| ToolError::InvalidParameters(e.to_string()))?;

                    let result = handlers::write_wiki_page(args, state)
                        .await
                        .map_err(|e| ToolError::ExecutionError(e.to_string()))?;

                    Ok(vec![Content::text(result.to_string())])
                }
                _ => Err(ToolError::NotFound(format!("Unknown tool: {}", tool_name))),
            }
        })
    }

    fn list_resources(&self) -> Vec<mcp_spec::resource::Resource> {
        vec![]
    }

    fn read_resource(
        &self,
        _uri: &str,
    ) -> Pin<Box<dyn Future<Output = Result<String, ResourceError>> + Send + 'static>> {
        Box::pin(async { Err(ResourceError::NotFound("Resources not supported".to_string())) })
    }

    fn list_prompts(&self) -> Vec<Prompt> {
        vec![]
    }

    fn get_prompt(
        &self,
        _prompt_name: &str,
    ) -> Pin<Box<dyn Future<Output = Result<String, PromptError>> + Send + 'static>> {
        Box::pin(async { Err(PromptError::NotFound("Prompts not supported".to_string())) })
    }
}
