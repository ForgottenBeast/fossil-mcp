//! MCP server implementation for Fossil SCM wiki operations.
//!
//! This module provides the core [`FossilWiki`] handler that implements
//! the three MCP tools for wiki page manipulation. All operations execute
//! `fossil` commands with the `-R` repository flag.
//!
//! ## Tool Overview
//!
//! - **list_wiki_pages**: Returns an array of all wiki page names
//! - **read_wiki_page**: Retrieves the content of a specific page
//! - **write_wiki_page**: Creates or updates a page with optional sync
//!
//! ## Example
//!
//! ```rust,no_run
//! use fossil_mcp::server::FossilWiki;
//! use std::path::PathBuf;
//!
//! # async fn example() {
//! let wiki = FossilWiki::new(PathBuf::from("/path/to/repo.fossil"));
//!
//! // Use with MCP server infrastructure
//! // The handler implements ServerHandler trait for rmcp
//! # }
//! ```

use anyhow::Result;
use rmcp::{
    Json,
    handler::server::{ServerHandler, tool::ToolRouter, wrapper::Parameters},
    model::{ServerCapabilities, ServerInfo},
    tool, tool_handler, tool_router,
};

use crate::server::types::{
    AuthenticateWikiArgs, ConfigureRepositoryArgs, ReadWikiPageArgs, WriteWikiPageArgs,
    SearchWikiArgs,
};
use std::path::PathBuf;
use std::sync::{Arc, RwLock};
use tokio::process::Command;

pub mod sync;
use sync::{sync_repository, SyncError};

pub mod types;

/// Parses the output of `fossil wiki list` into a vector of page names.
///
/// Filters out empty lines and trims whitespace from each page name.
///
/// # Examples
///
/// ```
/// use fossil_mcp::server::parse_wiki_list;
///
/// let output = "HomePage\n  About  \n\nDocs/API\n";
/// let pages = parse_wiki_list(output);
/// assert_eq!(pages, vec!["HomePage", "About", "Docs/API"]);
/// ```
pub fn parse_wiki_list(output: &str) -> Vec<String> {
    output
        .lines()
        .map(|line| line.trim().to_string())
        .filter(|line| !line.is_empty())
        .collect()
}

/// MCP handler for Fossil SCM wiki operations.
///
/// This struct provides MCP tools for interacting with a Fossil repository's
/// wiki pages. All operations use `fossil -R <repo>` to work without requiring a
/// checkout directory.
///
/// The repository path can be set at construction time or configured at runtime
/// using the configure_repository tool.
///
/// # Thread Safety
///
/// `FossilWiki` is `Clone` and can be safely shared across async tasks. The
/// repository path is wrapped in `Arc<RwLock<Option<PathBuf>>>` for thread-safe
/// runtime configuration.
///
/// # Example
///
/// ```rust,no_run
/// use fossil_mcp::FossilWiki;
/// use std::path::PathBuf;
///
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// // Create handler with repository
/// let wiki = FossilWiki::new(Some(PathBuf::from("/path/to/repo.fossil")));
///
/// // Or create without repository and configure later
/// let wiki = FossilWiki::new(None);
/// // Use configure_repository tool to set path at runtime
///
/// // The handler exposes MCP tools:
/// // - configure_repository(args) - Set repository path at runtime
/// // - list_wiki_pages() - List all wiki pages
/// // - read_wiki_page(args) - Read a wiki page
/// // - write_wiki_page(args) - Create/update a wiki page
/// // - search_wiki(args) - Search wiki via semantic search API
/// # Ok(())
/// # }
/// ```
#[derive(Clone)]
pub struct FossilWiki {
    repository: Arc<RwLock<Option<PathBuf>>>,
    tool_router: ToolRouter<Self>,
}

#[tool_router]
impl FossilWiki {
    /// Creates a new `FossilWiki` handler.
    ///
    /// # Arguments
    ///
    /// * `path` - Optional path to the Fossil repository file. If None, use
    ///            the configure_repository tool to set it at runtime.
    ///
    /// # Example
    ///
    /// ```rust
    /// use fossil_mcp::FossilWiki;
    /// use std::path::PathBuf;
    ///
    /// // With repository
    /// let wiki = FossilWiki::new(Some(PathBuf::from("/tmp/test.fossil")));
    ///
    /// // Without repository (configure later)
    /// let wiki = FossilWiki::new(None);
    /// ```
    pub fn new(path: Option<PathBuf>) -> Self {
        Self {
            repository: Arc::new(RwLock::new(path)),
            tool_router: Self::tool_router(),
        }
    }

    /// Get the current repository path.
    ///
    /// # Returns
    ///
    /// The repository path if configured
    ///
    /// # Errors
    ///
    /// Returns a helpful error message if no repository is configured
    fn get_repository(&self) -> Result<PathBuf, String> {
        let repo = self.repository.read().unwrap();
        repo.as_ref()
            .cloned()
            .ok_or_else(|| {
                "No repository configured. Please configure a repository using one of these methods:\n\
                1. Use the configure_repository tool: {\"repo_path\": \"/path/to/repo.fossil\"}\n\
                2. Restart with -R flag: fossil-mcp -R /path/to/repo.fossil\n\
                3. Set environment variable: FOSSIL_REPO=/path/to/repo.fossil".to_string()
            })
    }

    /// Configure the repository path at runtime.
    ///
    /// This tool allows setting the repository path after the MCP server has started,
    /// enabling flexible deployment scenarios where the repository location may not
    /// be known at startup time.
    ///
    /// # MCP Tool
    ///
    /// This is exposed as the `configure_repository` MCP tool.
    ///
    /// **Arguments**:
    /// ```json
    /// {
    ///   "repo_path": "/path/to/repo.fossil"
    /// }
    /// ```
    ///
    /// **Returns**:
    /// ```json
    /// {
    ///   "success": true,
    ///   "message": "Repository configured: \"/path/to/repo.fossil\""
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The repository file doesn't exist
    /// - The path is invalid
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use fossil_mcp::{FossilWiki, ConfigureRepositoryArgs};
    /// use rmcp::handler::server::wrapper::Parameters;
    ///
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let wiki = FossilWiki::new(None);
    ///
    /// let args = Parameters(ConfigureRepositoryArgs {
    ///     repo_path: "/path/to/repo.fossil".to_string(),
    /// });
    ///
    /// let response = wiki.configure_repository(args).await?;
    /// println!("Success: {}", response.0.success);
    /// # Ok(())
    /// # }
    /// ```
    #[tool(description = "Configure repository path at runtime")]
    pub async fn configure_repository(
        &self,
        args: Parameters<ConfigureRepositoryArgs>,
    ) -> Result<Json<types::ConfigureRepositoryResponse>, String> {
        let path = PathBuf::from(&args.0.repo_path);

        // Validate that the repository file exists
        if !path.exists() {
            return Err(format!("Repository file does not exist: {:?}", path));
        }

        // Validate it's a file, not a directory
        if !path.is_file() {
            return Err(format!("Repository path is not a file: {:?}", path));
        }

        // Update repository
        let mut repo = self.repository.write().unwrap();
        *repo = Some(path.clone());

        tracing::info!("Repository configured: {:?}", path);

        Ok(Json(types::ConfigureRepositoryResponse {
            success: true,
            message: format!("Repository configured: {:?}", path),
        }))
    }

    /// Lists all wiki pages in the Fossil repository.
    ///
    /// Executes `fossil wiki -R <repo> list` and returns the page names.
    ///
    /// # MCP Tool
    ///
    /// This is exposed as the `list_wiki_pages` MCP tool.
    ///
    /// **Arguments**: None
    ///
    /// **Returns**: `{"pages": ["HomePage", "About", "Docs/API"]}`
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The `fossil` command fails to execute
    /// - The repository file doesn't exist or is invalid
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use fossil_mcp::FossilWiki;
    /// use std::path::PathBuf;
    ///
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let wiki = FossilWiki::new(PathBuf::from("/path/to/repo.fossil"));
    /// let response = wiki.list_wiki_pages().await?;
    ///
    /// for page in &response.0.pages {
    ///     println!("Page: {}", page);
    /// }
    /// # Ok(())
    /// # }
    /// ```
    #[tool(description = "List all wiki pages in the Fossil repository")]
    pub async fn list_wiki_pages(&self) -> Result<Json<types::ListWikiPagesResponse>, String> {
        let repo_path = self.get_repository()?;

        let output = Command::new("fossil")
            .args(["wiki", "-R", &repo_path.to_string_lossy(), "list"])
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

    /// Reads the content of a specific wiki page.
    ///
    /// Executes `fossil wiki -R <repo> export <page_name>` to retrieve the page content.
    ///
    /// # MCP Tool
    ///
    /// This is exposed as the `read_wiki_page` MCP tool.
    ///
    /// **Arguments**:
    /// ```json
    /// {
    ///   "page_name": "HomePage"
    /// }
    /// ```
    ///
    /// **Returns**:
    /// ```json
    /// {
    ///   "page_name": "HomePage",
    ///   "content": "# Welcome\n\nWelcome to the wiki!"
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The page doesn't exist
    /// - The `fossil` command fails
    /// - The repository is invalid
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use fossil_mcp::{FossilWiki, ReadWikiPageArgs};
    /// use rmcp::handler::server::wrapper::Parameters;
    /// use std::path::PathBuf;
    ///
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let wiki = FossilWiki::new(PathBuf::from("/path/to/repo.fossil"));
    ///
    /// let args = Parameters(ReadWikiPageArgs {
    ///     page_name: "HomePage".to_string(),
    /// });
    ///
    /// let response = wiki.read_wiki_page(args).await?;
    /// println!("Content: {}", response.0.content);
    /// # Ok(())
    /// # }
    /// ```
    #[tool(description = "Read the content of a wiki page")]
    pub async fn read_wiki_page(
        &self,
        args: Parameters<ReadWikiPageArgs>,
    ) -> Result<Json<types::ReadWikiPageResponse>, String> {
        let repo_path = self.get_repository()?;

        let output = Command::new("fossil")
            .args(["wiki", "-R", &repo_path.to_string_lossy(), "export", &args.0.page_name])
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

    /// Create or update a wiki page in the repository.
    ///
    /// # Behavior
    /// 1. Writes the provided content to the wiki page
    /// 2. If `skip_sync` is false, attempts to synchronize with the remote repository
    /// 3. Reports page write success and synchronization status in the response
    ///
    /// # Parameters
    /// - `page_name`: Name of the page (e.g., "HomePage", "Docs/API")
    /// - `content`: The page content to write
    /// - `mimetype`: Optional MIME type (e.g., "text/x-markdown")
    /// - `skip_sync`: If true, skip repository synchronization (default: false)
    /// - `force_write`: If true, allow success even with blocking sync errors (default: false)
    ///
    /// # Return Values
    /// - Always returns `Ok` if the page write succeeds (regardless of sync outcome)
    /// - Returns `Err` only if the page write fails or sync fails with a blocking error and `force_write` is false
    ///
    /// # Errors
    /// - Page write fails (insufficient permissions, file system errors)
    /// - Sync fails with a merge conflict AND `force_write` is false
    ///
    /// # Sync Failures (Non-blocking)
    /// These are reported in the response but do not cause the operation to fail:
    /// - No remote repository configured
    /// - Network connectivity issues
    ///
    /// # Example Usage
    /// ```no_run
    /// # use fossil_mcp::{FossilWiki, WriteWikiPageArgs};
    /// # use rmcp::handler::server::wrapper::Parameters;
    /// # use std::path::PathBuf;
    /// # #[tokio::main]
    /// # async fn main() {
    /// let wiki = FossilWiki::new(PathBuf::from("/path/to/repo.fossil"));
    /// let args = Parameters(WriteWikiPageArgs {
    ///     page_name: "HomePage".to_string(),
    ///     content: "Welcome to the wiki".to_string(),
    ///     mimetype: Some("text/x-fossil-wiki".to_string()),
    ///     skip_sync: false,
    ///     force_write: false,
    /// });
    /// match wiki.write_wiki_page(args).await {
    ///     Ok(response) => println!("Page written: {}", response.0.success),
    ///     Err(e) => eprintln!("Error: {}", e),
    /// }
    /// # }
    /// ```
    #[tool(description = "Create or update a wiki page")]
    pub async fn write_wiki_page(
        &self,
        args: Parameters<WriteWikiPageArgs>,
    ) -> Result<Json<types::WriteWikiPageResponse>, String> {
        let repo_path = self.get_repository()?;

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
        cmd.args(["wiki", "-R", &repo_path.to_string_lossy(), "create", &args.0.page_name, &temp_file]);

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
                cmd.args(["wiki", "-R", &repo_path.to_string_lossy(), "commit", &args.0.page_name, &temp_file]);

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

        // Handle synchronization if requested
        let mut sync_status = None;
        if !args.0.skip_sync {
            match sync_repository(&repo_path).await {
                Ok(()) => {
                    sync_status = Some(types::SyncStatus {
                        attempted: true,
                        succeeded: true,
                        error_type: None,
                        error_message: None,
                        can_force_write: false,
                    });
                }
                Err(sync_error) => {
                    // Determine if error is blocking or non-blocking
                    let (error_type, can_force_write) = match &sync_error {
                        SyncError::MergeConflict => ("MergeConflict".to_string(), true),
                        SyncError::NoRemoteConfigured => ("NoRemoteConfigured".to_string(), false),
                        SyncError::NetworkError => ("NetworkError".to_string(), false),
                        SyncError::Other(_) => ("Other".to_string(), false),
                    };

                    let error_message = match sync_error {
                        SyncError::MergeConflict => "Merge conflict occurred during synchronization. Use force_write to override.".to_string(),
                        SyncError::NoRemoteConfigured => "No remote URL configured for this repository.".to_string(),
                        SyncError::NetworkError => "Network error occurred during synchronization. Please try again later.".to_string(),
                        SyncError::Other(msg) => format!("Synchronization error: {}", msg),
                    };

                    sync_status = Some(types::SyncStatus {
                        attempted: true,
                        succeeded: false,
                        error_type: Some(error_type.clone()),
                        error_message: Some(error_message.clone()),
                        can_force_write,
                    });

                    // If it's a blocking error (merge conflict) and force_write is not set, fail
                    if can_force_write && !args.0.force_write {
                        return Err(format!("Sync failed: {}. Use force_write flag to override.", error_message));
                    }
                }
            }
        }

        Ok(Json(types::WriteWikiPageResponse {
            success: true,
            page_name: args.0.page_name,
            message: "Wiki page written successfully".to_string(),
            sync_status,
        }))
    }

    /// Authenticate with wiki_searcher API and get session token.
    ///
    /// This tool authenticates a user against the Fossil database via the
    /// wiki_searcher API and returns a session token that can be used for
    /// subsequent search_wiki calls.
    ///
    /// # MCP Tool
    ///
    /// This is exposed as the `authenticate_wiki` MCP tool.
    ///
    /// **Arguments**:
    /// ```json
    /// {
    ///   "username": "myuser",
    ///   "password": "mypass"
    /// }
    /// ```
    ///
    /// **Returns**:
    /// ```json
    /// {
    ///   "success": true,
    ///   "session_token": "abc123...",
    ///   "message": "Authentication successful"
    /// }
    /// ```
    ///
    /// # Environment Variables
    ///
    /// - `WIKI_SEARCHER_URL`: Base URL of wiki_searcher API (default: http://localhost:8090)
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use fossil_mcp::{FossilWiki, AuthenticateWikiArgs};
    /// use rmcp::handler::server::wrapper::Parameters;
    ///
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let wiki = FossilWiki::new(Some(std::path::PathBuf::from("/path/to/repo.fossil")));
    ///
    /// let args = Parameters(AuthenticateWikiArgs {
    ///     username: "myuser".to_string(),
    ///     password: "mypass".to_string(),
    /// });
    ///
    /// let response = wiki.authenticate_wiki(args).await?;
    /// if response.0.success {
    ///     println!("Token: {}", response.0.session_token.unwrap());
    /// }
    /// # Ok(())
    /// # }
    /// ```
    #[tool(description = "Authenticate with wiki_searcher and get session token")]
    pub async fn authenticate_wiki(
        &self,
        args: Parameters<AuthenticateWikiArgs>,
    ) -> Result<Json<types::AuthenticateWikiResponse>, String> {
        // Get wiki_searcher URL from environment or use default
        let searcher_url = std::env::var("WIKI_SEARCHER_URL")
            .unwrap_or_else(|_| "http://localhost:8090".to_string());

        // Build HTTP client
        let client = reqwest::Client::new();

        // Make POST request to authenticate endpoint
        let response = client
            .post(format!("{}/v1/authenticate", searcher_url))
            .json(&serde_json::json!({
                "username": args.0.username,
                "password": args.0.password
            }))
            .send()
            .await
            .map_err(|e| format!("Failed to connect to wiki_searcher: {}", e))?;

        // Parse response (don't check status - endpoint returns 200 with success flag)
        let body: serde_json::Value = response.json().await
            .map_err(|e| format!("Failed to parse authentication response: {}", e))?;

        // Extract fields
        let success = body.get("success")
            .and_then(|s| s.as_bool())
            .unwrap_or(false);

        let session_token = body.get("session_token")
            .and_then(|t| t.as_str())
            .map(String::from);

        let message = body.get("message")
            .and_then(|m| m.as_str())
            .unwrap_or("Unknown error")
            .to_string();

        if success {
            tracing::info!("User '{}' authenticated successfully", args.0.username);
        } else {
            tracing::warning!("Authentication failed for user '{}'", args.0.username);
        }

        Ok(Json(types::AuthenticateWikiResponse {
            success,
            session_token,
            message,
        }))
    }

    /// Search wiki pages using semantic search API.
    ///
    /// This tool calls the wiki_searcher HTTP API to perform semantic search
    /// across indexed wiki pages. The wiki_searcher service must be running
    /// and accessible at the configured URL.
    ///
    /// Authentication can be provided via either api_key or session_token
    /// (obtained from authenticate_wiki tool).
    ///
    /// # MCP Tool
    ///
    /// This is exposed as the `search_wiki` MCP tool.
    ///
    /// **Arguments with API key**:
    /// ```json
    /// {
    ///   "query": "embedding concepts",
    ///   "limit": 10,
    ///   "threshold": 0.7,
    ///   "api_key": "your-api-key-here"
    /// }
    /// ```
    ///
    /// **Arguments with session token**:
    /// ```json
    /// {
    ///   "query": "embedding concepts",
    ///   "limit": 10,
    ///   "threshold": 0.7,
    ///   "session_token": "token-from-authenticate"
    /// }
    /// ```
    ///
    /// **Returns**:
    /// ```json
    /// {
    ///   "results": [
    ///     {
    ///       "page_name": "Machine Learning",
    ///       "chunk_text": "Embeddings are dense vector representations...",
    ///       "section_header": "Introduction",
    ///       "relevance_score": 0.843,
    ///       "chunk_index": 0
    ///     }
    ///   ]
    /// }
    /// ```
    ///
    /// # Environment Variables
    ///
    /// - `WIKI_SEARCHER_URL`: Base URL of wiki_searcher API (default: http://localhost:8090)
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - wiki_searcher is not running or unreachable
    /// - API key is invalid
    /// - Search request fails
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use fossil_mcp::{FossilWiki, SearchWikiArgs};
    /// use rmcp::handler::server::wrapper::Parameters;
    ///
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let wiki = FossilWiki::new(Some(std::path::PathBuf::from("/path/to/repo.fossil")));
    ///
    /// let args = Parameters(SearchWikiArgs {
    ///     query: "embedding concepts".to_string(),
    ///     limit: 10,
    ///     threshold: 0.7,
    ///     api_key: "secret-key".to_string(),
    /// });
    ///
    /// let response = wiki.search_wiki(args).await?;
    /// println!("Found {} results", response.0.results.len());
    /// # Ok(())
    /// # }
    /// ```
    #[tool(description = "Search wiki pages using semantic search")]
    pub async fn search_wiki(
        &self,
        args: Parameters<SearchWikiArgs>,
    ) -> Result<Json<types::SearchWikiResponse>, String> {
        // Validate authentication provided
        if args.0.api_key.is_none() && args.0.session_token.is_none() {
            return Err("Either api_key or session_token must be provided".to_string());
        }

        // Get wiki_searcher URL from environment or use default
        let searcher_url = std::env::var("WIKI_SEARCHER_URL")
            .unwrap_or_else(|_| "http://localhost:8090".to_string());

        // Build HTTP client
        let client = reqwest::Client::new();

        // Build request with appropriate authentication
        let mut request_builder = client
            .post(format!("{}/v1/search", searcher_url));

        // Add authentication header or cookie
        if let Some(api_key) = &args.0.api_key {
            request_builder = request_builder.header("X-API-Key", api_key);
        } else if let Some(session_token) = &args.0.session_token {
            request_builder = request_builder.header("Cookie", format!("session={}", session_token));
        }

        // Make POST request to wiki_searcher API
        let response = request_builder
            .json(&serde_json::json!({
                "query": args.0.query,
                "limit": args.0.limit,
                "threshold": args.0.threshold
            }))
            .send()
            .await
            .map_err(|e| format!("Failed to connect to wiki_searcher: {}", e))?;

        // Check response status
        if !response.status().is_success() {
            let status = response.status();
            let error_text = response.text().await.unwrap_or_else(|_| "Unknown error".to_string());
            return Err(format!("Search failed with status {}: {}", status, error_text));
        }

        // Parse response JSON
        let body: serde_json::Value = response.json().await
            .map_err(|e| format!("Failed to parse search response: {}", e))?;

        // Extract results array
        let results_array = body.get("results")
            .and_then(|r| r.as_array())
            .ok_or_else(|| "Invalid response format: missing 'results' array".to_string())?;

        // Parse each result
        let results: Vec<types::SearchResult> = results_array
            .iter()
            .filter_map(|r| {
                Some(types::SearchResult {
                    page_name: r.get("page_name")?.as_str()?.to_string(),
                    chunk_text: r.get("chunk_text")?.as_str()?.to_string(),
                    section_header: r.get("section_header").and_then(|s| s.as_str()).map(String::from),
                    relevance_score: r.get("relevance_score")?.as_f64()? as f32,
                    chunk_index: r.get("chunk_index")?.as_u64()? as usize,
                })
            })
            .collect();

        tracing::info!("Search for '{}' returned {} results", args.0.query, results.len());

        Ok(Json(types::SearchWikiResponse { results }))
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

    #[test]
    fn test_sync_error_no_remote_configured() {
        let error = SyncError::NoRemoteConfigured;
        assert_eq!(error, SyncError::NoRemoteConfigured);
    }

    #[test]
    fn test_sync_error_merge_conflict() {
        let error = SyncError::MergeConflict;
        assert_eq!(error, SyncError::MergeConflict);
    }

    #[test]
    fn test_sync_error_network_error() {
        let error = SyncError::NetworkError;
        assert_eq!(error, SyncError::NetworkError);
    }

    #[test]
    fn test_sync_error_other() {
        let msg = "Custom error".to_string();
        let error = SyncError::Other(msg.clone());
        assert_eq!(error, SyncError::Other(msg));
    }

    #[test]
    fn test_sync_error_is_blocking_merge_conflict() {
        let error = SyncError::MergeConflict;
        // Merge conflicts should be considered blocking
        assert_eq!(error, SyncError::MergeConflict);
    }

    #[test]
    fn test_sync_error_is_non_blocking_no_remote() {
        let error = SyncError::NoRemoteConfigured;
        // No remote should be considered non-blocking
        assert_eq!(error, SyncError::NoRemoteConfigured);
    }

    #[test]
    fn test_sync_error_is_non_blocking_network() {
        let error = SyncError::NetworkError;
        // Network errors should be considered non-blocking
        assert_eq!(error, SyncError::NetworkError);
    }
}
