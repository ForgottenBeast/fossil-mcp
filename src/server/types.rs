use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

fn is_false(value: &bool) -> bool {
    !value
}

/// Arguments for configuring the repository path at runtime.
///
/// # Example
/// ```json
/// {
///   "repo_path": "/path/to/repo.fossil"
/// }
/// ```
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct ConfigureRepositoryArgs {
    /// Path to the Fossil repository file
    pub repo_path: String,
}

/// Response from configuring the repository.
///
/// # Example
/// ```json
/// {
///   "success": true,
///   "message": "Repository configured: \"/path/to/repo.fossil\""
/// }
/// ```
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct ConfigureRepositoryResponse {
    /// Whether the configuration was successful
    pub success: bool,
    /// Human-readable message describing the result
    pub message: String,
}

/// Arguments for authenticating with wiki_searcher API.
///
/// # Example
/// ```json
/// {
///   "username": "myuser",
///   "password": "mypass"
/// }
/// ```
#[derive(Debug, Serialize, Deserialize, JsonSchema)]
pub struct AuthenticateWikiArgs {
    /// Fossil username
    pub username: String,
    /// User password
    pub password: String,
}

/// Response from wiki authentication.
///
/// # Example
/// ```json
/// {
///   "success": true,
///   "session_token": "abc123...",
///   "message": "Authentication successful"
/// }
/// ```
#[derive(Debug, Serialize, Deserialize, JsonSchema)]
pub struct AuthenticateWikiResponse {
    /// Whether authentication was successful
    pub success: bool,
    /// Session token for subsequent API calls (if successful)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub session_token: Option<String>,
    /// Human-readable message
    pub message: String,
}

/// Arguments for searching wiki pages via semantic search API.
///
/// Provide either api_key or session_token for authentication.
///
/// # Example with API key
/// ```json
/// {
///   "query": "embedding concepts",
///   "limit": 10,
///   "threshold": 0.7,
///   "api_key": "your-api-key-here"
/// }
/// ```
///
/// # Example with session token
/// ```json
/// {
///   "query": "embedding concepts",
///   "limit": 10,
///   "threshold": 0.7,
///   "session_token": "token-from-authenticate"
/// }
/// ```
#[derive(Debug, Serialize, Deserialize, JsonSchema)]
pub struct SearchWikiArgs {
    /// Search query text
    pub query: String,
    /// Maximum number of results to return (default: 10)
    #[serde(default = "default_limit")]
    pub limit: usize,
    /// Minimum relevance score threshold 0.0-1.0 (default: 0.7)
    #[serde(default = "default_threshold")]
    pub threshold: f32,
    /// API key for wiki_searcher authentication (mutually exclusive with session_token)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub api_key: Option<String>,
    /// Session token from authenticate_wiki (mutually exclusive with api_key)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub session_token: Option<String>,
}

fn default_limit() -> usize {
    10
}

fn default_threshold() -> f32 {
    0.7
}

/// Individual search result from wiki search.
///
/// # Example
/// ```json
/// {
///   "page_name": "Machine Learning",
///   "chunk_text": "Embeddings are dense vector representations...",
///   "section_header": "Introduction",
///   "relevance_score": 0.843,
///   "chunk_index": 0
/// }
/// ```
#[derive(Debug, Serialize, Deserialize, JsonSchema)]
pub struct SearchResult {
    /// Name of the wiki page
    pub page_name: String,
    /// Text content of the matching chunk
    pub chunk_text: String,
    /// Section header within the page (if applicable)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub section_header: Option<String>,
    /// Relevance score (0.0-1.0, higher is more relevant)
    pub relevance_score: f32,
    /// Index of the chunk within the page
    pub chunk_index: usize,
}

/// Response from wiki search operation.
///
/// # Example
/// ```json
/// {
///   "results": [
///     {
///       "page_name": "Machine Learning",
///       "chunk_text": "Embeddings are...",
///       "relevance_score": 0.843,
///       "chunk_index": 0
///     }
///   ]
/// }
/// ```
#[derive(Debug, Serialize, Deserialize, JsonSchema)]
pub struct SearchWikiResponse {
    /// List of search results ordered by relevance
    pub results: Vec<SearchResult>,
}

/// Arguments for reading a wiki page from a Fossil repository.
///
/// # Example
/// ```json
/// {
///   "page_name": "HomePage"
/// }
/// ```
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct ReadWikiPageArgs {
    /// The name of the wiki page to read
    pub page_name: String,
}

/// Arguments for writing a wiki page to a Fossil repository.
///
/// This structure controls both the page content and synchronization behavior.
///
/// # Fields
/// - `page_name`: The name of the wiki page (required)
/// - `content`: The content to write to the page (required)
/// - `mimetype`: Optional MIME type for the page (defaults to text/x-fossil-wiki if not specified)
/// - `skip_sync`: If `true`, skip repository synchronization after writing (default: `false`)
/// - `force_write`: If `true`, override sync errors (such as merge conflicts) and allow the page to be written anyway (default: `false`)
///
/// # Sync Behavior
/// - When `skip_sync` is `false`, the repository will be synchronized after the page is written
/// - If a merge conflict occurs during sync and `force_write` is `false`, the operation will fail
/// - If `force_write` is `true`, the page write succeeds even if sync fails, but the error is reported in the response
///
/// # Example
/// ```json
/// {
///   "page_name": "API/v2/Reference",
///   "content": "# API Documentation\n\nVersion 2.0 changelog...",
///   "mimetype": "text/x-markdown",
///   "skip_sync": false,
///   "force_write": false
/// }
/// ```
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct WriteWikiPageArgs {
    /// The name of the wiki page to create or update
    pub page_name: String,
    /// The content to write to the page
    pub content: String,
    /// Optional MIME type for the page content (e.g., "text/x-markdown", "text/x-fossil-wiki")
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mimetype: Option<String>,
    /// If true, skip synchronization with remote repository after writing
    #[serde(default, skip_serializing_if = "is_false")]
    pub skip_sync: bool,
    /// If true, allow page write to succeed even if sync fails (merge conflicts, network errors)
    #[serde(default, skip_serializing_if = "is_false")]
    pub force_write: bool,
}

/// Response for listing wiki pages
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct ListWikiPagesResponse {
    pub pages: Vec<String>,
}

/// Response for reading a wiki page
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct ReadWikiPageResponse {
    pub page_name: String,
    pub content: String,
}

/// Status of a synchronization operation.
///
/// Provides details about whether synchronization was attempted and its outcome.
/// The `can_force_write` flag indicates whether retrying with `force_write: true`
/// might resolve the issue.
///
/// # Blocking vs Non-blocking Errors
/// - **Blocking** (can_force_write=true): Merge conflicts prevent synchronization
/// - **Non-blocking** (can_force_write=false): Network or configuration issues
///
/// # Example
/// ```json
/// {
///   "attempted": true,
///   "succeeded": false,
///   "error_type": "MergeConflict",
///   "error_message": "Merge conflict occurred during synchronization. Use force_write to override.",
///   "can_force_write": true
/// }
/// ```
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct SyncStatus {
    /// Whether a sync operation was attempted
    pub attempted: bool,
    /// Whether the sync operation succeeded
    pub succeeded: bool,
    /// Type of error that occurred (if any): "MergeConflict", "NoRemoteConfigured", "NetworkError", "Other"
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error_type: Option<String>,
    /// Human-readable description of the error (if any)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error_message: Option<String>,
    /// Whether the operation can be retried with force_write flag to override the error
    pub can_force_write: bool,
}

/// Response from writing a wiki page.
///
/// The page is written to the repository regardless of sync success.
/// If synchronization was requested and failed, details are provided in `sync_status`.
///
/// # Success Conditions
/// - Page content is successfully written to the repository: `success` is `true`
/// - Sync may succeed, fail non-blockingly, or fail blockingly regardless
/// - To distinguish sync outcomes, check the `sync_status` field
///
/// # Example (successful write with failed non-blocking sync)
/// ```json
/// {
///   "success": true,
///   "page_name": "API/Reference",
///   "message": "Wiki page written successfully",
///   "sync_status": {
///     "attempted": true,
///     "succeeded": false,
///     "error_type": "NoRemoteConfigured",
///     "error_message": "No remote URL configured for this repository.",
///     "can_force_write": false
///   }
/// }
/// ```
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct WriteWikiPageResponse {
    /// Whether the page content was successfully written to the repository
    pub success: bool,
    /// The name of the wiki page that was written
    pub page_name: String,
    /// Human-readable message describing the operation result
    pub message: String,
    /// Optional synchronization status (only present if sync was requested and attempted)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sync_status: Option<SyncStatus>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_wiki_page_args_serialize() {
        let args = ReadWikiPageArgs {
            page_name: "HomePage".to_string(),
        };
        let json = serde_json::to_string(&args).unwrap();
        assert!(json.contains("HomePage"));
    }

    #[test]
    fn test_read_wiki_page_args_deserialize() {
        let json = r#"{"page_name":"TestPage"}"#;
        let args: ReadWikiPageArgs = serde_json::from_str(json).unwrap();
        assert_eq!(args.page_name, "TestPage");
    }

    #[test]
    fn test_write_wiki_page_args_with_mimetype() {
        let args = WriteWikiPageArgs {
            page_name: "Test".to_string(),
            content: "Content".to_string(),
            mimetype: Some("text/x-markdown".to_string()),
            skip_sync: false,
            force_write: false,
        };
        let json = serde_json::to_string(&args).unwrap();
        assert!(json.contains("text/x-markdown"));
    }

    #[test]
    fn test_write_wiki_page_args_without_mimetype() {
        let args = WriteWikiPageArgs {
            page_name: "Test".to_string(),
            content: "Content".to_string(),
            mimetype: None,
            skip_sync: false,
            force_write: false,
        };
        let json = serde_json::to_string(&args).unwrap();
        assert!(!json.contains("mimetype"));
    }

    #[test]
    fn test_write_wiki_page_args_deserialize_with_default() {
        let json = r#"{"page_name":"Test","content":"Content"}"#;
        let args: WriteWikiPageArgs = serde_json::from_str(json).unwrap();
        assert_eq!(args.mimetype, None);
        assert_eq!(args.skip_sync, false);
        assert_eq!(args.force_write, false);
    }

    #[test]
    fn test_write_wiki_page_args_with_skip_sync() {
        let args = WriteWikiPageArgs {
            page_name: "Test".to_string(),
            content: "Content".to_string(),
            mimetype: None,
            skip_sync: true,
            force_write: false,
        };
        let json = serde_json::to_string(&args).unwrap();
        assert!(json.contains("skip_sync"));
    }

    #[test]
    fn test_write_wiki_page_args_with_force_write() {
        let args = WriteWikiPageArgs {
            page_name: "Test".to_string(),
            content: "Content".to_string(),
            mimetype: None,
            skip_sync: false,
            force_write: true,
        };
        let json = serde_json::to_string(&args).unwrap();
        assert!(json.contains("force_write"));
    }

    #[test]
    fn test_write_wiki_page_args_skip_false_fields() {
        let args = WriteWikiPageArgs {
            page_name: "Test".to_string(),
            content: "Content".to_string(),
            mimetype: None,
            skip_sync: false,
            force_write: false,
        };
        let json = serde_json::to_string(&args).unwrap();
        assert!(!json.contains("skip_sync"));
        assert!(!json.contains("force_write"));
    }

    #[test]
    fn test_sync_status_creation() {
        let status = SyncStatus {
            attempted: true,
            succeeded: true,
            error_type: None,
            error_message: None,
            can_force_write: false,
        };
        assert_eq!(status.attempted, true);
        assert_eq!(status.succeeded, true);
        assert_eq!(status.error_type, None);
        assert_eq!(status.error_message, None);
        assert_eq!(status.can_force_write, false);
    }

    #[test]
    fn test_sync_status_with_error() {
        let status = SyncStatus {
            attempted: true,
            succeeded: false,
            error_type: Some("MergeConflict".to_string()),
            error_message: Some("Conflict in file A".to_string()),
            can_force_write: true,
        };
        assert_eq!(status.attempted, true);
        assert_eq!(status.succeeded, false);
        assert_eq!(status.error_type, Some("MergeConflict".to_string()));
        assert_eq!(status.error_message, Some("Conflict in file A".to_string()));
        assert_eq!(status.can_force_write, true);
    }

    #[test]
    fn test_sync_status_serialize() {
        let status = SyncStatus {
            attempted: true,
            succeeded: true,
            error_type: None,
            error_message: None,
            can_force_write: false,
        };
        let json = serde_json::to_string(&status).unwrap();
        assert!(json.contains("attempted"));
        assert!(json.contains("succeeded"));
        assert!(!json.contains("error_type"));
        assert!(!json.contains("error_message"));
    }

    #[test]
    fn test_sync_status_serialize_with_error() {
        let status = SyncStatus {
            attempted: true,
            succeeded: false,
            error_type: Some("NetworkError".to_string()),
            error_message: Some("Connection timeout".to_string()),
            can_force_write: false,
        };
        let json = serde_json::to_string(&status).unwrap();
        assert!(json.contains("NetworkError"));
        assert!(json.contains("Connection timeout"));
    }

    #[test]
    fn test_write_wiki_page_response_without_sync_status() {
        let response = WriteWikiPageResponse {
            success: true,
            page_name: "Test".to_string(),
            message: "Success".to_string(),
            sync_status: None,
        };
        let json = serde_json::to_string(&response).unwrap();
        assert!(!json.contains("sync_status"));
    }

    #[test]
    fn test_write_wiki_page_response_with_sync_status() {
        let status = SyncStatus {
            attempted: true,
            succeeded: true,
            error_type: None,
            error_message: None,
            can_force_write: false,
        };
        let response = WriteWikiPageResponse {
            success: true,
            page_name: "Test".to_string(),
            message: "Success".to_string(),
            sync_status: Some(status),
        };
        let json = serde_json::to_string(&response).unwrap();
        assert!(json.contains("sync_status"));
    }
}
