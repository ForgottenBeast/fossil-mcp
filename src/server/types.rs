use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

fn is_false(value: &bool) -> bool {
    !value
}

/// Arguments for reading a wiki page
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct ReadWikiPageArgs {
    pub page_name: String,
}

/// Arguments for writing a wiki page
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct WriteWikiPageArgs {
    pub page_name: String,
    pub content: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mimetype: Option<String>,
    #[serde(default, skip_serializing_if = "is_false")]
    pub skip_sync: bool,
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

/// Status of a synchronization operation
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct SyncStatus {
    /// Whether a sync was attempted
    pub attempted: bool,
    /// Whether the sync succeeded
    pub succeeded: bool,
    /// Type of error that occurred (if any)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error_type: Option<String>,
    /// Human-readable error message (if any)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error_message: Option<String>,
    /// Whether the operation can be retried with force_write
    pub can_force_write: bool,
}

/// Response for writing a wiki page
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct WriteWikiPageResponse {
    pub success: bool,
    pub page_name: String,
    pub message: String,
    /// Optional sync status information
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
