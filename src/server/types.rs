use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

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

/// Response for writing a wiki page
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct WriteWikiPageResponse {
    pub success: bool,
    pub page_name: String,
    pub message: String,
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
        };
        let json = serde_json::to_string(&args).unwrap();
        assert!(!json.contains("mimetype"));
    }

    #[test]
    fn test_write_wiki_page_args_deserialize_with_default() {
        let json = r#"{"page_name":"Test","content":"Content"}"#;
        let args: WriteWikiPageArgs = serde_json::from_str(json).unwrap();
        assert_eq!(args.mimetype, None);
    }
}
