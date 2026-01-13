use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// Arguments for listing wiki pages
#[derive(Debug, Serialize, Deserialize, JsonSchema, PartialEq, Eq)]
pub struct ListWikiPagesArgs {}

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
    pub count: usize,
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
    use proptest::prelude::*;

    #[test]
    fn test_list_wiki_pages_args_empty() {
        let args = ListWikiPagesArgs {};
        let json = serde_json::to_string(&args).unwrap();
        assert_eq!(json, "{}");
    }

    #[test]
    fn test_list_wiki_pages_args_deserialize() {
        let json = "{}";
        let args: ListWikiPagesArgs = serde_json::from_str(json).unwrap();
        assert_eq!(args, ListWikiPagesArgs {});
    }

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

    proptest! {
        #[test]
        fn test_read_wiki_page_args_roundtrip(page_name in "[a-zA-Z0-9_-]{1,50}") {
            let args = ReadWikiPageArgs { page_name: page_name.clone() };
            let json = serde_json::to_string(&args).unwrap();
            let deserialized: ReadWikiPageArgs = serde_json::from_str(&json).unwrap();
            assert_eq!(args, deserialized);
        }

        #[test]
        fn test_write_wiki_page_args_roundtrip(
            page_name in "[a-zA-Z0-9_-]{1,50}",
            content in ".*{0,1000}",
            has_mimetype in any::<bool>()
        ) {
            let mimetype = if has_mimetype {
                Some("text/x-fossil-wiki".to_string())
            } else {
                None
            };
            let args = WriteWikiPageArgs {
                page_name: page_name.clone(),
                content: content.clone(),
                mimetype: mimetype.clone(),
            };
            let json = serde_json::to_string(&args).unwrap();
            let deserialized: WriteWikiPageArgs = serde_json::from_str(&json).unwrap();
            assert_eq!(args, deserialized);
        }

        #[test]
        fn test_write_wiki_page_args_valid_mimetypes(
            page_name in "[a-zA-Z0-9_-]{1,50}",
            content in ".*{0,100}",
            mimetype_idx in 0..3usize
        ) {
            let mimetypes = [
                "text/x-fossil-wiki",
                "text/x-markdown",
                "text/plain"
            ];
            let args = WriteWikiPageArgs {
                page_name,
                content,
                mimetype: Some(mimetypes[mimetype_idx].to_string()),
            };
            let json = serde_json::to_string(&args).unwrap();
            let deserialized: WriteWikiPageArgs = serde_json::from_str(&json).unwrap();
            assert_eq!(args, deserialized);
            assert!(mimetypes.contains(&deserialized.mimetype.as_ref().unwrap().as_str()));
        }

        #[test]
        fn test_list_wiki_pages_args_roundtrip(_dummy in any::<u8>()) {
            let args = ListWikiPagesArgs {};
            let json = serde_json::to_string(&args).unwrap();
            let deserialized: ListWikiPagesArgs = serde_json::from_str(&json).unwrap();
            assert_eq!(args, deserialized);
        }
    }
}
