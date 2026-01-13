use fossil_mcp::{AppState, FossilRouter};
use mcp_server::router::Router;
use std::path::PathBuf;

#[test]
fn test_fossil_router_creation() {
    let state = AppState::new(PathBuf::from("/test/repo.fossil"));
    let router = FossilRouter::new(state);

    assert_eq!(router.name(), "fossil-mcp");
    assert!(!router.instructions().is_empty());
}

#[test]
fn test_fossil_router_capabilities() {
    let state = AppState::new(PathBuf::from("/test/repo.fossil"));
    let router = FossilRouter::new(state);

    let capabilities = router.capabilities();
    assert!(capabilities.tools.is_some());
}

#[test]
fn test_fossil_router_lists_tools() {
    let state = AppState::new(PathBuf::from("/test/repo.fossil"));
    let router = FossilRouter::new(state);

    let tools = router.list_tools();
    assert_eq!(tools.len(), 3);

    let tool_names: Vec<_> = tools.iter().map(|t| t.name.as_str()).collect();
    assert!(tool_names.contains(&"list_wiki_pages"));
    assert!(tool_names.contains(&"read_wiki_page"));
    assert!(tool_names.contains(&"write_wiki_page"));
}

#[test]
fn test_fossil_router_tool_schemas() {
    let state = AppState::new(PathBuf::from("/test/repo.fossil"));
    let router = FossilRouter::new(state);

    let tools = router.list_tools();

    for tool in tools {
        // Each tool should have a description
        assert!(!tool.description.is_empty());

        // Each tool should have a valid JSON schema
        assert!(tool.input_schema.is_object());

        // Schema should have type and properties
        assert_eq!(tool.input_schema["type"], "object");
        assert!(tool.input_schema.get("properties").is_some());
        assert!(tool.input_schema.get("required").is_some());
    }
}

#[test]
fn test_fossil_router_resources() {
    let state = AppState::new(PathBuf::from("/test/repo.fossil"));
    let router = FossilRouter::new(state);

    let resources = router.list_resources();
    // This implementation doesn't support resources
    assert_eq!(resources.len(), 0);
}

#[test]
fn test_fossil_router_prompts() {
    let state = AppState::new(PathBuf::from("/test/repo.fossil"));
    let router = FossilRouter::new(state);

    let prompts = router.list_prompts();
    // This implementation doesn't support prompts
    assert_eq!(prompts.len(), 0);
}

#[cfg(test)]
mod proptest_integration {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_router_with_any_path(path_str in "[a-zA-Z0-9/_.-]{1,100}") {
            let state = AppState::new(PathBuf::from(&path_str));
            let router = FossilRouter::new(state);

            // Router should always return the same name
            assert_eq!(router.name(), "fossil-mcp");

            // Router should always have 3 tools
            let tools = router.list_tools();
            assert_eq!(tools.len(), 3);
        }

        #[test]
        fn test_appstate_consistency(path_str in "[a-zA-Z0-9/_.-]{1,100}") {
            let path = PathBuf::from(&path_str);
            let state = AppState::new(path.clone());

            // Path should be preserved
            assert_eq!(*state.repository_path, path);

            // Clone should preserve the path
            let cloned = state.clone();
            assert_eq!(*cloned.repository_path, path);
        }

        #[test]
        fn test_multiple_routers_same_state(path_str in "[a-zA-Z0-9/_.-]{1,100}") {
            let state = AppState::new(PathBuf::from(&path_str));

            let router1 = FossilRouter::new(state.clone());
            let router2 = FossilRouter::new(state.clone());

            // Both routers should have identical configurations
            assert_eq!(router1.name(), router2.name());
            assert_eq!(router1.list_tools().len(), router2.list_tools().len());
        }
    }
}

#[cfg(test)]
mod tool_validation {
    use super::*;

    #[test]
    fn test_list_wiki_pages_tool_schema() {
        let state = AppState::new(PathBuf::from("/test/repo.fossil"));
        let router = FossilRouter::new(state);

        let tools = router.list_tools();
        let list_tool = tools.iter().find(|t| t.name == "list_wiki_pages").unwrap();

        // Should have empty required array
        assert_eq!(list_tool.input_schema["required"].as_array().unwrap().len(), 0);

        // Should have empty properties
        let props = list_tool.input_schema["properties"].as_object().unwrap();
        assert_eq!(props.len(), 0);
    }

    #[test]
    fn test_read_wiki_page_tool_schema() {
        let state = AppState::new(PathBuf::from("/test/repo.fossil"));
        let router = FossilRouter::new(state);

        let tools = router.list_tools();
        let read_tool = tools.iter().find(|t| t.name == "read_wiki_page").unwrap();

        // Should require page_name
        let required = read_tool.input_schema["required"].as_array().unwrap();
        assert_eq!(required.len(), 1);
        assert_eq!(required[0], "page_name");

        // Should have page_name property
        let props = read_tool.input_schema["properties"].as_object().unwrap();
        assert!(props.contains_key("page_name"));
        assert_eq!(props["page_name"]["type"], "string");
    }

    #[test]
    fn test_write_wiki_page_tool_schema() {
        let state = AppState::new(PathBuf::from("/test/repo.fossil"));
        let router = FossilRouter::new(state);

        let tools = router.list_tools();
        let write_tool = tools.iter().find(|t| t.name == "write_wiki_page").unwrap();

        // Should require page_name and content
        let required = write_tool.input_schema["required"].as_array().unwrap();
        assert_eq!(required.len(), 2);
        assert!(required.contains(&serde_json::json!("page_name")));
        assert!(required.contains(&serde_json::json!("content")));

        // Should have all three properties
        let props = write_tool.input_schema["properties"].as_object().unwrap();
        assert!(props.contains_key("page_name"));
        assert!(props.contains_key("content"));
        assert!(props.contains_key("mimetype"));

        // Mimetype should have enum values
        let mimetype_enum = props["mimetype"]["enum"].as_array().unwrap();
        assert_eq!(mimetype_enum.len(), 3);
        assert!(mimetype_enum.contains(&serde_json::json!("text/x-fossil-wiki")));
        assert!(mimetype_enum.contains(&serde_json::json!("text/x-markdown")));
        assert!(mimetype_enum.contains(&serde_json::json!("text/plain")));
    }
}
