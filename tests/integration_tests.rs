use fossil_mcp::{AppState, FossilRouter};
use rmcp::handler::server::ServerHandler;
use std::path::PathBuf;

#[test]
fn test_fossil_router_creation() {
    let state = AppState::new(PathBuf::from("/test/repo.fossil"));
    let router = FossilRouter::new(state);

    let info = router.get_info();
    assert!(info.instructions.is_some());
    assert!(!info.instructions.unwrap().is_empty());
}

#[test]
fn test_fossil_router_capabilities() {
    let state = AppState::new(PathBuf::from("/test/repo.fossil"));
    let router = FossilRouter::new(state);

    let info = router.get_info();
    assert!(info.capabilities.tools.is_some());
}

#[cfg(test)]
mod proptest_integration {
    use super::*;
    use proptest::prelude::*;

    proptest! {
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
            let router2 = FossilRouter::new(state);

            // Both routers should have the same capabilities
            let info1 = router1.get_info();
            let info2 = router2.get_info();

            assert_eq!(info1.instructions, info2.instructions);
            assert_eq!(info1.capabilities.tools.is_some(), info2.capabilities.tools.is_some());
        }
    }
}
