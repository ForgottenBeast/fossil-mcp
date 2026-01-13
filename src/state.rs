use std::path::PathBuf;
use std::sync::Arc;

/// Shared application state containing the repository path
#[derive(Clone)]
pub struct AppState {
    pub repository_path: Arc<PathBuf>,
}

impl AppState {
    /// Create a new AppState with the given repository path
    pub fn new(repository_path: PathBuf) -> Self {
        Self {
            repository_path: Arc::new(repository_path),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn test_appstate_new() {
        let path = PathBuf::from("/test/path/repo.fossil");
        let state = AppState::new(path.clone());
        assert_eq!(*state.repository_path, path);
    }

    #[test]
    fn test_appstate_clone() {
        let path = PathBuf::from("/test/path/repo.fossil");
        let state1 = AppState::new(path.clone());
        let state2 = state1.clone();

        // Both should point to the same Arc
        assert!(Arc::ptr_eq(&state1.repository_path, &state2.repository_path));
        assert_eq!(*state1.repository_path, *state2.repository_path);
    }

    proptest! {
        #[test]
        fn test_appstate_any_path(path_str in "[a-zA-Z0-9/_.-]+") {
            let path = PathBuf::from(&path_str);
            let state = AppState::new(path.clone());
            assert_eq!(*state.repository_path, path);
        }

        #[test]
        fn test_appstate_clone_preserves_path(path_str in "[a-zA-Z0-9/_.-]+") {
            let path = PathBuf::from(&path_str);
            let state1 = AppState::new(path);
            let state2 = state1.clone();
            assert_eq!(*state1.repository_path, *state2.repository_path);
        }

        #[test]
        fn test_appstate_multiple_clones(path_str in "[a-zA-Z0-9/_.-]+", clone_count in 1..10usize) {
            let path = PathBuf::from(&path_str);
            let state = AppState::new(path.clone());

            let clones: Vec<_> = (0..clone_count).map(|_| state.clone()).collect();

            for cloned_state in clones {
                assert_eq!(*cloned_state.repository_path, path);
                assert!(Arc::ptr_eq(&state.repository_path, &cloned_state.repository_path));
            }
        }
    }
}
