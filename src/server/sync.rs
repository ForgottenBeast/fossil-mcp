use std::path::PathBuf;
use tokio::process::Command;

/// Errors that can occur during Fossil synchronization
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyncError {
    /// No remote configured in the repository
    NoRemoteConfigured,
    /// Merge conflict occurred during sync
    MergeConflict,
    /// Network error occurred
    NetworkError,
    /// Other synchronization error
    Other(String),
}

/// Executes 'fossil sync' and parses errors into appropriate SyncError variants
pub async fn sync_repository(repository_path: &PathBuf) -> Result<(), SyncError> {
    let output = Command::new("fossil")
        .args(["sync", "-R", &repository_path.to_string_lossy()])
        .output()
        .await
        .map_err(|e| SyncError::Other(format!("Failed to execute fossil sync: {}", e)))?;

    if output.status.success() {
        return Ok(());
    }

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stderr_str = stderr.as_ref();

    // Parse error messages to categorize the sync error
    if stderr_str.contains("no remote URL") || stderr_str.contains("no remote") {
        Err(SyncError::NoRemoteConfigured)
    } else if stderr_str.contains("conflict") || stderr_str.contains("merge") {
        Err(SyncError::MergeConflict)
    } else if stderr_str.contains("network") || stderr_str.contains("connection") || stderr_str.contains("timeout") {
        Err(SyncError::NetworkError)
    } else {
        Err(SyncError::Other(stderr_str.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn test_sync_error_debug_impl() {
        let error = SyncError::MergeConflict;
        let debug_str = format!("{:?}", error);
        assert!(debug_str.contains("MergeConflict"));
    }

    #[test]
    fn test_sync_error_clone() {
        let error = SyncError::NetworkError;
        let cloned = error.clone();
        assert_eq!(error, cloned);
    }
}


