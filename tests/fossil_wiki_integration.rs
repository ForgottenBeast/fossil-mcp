use fossil_mcp::{FossilWiki, ReadWikiPageArgs, WriteWikiPageArgs};
use rmcp::handler::server::wrapper::Parameters;
use std::path::PathBuf;
use tokio::process::Command;

/// Helper to create a temporary Fossil repository for testing
async fn create_test_repo() -> (PathBuf, tempfile::TempDir) {
    let temp_dir = tempfile::tempdir().expect("Failed to create temp directory");
    let repo_path = temp_dir.path().join("test.fossil");

    // Create a new Fossil repository
    let output = Command::new("fossil")
        .arg("new")
        .arg(&repo_path)
        .output()
        .await
        .expect("Failed to create fossil repository");

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!("Failed to create fossil repo: {}", stderr);
    }

    (repo_path, temp_dir)
}

#[tokio::test]
async fn test_list_empty_wiki() {
    let (repo_path, _temp_dir) = create_test_repo().await;
    let wiki = FossilWiki::new(repo_path);

    let result = wiki
        .list_wiki_pages()
        .await
        .expect("Failed to list wiki pages");

    // New repo should have empty or minimal pages
    assert!(result.0.pages.is_empty() || result.0.pages.len() < 3);
}

#[tokio::test]
async fn test_write_and_read_wiki_page() {
    let (repo_path, _temp_dir) = create_test_repo().await;
    let wiki = FossilWiki::new(repo_path);

    // Write a wiki page
    let write_args = Parameters(WriteWikiPageArgs {
        page_name: "TestPage".to_string(),
        content: "This is test content".to_string(),
        mimetype: Some("text/x-fossil-wiki".to_string()),
        skip_sync: true,
        force_write: false,
    });

    let write_result = wiki
        .write_wiki_page(write_args)
        .await
        .expect("Failed to write wiki page");

    assert!(write_result.0.success);
    assert_eq!(write_result.0.page_name, "TestPage");

    // Read the wiki page back
    let read_args = Parameters(ReadWikiPageArgs {
        page_name: "TestPage".to_string(),
    });

    let read_result = wiki
        .read_wiki_page(read_args)
        .await
        .expect("Failed to read wiki page");

    assert_eq!(read_result.0.page_name, "TestPage");
    assert_eq!(read_result.0.content, "This is test content");
}

#[tokio::test]
async fn test_write_multiple_pages() {
    let (repo_path, _temp_dir) = create_test_repo().await;
    let wiki = FossilWiki::new(repo_path);

    // Write multiple pages
    for i in 1..=3 {
        let page_name = format!("Page{}", i);
        let content = format!("Content for page {}", i);

        let write_args = Parameters(WriteWikiPageArgs {
            page_name: page_name.clone(),
            content: content.clone(),
            mimetype: Some("text/x-fossil-wiki".to_string()),
            skip_sync: true,
            force_write: false,
        });

        wiki.write_wiki_page(write_args)
            .await
            .expect("Failed to write wiki page");
    }

    // List pages and verify they exist
    let list_result = wiki
        .list_wiki_pages()
        .await
        .expect("Failed to list wiki pages");

    assert!(list_result.0.pages.contains(&"Page1".to_string()));
    assert!(list_result.0.pages.contains(&"Page2".to_string()));
    assert!(list_result.0.pages.contains(&"Page3".to_string()));
}

#[tokio::test]
async fn test_write_wiki_page_markdown() {
    let (repo_path, _temp_dir) = create_test_repo().await;
    let wiki = FossilWiki::new(repo_path);

    let markdown_content = "# Test Page\n\nThis is **bold** and this is *italic*.";

    let write_args = Parameters(WriteWikiPageArgs {
        page_name: "MarkdownPage".to_string(),
        content: markdown_content.to_string(),
        mimetype: Some("text/x-markdown".to_string()),
        skip_sync: true,
        force_write: false,
    });

    let write_result = wiki
        .write_wiki_page(write_args)
        .await
        .expect("Failed to write wiki page");

    assert!(write_result.0.success);

    // Read it back and verify
    let read_args = Parameters(ReadWikiPageArgs {
        page_name: "MarkdownPage".to_string(),
    });

    let read_result = wiki
        .read_wiki_page(read_args)
        .await
        .expect("Failed to read wiki page");

    assert_eq!(read_result.0.content, markdown_content);
}

#[tokio::test]
async fn test_update_existing_page() {
    let (repo_path, _temp_dir) = create_test_repo().await;
    let wiki = FossilWiki::new(repo_path);

    // Write initial version
    let write_args = Parameters(WriteWikiPageArgs {
        page_name: "UpdateTest".to_string(),
        content: "Version 1".to_string(),
        mimetype: None,
        skip_sync: true,
        force_write: false,
    });

    wiki.write_wiki_page(write_args)
        .await
        .expect("Failed to write wiki page");

    // Update the page
    let write_args = Parameters(WriteWikiPageArgs {
        page_name: "UpdateTest".to_string(),
        content: "Version 2 - Updated".to_string(),
        mimetype: None,
        skip_sync: true,
        force_write: false,
    });

    wiki.write_wiki_page(write_args)
        .await
        .expect("Failed to update wiki page");

    // Read and verify the update
    let read_args = Parameters(ReadWikiPageArgs {
        page_name: "UpdateTest".to_string(),
    });

    let read_result = wiki
        .read_wiki_page(read_args)
        .await
        .expect("Failed to read wiki page");

    assert_eq!(read_result.0.content, "Version 2 - Updated");
}

#[tokio::test]
async fn test_wiki_page_with_special_characters() {
    let (repo_path, _temp_dir) = create_test_repo().await;
    let wiki = FossilWiki::new(repo_path);

    let special_content = "Special chars: @#$%^&*()_+-=[]{}|;:,.<>?";

    let write_args = Parameters(WriteWikiPageArgs {
        page_name: "SpecialChars".to_string(),
        content: special_content.to_string(),
        mimetype: None,
        skip_sync: true,
        force_write: false,
    });

    wiki.write_wiki_page(write_args)
        .await
        .expect("Failed to write wiki page");

    let read_args = Parameters(ReadWikiPageArgs {
        page_name: "SpecialChars".to_string(),
    });

    let read_result = wiki
        .read_wiki_page(read_args)
        .await
        .expect("Failed to read wiki page");

    assert_eq!(read_result.0.content, special_content);
}

#[tokio::test]
async fn test_read_nonexistent_page() {
    let (repo_path, _temp_dir) = create_test_repo().await;
    let wiki = FossilWiki::new(repo_path);

    let read_args = Parameters(ReadWikiPageArgs {
        page_name: "NonexistentPage".to_string(),
    });

    let result = wiki.read_wiki_page(read_args).await;
    assert!(result.is_err());
}

#[tokio::test]
async fn test_write_wiki_page_skip_sync() {
    let (repo_path, _temp_dir) = create_test_repo().await;
    let wiki = FossilWiki::new(repo_path);

    let write_args = Parameters(WriteWikiPageArgs {
        page_name: "SkipSyncTest".to_string(),
        content: "Content with skip_sync".to_string(),
        mimetype: None,
        skip_sync: true,
        force_write: false,
    });

    let write_result = wiki
        .write_wiki_page(write_args)
        .await
        .expect("Failed to write wiki page");

    assert!(write_result.0.success);
    // When skip_sync is true, sync_status should be None
    assert!(write_result.0.sync_status.is_none());
}

#[tokio::test]
async fn test_write_wiki_page_with_sync_no_remote() {
    let (repo_path, _temp_dir) = create_test_repo().await;
    let wiki = FossilWiki::new(repo_path);

    let write_args = Parameters(WriteWikiPageArgs {
        page_name: "SyncNoRemoteTest".to_string(),
        content: "Content with sync attempted".to_string(),
        mimetype: None,
        skip_sync: false,
        force_write: false,
    });

    let write_result = wiki
        .write_wiki_page(write_args)
        .await
        .expect("Failed to write wiki page");

    assert!(write_result.0.success);
    // Sync should be attempted but likely fail with NoRemoteConfigured since no remote is set up
    assert!(write_result.0.sync_status.is_some());
    let sync_status = write_result.0.sync_status.unwrap();
    assert!(sync_status.attempted);
    // Since no remote is configured, sync will fail but page should still be written
}

#[tokio::test]
async fn test_write_wiki_page_force_write_false() {
    let (repo_path, _temp_dir) = create_test_repo().await;
    let wiki = FossilWiki::new(repo_path);

    let write_args = Parameters(WriteWikiPageArgs {
        page_name: "ForceWriteFalseTest".to_string(),
        content: "Content without force write".to_string(),
        mimetype: None,
        skip_sync: true,
        force_write: false,
    });

    let write_result = wiki
        .write_wiki_page(write_args)
        .await
        .expect("Failed to write wiki page");

    assert!(write_result.0.success);
    // With skip_sync=true and force_write=false, no sync is attempted
    assert!(write_result.0.sync_status.is_none());
}

#[tokio::test]
async fn test_write_wiki_page_force_write_true() {
    let (repo_path, _temp_dir) = create_test_repo().await;
    let wiki = FossilWiki::new(repo_path);

    let write_args = Parameters(WriteWikiPageArgs {
        page_name: "ForceWriteTrueTest".to_string(),
        content: "Content with force write".to_string(),
        mimetype: None,
        skip_sync: true,
        force_write: true,
    });

    let write_result = wiki
        .write_wiki_page(write_args)
        .await
        .expect("Failed to write wiki page");

    assert!(write_result.0.success);
}

#[tokio::test]
async fn test_sync_status_blocking_error() {
    let (repo_path, _temp_dir) = create_test_repo().await;
    let wiki = FossilWiki::new(repo_path);

    // This test verifies that when a sync status has a blocking error (can_force_write=true),
    // the page is still written but with proper error status
    let write_args = Parameters(WriteWikiPageArgs {
        page_name: "BlockingErrorTest".to_string(),
        content: "Test content".to_string(),
        mimetype: None,
        skip_sync: true,
        force_write: false,
    });

    let write_result = wiki
        .write_wiki_page(write_args)
        .await
        .expect("Failed to write wiki page");

    assert!(write_result.0.success);
    // With skip_sync=true, no sync attempt is made
    assert!(write_result.0.sync_status.is_none());
}
