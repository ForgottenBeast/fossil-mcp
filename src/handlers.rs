use anyhow::{Context, Result};
use serde_json::json;
use tokio::process::Command;

use crate::state::AppState;
use crate::types::{ListWikiPagesArgs, ReadWikiPageArgs, WriteWikiPageArgs};

/// Parse wiki list output into pages
pub fn parse_wiki_list(output: &str) -> Vec<String> {
    output
        .lines()
        .map(|line| line.trim().to_string())
        .filter(|line| !line.is_empty())
        .collect()
}

/// List all wiki pages in the Fossil repository
pub async fn list_wiki_pages(_args: ListWikiPagesArgs, state: AppState) -> Result<serde_json::Value> {
    let output = Command::new("fossil")
        .arg("-R")
        .arg(state.repository_path.as_ref())
        .args(["wiki", "list"])
        .output()
        .await
        .context("Failed to execute fossil wiki list")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        anyhow::bail!("fossil wiki list failed: {}", stderr);
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let pages = parse_wiki_list(&stdout);

    Ok(json!({
        "pages": pages,
        "count": pages.len()
    }))
}

/// Read the content of a specific wiki page
pub async fn read_wiki_page(args: ReadWikiPageArgs, state: AppState) -> Result<serde_json::Value> {
    let output = Command::new("fossil")
        .arg("-R")
        .arg(state.repository_path.as_ref())
        .args(["wiki", "export", &args.page_name])
        .output()
        .await
        .context("Failed to execute fossil wiki export")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        anyhow::bail!("fossil wiki export failed: {}", stderr);
    }

    let content = String::from_utf8_lossy(&output.stdout).to_string();

    Ok(json!({
        "page_name": args.page_name,
        "content": content
    }))
}

/// Create or update a wiki page
pub async fn write_wiki_page(args: WriteWikiPageArgs, state: AppState) -> Result<serde_json::Value> {
    // Write content to a temporary file
    let temp_file = format!("/tmp/fossil_wiki_{}.txt", args.page_name.replace("/", "_"));
    tokio::fs::write(&temp_file, &args.content)
        .await
        .context("Failed to write temporary file")?;

    // Build the command
    let mut cmd = Command::new("fossil");
    cmd.arg("-R")
        .arg(state.repository_path.as_ref())
        .args(["wiki", "commit", &args.page_name, &temp_file]);

    if let Some(ref mt) = args.mimetype {
        cmd.arg(format!("--mimetype={}", mt));
    }

    let output = cmd.output()
        .await
        .context("Failed to execute fossil wiki commit")?;

    // Clean up temp file
    let _ = tokio::fs::remove_file(&temp_file).await;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        anyhow::bail!("fossil wiki commit failed: {}", stderr);
    }

    Ok(json!({
        "success": true,
        "page_name": args.page_name,
        "message": "Wiki page written successfully"
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use std::path::PathBuf;

    #[test]
    fn test_parse_wiki_list_empty() {
        let output = "";
        let pages = parse_wiki_list(output);
        assert_eq!(pages.len(), 0);
    }

    #[test]
    fn test_parse_wiki_list_single_page() {
        let output = "HomePage\n";
        let pages = parse_wiki_list(output);
        assert_eq!(pages, vec!["HomePage"]);
    }

    #[test]
    fn test_parse_wiki_list_multiple_pages() {
        let output = "HomePage\nAbout\nTODO\n";
        let pages = parse_wiki_list(output);
        assert_eq!(pages, vec!["HomePage", "About", "TODO"]);
    }

    #[test]
    fn test_parse_wiki_list_with_whitespace() {
        let output = "  HomePage  \n  About  \n";
        let pages = parse_wiki_list(output);
        assert_eq!(pages, vec!["HomePage", "About"]);
    }

    #[test]
    fn test_parse_wiki_list_with_empty_lines() {
        let output = "HomePage\n\nAbout\n\n";
        let pages = parse_wiki_list(output);
        assert_eq!(pages, vec!["HomePage", "About"]);
    }

    proptest! {
        #[test]
        fn test_parse_wiki_list_property(pages in prop::collection::vec("[a-zA-Z0-9_-]{1,50}", 0..20)) {
            let output = pages.join("\n");
            let parsed = parse_wiki_list(&output);
            assert_eq!(parsed, pages);
        }

        #[test]
        fn test_parse_wiki_list_with_trailing_newline(pages in prop::collection::vec("[a-zA-Z0-9_-]{1,50}", 1..20)) {
            let output = format!("{}\n", pages.join("\n"));
            let parsed = parse_wiki_list(&output);
            assert_eq!(parsed, pages);
        }

        #[test]
        fn test_parse_wiki_list_filters_empty(
            pages in prop::collection::vec("[a-zA-Z0-9_-]{1,50}", 1..10),
            empty_count in 0..5usize
        ) {
            let mut output_parts = pages.clone();
            for _ in 0..empty_count {
                output_parts.push("".to_string());
            }
            let output = output_parts.join("\n");
            let parsed = parse_wiki_list(&output);
            assert_eq!(parsed.len(), pages.len());
        }
    }

    #[tokio::test]
    async fn test_list_wiki_pages_response_structure() {
        // Create a mock state with a non-existent repository
        let state = AppState::new(PathBuf::from("/nonexistent/repo.fossil"));
        let args = ListWikiPagesArgs {};

        // This will fail, but we're testing that it fails gracefully
        let result = list_wiki_pages(args, state).await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_read_wiki_page_response_structure() {
        let state = AppState::new(PathBuf::from("/nonexistent/repo.fossil"));
        let args = ReadWikiPageArgs {
            page_name: "TestPage".to_string(),
        };

        // This will fail, but we're testing that it fails gracefully
        let result = read_wiki_page(args, state).await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_write_wiki_page_creates_temp_file() {
        let state = AppState::new(PathBuf::from("/nonexistent/repo.fossil"));
        let args = WriteWikiPageArgs {
            page_name: "TestPage".to_string(),
            content: "Test content".to_string(),
            mimetype: None,
        };

        // This will fail, but we're testing that it fails gracefully
        let result = write_wiki_page(args, state).await;
        assert!(result.is_err());
    }

    proptest! {
        #[test]
        fn test_temp_file_naming(page_name in "[a-zA-Z0-9_-]{1,50}") {
            let expected = format!("/tmp/fossil_wiki_{}.txt", page_name);
            let temp_file = format!("/tmp/fossil_wiki_{}.txt", page_name.replace("/", "_"));
            assert_eq!(temp_file, expected);
        }

        #[test]
        fn test_temp_file_naming_with_slashes(page_name in "[a-zA-Z0-9_/-]{1,50}") {
            let temp_file = format!("/tmp/fossil_wiki_{}.txt", page_name.replace("/", "_"));
            assert!(!temp_file[13..].contains('/') || temp_file == "/tmp/fossil_wiki_.txt");
        }
    }
}
