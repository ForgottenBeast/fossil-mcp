//! # Fossil MCP Server
//!
//! This library provides MCP (Model Context Protocol) server functionality
//! for interacting with Fossil SCM wiki pages.
//!
//! ## Modules
//!
//! - `server`: MCP server implementation with FossilWiki handler

pub mod server;

// Re-export commonly used types for convenience
pub use server::FossilWiki;
pub use server::types::{
    ReadWikiPageArgs, ReadWikiPageResponse,
    WriteWikiPageArgs, WriteWikiPageResponse,
};
