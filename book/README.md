# Fossil MCP Documentation

This directory contains the user and developer documentation built with [mdBook](https://rust-lang.github.io/mdBook/).

## Building Documentation

### Using Nix (Recommended)

Build both rustdoc and mdBook together:

```bash
# Build all documentation
nix build .#docs

# View documentation (opens in browser)
nix run .#docs

# Documentation will be at:
# ./result/share/doc/fossil-mcp/index.html
```

### Using mdBook Directly

```bash
# Install mdBook
cargo install mdbook

# Build the book
mdbook build

# Serve with live reload
mdbook serve

# Open http://localhost:3000
```

### Building Rustdoc

```bash
# Build API documentation
cargo doc --no-deps --open
```

## Documentation Structure

```
book/
├── book.toml           # mdBook configuration
├── src/                # Markdown source files
│   ├── SUMMARY.md      # Table of contents
│   ├── introduction.md
│   ├── user-guide/     # User documentation
│   ├── developer-guide/# Developer documentation
│   ├── api/            # API reference
│   └── appendices/     # Additional resources
└── output/             # Generated HTML (gitignored)
```

## Adding Content

1. Create a new `.md` file in the appropriate directory
2. Add it to `SUMMARY.md` to include in navigation
3. Write content using GitHub-flavored Markdown
4. Build to verify

## Style Guide

- Use `#` for chapter titles
- Use `##` for major sections
- Use `###` for subsections
- Include code examples with appropriate language tags
- Use `bash` for shell commands
- Use `json` for JSON-RPC examples
- Use `rust` for Rust code

## Testing

All code examples should be tested:

```bash
# Test doctests
cargo test --doc

# Test all
cargo test
```

## Publishing

Documentation is automatically built and deployed via GitHub Actions (TODO: add workflow).

## Links

- [mdBook Documentation](https://rust-lang.github.io/mdBook/)
- [Fossil MCP Repository](https://github.com/yourusername/fossil-mcp)
- [MCP Protocol](https://modelcontextprotocol.io)
