# MCP Client Integration

Learn how to integrate fossil-mcp with popular MCP clients.

## Claude Desktop

Add fossil-mcp to your Claude Desktop configuration:

### macOS

Edit `~/Library/Application Support/Claude/claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "fossil": {
      "command": "/usr/local/bin/fossil-mcp",
      "args": ["-R", "/path/to/your/repo.fossil"]
    }
  }
}
```

### Linux

Edit `~/.config/Claude/claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "fossil": {
      "command": "/usr/local/bin/fossil-mcp",
      "args": ["-R", "/path/to/your/repo.fossil"]
    }
  }
}
```

### Windows

Edit `%APPDATA%\Claude\claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "fossil": {
      "command": "C:\\path\\to\\fossil-mcp.exe",
      "args": ["-R", "C:\\path\\to\\repo.fossil"]
    }
  }
}
```

After adding the configuration:
1. Restart Claude Desktop
2. The fossil-mcp tools will appear in Claude's tool list
3. Ask Claude to "list wiki pages" or "read the HomePage wiki"

## MCP Inspector

Use the [MCP Inspector](https://github.com/modelcontextprotocol/inspector) for testing:

```bash
# Install inspector
npm install -g @modelcontextprotocol/inspector

# Run inspector with fossil-mcp
mcp-inspector fossil-mcp -R /path/to/repo.fossil
```

This opens a web UI where you can:
- See available tools
- Test tool calls
- Inspect JSON-RPC messages
- Debug protocol issues

## Custom MCP Client

Integrate fossil-mcp into your own MCP client:

```javascript
import { spawn } from 'child_process';

// Start the server
const server = spawn('fossil-mcp', ['-R', '/path/to/repo.fossil']);

// Send initialize request
server.stdin.write(JSON.stringify({
  jsonrpc: '2.0',
  id: 1,
  method: 'initialize',
  params: {
    protocolVersion: '2024-11-05',
    capabilities: {},
    clientInfo: { name: 'my-client', version: '1.0' }
  }
}) + '\n');

// Handle responses
server.stdout.on('data', (data) => {
  const response = JSON.parse(data.toString());
  console.log('Response:', response);
});
```

## Environment Variables

Configure fossil-mcp behavior via environment:

```bash
# Set Fossil binary path
export FOSSIL_PATH=/opt/fossil/bin/fossil

# Enable debug logging
export RUST_LOG=debug

# Run server
fossil-mcp -R repo.fossil
```

## Multiple Repositories

Configure multiple fossil repositories:

```json
{
  "mcpServers": {
    "fossil-main": {
      "command": "/usr/local/bin/fossil-mcp",
      "args": ["-R", "/path/to/main.fossil"]
    },
    "fossil-docs": {
      "command": "/usr/local/bin/fossil-mcp",
      "args": ["-R", "/path/to/docs.fossil"]
    }
  }
}
```

## Troubleshooting

### Server Not Starting

Check that:
1. The fossil binary is in PATH: `which fossil`
2. The repository file exists and is valid
3. You have read/write permissions

### Tools Not Appearing

1. Check Claude Desktop logs
2. Verify JSON syntax in config file
3. Restart Claude Desktop completely

### Permission Errors

Ensure the repository file has appropriate permissions:

```bash
chmod 644 /path/to/repo.fossil
```

## Next Steps

- [Configuration](./configuration.md) - Advanced setup
- [Usage](./usage.md) - Detailed tool usage
