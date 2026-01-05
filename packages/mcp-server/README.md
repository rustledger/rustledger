# @rustledger/mcp-server

MCP (Model Context Protocol) server for [rustledger](https://rustledger.github.io) - validate, query, and format Beancount ledgers directly from AI assistants.

## Installation

```bash
npm install -g @rustledger/mcp-server
```

Or use directly with npx:

```bash
npx @rustledger/mcp-server
```

## Configuration

### Claude Desktop

Add to your `claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "rustledger": {
      "command": "npx",
      "args": ["-y", "@rustledger/mcp-server"]
    }
  }
}
```

### Claude Code

Add to your Claude Code settings:

```json
{
  "mcpServers": {
    "rustledger": {
      "command": "npx",
      "args": ["-y", "@rustledger/mcp-server"]
    }
  }
}
```

## Available Tools

| Tool | Description |
|------|-------------|
| `validate` | Validate a Beancount ledger for errors |
| `query` | Run BQL queries on a ledger |
| `balances` | Get account balances (shorthand for BALANCES query) |
| `format` | Format a ledger with consistent alignment |
| `parse` | Parse a ledger and return structured data |
| `completions` | Get BQL query completions |
| `list_plugins` | List available native plugins |
| `run_plugin` | Run a native plugin on a ledger |

## Example Usage

Once configured, you can ask your AI assistant:

- "Validate this beancount file for errors"
- "What's my current balance in Assets:Checking?"
- "Show me all restaurant expenses this month"
- "Format this beancount ledger"

## Resources

The server also exposes documentation:

- `rustledger://docs/bql` - BQL Query Language Reference

## License

GPL-3.0
