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

### Core Tools

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

### Editor Tools (LSP-like)

| Tool | Description |
|------|-------------|
| `editor_completions` | Get context-aware completions at a position |
| `editor_hover` | Get hover information for symbols |
| `editor_definition` | Go to definition for accounts/currencies |
| `editor_document_symbols` | Get document outline/structure |
| `editor_references` | Find all references to accounts/currencies/payees |

Each editor tool accepts either inline `source` **or** a `file_path` (one is
required). With `file_path` the server reads the file from disk, so you can ask
for hover/completions at a cursor position without inlining the whole ledger.
If both are given, `source` is the unsaved-buffer contents and wins, while
`file_path` still anchors include resolution.

`editor_hover` and `editor_completions` additionally **resolve `include`
directives** when `file_path` is set — so an account's balance/usage count and
the completion candidates reflect the whole ledger, not just the edited file.
`editor_definition`, `editor_references` and `editor_document_symbols` operate
on the edited document only (their results are file-local locations, so
cross-file resolution is intentionally not performed).

### Analysis Tools

| Tool | Description |
|------|-------------|
| `ledger_stats` | Get statistics (directive counts, date range, etc.) |
| `list_accounts` | List all accounts with open/close dates |
| `list_commodities` | List all currencies/commodities |
| `account_activity` | Get activity summary for an account |

### Utility Tools

| Tool | Description |
|------|-------------|
| `format_check` | Check if ledger is properly formatted |
| `bql_tables` | Get BQL table documentation |
| `directive_at_line` | Get directive at a specific line |
| `find_transactions` | Find transactions by criteria |

### Report Tools

| Tool | Description |
|------|-------------|
| `report` | Generate balance sheet, income, holdings, networth |

### File Operation Tools

| Tool | Description |
|------|-------------|
| `validate_file` | Validate a file from filesystem |
| `query_file` | Run BQL query on a file |
| `format_file` | Format a file (with optional write-back) |

## Resources

The server exposes documentation resources:

| Resource | Description |
|----------|-------------|
| `rustledger://docs/bql` | BQL Query Language Reference |
| `rustledger://docs/validation-errors` | All 26 validation error codes |
| `rustledger://docs/bql-functions` | Complete BQL function reference |
| `rustledger://docs/directives` | Beancount directive syntax |

## Prompts

The server provides helpful prompts:

| Prompt | Description |
|--------|-------------|
| `analyze_ledger` | Analyze a ledger for insights |
| `write_query` | Help write BQL queries from natural language |
| `categorize_transaction` | Help categorize transactions |

## Example Usage

Once configured, you can ask your AI assistant:

- "Validate this beancount file for errors"
- "What's my current balance in Assets:Checking?"
- "Show me all restaurant expenses this month"
- "Format this beancount ledger"
- "Generate a balance sheet report"
- "Find all transactions with 'Amazon' in the payee"
- "What accounts do I have?"

## Development

To develop the MCP server locally with a local build of the WASM package:

```bash
# Build the WASM package
cd crates/rustledger-wasm
wasm-pack build --target web

# Rename package for npm link compatibility
cd pkg
sed -i 's/"name": "rustledger-wasm"/"name": "@rustledger\/wasm"/' package.json
npm link

# Link in the MCP server
cd ../../../packages/mcp-server
npm link @rustledger/wasm
npm install
npm run build
```

To unlink and use the published npm package:

```bash
cd packages/mcp-server
npm unlink @rustledger/wasm
npm install
```

## License

GPL-3.0
