# rustledger-lsp

Language Server Protocol (LSP) implementation for Beancount files.

## Features

- **Diagnostics**: Real-time syntax and validation errors
- **Completion**: Accounts, currencies, payees, tags, links
- **Hover**: Account balances, metadata, directive info
- **Go to Definition**: Jump to account/commodity declarations
- **Find References**: Find all uses of an account or commodity
- **Document Symbols**: Outline view of accounts and directives
- **Workspace Symbols**: Search across all files
- **Rename**: Rename accounts across files
- **Code Actions**: Quick fixes for common issues
- **Formatting**: Format documents and selections
- **Folding**: Collapse transactions and sections
- **Semantic Highlighting**: Rich syntax coloring
- **Inlay Hints**: Inline balance and cost annotations
- **Code Lens**: Inline account statistics

## Installation

The LSP server is included with rustledger:

```bash
# Via package manager (includes rledger-lsp)
brew install rustledger/rustledger/rustledger
yay -S rustledger-bin
cargo install rustledger

# Or build from source
cargo build --release -p rustledger-lsp
```

## Usage

```bash
# Start the LSP server (communicates via stdio)
rledger-lsp

# Check version
rledger-lsp --version
```

## Editor Setup

### VS Code

Install the Beancount extension and configure custom LSP:

```json
// .vscode/settings.json
{
  "beancount.languageServerPath": "rledger-lsp"
}
```

Or use a generic LSP client extension like "vscode-lsp-sample".

### Neovim (nvim-lspconfig)

```lua
-- Add to your Neovim config
local lspconfig = require('lspconfig')
local configs = require('lspconfig.configs')

-- Register rledger-lsp if not already defined
if not configs.rledger then
  configs.rledger = {
    default_config = {
      cmd = { 'rledger-lsp' },
      filetypes = { 'beancount' },
      root_dir = lspconfig.util.root_pattern('.git', '*.beancount'),
      settings = {},
    },
  }
end

lspconfig.rledger.setup {}
```

### Helix

Add to `~/.config/helix/languages.toml`:

```toml
[[language]]
name = "beancount"
scope = "source.beancount"
injection-regex = "beancount"
file-types = ["beancount", "bean"]
comment-token = ";"
indent = { tab-width = 2, unit = "  " }
language-servers = ["rledger-lsp"]

[language-server.rledger-lsp]
command = "rledger-lsp"
```

### Zed

Add to `~/.config/zed/settings.json`:

```json
{
  "lsp": {
    "rledger-lsp": {
      "binary": {
        "path": "rledger-lsp"
      }
    }
  },
  "languages": {
    "Beancount": {
      "language_servers": ["rledger-lsp"]
    }
  }
}
```

### Emacs (lsp-mode)

```elisp
(use-package lsp-mode
  :hook (beancount-mode . lsp)
  :config
  (lsp-register-client
   (make-lsp-client
    :new-connection (lsp-stdio-connection '("rledger-lsp"))
    :major-modes '(beancount-mode)
    :server-id 'rledger-lsp)))
```

### Emacs (eglot)

```elisp
(add-to-list 'eglot-server-programs
             '(beancount-mode . ("rledger-lsp")))
```

### Sublime Text (LSP)

Install the LSP package, then add to LSP settings:

```json
{
  "clients": {
    "rledger": {
      "enabled": true,
      "command": ["rledger-lsp"],
      "selector": "source.beancount"
    }
  }
}
```

## Troubleshooting

**LSP not starting?**
- Ensure `rledger-lsp` is in your PATH: `which rledger-lsp`
- Check logs: most editors have an LSP log panel
- Try running manually: `echo '{"jsonrpc":"2.0","method":"initialize","id":1,"params":{}}' | rledger-lsp`

**No completions?**
- Ensure the file has `.beancount` extension
- Check that your editor's LSP client is configured for the beancount filetype

## Architecture

Based on rust-analyzer patterns:
- Main loop handles LSP messages via stdio
- Notifications processed synchronously
- Requests dispatched to threadpool
- Revision-based cancellation for stale requests
- Virtual file system for unsaved buffers

## License

GPL-3.0-only
