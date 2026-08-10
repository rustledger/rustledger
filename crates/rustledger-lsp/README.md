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
brew install rustledger
yay -S rustledger-bin

# Via Cargo (LSP is a separate crate)
cargo install rustledger-lsp

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

Download `rustledger-vscode.vsix` from the [latest release](https://github.com/rustledger/rustledger/releases/latest) and install:

```bash
code --install-extension rustledger-vscode.vsix
```

The extension provides syntax highlighting and automatically connects to `rledger-lsp` for completions, diagnostics, hover, and more. If `rledger-lsp` is not installed, it will prompt you to install it.

#### Nix / home-manager

The extension is a flake output, so it can be pinned with the same input as
everything else (issue #1998):

In your flake, add the input and hand it to home-manager:

```nix
# flake.nix
{
  inputs.rustledger.url = "github:rustledger/rustledger";

  outputs = { nixpkgs, home-manager, rustledger, ... }: {
    homeConfigurations."you" = home-manager.lib.homeManagerConfiguration {
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      extraSpecialArgs = { inherit rustledger; };
      modules = [ ./home.nix ];
    };
  };
}
```

Then, in the home-manager module:

```nix
# home.nix
{ pkgs, rustledger, ... }:
{
  programs.vscode.profiles.default.extensions = [
    rustledger.packages.${pkgs.system}.vscode-extension
  ];

  # The extension looks for `rledger-lsp` on PATH. This flake's `rustledger`
  # package ships it alongside `rledger`, so installing it here gives an
  # extension and a server that are guaranteed to be the same version.
  home.packages = [ rustledger.packages.${pkgs.system}.default ];
}
```

If you would rather not put the server on PATH, set `rustledger.server.path`
to an absolute path instead.

The extension's built-in update check is **disabled by default in the Nix
build**. Elsewhere it offers to download a newer `.vsix` from GitHub and
install it, which would place a second copy outside Nix and quietly detach the
extension from your configuration. Re-enable `rustledger.checkForUpdates` if
you want that behavior anyway.

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
