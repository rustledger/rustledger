______________________________________________________________________

## title: Editor Integration description: VS Code, Vim, Neovim, and Emacs setup

# Editor Integration

Set up your editor for beancount editing with syntax highlighting, completion, and diagnostics.

## VS Code

The VS Code extension is a thin wrapper that connects to `rledger-lsp`. **All features require `rledger-lsp` to be installed.**

### 1. Install rledger-lsp

```bash
# macOS
brew install rustledger

# Arch Linux
yay -S rustledger-bin

# Cargo
cargo install rustledger-lsp
```

### 2. Install the extension

Download `rustledger-vscode.vsix` from the [latest release](https://github.com/rustledger/rustledger/releases/latest) and install:

```bash
code --install-extension rustledger-vscode.vsix
```

Or in VS Code: `Ctrl+Shift+P` → "Extensions: Install from VSIX..." → select the downloaded file.

### Optional: Enable format on save

Add to your `.vscode/settings.json`:

```json
{
  "[beancount]": {
    "editor.formatOnSave": true
  }
}
```

### Settings

| Setting | Default | Description |
|---------|---------|-------------|
| `rustledger.server.path` | `rledger-lsp` | Path to the rledger-lsp binary |
| `rustledger.server.extraArgs` | `[]` | Extra arguments passed to rledger-lsp |
| `rustledger.journalFile` | `""` | Root journal file (auto-discovered if empty) |
| `rustledger.checkForUpdates` | `true` | Check for extension updates on startup |

### Auto-Update

The extension automatically checks for updates on startup and notifies you when a new version is available. Updates are downloaded directly from GitHub Releases. To disable, set `rustledger.checkForUpdates` to `false`.

You can also manually check via: `Ctrl+Shift+P` → "rustledger: Check for Updates"

### Features

All features are provided by `rledger-lsp`:

- Semantic highlighting
- Real-time error diagnostics
- Account, payee, and tag completion
- Go to definition (accounts, commodities)
- Find all references
- Hover information (account balances, metadata)
- Document symbols / outline
- Code formatting
- Rename refactoring
- Inlay hints and code lens

### Troubleshooting VS Code

If LSP features aren't working:

1. Ensure `rledger-lsp` is in your PATH:

   ```bash
   which rledger-lsp
   ```

1. Check the Output panel (`View > Output`) and select "rustledger" from the dropdown

1. If you installed via a package manager, you may need to restart VS Code after installation

## Vim / Neovim

### Using Native LSP (Neovim)

Neovim 0.5+ has built-in LSP support. Add to your config:

```lua
-- init.lua or lua/lsp.lua

local lspconfig = require('lspconfig')

-- rustledger LSP configuration
local configs = require('lspconfig.configs')
if not configs.rustledger then
  configs.rustledger = {
    default_config = {
      cmd = { 'rledger-lsp' },
      filetypes = { 'beancount' },
      root_dir = lspconfig.util.root_pattern('.git', 'main.beancount', 'ledger.beancount'),
      settings = {},
    },
  }
end

lspconfig.rustledger.setup{}
```

### Using coc.nvim

Add to `~/.vim/coc-settings.json`:

```json
{
  "languageserver": {
    "rustledger": {
      "command": "rledger-lsp",
      "args": [],
      "filetypes": ["beancount"],
      "rootPatterns": [".git", "main.beancount", "ledger.beancount"]
    }
  }
}
```

### Syntax Highlighting

For syntax highlighting without LSP, use the beancount vim plugin:

```vim
" vim-plug
Plug 'nathangrigg/vim-beancount'

" Or Packer (Neovim)
use 'nathangrigg/vim-beancount'
```

### Filetype Detection

If `.beancount` files aren't detected, add to your config:

```vim
" ~/.vimrc or init.vim
autocmd BufNewFile,BufRead *.beancount setfiletype beancount
```

### Complete Neovim Setup

Example `init.lua` with LSP, completion, and formatting:

```lua
-- Plugin manager (lazy.nvim example)
require('lazy').setup({
  'nathangrigg/vim-beancount',
  'neovim/nvim-lspconfig',
  'hrsh7th/nvim-cmp',
  'hrsh7th/cmp-nvim-lsp',
})

-- LSP setup
local lspconfig = require('lspconfig')
local configs = require('lspconfig.configs')

if not configs.rustledger then
  configs.rustledger = {
    default_config = {
      cmd = { 'rledger-lsp' },
      filetypes = { 'beancount' },
      root_dir = lspconfig.util.root_pattern('.git', '*.beancount'),
    },
  }
end

lspconfig.rustledger.setup{
  capabilities = require('cmp_nvim_lsp').default_capabilities(),
}

-- Completion setup
local cmp = require('cmp')
cmp.setup({
  sources = {
    { name = 'nvim_lsp' },
  },
  mapping = cmp.mapping.preset.insert({
    ['<C-Space>'] = cmp.mapping.complete(),
    ['<CR>'] = cmp.mapping.confirm({ select = true }),
  }),
})

-- Format on save
vim.api.nvim_create_autocmd('BufWritePre', {
  pattern = '*.beancount',
  callback = function()
    vim.lsp.buf.format()
  end,
})
```

## Emacs

### Using eglot (built-in, Emacs 29+)

```elisp
;; init.el
(require 'eglot)

(add-to-list 'eglot-server-programs
             '(beancount-mode . ("rledger-lsp")))

(add-hook 'beancount-mode-hook 'eglot-ensure)
```

### Using lsp-mode

```elisp
;; init.el
(require 'lsp-mode)

(add-to-list 'lsp-language-id-configuration
             '(beancount-mode . "beancount"))

(lsp-register-client
 (make-lsp-client
  :new-connection (lsp-stdio-connection '("rledger-lsp"))
  :major-modes '(beancount-mode)
  :server-id 'rustledger))

(add-hook 'beancount-mode-hook #'lsp)
```

### beancount-mode

Install beancount-mode for syntax highlighting:

```elisp
;; Using use-package
(use-package beancount
  :mode ("\\.beancount\\'" . beancount-mode)
  :hook (beancount-mode . eglot-ensure))
```

Or manually:

```elisp
(add-to-list 'load-path "/path/to/beancount-mode")
(require 'beancount)
(add-to-list 'auto-mode-alist '("\\.beancount\\'" . beancount-mode))
```

## Helix

Add to `~/.config/helix/languages.toml`:

```toml
[[language]]
name = "beancount"
scope = "source.beancount"
injection-regex = "beancount"
file-types = ["beancount"]
roots = [".git"]
language-servers = ["rustledger"]

[language-server.rustledger]
command = "rledger-lsp"
args = []
```

## Sublime Text

### LSP-rustledger

1. Install Package Control
1. Install "LSP" package
1. Add to LSP settings:

```json
{
  "clients": {
    "rustledger": {
      "enabled": true,
      "command": ["rledger-lsp"],
      "selector": "source.beancount"
    }
  }
}
```

### Syntax Highlighting

Install "Beancount" package from Package Control.

## Troubleshooting

### LSP Not Starting

Check that `rledger-lsp` is in your PATH:

```bash
which rledger-lsp
rledger-lsp --version
```

Test LSP manually:

```bash
echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}' | rledger-lsp
```

### No Completions

Ensure your ledger file is valid:

```bash
rledger check ledger.beancount
```

LSP features require a parseable file.

### Slow Diagnostics

For large ledgers, consider using `include` to split files. The LSP only processes files in the include tree.

### File Not Recognized

Ensure `.beancount` extension and proper filetype detection:

```bash
# Check file type in Vim
:set ft?

# Should show: filetype=beancount
```

## See Also

- [Configuration](../getting-started/configuration.md) - Config file reference
- [format command](../commands/format.md) - CLI formatting
