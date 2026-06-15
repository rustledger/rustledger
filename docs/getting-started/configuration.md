______________________________________________________________________

## title: Configuration description: Configure rustledger with profiles and options

# Configuration

rustledger can be configured via environment variables, config files, and command-line options.

## Environment Variables

| Variable | Description | Example |
|----------|-------------|---------|
| `RLEDGER_FILE` | Default beancount file | `~/ledger.beancount` |
| `RLEDGER_PROFILE` | Active profile name | `business` |
| `NO_COLOR` | Disable colored output | `1` |

Set in your shell profile (`~/.bashrc`, `~/.zshrc`):

```bash
export RLEDGER_FILE="$HOME/finances/main.beancount"
```

## Config File

rustledger looks for configuration in these locations (highest to lowest priority):

1. `.rledger.toml` in the current directory (searching upward)
1. `~/.config/rledger/config.toml` (user config)
1. `/etc/rledger/config.toml` (system config, Unix only)

Higher priority configs override lower ones. You can also generate a default config with:

```bash
rledger config init           # Create user config
rledger config init --project # Create project config (.rledger.toml)
rledger config edit           # Open config in editor
rledger config show           # Show merged configuration
```

### Example Config

```toml
# ~/.config/rledger/config.toml

[default]
# Default beancount file
file = "~/finances/main.beancount"

# Editor for interactive commands (defaults to $EDITOR)
# editor = "nvim"

# Command-specific output settings
[commands.query.output]
format = "text"

[commands.report.output]
format = "text"

# Profiles for different ledgers
[profiles.personal]
file = "~/finances/personal.beancount"

[profiles.business]
file = "~/finances/business.beancount"

# Command aliases
[aliases]
bal = "report balances"
is = "report income"
bs = "report balsheet"
```

### Using Profiles

```bash
# Use a profile
rledger check -P personal
rledger report balances -P business

# Override ledger file
rledger check ~/other/ledger.beancount
```

## Beancount Options

Set options in your beancount file:

```beancount
option "title" "My Personal Finances"
option "operating_currency" "USD"
option "booking_method" "FIFO"
```

### Common Options

| Option | Description | Default |
|--------|-------------|---------|
| `title` | Ledger title | (none) |
| `operating_currency` | Main currency | (none) |
| `booking_method` | FIFO, LIFO, AVERAGE, etc. | STRICT |
| `account_previous_balances` | Retained earnings account | `Equity:Opening-Balances` |
| `account_current_earnings` | Current earnings account | `Equity:Earnings:Current` |
| `inferred_tolerance_default` | Per-currency balance tolerance (e.g. `USD:0.005`) | (none) |

### Booking Methods

```beancount
; First-in, first-out
option "booking_method" "FIFO"

; Last-in, first-out
option "booking_method" "LIFO"

; Average cost
option "booking_method" "AVERAGE"

; Strict matching (default)
option "booking_method" "STRICT"
```

## Shell Aliases

For quick commands, add aliases to your shell:

```bash
# ~/.bashrc or ~/.zshrc

export RLEDGER_FILE="$HOME/finances/main.beancount"

# Quick commands
alias rc='rledger check'
alias rq='rledger query'
alias rb='rledger report balances -a'
alias rr='rledger report journal -a'
alias rbal='rledger report balsheet'
alias ris='rledger report income'

# Usage:
# rc                    - check ledger
# rb Expenses:Food      - balance for food expenses
# rr Assets:Bank        - register for bank accounts
```

## Editor Integration

### VS Code

Install the rustledger VS Code extension (a thin LSP client around `rledger-lsp`). Point it at the LSP binary if it is not already on your `PATH`:

```json
{
  "rustledger.server.path": "rledger-lsp"
}
```

### Neovim

Using nvim-lspconfig (register the server manually, since it is not built in):

```lua
local lspconfig = require('lspconfig')
local configs = require('lspconfig.configs')

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
language-servers = ["rustledger"]

[language-server.rustledger]
command = "rledger-lsp"
```

See [Editor Integration](../guides/editor-integration.md) for detailed setup instructions.

## Next Steps

- [Commands Reference](../commands/index.md) - All CLI commands
- [Shell Aliases](../guides/shell-aliases.md) - More alias examples
- [Editor Integration](../guides/editor-integration.md) - Full editor setup
