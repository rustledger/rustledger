______________________________________________________________________

## title: Shell Aliases description: Create shortcuts for common commands

# Shell Aliases

Create convenient shortcuts for common rustledger commands.

## Why Aliases?

If you're coming from ledger-cli or hledger, you might miss commands like `bal` and `reg`. With shell aliases, you can create any shortcuts you want.

## Basic Setup

Add these to your `~/.bashrc`, `~/.zshrc`, or shell config:

```bash
# Primary ledger file
export LEDGER_FILE="$HOME/finances/ledger.beancount"

# Short command name
alias rl='rledger'

# Common reports
alias bal='rledger report "$LEDGER_FILE" balances'
alias balsheet='rledger report "$LEDGER_FILE" balsheet'
alias is='rledger report "$LEDGER_FILE" income'
alias reg='rledger report "$LEDGER_FILE" journal'

# Validation
alias check='rledger check "$LEDGER_FILE"'

# Query shortcut
alias q='rledger query "$LEDGER_FILE"'
```

## Usage Examples

After setting up aliases:

```bash
# Check your ledger
check

# View account balances
bal

# View recent transactions
reg

# Run a query
q "SELECT account, sum(position) WHERE account ~ 'Expenses' GROUP BY account"
```

## Advanced Aliases

### With Arguments

Create functions for more flexibility:

```bash
# Balance for specific account
bal() {
  if [ -n "$1" ]; then
    rledger report "$LEDGER_FILE" balances -a "$1"
  else
    rledger report "$LEDGER_FILE" balances
  fi
}

# Register filtered by account
reg() {
  if [ -n "$1" ]; then
    rledger report "$LEDGER_FILE" journal -a "$1"
  else
    rledger report "$LEDGER_FILE" journal
  fi
}

# Usage:
# bal                    # All balances
# bal Assets:Bank        # Just bank accounts
# reg Expenses:Food      # Food transactions
```

### Common Queries

```bash
# Monthly expenses summary
alias expenses='rledger query "$LEDGER_FILE" "SELECT root(account, 2), sum(cost(position)) WHERE account ~ \"Expenses\" GROUP BY 1 ORDER BY sum(cost(position)) DESC"'

# Net worth
alias networth='rledger query "$LEDGER_FILE" "SELECT sum(cost(position)) WHERE account ~ \"Assets\" OR account ~ \"Liabilities\""'

# This month's spending
alias thismonth='rledger query "$LEDGER_FILE" "SELECT root(account, 2), sum(cost(position)) WHERE account ~ \"Expenses\" AND year(date) = year(today()) AND month(date) = month(today()) GROUP BY 1"'
```

### Date Filters

```bash
# Transactions from specific period
period() {
  rledger query "$LEDGER_FILE" "SELECT date, account, position WHERE date >= $1 AND date <= $2"
}

# Usage: period 2024-01-01 2024-03-31
```

## Output Format Shortcuts

```bash
# CSV export
alias bal-csv='rledger report "$LEDGER_FILE" balances -f csv'

# JSON for scripting
alias bal-json='rledger report "$LEDGER_FILE" balances -f json'
```

## Per-Project Aliases

For multiple ledgers, use shell functions:

```bash
# Personal finances
personal() {
  LEDGER_FILE="$HOME/finances/personal.beancount" "$@"
}

# Business finances
business() {
  LEDGER_FILE="$HOME/finances/business.beancount" "$@"
}

# Usage:
# personal bal
# business check
```

Or use direnv for directory-based switching:

```bash
# ~/finances/personal/.envrc
export LEDGER_FILE="$PWD/ledger.beancount"

# ~/finances/business/.envrc
export LEDGER_FILE="$PWD/ledger.beancount"
```

## Complete Example

Here's a complete alias setup:

```bash
# ~/.bashrc or ~/.zshrc

# === Rustledger Configuration ===
export LEDGER_FILE="$HOME/finances/ledger.beancount"

# Base command
alias rl='rledger'

# Validation
alias check='rledger check "$LEDGER_FILE"'

# Reports
alias bal='rledger report "$LEDGER_FILE" balances'
alias balsheet='rledger report "$LEDGER_FILE" balsheet'
alias is='rledger report "$LEDGER_FILE" income'

# Journal/register with optional account filter
reg() {
  if [ -n "$1" ]; then
    rledger report "$LEDGER_FILE" journal -a "$1"
  else
    rledger report "$LEDGER_FILE" journal
  fi
}

# Query shortcut
q() {
  rledger query "$LEDGER_FILE" "$@"
}

# Common reports
alias expenses='q "SELECT root(account, 2), sum(cost(position)) WHERE account ~ \"Expenses\" GROUP BY 1 ORDER BY sum(cost(position)) DESC"'
alias networth='q "SELECT sum(cost(position)) WHERE account ~ \"Assets\" OR account ~ \"Liabilities\""'

# Format in-place
alias fmt='rledger format --in-place "$LEDGER_FILE"'

# Edit ledger
alias led='$EDITOR "$LEDGER_FILE"'
```

## Fish Shell

For Fish shell users:

```fish
# ~/.config/fish/config.fish

set -x LEDGER_FILE "$HOME/finances/ledger.beancount"

alias rl='rledger'
alias check='rledger check $LEDGER_FILE'
alias bal='rledger report $LEDGER_FILE balances'
alias balsheet='rledger report $LEDGER_FILE balsheet'

function reg
    if test -n "$argv[1]"
        rledger report $LEDGER_FILE journal -a $argv[1]
    else
        rledger report $LEDGER_FILE journal
    end
end

function q
    rledger query $LEDGER_FILE $argv
end
```

## See Also

- [Configuration](../getting-started/configuration.md) - Config file setup
- [Common Queries](common-queries.md) - Queries to use with aliases
