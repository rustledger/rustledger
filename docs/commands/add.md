______________________________________________________________________

## title: rledger add description: Add transactions interactively

# rledger add

Add transactions to your ledger interactively or via quick mode.

## Usage

```bash
rledger add [OPTIONS] [FILE]
```

## Arguments

| Argument | Description |
|----------|-------------|
| `FILE` | File to append transaction to (uses config default if not specified) |

## Options

| Option | Description |
|--------|-------------|
| `-P, --profile <PROFILE>` | Use a profile from config |
| `-d, --date <DATE>` | Transaction date (YYYY-MM-DD, "today", "yesterday", "+1", "-1") |
| `-n, --dry-run` | Print transaction without appending |
| `-y, --yes` | Append without the confirmation prompt. Needed when stdin is not a terminal: there only an explicit `y` answers the prompt, and no answer is an error that writes nothing |
| `-q, --quick <ARGS>...` | Quick mode (see below) |
| `--no-completion` | Disable account tab completion |

## Interactive Mode

Without `--quick`, opens an interactive prompt:

```bash
rledger add ledger.beancount
```

```
Date [today]: 2024-03-15
Payee: Coffee Shop
Narration: Morning coffee
Account: Expenses:Food:Coffee
Amount: 5.50 USD
Account: Assets:Wallet
Amount: [auto-balanced]

2024-03-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food:Coffee  5.50 USD
  Assets:Wallet        -5.50 USD

Append to ledger.beancount? [Y/n]
```

Features:

- Tab completion for account names
- Auto-balancing for the last posting
- Date shortcuts: "today", "yesterday", "+1" (tomorrow), "-1" (yesterday)

## Quick Mode

Add transactions in a single command:

```bash
rledger add -q "Coffee Shop" "Morning coffee" Expenses:Food:Coffee 5.50 Assets:Wallet
```

Format: `payee narration account amount [account [amount]]...`

### Examples

```bash
# Simple expense
rledger add -q "Grocery Store" "Weekly groceries" Expenses:Food 85.50 Assets:Bank:Checking

# With specific date
rledger add -d 2024-03-10 -q "Amazon" "Books" Expenses:Books 29.99 Liabilities:CreditCard

# Multiple postings
rledger add -q "Transfer" "Savings" Assets:Savings 500 Assets:Checking -500

# Dry run (preview without saving)
rledger add -n -q "Test" "Test transaction" Expenses:Test 10 Assets:Cash
```

## See Also

- [Quick Start](../getting-started/quick-start.md) - Getting started guide
- [Syntax Reference](../reference/syntax.md) - Transaction syntax
