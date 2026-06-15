______________________________________________________________________

## title: Quick Start description: Your first rustledger commands

# Quick Start

This guide walks you through basic rustledger usage.

## Create a Ledger File

Create a file called `ledger.beancount`:

```beancount
; Define accounts
2024-01-01 open Assets:Bank:Checking
2024-01-01 open Assets:Cash
2024-01-01 open Expenses:Food
2024-01-01 open Expenses:Transport
2024-01-01 open Income:Salary
2024-01-01 open Equity:Opening-Balances

; Opening balance
2024-01-01 * "Opening Balance"
  Assets:Bank:Checking   1000.00 USD
  Equity:Opening-Balances

; Transactions
2024-01-15 * "Employer" "Monthly salary"
  Assets:Bank:Checking   3000.00 USD
  Income:Salary

2024-01-16 * "Grocery Store" "Weekly groceries"
  Expenses:Food           150.00 USD
  Assets:Bank:Checking

2024-01-17 * "Metro" "Transit pass"
  Expenses:Transport       50.00 USD
  Assets:Cash
```

## Validate Your Ledger

Check for errors:

```bash
rledger check ledger.beancount
```

If everything is correct, you'll see:

```
✓ No errors found
```

## View Balances

See all account balances:

```bash
rledger report ledger.beancount balances
```

Output:

```
Account Balances
============================================================

Assets:Bank:Checking
          3850.00 USD
Assets:Cash
           -50.00 USD
Equity:Opening-Balances
         -1000.00 USD
Expenses:Food
           150.00 USD
Expenses:Transport
            50.00 USD
Income:Salary
         -3000.00 USD
```

## Run Queries

Use BQL (Beancount Query Language) for custom reports:

```bash
# Total expenses by category
rledger query ledger.beancount "
  SELECT account, sum(position)
  WHERE account ~ 'Expenses'
  GROUP BY account
"

# Recent transactions
rledger query ledger.beancount "
  SELECT date, narration, account, position
  ORDER BY date DESC
  LIMIT 5
"
```

## Generate Reports

```bash
# Balance sheet
rledger report ledger.beancount balsheet

# Income statement
rledger report ledger.beancount income

# Transaction register
rledger report ledger.beancount journal
```

## Format Your Ledger

Auto-format your file for consistent style:

```bash
# Preview changes
rledger format ledger.beancount

# Format in place
rledger format --in-place ledger.beancount
```

## Set a Default Ledger File

Avoid typing the filename every time:

```bash
# Set environment variable
export RLEDGER_FILE="$HOME/finances/ledger.beancount"

# Now commands use it automatically
rledger check
rledger report balances
```

Add this to your `~/.bashrc` or `~/.zshrc` to make it permanent.

Alternatively, create a config file:

```bash
rledger config init
rledger config edit  # In the [default] section, set file = "~/finances/ledger.beancount"
```

## Next Steps

- [Configuration](configuration.md) - Profiles, options, and customization
- [Commands Reference](../commands/index.md) - Full CLI documentation
- [Common Queries](../guides/common-queries.md) - Useful BQL examples
