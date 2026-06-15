______________________________________________________________________

## title: Multi-file Ledgers description: Organizing large ledgers across multiple files

# Multi-file Ledgers

As your ledger grows, splitting it across multiple files improves organization and performance.

## Basic Structure

Use `include` directives to combine files:

```beancount
; main.beancount - Entry point
option "title" "Personal Finances"
option "operating_currency" "USD"

include "accounts.beancount"
include "prices.beancount"
include "2023.beancount"
include "2024.beancount"
```

## Recommended Layout

```
finances/
├── main.beancount          # Entry point, options
├── accounts.beancount      # Account definitions
├── commodities.beancount   # Commodity definitions
├── prices.beancount        # Price history
├── 2023/
│   ├── index.beancount     # include all 2023 files
│   ├── q1.beancount
│   ├── q2.beancount
│   ├── q3.beancount
│   └── q4.beancount
└── 2024/
    ├── index.beancount
    └── ...
```

### main.beancount

```beancount
option "title" "Personal Finances"
option "operating_currency" "USD"

include "accounts.beancount"
include "commodities.beancount"
include "prices.beancount"
include "2023/index.beancount"
include "2024/index.beancount"
```

### accounts.beancount

```beancount
; Account definitions
2020-01-01 open Assets:Bank:Checking        USD
2020-01-01 open Assets:Bank:Savings         USD
2020-01-01 open Assets:Brokerage            USD,AAPL,GOOGL
2020-01-01 open Liabilities:CreditCard      USD
2020-01-01 open Expenses:Food
2020-01-01 open Expenses:Transport
2020-01-01 open Income:Salary               USD
2020-01-01 open Equity:Opening-Balances
```

### 2024/index.beancount

```beancount
include "q1.beancount"
include "q2.beancount"
```

## Organization Strategies

### By Time Period

Most common approach - one file per month or quarter:

```
2024/
├── 01-january.beancount
├── 02-february.beancount
└── ...
```

### By Account

For separate tracking of business/personal:

```
finances/
├── personal/
│   ├── main.beancount
│   └── ...
└── business/
    ├── main.beancount
    └── ...
```

### By Source

Organize by data source (bank, credit card):

```
finances/
├── accounts.beancount
├── imports/
│   ├── chase-checking.beancount
│   ├── chase-card.beancount
│   └── schwab-brokerage.beancount
└── manual.beancount
```

## Include Patterns

### Glob Patterns

Include multiple files with wildcards:

```beancount
include "2024/*.beancount"
include "imports/**/*.beancount"
```

### Conditional Includes

No built-in conditional, but you can use separate entry points:

```bash
# Full ledger
rledger check main.beancount

# Just 2024
rledger check 2024/index.beancount
```

## Best Practices

### 1. One Entry Point

Have a single `main.beancount` that includes everything:

```bash
# Always use the same entry point
rledger check main.beancount
rledger report main.beancount balances
```

### 2. Accounts in One Place

Keep all `open` and `close` directives together:

```beancount
; accounts.beancount
2020-01-01 open Assets:Bank:Checking USD
; ... all accounts
```

### 3. Chronological Transaction Files

Keep transactions in date order within files:

```beancount
; 2024/q1.beancount
2024-01-02 * "Transaction 1"
  ...

2024-01-03 * "Transaction 2"
  ...
```

### 4. Prices Separate

Price directives don't need to be near transactions:

```beancount
; prices.beancount
2024-01-01 price AAPL 185.00 USD
2024-01-02 price AAPL 186.50 USD
; Auto-updated by rledger price
```

### 5. Include Order Matters

For options and plugins, include order affects behavior:

```beancount
; Options must come first
option "operating_currency" "USD"

; Then plugins
plugin "beancount.plugins.auto_accounts"

; Then data files
include "accounts.beancount"
include "transactions.beancount"
```

## Working with Multi-file Ledgers

### Check All Files

```bash
rledger check main.beancount
```

Errors show file paths:

```
accounts.beancount:15: error: Duplicate account open
```

### Query Across Files

Queries work on the combined ledger:

```bash
rledger query main.beancount "SELECT ..."
```

### Format All Files

```bash
# Format each file individually
for f in *.beancount 2024/*.beancount; do
  rledger format --in-place "$f"
done
```

### LSP Support

Point your editor to `main.beancount`. The LSP follows includes automatically.

## Troubleshooting

### Duplicate Definitions

If you get duplicate account errors, ensure accounts are only opened once:

```bash
rledger query main.beancount "SELECT DISTINCT account" | sort | uniq -d
```

### Missing Includes

Check for typos in include paths:

```bash
rledger check main.beancount
# Will error on missing files
```

### Circular Includes

Avoid files that include each other:

```beancount
; a.beancount
include "b.beancount"  ; DON'T if b includes a

; b.beancount
include "a.beancount"  ; Creates circular dependency
```

## See Also

- [Configuration](../getting-started/configuration.md) - Config file setup
- [check command](../commands/check.md) - Validation
