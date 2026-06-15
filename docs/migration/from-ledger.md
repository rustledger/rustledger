______________________________________________________________________

## title: Migrating from Ledger-CLI description: Switch from ledger-cli to rustledger

# Migrating from Ledger-CLI

This guide helps you migrate from ledger-cli to rustledger's beancount format.

## Key Differences

### Syntax

| Feature | Ledger | Beancount |
|---------|--------|-----------|
| Account separator | `:` | `:` |
| Transaction flag | None or `*`/`!` | Required `*` or `!` |
| Amounts | Right side | Right side |
| Balance assertions | `= AMOUNT` | `balance` directive |
| Currencies | After amount | After amount |
| Comments | `;` or `#` | `;` |

### Philosophy

| Aspect | Ledger | Beancount |
|--------|--------|-----------|
| Double-entry | Optional | Required |
| Balance checking | Optional | Always |
| Account declaration | Optional | Required (`open`) |
| Commodity declaration | Optional | Optional (`commodity`) |

## Conversion Example

### Ledger Format

```ledger
; ~/.ledger
2024-01-15 Coffee Shop
    Expenses:Food:Coffee     $5.00
    Assets:Cash

2024-01-16 * Grocery Store
    Expenses:Food:Groceries  $45.00
    Assets:Checking

= Expenses:Food
    [Budget:Food]           -1.0
```

### Beancount Format

```beancount
; ledger.beancount
option "operating_currency" "USD"

2020-01-01 open Assets:Cash            USD
2020-01-01 open Assets:Checking        USD
2020-01-01 open Expenses:Food:Coffee
2020-01-01 open Expenses:Food:Groceries

2024-01-15 * "Coffee Shop"
  Expenses:Food:Coffee     5.00 USD
  Assets:Cash             -5.00 USD

2024-01-16 * "Grocery Store"
  Expenses:Food:Groceries  45.00 USD
  Assets:Checking         -45.00 USD
```

## Migration Steps

### 1. Export from Ledger

First, print your ledger in a clean format:

```bash
ledger -f ledger.dat print > ledger-export.dat
```

### 2. Convert Syntax

Key changes needed:

#### Add Account Opens

Extract all accounts and create opens:

```bash
ledger -f ledger.dat accounts | while read account; do
  echo "2020-01-01 open $account"
done > accounts.beancount
```

#### Convert Transactions

For each transaction:

1. Add quotes around payee: `"Payee Name"`
1. Add flag if missing: `*` for cleared
1. Ensure amounts balance explicitly (no auto-balance)
1. Change `$5.00` to `5.00 USD`

#### Convert Balance Assertions

Ledger:

```ledger
2024-01-31 Balance
    Assets:Checking  = $1234.56
```

Beancount:

```beancount
2024-01-31 balance Assets:Checking  1234.56 USD
```

### 3. Conversion Script

Basic conversion script (adjust as needed):

```bash
#!/bin/bash
# convert-ledger.sh

INPUT="$1"
OUTPUT="${INPUT%.dat}.beancount"

# Extract and create account opens
echo "; Accounts" > "$OUTPUT"
ledger -f "$INPUT" accounts | while read account; do
  echo "2020-01-01 open $account" >> "$OUTPUT"
done

echo "" >> "$OUTPUT"
echo "; Transactions" >> "$OUTPUT"

# This is a starting point - manual review needed
ledger -f "$INPUT" print >> "$OUTPUT"

echo "Exported to $OUTPUT - manual conversion needed"
```

### 4. Manual Cleanup

After automated conversion, manually:

1. Add quotes around payees
1. Fix commodity positions (`$5.00` → `5.00 USD`)
1. Add explicit balancing amounts
1. Review balance assertions

### 5. Validate

```bash
rledger check ledger.beancount
```

Fix errors until validation passes.

## Command Mapping

| Ledger Command | rustledger Command |
|----------------|-------------------|
| `ledger bal` | `rledger report balances` |
| `ledger reg` | `rledger report journal` |
| `ledger print` | `rledger format` |
| `ledger accounts` | `rledger report accounts` |
| `ledger payees` | `rledger query "SELECT DISTINCT payee"` |
| `ledger commodities` | `rledger report commodities` |

## Shell Aliases

Recreate familiar commands:

```bash
# ~/.bashrc
export LEDGER_FILE="$HOME/finances/ledger.beancount"

alias bal='rledger report "$LEDGER_FILE" balances'
alias reg='rledger report "$LEDGER_FILE" journal'

# With account filter
bal() {
  rledger report "$LEDGER_FILE" balances ${1:+-a "$1"}
}

reg() {
  rledger report "$LEDGER_FILE" journal ${1:+-a "$1"}
}
```

See [Shell Aliases Guide](../guides/shell-aliases.md) for more.

## Feature Comparison

### Available in Both

- Double-entry accounting
- Multiple commodities/currencies
- Command-line interface
- Reports (balance, register)
- Date filtering

### Ledger Features Not in Beancount

- **Automated transactions**: Use plugins instead
- **Periodic transactions**: Not supported
- **Virtual accounts**: Use tags instead
- **Flexible balance**: Must always balance

### Beancount Features Not in Ledger

- **Booking methods**: FIFO, LIFO, etc.
- **BQL query language**: SQL-like queries
- **Plugins**: Extensible validation
- **LSP support**: Editor integration

## Troubleshooting

### "Transaction does not balance"

Beancount requires explicit balancing. Add the missing leg:

```beancount
2024-01-15 * "Coffee"
  Expenses:Food    5.00 USD
  Assets:Cash     -5.00 USD  ; Must be explicit
```

### "Account not opened"

Add open directive before first use:

```beancount
2020-01-01 open Expenses:Food
```

Or use `rledger doctor missing-open` to generate them.

### Commodity Position

Move commodity after amount:

```
Wrong: $5.00
Right: 5.00 USD
```

## See Also

- [Quick Start](../getting-started/quick-start.md) - Beancount basics
- [Shell Aliases](../guides/shell-aliases.md) - Recreate ledger commands
- [BQL Reference](../reference/bql.md) - Query language
