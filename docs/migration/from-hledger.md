______________________________________________________________________

## title: Migrating from hledger description: Switch from hledger to rustledger

# Migrating from hledger

This guide helps you migrate from hledger to rustledger's beancount format.

## Key Differences

hledger uses a format compatible with ledger-cli. Beancount has stricter syntax requirements.

### Syntax Comparison

| Feature | hledger | Beancount |
|---------|---------|-----------|
| File extension | `.journal` | `.beancount` |
| Account opens | Optional | Required |
| Payee format | After date | In quotes |
| Amounts | Can auto-balance | Must balance |
| Comments | `;` or `#` | `;` |
| Directives | `account`, `commodity` | `open`, `commodity` |

### Example Comparison

**hledger:**

```journal
2024-01-15 Coffee Shop
    expenses:food:coffee     $5.00
    assets:cash

2024-01-15 balance assets:checking  = $1234.56
```

**Beancount:**

```beancount
2020-01-01 open Assets:Cash              USD
2020-01-01 open Assets:Checking          USD
2020-01-01 open Expenses:Food:Coffee

2024-01-15 * "Coffee Shop"
  Expenses:Food:Coffee     5.00 USD
  Assets:Cash             -5.00 USD

2024-01-15 balance Assets:Checking  1234.56 USD
```

## Migration Steps

### 1. Export from hledger

```bash
hledger print -f main.journal > export.journal
```

### 2. Convert Account Names

Beancount accounts must be Title:Case:

```
expenses:food:coffee  →  Expenses:Food:Coffee
assets:checking       →  Assets:Checking
```

Script to help:

```bash
# Convert account names to Title Case
sed -E 's/([a-z]+:)/\u\1/g' export.journal
```

### 3. Generate Account Opens

```bash
hledger accounts -f main.journal | while read account; do
  # Convert to Title Case
  titled=$(echo "$account" | sed 's/\(^\|:\)\([a-z]\)/\1\u\2/g')
  echo "2020-01-01 open $titled"
done > accounts.beancount
```

### 4. Convert Transactions

Key changes:

1. **Add quotes around payees**

   ```
   2024-01-15 Coffee Shop
   →
   2024-01-15 * "Coffee Shop"
   ```

1. **Convert commodities**

   ```
   $5.00  →  5.00 USD
   €10    →  10.00 EUR
   ```

1. **Add explicit balance**

   ```
   expenses:food    $5.00
   assets:cash
   →
   Expenses:Food     5.00 USD
   Assets:Cash      -5.00 USD
   ```

1. **Convert balance assertions**

   ```
   2024-01-15 balance assets:checking  = $1234.56
   →
   2024-01-15 balance Assets:Checking  1234.56 USD
   ```

### 5. Validate

```bash
rledger check ledger.beancount
```

## Command Mapping

| hledger | rustledger |
|---------|------------|
| `hledger bal` | `rledger report balances` |
| `hledger reg` | `rledger report journal` |
| `hledger print` | `rledger format` |
| `hledger accounts` | `rledger report accounts` |
| `hledger bs` | `rledger report balsheet` |
| `hledger is` | `rledger report income` |
| `hledger check` | `rledger check` |

### Query Differences

hledger uses its own query syntax; rustledger uses BQL:

**hledger:**

```bash
hledger reg expenses:food date:2024
```

**rustledger (BQL):**

```bash
rledger query ledger.beancount \
  "SELECT date, narration, position
   WHERE account ~ 'Expenses:Food' AND year(date) = 2024"
```

## Shell Aliases

Recreate hledger-style commands:

```bash
# ~/.bashrc
export LEDGER_FILE="$HOME/finances/ledger.beancount"

alias bal='rledger report "$LEDGER_FILE" balances'
alias bs='rledger report "$LEDGER_FILE" balsheet'
alias is='rledger report "$LEDGER_FILE" income'

reg() {
  if [ -n "$1" ]; then
    rledger report "$LEDGER_FILE" journal -a "$1"
  else
    rledger report "$LEDGER_FILE" journal
  fi
}
```

## hledger Features

### Supported Differently

| hledger Feature | Beancount Equivalent |
|-----------------|---------------------|
| `account` directive | `open` directive |
| Lowercase accounts | Title Case required |
| Auto-balance | Explicit amounts |
| Balance assertions | `balance` directive |
| `include` | `include` |
| Tags | Tags and links |

### Not Supported

| Feature | Alternative |
|---------|-------------|
| Virtual accounts | Use regular accounts with tags |
| Periodic transactions | Manual entry or scripts |
| `alias` directive | None (use search-replace) |
| CSV rules | `rledger extract` with config |

### Beancount Extras

Features available in beancount but not hledger:

- **Booking methods**: FIFO, LIFO, STRICT, etc. for investments
- **Cost basis tracking**: Built-in capital gains handling
- **Plugins**: Validation and transformation plugins
- **BQL**: SQL-like query language

## Conversion Script

Basic conversion script:

```python
#!/usr/bin/env python3
"""Convert hledger journal to beancount format."""

import re
import sys

def title_case(account):
    """Convert account:name to Account:Name."""
    return ':'.join(word.title() for word in account.split(':'))

def convert_amount(amount):
    """Convert $5.00 to 5.00 USD."""
    match = re.match(r'\$([0-9.,]+)', amount)
    if match:
        return f"{match.group(1)} USD"
    match = re.match(r'€([0-9.,]+)', amount)
    if match:
        return f"{match.group(1)} EUR"
    return amount

def convert_line(line):
    """Convert a single line."""
    # Skip comments
    if line.strip().startswith(';') or line.strip().startswith('#'):
        return line

    # Convert posting
    match = re.match(r'(\s+)([a-z:]+)\s+(.+)', line)
    if match:
        indent, account, amount = match.groups()
        return f"{indent}{title_case(account)}  {convert_amount(amount.strip())}\n"

    # Convert transaction header
    match = re.match(r'(\d{4}-\d{2}-\d{2})\s+(.+)', line)
    if match:
        date, payee = match.groups()
        return f'{date} * "{payee.strip()}"\n'

    return line

if __name__ == '__main__':
    for line in sys.stdin:
        print(convert_line(line), end='')
```

Usage:

```bash
python3 convert.py < main.journal > ledger.beancount
```

Note: This is a starting point. Manual review and cleanup will be needed.

## Troubleshooting

### Account Name Errors

Ensure accounts are Title:Case:

```
Error: Invalid account name 'expenses:food'
Fix: Use 'Expenses:Food'
```

### Missing Open Directives

Generate them:

```bash
rledger doctor missing-open ledger.beancount
```

### Balance Assertion Failures

Check date format and amount:

```beancount
; hledger: balance assets:checking  = $1234.56
; beancount:
2024-01-15 balance Assets:Checking  1234.56 USD
```

## See Also

- [Quick Start](../getting-started/quick-start.md) - Beancount basics
- [From Ledger](from-ledger.md) - Similar migration guide
- [Shell Aliases](../guides/shell-aliases.md) - Command shortcuts
