# Importing Bank Statements

This guide shows how to import transactions from CSV and OFX bank exports using `rledger extract`.

## Quick Start

```bash
# Basic CSV import
rledger extract bank-statement.csv >> ledger.beancount

# With account and currency
rledger extract -a Assets:Bank:Chase -c USD statement.csv >> ledger.beancount
```

## CSV Import Examples

### Example 1: Simple Bank Export

Given a CSV file `chase.csv`:
```csv
Date,Description,Amount
2024-01-15,COFFEE SHOP,-4.50
2024-01-16,PAYROLL DIRECT DEP,2500.00
2024-01-17,GROCERY STORE,-85.23
```

Import command:
```bash
rledger extract chase.csv -a Assets:Bank:Chase
```

Output:
```beancount
2024-01-15 * "COFFEE SHOP"
  Assets:Bank:Chase  -4.50 USD
  Expenses:Unknown    4.50 USD

2024-01-16 * "PAYROLL DIRECT DEP"
  Assets:Bank:Chase  2500.00 USD
  Income:Unknown    -2500.00 USD

2024-01-17 * "GROCERY STORE"
  Assets:Bank:Chase  -85.23 USD
  Expenses:Unknown    85.23 USD
```

### Example 2: Custom Column Names

Bank exports often have different column names:
```csv
Transaction Date,Memo,Debit,Credit
01/15/2024,Coffee Shop,4.50,
01/16/2024,Payroll,,2500.00
```

Import command:
```bash
rledger extract statement.csv \
  --date-column "Transaction Date" \
  --date-format "%m/%d/%Y" \
  --narration-column "Memo" \
  --debit-column "Debit" \
  --credit-column "Credit" \
  -a Assets:Bank:BofA
```

### Example 3: Separate Payee Column

Some exports include payee information:
```csv
Date,Payee,Description,Amount
2024-01-15,Starbucks,Coffee purchase,-4.50
```

Import command:
```bash
rledger extract statement.csv \
  --payee-column "Payee" \
  --narration-column "Description" \
  -a Assets:Bank:Checking
```

Output:
```beancount
2024-01-15 * "Starbucks" "Coffee purchase"
  Assets:Bank:Checking  -4.50 USD
  Expenses:Unknown       4.50 USD
```

### Example 4: Credit Card (Inverted Signs)

Credit card statements often show purchases as positive:
```csv
Date,Description,Amount
2024-01-15,Restaurant,45.00
2024-01-16,Payment Received,-500.00
```

Import with inverted signs:
```bash
rledger extract creditcard.csv \
  --invert-sign \
  -a Liabilities:CreditCard:Amex
```

### Example 5: Tab-Delimited File

```bash
rledger extract statement.tsv --delimiter $'\t' -a Assets:Bank:Main
```

### Example 6: Skip Header Rows

Some bank exports have extra header rows:
```
Downloaded: 2024-01-20
Account: ****1234

Date,Description,Amount
2024-01-15,Coffee,-4.50
```

Skip the first 3 rows:
```bash
rledger extract statement.csv --skip-rows 3 -a Assets:Bank:Main
```

### Example 7: No Header Row

For files without headers, use column indices (0-based):
```csv
2024-01-15,Coffee Shop,-4.50
2024-01-16,Grocery Store,-25.00
```

```bash
rledger extract statement.csv \
  --no-header \
  --date-column 0 \
  --narration-column 1 \
  --amount-column 2 \
  -a Assets:Bank:Main
```

## Command Reference

| Option | Default | Description |
|--------|---------|-------------|
| `-a, --account` | `Assets:Bank:Checking` | Target account for transactions |
| `-c, --currency` | `USD` | Currency for amounts |
| `--date-column` | `Date` | Column name or index for dates |
| `--date-format` | `%Y-%m-%d` | Date format ([strftime](https://strftime.org/)) |
| `--narration-column` | `Description` | Column for transaction description |
| `--payee-column` | (none) | Column for payee (optional) |
| `--amount-column` | `Amount` | Column for amount (single column) |
| `--debit-column` | (none) | Column for debits (separate columns) |
| `--credit-column` | (none) | Column for credits (separate columns) |
| `--delimiter` | `,` | CSV delimiter character |
| `--skip-rows` | `0` | Header rows to skip |
| `--invert-sign` | off | Flip amount signs |
| `--no-header` | off | CSV has no header row |

## Common Date Formats

| Bank Style | Format String |
|------------|---------------|
| `2024-01-15` | `%Y-%m-%d` (default) |
| `01/15/2024` | `%m/%d/%Y` |
| `15/01/2024` | `%d/%m/%Y` |
| `Jan 15, 2024` | `%b %d, %Y` |
| `15-Jan-2024` | `%d-%b-%Y` |
| `20240115` | `%Y%m%d` |

## Workflow Tips

### 1. Preview Before Appending

```bash
# Preview output
rledger extract statement.csv -a Assets:Bank:Chase

# If it looks good, append to ledger
rledger extract statement.csv -a Assets:Bank:Chase >> ledger.beancount
```

### 2. Validate After Import

```bash
rledger extract statement.csv >> ledger.beancount
rledger check ledger.beancount
```

### 3. Categorize with Search & Replace

After import, use your editor to categorize:
- Find: `Expenses:Unknown`
- Replace with appropriate category based on payee patterns

### 4. Create Import Scripts

Save common import commands:
```bash
#!/bin/bash
# import-chase.sh
rledger extract "$1" \
  -a Assets:Bank:Chase \
  --date-format "%m/%d/%Y" \
  --narration-column "Description" \
  --amount-column "Amount"
```

### 5. Deduplicate

rustledger doesn't auto-deduplicate. Use the `noduplicates` plugin to detect duplicates:
```bash
rledger check --native-plugin noduplicates ledger.beancount
```

## OFX/QFX Import

OFX files from banks are also supported:
```bash
rledger extract statement.ofx -a Assets:Bank:Main >> ledger.beancount
```

OFX files contain structured data, so column options are not needed.

## Troubleshooting

**"Date parse error"**
- Check your `--date-format` matches the CSV dates
- Use `--skip-rows` if there are extra header lines

**"Column not found"**
- Column names are case-sensitive
- Try using column index (0-based) instead of name
- Check for hidden characters in CSV headers

**"Amounts look wrong"**
- Try `--invert-sign` for credit card statements
- Check if bank uses separate debit/credit columns

**"Encoding issues"**
- Ensure CSV is UTF-8 encoded
- Convert with: `iconv -f ISO-8859-1 -t UTF-8 input.csv > output.csv`
