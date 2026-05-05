______________________________________________________________________

## title: rledger query description: Run BQL queries on your ledger

# rledger query

Run BQL (Beancount Query Language) queries against your ledger.

## Usage

```bash
rledger query [OPTIONS] [FILE] [QUERY]
```

## Arguments

| Argument | Description |
|----------|-------------|
| `FILE` | The beancount file (uses `$RLEDGER_FILE` or config if not specified) |
| `QUERY` | BQL query string (interactive mode if not specified) |

## Options

| Option | Description |
|--------|-------------|
| `-P, --profile <PROFILE>` | Use a profile from config |
| `-F, --query-file <FILE>` | Read query from file |
| `-o, --output <FILE>` | Output file (default: stdout) |
| `-f, --format <FORMAT>` | Output format: `text`, `csv`, `json`, `beancount` |
| `-m, --numberify` | Remove currencies, output raw numbers |
| `-q, --no-errors` | Suppress ledger validation errors on load |
| `-v, --verbose` | Show verbose output |

## Examples

### One-shot Query

```bash
rledger query ledger.beancount "SELECT account, sum(position) GROUP BY account"
```

### Interactive Mode

```bash
rledger query ledger.beancount
```

Opens an interactive shell with tab completion:

```
rledger> SELECT date, narration WHERE account ~ 'Expenses'
rledger> BALANCES
rledger> .exit
```

### Output Formats

```bash
# Text (default)
rledger query ledger.beancount "BALANCES"

# CSV (for spreadsheets)
rledger query ledger.beancount "BALANCES" -f csv > balances.csv

# JSON (for scripts)
rledger query ledger.beancount "BALANCES" -f json | jq '.rows[]'
```

### Common Queries

```bash
# Account balances
rledger query ledger.beancount "BALANCES"

# Expenses by category
rledger query ledger.beancount "
  SELECT account, sum(position)
  WHERE account ~ 'Expenses'
  GROUP BY account
  ORDER BY sum(position) DESC
"

# Recent transactions
rledger query ledger.beancount "
  SELECT date, payee, narration, account, position
  ORDER BY date DESC
  LIMIT 20
"

# Transactions matching pattern
rledger query ledger.beancount "
  SELECT date, narration, position
  WHERE narration ~ 'Coffee'
"

# Monthly expenses
rledger query ledger.beancount "
  SELECT month(date) as month, sum(number) as total
  WHERE account ~ 'Expenses'
  GROUP BY month
  ORDER BY month
"
```

### Using with Pipes

```bash
# Filter output with grep
rledger query ledger.beancount "BALANCES" | grep Expenses

# Process JSON with jq
rledger query ledger.beancount "BALANCES" -f json | jq '.rows[] | select(.balance > 100)'

# Export to file
rledger query ledger.beancount "SELECT *" -f csv > transactions.csv
```

## BQL Reference

See [BQL Reference](../reference/bql.md) for complete query language documentation.

### Quick Reference

```sql
-- Select columns
SELECT date, narration, account, position

-- Filter rows
WHERE account ~ 'Expenses' AND year(date) = 2024

-- Aggregate
GROUP BY account
HAVING sum(number) > 100

-- Sort and limit
ORDER BY date DESC
LIMIT 10

-- Built-in reports
BALANCES [FROM ...]
JOURNAL 'Account:Name'
```

## Output precision

Numbers in query output are rendered using a per-currency precision inferred from the input file. This matches Python `bean-query`'s default behavior, so a column of `Position` values for USD prints with the same number of decimal places `bean-query` would use.

### How precision is inferred

For each currency, rledger tracks a frequency distribution of decimal-place counts seen across postings, balances, and price annotations during loading. The displayed precision for that currency is the **mode** of the distribution — i.e. the most common dp count. Outliers (a single 28-decimal computed price annotation, a single integer-valued cost amid mostly 2-decimal postings) don't dominate the inferred precision.

Inspect the inferred precision and the underlying distribution with:

```bash
rledger doctor display-context my-ledger.beancount
```

Sample output:

```
Display Context for my-ledger.beancount
============================================================

Inference policy: MostCommon (default; matches Python bean-query)

USD:
  effective: 2 dp
  distribution: dp=0: 5, dp=2: 141
  mode (MostCommon): 2
  max (Maximum):     4

VBMPX:
  effective: 3 dp
  distribution: dp=3: 4
```

`mode` and `max` are shown side-by-side when they differ, so you can see why a particular column rendered at the precision it did.

### Overriding inference

Inferred precision is a heuristic. To pin a currency's display precision explicitly, use the `display_precision` option in your beancount file:

```beancount
option "display_precision" "USD" "2"
option "display_precision" "BTC" "8"
```

Fixed overrides take precedence over inference for any matching currency, regardless of what the per-currency distribution shows. This is the recommended way to enforce a specific precision when the inferred mode would produce surprising results — for example, a small file with more `Price` directives than postings could see the inferred precision shift toward the price precision.

### Naked-decimal columns

Columns that produce bare numbers (no associated currency) — `cost_number`, `SUM(number)`, etc. — are tracked independently per column. Each value renders at its own natural decimal scale (matching `bean-query`'s `DecimalRenderer`), with one exception: if an aggregate collapses to literal zero, the column's inferred default precision is used to pad it (so `SUM(0.00)` renders as `0.00`, not `0`).

## See Also

- [BQL Reference](../reference/bql.md) - Full query language docs
- [Common Queries](../guides/common-queries.md) - Useful query examples
