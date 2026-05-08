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

Inferred precision is a heuristic. There are two ways to pin a currency's display precision explicitly.

**`option "display_precision"`** — file-level setting (precision is the scale of the example value):

```beancount
option "display_precision" "USD:0.01"      ; 2dp
option "display_precision" "BTC:0.00000001" ; 8dp
```

**`precision: N` metadata on a `commodity` directive** (rledger extension, issue #991):

```beancount
2024-01-01 commodity USD
  precision: 2

2024-01-01 commodity BTC
  precision: 8

2024-01-01 commodity JPY
  precision: 0
```

Both achieve the same outcome — pinning the displayed precision for that currency regardless of what the inferred distribution shows. Use whichever is more ergonomic: `option "display_precision"` keeps the configuration in one place, while `precision:` metadata co-locates the precision with the rest of the commodity declaration (asset class, ticker, etc.).

**Precedence.** When both are set for the same currency, the per-commodity `precision:` metadata wins:

```beancount
option "display_precision" "USD:0.01"  ; 2dp

2024-01-01 commodity USD
  precision: 4    ; this wins — USD renders at 4dp
```

If the same currency has `precision:` metadata on multiple `commodity` directives, the last one in load order wins.

**Validation.** `precision:` metadata must be a non-negative integer (0 through 4_294_967_295). Invalid values — strings, negatives, fractions, out-of-range — produce an `E5003` warning during validation and the loader ignores that declaration. The currency's effective precision then falls back through the precedence stack: any other valid `precision:` metadata on the same currency, then `option "display_precision"` if set, then inference. Loading does not fail.

**Reserved key.** The `precision` key on `commodity` directives is reserved by the loader — pre-existing user-defined uses of this key on commodity directives will be reinterpreted as a precision override. Pick a different key (e.g. `display_precision`, `precision_note`) if you need to attach unrelated metadata.

### Naked-decimal columns

Columns that produce bare numbers (no associated currency) — `cost_number`, `SUM(number)`, etc. — are tracked independently per column. Each value renders at its own natural decimal scale (matching `bean-query`'s `DecimalRenderer`), with one exception: if an aggregate collapses to literal zero, the column's inferred default precision is used to pad it (so `SUM(0.00)` renders as `0.00`, not `0`).

## See Also

- [BQL Reference](../reference/bql.md) - Full query language docs
- [Common Queries](../guides/common-queries.md) - Useful query examples
