______________________________________________________________________

## title: BQL Reference description: Beancount Query Language syntax reference

# BQL Reference

BQL (Beancount Query Language) is a SQL-like language for querying beancount ledgers.

## Basic Syntax

```sql
SELECT columns
WHERE condition
GROUP BY columns
ORDER BY columns
LIMIT n
```

## SELECT Clause

### Columns

```sql
-- Basic columns
SELECT account, date, narration, payee, position

-- All columns
SELECT *

-- Expressions
SELECT account, sum(position) AS total

-- Functions
SELECT year(date), month(date), sum(cost(position))
```

### Column Aliases

```sql
SELECT account AS acc, sum(position) AS balance
```

## WHERE Clause

### Comparison Operators

```sql
WHERE date = 2024-01-15
WHERE date > 2024-01-01
WHERE date >= 2024-01-01
WHERE date < 2024-12-31
WHERE date <= 2024-12-31
WHERE date != 2024-01-15
```

### String Matching

```sql
-- Exact match
WHERE account = "Assets:Bank:Checking"

-- Regex match (case-insensitive by default)
WHERE account ~ "Assets:Bank"
WHERE narration ~ "coffee"
WHERE payee ~ "Amazon"
```

### Logical Operators

```sql
WHERE account ~ "Assets" AND date >= 2024-01-01
WHERE account ~ "Income" OR account ~ "Expenses"
WHERE NOT account ~ "Equity"
```

### NULL Checks

```sql
WHERE payee IS NOT NULL
WHERE payee IS NULL
```

### IN Operator

```sql
WHERE account IN ("Assets:Bank", "Assets:Cash")
WHERE "vacation" IN tags
```

## GROUP BY Clause

```sql
SELECT account, sum(position)
GROUP BY account

-- Multiple columns
SELECT year(date), month(date), sum(position)
GROUP BY year(date), month(date)

-- By position (1-indexed)
SELECT year(date), sum(position)
GROUP BY 1
```

## ORDER BY Clause

```sql
ORDER BY date
ORDER BY date DESC
ORDER BY account ASC

-- Multiple columns
ORDER BY year(date), month(date)

-- By expression
ORDER BY sum(position) DESC
```

## LIMIT Clause

```sql
LIMIT 10
LIMIT 100
```

## PIVOT BY Clause

Pivot results to create columns from row values:

```sql
-- Expenses by category and year, pivoted by year
SELECT root(account, 2), year(date), sum(cost(position))
WHERE account ~ "Expenses"
GROUP BY 1, 2
PIVOT BY 2
```

Note: PIVOT BY must reference a SELECT output column, either by name or by its 1-indexed position; pivoting by an arbitrary expression (for example, `PIVOT BY YEAR(date)`) is not supported.

## Aggregate Functions

| Function | Description |
|----------|-------------|
| `sum(position)` | Sum positions |
| `count(*)` | Count rows |
| `first(x)` | First value |
| `last(x)` | Last value |
| `min(x)` | Minimum value |
| `max(x)` | Maximum value |

### Examples

```sql
SELECT account, sum(position) GROUP BY account
SELECT count(*) WHERE account ~ "Expenses"
SELECT min(date), max(date)
```

## Scalar Functions

### Date Functions

| Function | Description | Example |
|----------|-------------|---------|
| `year(date)` | Extract year | `2024` |
| `month(date)` | Extract month | `3` |
| `day(date)` | Extract day | `15` |
| `quarter(date)` | Extract quarter | `1` |
| `weekday(date)` | Day of week (0=Mon) | `4` |
| `today()` | Current date | `2024-03-15` |

### Amount Functions

| Function | Description |
|----------|-------------|
| `cost(position)` | Convert to cost basis |
| `units(position)` | Get units (number) |
| `currency(position)` | Get currency |
| `number(amount)` | Extract number from amount |

### String Functions

| Function | Description |
|----------|-------------|
| `length(str)` | String length |
| `upper(str)` | Convert to uppercase |
| `lower(str)` | Convert to lowercase |
| `root(account, n)` | First n account segments |
| `leaf(account)` | Last account segment |
| `parent(account)` | All but last segment |

### Metadata Functions

Beancount metadata can live on a **transaction** (the line under the header,
before any postings) or on a **posting** (indented one level deeper than the
posting itself). BQL exposes three lookup functions because the distinction
matters at query time:

| Function | Looks at | Use when |
|----------|----------|----------|
| `meta(key)` | Posting metadata only | The key is set per-posting (e.g. a `lot-id` on one leg of a transfer) |
| `entry_meta(key)` | Transaction metadata only | The key is set on the transaction header (e.g. a `budget-category` shared by every posting) |
| `any_meta(key)` | Posting first, then transaction | You don't know or don't care which level it's set on |

All three return `NULL` when the key is absent at the relevant level — so a
`WHERE meta('foo') = 'bar'` filter quietly drops every row when `foo` was
actually set on the transaction.

```beancount
2024-01-15 * "Grocery Store"
  budget-category: "food"          ; on the transaction
  Expenses:Food:Groceries  85.00 USD
    receipt-id: "R-12345"          ; on this posting only
  Assets:Bank:Checking
```

```sql
-- Doesn't match: budget-category is on the transaction, not the posting.
SELECT account WHERE meta('budget-category') = 'food'

-- Matches every posting in the transaction.
SELECT account WHERE entry_meta('budget-category') = 'food'

-- Matches whichever level happens to carry the key.
SELECT account WHERE any_meta('budget-category') = 'food'

-- Matches only the Expenses posting, since receipt-id is per-posting.
SELECT account WHERE meta('receipt-id') = 'R-12345'
```

This mirrors Python `bean-query`'s `meta` / `entry_meta` / `any_meta`
exactly, so queries are portable between the two engines.

### Examples

```sql
-- Expense by category
SELECT root(account, 2) AS category, sum(cost(position))
WHERE account ~ "Expenses"
GROUP BY category

-- Monthly totals
SELECT year(date) AS y, month(date) AS m, sum(cost(position))
GROUP BY y, m
ORDER BY y, m
```

## Position and Amount

BQL distinguishes between:

- **Position**: Amount with cost basis (e.g., `10 AAPL {150.00 USD}`)
- **Amount**: Simple number with currency (e.g., `1500.00 USD`)

### Converting Positions

```sql
-- Get cost in operating currency
SELECT sum(cost(position))

-- Get units (ignoring currency)
SELECT sum(units(position))

-- Get currency
SELECT currency(position)
```

## Date Literals

Dates without quotes:

```sql
WHERE date = 2024-01-15
WHERE date >= 2024-01-01 AND date < 2024-04-01
```

## Tags and Links

### Filtering by Tag

```sql
WHERE "vacation" IN tags
WHERE "project" IN tags
```

### Filtering by Link

```sql
WHERE "trip-2024" IN links
```

## Subqueries

Not currently supported. Use multiple queries or shell piping.

## Examples

### Account Balances

```sql
SELECT account, sum(position)
GROUP BY account
ORDER BY account
```

### Monthly Expenses

```sql
SELECT year(date), month(date), sum(cost(position))
WHERE account ~ "Expenses"
GROUP BY 1, 2
ORDER BY 1, 2
```

### Top Spending Categories

```sql
SELECT root(account, 2), sum(cost(position))
WHERE account ~ "Expenses"
GROUP BY 1
ORDER BY 2 DESC
LIMIT 10
```

### Transactions with Payee

```sql
SELECT date, payee, narration, account, position
WHERE payee ~ "Amazon"
ORDER BY date DESC
```

### Net Worth

```sql
SELECT sum(cost(position))
WHERE account ~ "Assets" OR account ~ "Liabilities"
```

### Year-over-Year

```sql
-- Run separate queries for each year
SELECT root(account, 2), sum(cost(position)) AS "2023"
WHERE account ~ "Expenses" AND year(date) = 2023
GROUP BY 1
ORDER BY 1

SELECT root(account, 2), sum(cost(position)) AS "2024"
WHERE account ~ "Expenses" AND year(date) = 2024
GROUP BY 1
ORDER BY 1
```

## Output Formats

```bash
# Text (default)
rledger query ledger.beancount "SELECT ..."

# CSV
rledger query -f csv ledger.beancount "SELECT ..."

# JSON
rledger query -f json ledger.beancount "SELECT ..."
```

## Tips

### Use Regex for Account Matching

```sql
-- Match all bank accounts
WHERE account ~ "Assets:Bank"

-- Match any asset
WHERE account ~ "^Assets:"
```

### Group by Account Hierarchy

```sql
-- Top-level categories
SELECT root(account, 1), sum(position) GROUP BY 1

-- Two levels deep
SELECT root(account, 2), sum(position) GROUP BY 1
```

### Date Range Filtering

```sql
-- This year
WHERE year(date) = year(today())

-- This month
WHERE year(date) = year(today()) AND month(date) = month(today())

-- Specific date range
WHERE date >= 2024-01-01 AND date < 2024-02-01
```

## See Also

- [query command](../commands/query.md) - Running queries
- [Common Queries](../guides/common-queries.md) - Useful query examples
