# Beancount Query Language (BQL) Specification

## Overview

BQL is a specialized SQL-like query engine designed for financial data analysis. It operates on transaction postings while respecting double-entry bookkeeping constraints.

## Query Structure

```sql
SELECT <target1>, <target2>, ...
FROM <entry-filter-expression>
WHERE <posting-filter-expression>
[GROUP BY <columns>]
[ORDER BY <columns>]
[LIMIT <n>];
```

The `FROM` clause filters entire transactions (preserving accounting equation). The `WHERE` clause filters postings from matching transactions.

## Data Types

| Type | Description |
|------|-------------|
| String | Text values |
| Date | `YYYY-MM-DD` format |
| Integer | Whole numbers |
| Boolean | `TRUE`, `FALSE` |
| Number | Decimal precision |
| Set of Strings | Collections (e.g., tags, links) |
| NULL | Absence of value |
| Position | Single lot with optional cost |
| Inventory | Aggregated positions across multiple lots |

## Position/Inventory Rendering Functions

Functions transform positions into derived quantities:

| Function | Purpose |
|----------|---------|
| `units(pos)` | Currency and quantity only |
| `cost(pos)` | Total cost (units × per-unit cost) |
| `weight(pos)` | Amount used for transaction balancing |
| `value(pos)` | Market value at last known price |

## Operators

### Comparison
`=`, `!=`, `<`, `<=`, `>`, `>=`

### Logical
`AND`, `OR`, `NOT`

### Special
- `IN` — Set membership test
- `~` — Regular expression match

**Note:** Unlike standard SQL, `NULL = NULL` yields `TRUE`.

## Column Types

### Posting Columns (SELECT/WHERE)

| Column | Type | Description |
|--------|------|-------------|
| `date` | Date | Transaction date |
| `account` | String | Account name |
| `position` | Position | Full position with cost |
| `units` | Amount | Units only |
| `cost` | Amount | Cost basis |
| `weight` | Amount | Balancing weight |
| `narration` | String | Transaction narration |
| `payee` | String | Payee |
| `tags` | Set | Transaction tags |
| `links` | Set | Transaction links |
| `flag` | String | Transaction flag (* or !) |
| `balance` | Inventory | Running balance after posting |

### Entry Columns (FROM clause)

| Column | Type | Description |
|--------|------|-------------|
| `date` | Date | Directive date |
| `flag` | String | Transaction flag |
| `payee` | String | Payee |
| `narration` | String | Narration |
| `tags` | Set | Tags |
| `links` | Set | Links |
| `id` | String | Unique stable hash |
| `type` | String | Directive type name |

## Simple Functions

### Position/Amount Functions
- `COST(Position|Inventory)` → Amount
- `UNITS(Position|Inventory)` → Amount
- `NUMBER(Amount)` → Decimal
- `CURRENCY(Amount)` → String

### Date Functions
- `DAY(date)` → Integer
- `MONTH(date)` → Integer
- `YEAR(date)` → Integer
- `QUARTER(date)` → Integer
- `WEEKDAY(date)` → Integer

### String Functions
- `LENGTH(string)` → Integer
- `UPPER(string)` → String
- `LOWER(string)` → String

### Account Functions
- `PARENT(account)` → String (parent account name)
- `LEAF(account)` → String (last component)
- `ROOT(account, n)` → String (first n components)

### Other
- `LENGTH(set|list)` → Integer

## Aggregate Functions

| Function | Description |
|----------|-------------|
| `COUNT(*)` | Count of postings |
| `FIRST(x)` | First value in group |
| `LAST(x)` | Last value in group |
| `MIN(x)` | Minimum value |
| `MAX(x)` | Maximum value |
| `SUM(x)` | Sum (works on amounts, positions, inventories) |

Queries with aggregate functions require `GROUP BY` for non-aggregated columns.

## Query Types

### Simple Query
One result row per matching posting:
```sql
SELECT date, account, narration, position
WHERE account ~ "Expenses:";
```

### Aggregate Query
One result row per group:
```sql
SELECT account, SUM(position)
WHERE account ~ "Expenses:"
GROUP BY account;
```

Group keys can reference:
- Column names
- Ordinal indices (1, 2, ...)
- Expressions

## Result Control Clauses

### DISTINCT
```sql
SELECT DISTINCT account;
```
Removes duplicate result rows.

### ORDER BY
```sql
ORDER BY date DESC, account ASC;
```
Default is `ASC`. Multiple columns supported.

### LIMIT
```sql
LIMIT 100;
```
Stops output after N rows.

## Statement Operators (FROM Extensions)

These transform selected transactions before posting projection:

### OPEN ON \<date\>

Replaces all entries before the date with summarization entries:
- Asset/Liability balances → booked to Equity:Opening-Balances
- Income/Expense balances → cleared to Equity:Earnings:Previous

```sql
SELECT * FROM has_account("Invest") OPEN ON 2024-01-01;
```

### CLOSE [ON \<date\>]

Truncates entries after the date. Leaves income/expense balances untouched (used for income statements).

```sql
SELECT * FROM condition CLOSE ON 2024-12-31;
```

### CLEAR

Transfers income and expense balances to Equity "current earnings," zeroing those accounts (used for balance sheets).

```sql
SELECT account, SUM(position)
FROM OPEN ON 2023-01-01 CLOSE ON 2024-01-01 CLEAR
WHERE account ~ "^(Assets|Liabilities)"
GROUP BY 1;
```

## High-Level Query Shortcuts

### JOURNAL
```sql
JOURNAL <account-regexp> [AT <function>] [FROM ...]
```
Generates account statement with optional aggregation function.

Example:
```sql
JOURNAL "Assets:Checking" AT cost
```

### BALANCES
```sql
BALANCES [AT <function>] [FROM ...]
```
Produces account balance table.

Example:
```sql
BALANCES AT units FROM year = 2024
```

### PRINT
```sql
PRINT [FROM ...]
```
Outputs filtered transactions in Beancount syntax.

## Wildcard Selection

```sql
SELECT *;
```
Selects sensible default columns.

## FROM Clause Filters

The FROM clause filters at the transaction level using special predicates:

| Predicate | Description |
|-----------|-------------|
| `has_account(pattern)` | Transaction has posting matching account pattern |
| `year = N` | Transaction year equals N |
| `month = N` | Transaction month equals N |
| `date >= D` | Transaction date comparison |

## Key Distinctions from SQL

1. **Two-level filtering**: FROM filters transactions, WHERE filters postings
2. **Native inventory types**: Position and Inventory are first-class types
3. **Cost operations**: Built-in functions for cost basis calculations
4. **Accounting equation preservation**: Transaction-level filtering maintains balance
5. **Running balance column**: `balance` without window functions
6. **Simplified NULL**: Binary logic (NULL = NULL is TRUE)

## Grammar Summary

```
query       := select_stmt | journal_stmt | balances_stmt | print_stmt

select_stmt := SELECT [DISTINCT] targets
               [FROM from_expr]
               [WHERE where_expr]
               [GROUP BY group_exprs]
               [ORDER BY order_exprs]
               [LIMIT n]

targets     := target ("," target)*
target      := expr [AS name]

from_expr   := [OPEN ON date] [CLOSE ON date] [CLEAR] [filter_expr]
filter_expr := predicate (AND predicate)*

where_expr  := condition (AND|OR condition)*
condition   := expr op expr | NOT condition | "(" where_expr ")"

group_exprs := expr ("," expr)*
order_exprs := expr [ASC|DESC] ("," expr [ASC|DESC])*

expr        := column | function(args) | literal | expr op expr
```
