# BQL Quick Reference

BQL (Beancount Query Language) is a SQL-like language for querying your ledger.

## Running Queries

```bash
# Interactive mode
rledger query ledger.beancount

# One-shot query
rledger query ledger.beancount "SELECT account, sum(position) GROUP BY account"

# From file
rledger query ledger.beancount -F query.bql

# Output formats
rledger query ledger.beancount "BALANCES" -f csv
rledger query ledger.beancount "BALANCES" -f json
```

## Built-in Queries

| Query | Description |
|-------|-------------|
| `BALANCES` | All account balances |
| `BALANCES FROM OPEN ON 2024-01-01` | Balances at a specific date |
| `JOURNAL "Account:Name"` | Transaction register for account |
| `PRINT` | Print all entries |

## SELECT Syntax

```sql
SELECT [DISTINCT] columns
[FROM entries]
[WHERE conditions]
[GROUP BY columns]
[ORDER BY columns [ASC|DESC]]
[LIMIT n]
```

## Available Columns

### Transaction Columns
| Column | Type | Description |
|--------|------|-------------|
| `date` | date | Transaction date |
| `flag` | string | `*` or `!` |
| `payee` | string | Payee name |
| `narration` | string | Description |
| `tags` | set | Transaction tags |
| `links` | set | Transaction links |

### Posting Columns
| Column | Type | Description |
|--------|------|-------------|
| `account` | string | Account name |
| `position` | position | Amount with currency |
| `balance` | inventory | Running balance |
| `cost` | amount | Cost basis |
| `price` | amount | Price annotation |

### Metadata
| Column | Type | Description |
|--------|------|-------------|
| `filename` | string | Source file |
| `lineno` | int | Line number |

## Functions

### Aggregate Functions
```sql
sum(position)      -- Sum of positions
count()            -- Count rows
first(x)           -- First value
last(x)            -- Last value
min(x)             -- Minimum
max(x)             -- Maximum
```

### Date Functions
```sql
year(date)         -- Year (2024)
month(date)        -- Month (1-12)
day(date)          -- Day (1-31)
quarter(date)      -- Quarter (1-4)
weekday(date)      -- Day of week (0=Mon, 6=Sun)
```

### Account Functions
```sql
root(account, n)   -- First n components: root("A:B:C", 2) = "A:B"
leaf(account)      -- Last component: leaf("A:B:C") = "C"
parent(account)    -- Parent: parent("A:B:C") = "A:B"
```

### String Functions
```sql
length(s)          -- String length
upper(s)           -- Uppercase
lower(s)           -- Lowercase
```

### Conversion Functions
```sql
units(position)    -- Just the number and currency
cost(position)     -- Cost basis amount
value(position)    -- Market value (requires prices)
```

## Operators

### Comparison
```sql
=    !=    <    >    <=    >=
```

### Pattern Matching
```sql
account ~ "Expenses:.*"     -- Regex match
account = "Expenses:Food"   -- Exact match
```

### Boolean
```sql
AND    OR    NOT
```

### Membership
```sql
currency IN ("USD", "EUR")
"vacation" IN tags
```

## Example Queries

### Basic Balances
```sql
-- All account balances
BALANCES

-- Specific account type
SELECT account, sum(position)
WHERE account ~ "^Assets:"
GROUP BY account
```

### Date Filtering
```sql
-- This year
SELECT date, narration, position
WHERE year(date) = 2024

-- Date range
SELECT date, account, position
WHERE date >= 2024-01-01 AND date < 2024-02-01

-- Last 30 days
SELECT date, narration, position
WHERE date >= today() - 30
```

### Monthly Reports
```sql
-- Monthly expenses
SELECT year(date) as year, month(date) as month, sum(position)
WHERE account ~ "^Expenses:"
GROUP BY year(date), month(date)
ORDER BY year, month

-- Monthly by category
SELECT month(date) as month, root(account, 2) as category, sum(position)
WHERE account ~ "^Expenses:" AND year(date) = 2024
GROUP BY month(date), root(account, 2)
ORDER BY month, category
```

### Account Analysis
```sql
-- Top spending categories
SELECT root(account, 2) as category, sum(position) as total
WHERE account ~ "^Expenses:"
GROUP BY root(account, 2)
ORDER BY total DESC
LIMIT 10

-- Transactions for specific account
JOURNAL "Assets:Bank:Checking"

-- Large transactions
SELECT date, narration, position
WHERE account ~ "^Expenses:" AND position > 500 USD
ORDER BY position DESC
```

### Payee Analysis
```sql
-- Spending by payee
SELECT payee, sum(position) as total
WHERE account ~ "^Expenses:" AND payee != ""
GROUP BY payee
ORDER BY total DESC
LIMIT 20
```

### Income vs Expenses
```sql
-- Monthly income
SELECT month(date) as month, -sum(position) as income
WHERE account ~ "^Income:" AND year(date) = 2024
GROUP BY month(date)
ORDER BY month

-- Net income by month
SELECT month(date) as month,
       sum(position) FILTER (WHERE account ~ "^Expenses:") as expenses,
       -sum(position) FILTER (WHERE account ~ "^Income:") as income
WHERE year(date) = 2024
GROUP BY month(date)
```

### Tags and Links
```sql
-- Find tagged transactions
SELECT date, narration, position
WHERE "vacation" IN tags

-- Find linked transactions
SELECT date, narration, position
WHERE "^trip-2024" IN links
```

### Balance History
```sql
-- Account balance over time
SELECT date, balance
WHERE account = "Assets:Bank:Checking"
ORDER BY date
```

## Output Formats

```bash
# Default text table
rledger query ledger.beancount "BALANCES"

# CSV for spreadsheets
rledger query ledger.beancount "BALANCES" -f csv > balances.csv

# JSON for scripts
rledger query ledger.beancount "BALANCES" -f json | jq '.rows[]'

# Beancount format
rledger query ledger.beancount "SELECT *" -f beancount
```

## Tips

### Use Aliases in Interactive Mode
```
beancount> BALANCES
beancount> JOURNAL "Assets:Checking"
```

### Combine with Shell Tools
```bash
# Count transactions per month
rledger query ledger.beancount \
  "SELECT year(date), month(date), count() GROUP BY 1, 2" -f csv | \
  sort -t, -k1,2

# Export to spreadsheet
rledger query ledger.beancount "BALANCES" -f csv > ~/Desktop/balances.csv
```

### Query Files
Save complex queries in `.bql` files:
```sql
-- monthly-expenses.bql
SELECT
  year(date) as year,
  month(date) as month,
  root(account, 2) as category,
  sum(position) as total
WHERE account ~ "^Expenses:"
GROUP BY year(date), month(date), root(account, 2)
ORDER BY year, month, category
```

Run with:
```bash
rledger query ledger.beancount -F monthly-expenses.bql
```
