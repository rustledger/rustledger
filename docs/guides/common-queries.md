______________________________________________________________________

## title: Common Queries description: Useful BQL queries for everyday reporting

# Common Queries

A collection of useful BQL queries for everyday financial reporting.

## Balance Queries

### Current Balances

```sql
-- All account balances
SELECT account, sum(position) AS balance
GROUP BY account ORDER BY account

-- Specific account
SELECT account, sum(position) AS balance
WHERE account ~ "Assets:Bank"
GROUP BY account

-- Top-level summary
SELECT root(account, 1) AS type, sum(position) AS balance
GROUP BY type
```

### Balance at Date

```sql
-- Balances as of a specific date
SELECT account, sum(position) AS balance
WHERE date <= 2024-06-30
GROUP BY account
```

## Expense Analysis

### Monthly Expenses

```sql
-- Total expenses by month
SELECT year(date) AS year, month(date) AS month, sum(cost(position)) AS total
WHERE account ~ "Expenses"
GROUP BY year, month
ORDER BY year, month
```

### Expenses by Category

```sql
-- Breakdown by expense category
SELECT root(account, 2) AS category, sum(cost(position)) AS total
WHERE account ~ "Expenses"
GROUP BY category
ORDER BY total DESC
```

### Year-over-Year Comparison

```sql
-- Compare years with separate queries
-- 2023 expenses:
SELECT root(account, 2) AS category, sum(cost(position)) AS total
WHERE account ~ "Expenses" AND year(date) = 2023
GROUP BY category ORDER BY total DESC

-- 2024 expenses:
SELECT root(account, 2) AS category, sum(cost(position)) AS total
WHERE account ~ "Expenses" AND year(date) = 2024
GROUP BY category ORDER BY total DESC
```

## Income Analysis

### Income by Source

```sql
SELECT root(account, 2) AS source, sum(cost(position)) AS total
WHERE account ~ "Income"
GROUP BY source
ORDER BY total
```

### Monthly Income vs Expenses

```sql
-- Monthly income
SELECT year(date) AS year, month(date) AS month, sum(cost(position)) AS income
WHERE account ~ "Income"
GROUP BY year, month ORDER BY year, month

-- Monthly expenses
SELECT year(date) AS year, month(date) AS month, sum(cost(position)) AS expenses
WHERE account ~ "Expenses"
GROUP BY year, month ORDER BY year, month
```

## Transaction Queries

### Recent Transactions

```sql
-- Last 20 transactions
SELECT date, narration, account, position
ORDER BY date DESC
LIMIT 20
```

### Search by Payee

```sql
SELECT date, payee, narration, account, position
WHERE payee ~ "Amazon"
ORDER BY date DESC
```

### Large Transactions

```sql
-- Find transactions over $500 (filter results manually or use report command)
SELECT date, payee, narration, account, cost(position) AS amount
WHERE account ~ "Expenses"
ORDER BY date DESC
```

### Transactions with Tag

```sql
SELECT date, narration, account, position
WHERE "vacation" IN tags
ORDER BY date
```

## Investment Queries

### Holdings with Cost Basis

```sql
SELECT account, currency, sum(units(position)) AS units,
       sum(cost(position)) AS cost_basis
WHERE account ~ "Assets:Brokerage"
GROUP BY account, currency
```

### Realized Gains

```sql
SELECT year(date) AS year, sum(cost(position)) AS gains
WHERE account ~ "Income:CapitalGains"
GROUP BY year
```

## Net Worth

### Current Net Worth

```sql
SELECT sum(cost(position)) AS net_worth
WHERE account ~ "Assets" OR account ~ "Liabilities"
```

### Net Worth by Account Type

```sql
SELECT root(account, 1) AS type, sum(cost(position)) AS total
WHERE account ~ "Assets" OR account ~ "Liabilities"
GROUP BY type
```

## Utility Queries

### List All Accounts

```sql
SELECT DISTINCT account
ORDER BY account
```

### List All Payees

```sql
SELECT DISTINCT payee
WHERE payee IS NOT NULL
ORDER BY payee
```

### Account Activity

```sql
-- Find accounts with transactions in a date range
SELECT DISTINCT account
WHERE date >= 2024-01-01 AND date <= 2024-03-31
ORDER BY account
```

## Tips

### Save Common Queries

Create shell aliases for frequently used queries:

```bash
alias expenses='rledger query ledger.beancount "SELECT root(account, 2) AS category, sum(cost(position)) AS total WHERE account ~ \"Expenses\" GROUP BY category ORDER BY total DESC"'
```

### Output to CSV

```bash
rledger query -f csv ledger.beancount "SELECT ..." > report.csv
```

### Combine with Other Tools

```bash
# Pipe to jq for JSON processing
rledger query -f json ledger.beancount "SELECT ..." | jq '.rows[]'

# Use with datamash for quick stats
rledger query -f csv ledger.beancount "SELECT ..." | datamash sum 2
```

## See Also

- [query command](../commands/query.md) - Full query command reference
- [BQL Reference](../reference/bql.md) - Complete BQL syntax
