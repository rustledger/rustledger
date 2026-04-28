______________________________________________________________________

## title: Budgeting description: Track budgets and compare against actual spending

# Budgeting

Methods for tracking budgets and comparing against actual spending in beancount.

## Approach 1: Query-Based Budgeting

The simplest approach - define budgets externally and query actuals.

### Define Your Budget

Create a reference file or spreadsheet:

| Category | Monthly Budget |
|----------|---------------|
| Food:Groceries | $400 |
| Food:Restaurants | $150 |
| Transport | $200 |
| Entertainment | $100 |

### Query Actuals

```bash
# This month's spending by category
rledger query ledger.beancount "
  SELECT root(account, 2) AS category, sum(cost(position)) AS spent
  WHERE account ~ 'Expenses'
    AND year(date) = year(today())
    AND month(date) = month(today())
  GROUP BY category
  ORDER BY spent DESC
"
```

### Compare in Shell Script

```bash
#!/bin/bash
# budget-check.sh

LEDGER="ledger.beancount"
MONTH=$(date +%Y-%m)

echo "Budget vs Actual for $MONTH"
echo "============================"

# Food:Groceries - Budget $400
actual=$(rledger query "$LEDGER" "
  SELECT sum(cost(position))
  WHERE account ~ 'Expenses:Food:Groceries'
    AND year(date) = year(today())
    AND month(date) = month(today())
" -f csv | tail -1)

echo "Groceries:    \$${actual} / \$400"

# Add more categories...
```

## Approach 2: Budget Accounts

Track budgets within beancount using special accounts.

### Setup

```beancount
; Budget accounts
2024-01-01 open Assets:Budget:Food
2024-01-01 open Assets:Budget:Transport
2024-01-01 open Assets:Budget:Entertainment
2024-01-01 open Income:Budget:Allocation
```

### Allocate Budget Monthly

At the start of each month, allocate your budget:

```beancount
2024-01-01 * "January budget allocation"
  Assets:Budget:Food            550.00 USD
  Assets:Budget:Transport       200.00 USD
  Assets:Budget:Entertainment   100.00 USD
  Income:Budget:Allocation     -850.00 USD
```

### Track Spending Against Budget

When you spend, reduce both your real account and budget:

```beancount
2024-01-15 * "Grocery Store"
  Expenses:Food:Groceries    85.00 USD
  Assets:Bank:Checking      -85.00 USD
  ; Track against budget
  Assets:Budget:Food        -85.00 USD
  Expenses:Budget:Food       85.00 USD
```

### Check Remaining Budget

```bash
rledger query ledger.beancount "
  SELECT account, sum(position)
  WHERE account ~ 'Assets:Budget'
  GROUP BY account
"
```

Output:

```
Assets:Budget:Entertainment    75.00 USD
Assets:Budget:Food            120.00 USD
Assets:Budget:Transport       150.00 USD
```

## Approach 3: Envelope Budgeting

A variation where you "move" money into envelopes.

### Setup

```beancount
; Envelope accounts (virtual, for budgeting)
2024-01-01 open Assets:Envelopes:Groceries
2024-01-01 open Assets:Envelopes:Dining
2024-01-01 open Assets:Envelopes:Gas
2024-01-01 open Assets:Envelopes:Fun

; Holding account for unallocated funds
2024-01-01 open Assets:Envelopes:Unallocated
```

### Fund Envelopes from Income

```beancount
2024-01-15 * "Paycheck"
  Assets:Bank:Checking      3500.00 USD
  Income:Salary            -3500.00 USD

2024-01-15 * "Fund envelopes"
  Assets:Envelopes:Groceries      400.00 USD
  Assets:Envelopes:Dining         150.00 USD
  Assets:Envelopes:Gas            200.00 USD
  Assets:Envelopes:Fun            100.00 USD
  Assets:Envelopes:Unallocated   2650.00 USD
  Assets:Bank:Checking          -3500.00 USD  ; Virtual transfer
```

Wait - this double-counts the money! Let's fix that.

### Better: Use Virtual Accounts

Instead, track envelopes separately from real money:

```beancount
2024-01-15 * "Allocate to envelopes" ^budget-jan
  Assets:Envelopes:Groceries      400.00 USD
  Assets:Envelopes:Dining         150.00 USD
  Assets:Envelopes:Gas            200.00 USD
  Assets:Envelopes:Fun            100.00 USD
  Equity:Budgeted                -850.00 USD
```

When you spend:

```beancount
2024-01-20 * "Grocery Store"
  Expenses:Food:Groceries    85.00 USD
  Assets:Bank:Checking      -85.00 USD
  ; Reduce envelope
  Equity:Budgeted            85.00 USD
  Assets:Envelopes:Groceries -85.00 USD
```

## Approach 4: Custom Metadata

Tag transactions with budget categories:

```beancount
2024-01-15 * "Grocery Store"
  budget-category: "food"
  Expenses:Food:Groceries   85.00 USD
  Assets:Bank:Checking

2024-01-16 * "Gas Station"
  budget-category: "transport"
  Expenses:Transport:Gas    45.00 USD
  Assets:Bank:Checking
```

Query by budget category:

```bash
rledger query ledger.beancount "
  SELECT sum(cost(position))
  WHERE entry_meta('budget-category') = 'food'
    AND month(date) = 1 AND year(date) = 2024
"
```

> **Note:** Use `entry_meta(...)` (or `any_meta(...)`) when the metadata is on the
> transaction header. The `meta(...)` function only inspects metadata attached
> directly to a posting — see [BQL → Metadata functions](../reference/bql.md#metadata-functions)
> for the full distinction.

## Monthly Budget Review

### Summary Report Script

```bash
#!/bin/bash
# monthly-review.sh

LEDGER="${LEDGER_FILE:-ledger.beancount}"
YEAR=$(date +%Y)
MONTH=$(date +%m)

echo "=== Monthly Budget Review: $YEAR-$MONTH ==="
echo ""

# Income
echo "INCOME"
rledger query "$LEDGER" "
  SELECT root(account, 2), sum(cost(position)) AS amount
  WHERE account ~ 'Income'
    AND year(date) = $YEAR AND month(date) = $MONTH
  GROUP BY 1
  ORDER BY amount
"

echo ""
echo "EXPENSES BY CATEGORY"
rledger query "$LEDGER" "
  SELECT root(account, 2), sum(cost(position)) AS amount
  WHERE account ~ 'Expenses'
    AND year(date) = $YEAR AND month(date) = $MONTH
  GROUP BY 1
  ORDER BY amount DESC
"

echo ""
echo "NET INCOME"
rledger query "$LEDGER" "
  SELECT sum(cost(position)) AS net
  WHERE (account ~ 'Income' OR account ~ 'Expenses')
    AND year(date) = $YEAR AND month(date) = $MONTH
"
```

### Year-to-Date Comparison

```sql
-- Query each month separately
SELECT root(account, 2) AS category, sum(cost(position)) AS total
WHERE account ~ "Expenses" AND year(date) = 2024 AND month(date) = 1
GROUP BY category ORDER BY category

SELECT root(account, 2) AS category, sum(cost(position)) AS total
WHERE account ~ "Expenses" AND year(date) = 2024 AND month(date) = 2
GROUP BY category ORDER BY category
```

## Savings Goals

Track progress toward savings goals:

```beancount
2024-01-01 open Assets:Savings:Emergency
2024-01-01 open Assets:Savings:Vacation
2024-01-01 open Assets:Savings:House

; Monthly allocation
2024-01-15 * "Savings allocation"
  Assets:Savings:Emergency   200.00 USD
  Assets:Savings:Vacation    150.00 USD
  Assets:Savings:House       300.00 USD
  Assets:Bank:Checking      -650.00 USD
```

Check progress:

```bash
rledger query ledger.beancount "
  SELECT account, sum(position) AS balance
  WHERE account ~ 'Assets:Savings'
  GROUP BY account
"
```

## Tips

### 1. Keep It Simple

Start with query-based budgeting. Only add complexity if needed.

### 2. Review Regularly

Set a monthly reminder to review spending vs budget.

### 3. Adjust Budgets

Your first budget will be wrong. Adjust based on actual spending patterns.

### 4. Use Rolling Averages

Instead of fixed budgets, track 3-month averages:

```sql
-- Get last 3 months of expenses (adjust date range as needed)
SELECT root(account, 2),
       sum(cost(position)) / 3 AS monthly_avg
WHERE account ~ "Expenses"
  AND date >= 2024-01-01 AND date < 2024-04-01
GROUP BY 1
ORDER BY 2 DESC
```

### 5. Separate Needs vs Wants

Use account hierarchy:

```
Expenses:Needs:Housing
Expenses:Needs:Utilities
Expenses:Needs:Groceries
Expenses:Wants:Dining
Expenses:Wants:Entertainment
Expenses:Wants:Shopping
```

Query each:

```sql
SELECT sum(cost(position))
WHERE account ~ "Expenses:Needs"
```

## See Also

- [Common Queries](common-queries.md) - More query examples
- [Cookbook](cookbook.md) - Transaction examples
- [Accounting Concepts](accounting-concepts.md) - Double-entry basics
