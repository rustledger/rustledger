______________________________________________________________________

## title: Accounting Concepts description: Introduction to double-entry bookkeeping

# Accounting Concepts

A practical introduction to double-entry bookkeeping for plain-text accounting.

## What is Double-Entry Bookkeeping?

Double-entry bookkeeping is a system where every transaction affects at least two accounts. Money never appears or disappears - it always moves from one place to another.

When you buy coffee:

- Your cash **decreases** (Assets go down)
- Your expenses **increase** (Expenses go up)

```beancount
2024-01-15 * "Coffee Shop"
  Expenses:Food:Coffee    4.50 USD   ; Expense increases
  Assets:Cash            -4.50 USD   ; Asset decreases
```

**The key rule**: Every transaction must balance to zero.

## The Five Account Types

All accounts fall into five categories:

| Type | What it tracks | Normal balance |
|------|----------------|----------------|
| **Assets** | What you own | Positive |
| **Liabilities** | What you owe | Negative |
| **Equity** | Net worth adjustments | Negative |
| **Income** | Money coming in | Negative |
| **Expenses** | Money going out | Positive |

### Assets

Things you own that have value.

```
Assets:Bank:Checking      ; Your bank balance
Assets:Cash               ; Physical cash
Assets:Brokerage          ; Investment accounts
Assets:House              ; Property value
Assets:Receivables:John   ; Money owed to you
```

**Rule**: When you gain an asset, the balance increases (positive).

### Liabilities

Debts and obligations you owe.

```
Liabilities:CreditCard    ; Credit card balance
Liabilities:Mortgage      ; Home loan
Liabilities:Loans:Auto    ; Car loan
```

**Rule**: When you owe more, the balance becomes more negative.

### Equity

Adjustments to your net worth, typically for:

- Opening balances when starting to track
- Rounding differences
- Retained earnings

```
Equity:Opening-Balances   ; Starting balances
Equity:Retained-Earnings  ; Accumulated profits
```

### Income

Money you earn (flows in).

```
Income:Salary             ; Paycheck
Income:Interest           ; Bank interest
Income:Dividends          ; Investment dividends
Income:CapitalGains       ; Profits from selling investments
```

**Rule**: Income is negative in the ledger (counterintuitive but correct).

### Expenses

Money you spend (flows out).

```
Expenses:Food             ; Groceries, restaurants
Expenses:Housing:Rent     ; Monthly rent
Expenses:Transport        ; Gas, transit, car maintenance
Expenses:Taxes:Federal    ; Tax payments
```

**Rule**: Expenses are positive in the ledger.

## The Accounting Equation

The fundamental equation of accounting:

```
Assets = Liabilities + Equity
```

Or rearranged:

```
Assets - Liabilities - Equity = 0
```

In beancount terms (including Income and Expenses):

```
Assets + Expenses + Liabilities + Income + Equity = 0
```

This is why every transaction must sum to zero.

## Why Income is Negative

This confuses many beginners. Here's the logic:

When you earn money, two things happen:

1. Your bank account (Asset) **increases**: `+$1000`
1. Something must **decrease** to balance: `-$1000`

That "something" is Income. Income being negative means "money flowed in."

```beancount
2024-01-15 * "Employer" "Salary"
  Assets:Bank:Checking   1000.00 USD   ; +1000 (your bank grows)
  Income:Salary         -1000.00 USD   ; -1000 (balances to zero)
```

Think of negative income as "a reduction in what the world owes you."

## Expenses are Positive

When you spend money:

```beancount
2024-01-15 * "Grocery Store"
  Expenses:Food          50.00 USD   ; +50 (expense recorded)
  Assets:Bank:Checking  -50.00 USD   ; -50 (your bank shrinks)
```

Positive expense = value consumed.

## Common Transactions Explained

### Buying Something with Cash

```beancount
2024-01-15 * "Bookstore"
  Expenses:Books        25.00 USD    ; Expense increases (+)
  Assets:Cash          -25.00 USD    ; Asset decreases (-)
```

Net change: `+25 + (-25) = 0` ✓

### Buying Something with Credit Card

```beancount
2024-01-15 * "Restaurant"
  Expenses:Food         45.00 USD    ; Expense increases (+)
  Liabilities:CreditCard -45.00 USD  ; Liability increases (more negative)
```

Your credit card balance (a liability) becomes *more negative* because you owe more.

### Receiving Income

```beancount
2024-01-15 * "Employer" "Paycheck"
  Assets:Bank:Checking  3000.00 USD  ; Asset increases (+)
  Income:Salary        -3000.00 USD  ; Income (negative)
```

### Paying Off Credit Card

```beancount
2024-02-01 * "Credit Card Payment"
  Liabilities:CreditCard  500.00 USD  ; Liability decreases (less negative)
  Assets:Bank:Checking   -500.00 USD  ; Asset decreases (-)
```

### Transferring Between Accounts

```beancount
2024-01-15 * "Transfer to Savings"
  Assets:Bank:Savings    1000.00 USD  ; One asset increases
  Assets:Bank:Checking  -1000.00 USD  ; Another decreases
```

This is just money moving - no income or expense involved.

## Net Worth

Your net worth is:

```
Net Worth = Assets - Liabilities
```

Or equivalently:

```
Net Worth = -(Income + Expenses + Equity)
```

Query your net worth:

```sql
SELECT sum(cost(position))
WHERE account ~ "Assets" OR account ~ "Liabilities"
```

## Profit and Loss

Your profit (or loss) for a period is:

```
Profit = Income + Expenses
```

Remember: Income is negative, so if you earned more than you spent, the sum is negative (profit). If you spent more, it's positive (loss).

Query this year's profit:

```sql
SELECT sum(cost(position))
WHERE (account ~ "Income" OR account ~ "Expenses")
  AND year(date) = 2024
```

## Period Reporting

### Balance Sheet

Shows your financial position at a point in time:

- **Assets**: What you own
- **Liabilities**: What you owe
- **Net Worth**: The difference

```bash
rledger report ledger.beancount balsheet
```

### Income Statement

Shows financial activity over a period:

- **Income**: Money earned
- **Expenses**: Money spent
- **Net Income**: The difference

```bash
rledger report ledger.beancount income
```

## Account Hierarchy

Organize accounts hierarchically:

```
Assets
├── Bank
│   ├── Checking
│   └── Savings
├── Brokerage
│   ├── AAPL
│   └── VTI
└── Cash

Expenses
├── Food
│   ├── Groceries
│   └── Restaurants
├── Housing
│   ├── Rent
│   └── Utilities
└── Transport
    ├── Gas
    └── Maintenance
```

Benefits:

- Query at any level: `account ~ "Expenses:Food"` matches all food expenses
- Reports can roll up to parent categories
- Keeps related transactions together

## Tips for Beginners

### 1. Start Simple

Begin with just a few accounts:

```beancount
2024-01-01 open Assets:Bank:Checking
2024-01-01 open Expenses:Everything
2024-01-01 open Income:Everything
```

Add detail as you learn what you want to track.

### 2. Don't Worry About Perfection

You can always recategorize later. The important thing is capturing transactions.

### 3. Let One Posting Auto-Calculate

Only one posting per currency can omit the amount:

```beancount
2024-01-15 * "Coffee"
  Expenses:Food   4.50 USD
  Assets:Cash              ; Automatically: -4.50 USD
```

### 4. Verify with Balance Assertions

Add periodic checks:

```beancount
2024-01-31 balance Assets:Bank:Checking  1234.56 USD
```

If wrong, rustledger will tell you.

### 5. Use Tags for Analysis

Tag transactions for later querying:

```beancount
2024-01-15 * "Dinner" #vacation #food
  Expenses:Food   45.00 USD
  Assets:Cash
```

## See Also

- [Quick Start](../getting-started/quick-start.md) - Start using rustledger
- [Syntax Reference](../reference/syntax.md) - Complete syntax guide
- [Cookbook](cookbook.md) - Real-world examples
