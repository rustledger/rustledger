---
title: Beancount Syntax Reference
description: Complete guide to beancount file syntax
---

# Beancount Syntax Reference

Complete reference for the beancount file format.

## File Structure

A beancount file is a plain text file (typically `.beancount` extension) containing:

- Directives (dated entries)
- Options (configuration)
- Comments

```beancount
; This is a comment
option "title" "My Finances"

2024-01-01 open Assets:Bank:Checking  USD
2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food:Coffee   4.50 USD
  Assets:Bank:Checking
```

## Comments

```beancount
; Semicolon comment (anywhere on line)
* Org-mode header (treated as comment at start of line)
```

## Directives

All directives start with a date in `YYYY-MM-DD` format.

### Open

Declare an account before using it.

```beancount
2020-01-01 open Assets:Bank:Checking  USD
2020-01-01 open Assets:Brokerage      USD,AAPL,GOOGL
2020-01-01 open Expenses:Food
2020-01-01 open Liabilities:CreditCard  USD  "STRICT"
```

Syntax: `DATE open ACCOUNT [CURRENCIES] [BOOKING]`

- **CURRENCIES**: Optional comma-separated list of allowed currencies
- **BOOKING**: Optional booking method (`"STRICT"`, `"STRICT_WITH_SIZE"`, `"FIFO"`, `"LIFO"`, `"HIFO"`, `"AVERAGE"`, `"NONE"`)

### Close

Close an account (no transactions allowed after this date).

```beancount
2024-12-31 close Assets:Bank:OldAccount
```

The account must have zero balance when closed.

### Commodity

Declare a currency or commodity.

```beancount
2020-01-01 commodity USD
  name: "US Dollar"

2020-01-01 commodity AAPL
  name: "Apple Inc."
  asset-class: "stock"
```

### Transaction

Record a financial transaction.

```beancount
2024-01-15 * "Payee" "Narration"
  Assets:Bank:Checking   -50.00 USD
  Expenses:Food           50.00 USD
```

Full syntax:

```
DATE [FLAG] ["PAYEE"] "NARRATION" [TAGS] [LINKS]
  [METADATA]
  ACCOUNT  [AMOUNT] [COST] [PRICE]
  ACCOUNT  [AMOUNT] [COST] [PRICE]
```

#### Flags

| Flag | Meaning |
|------|---------|
| `*` | Cleared/completed transaction |
| `!` | Pending/flagged transaction |

#### Tags and Links

```beancount
2024-01-15 * "Dinner" #vacation #food ^trip-2024
  Expenses:Food    45.00 USD
  Assets:Cash
```

- **Tags**: `#tagname` - categorize transactions
- **Links**: `^linkname` - connect related transactions

### Balance

Assert an account balance at a point in time.

```beancount
2024-01-31 balance Assets:Bank:Checking  1234.56 USD
```

Validation fails if the computed balance doesn't match.

### Pad

Automatically insert a balancing transaction.

```beancount
2024-01-01 pad Assets:Bank:Checking  Equity:Opening-Balances
2024-01-01 balance Assets:Bank:Checking  1000.00 USD
```

The pad directive creates a transaction to make the balance assertion true.

### Price

Record a market price for a commodity.

```beancount
2024-01-15 price AAPL  185.50 USD
2024-01-15 price EUR   1.08 USD
```

### Event

Record a non-financial event.

```beancount
2024-01-15 event "location" "New York"
2024-03-01 event "employer" "Acme Corp"
```

### Note

Add a note to an account.

```beancount
2024-01-15 note Assets:Bank:Checking "Called bank about fees"
```

### Document

Link a document to an account.

```beancount
2024-01-15 document Assets:Bank:Checking "/path/to/statement.pdf"
```

### Custom

Define custom directives (for plugins).

```beancount
2024-01-15 custom "budget" Expenses:Food  500 USD
```

## Amounts and Currencies

### Basic Amounts

```beancount
100 USD
-50.00 EUR
1,234.56 USD    ; Comma grouping allowed
1234.5678 BTC   ; Arbitrary precision
```

### Currency Names

- Must be uppercase letters (A-Z)
- Can include numbers after first character
- Common: `USD`, `EUR`, `GBP`, `BTC`, `AAPL`

## Costs and Prices

### Cost Basis

Record what you paid for something:

```beancount
; Buy 10 shares at $150 each
Assets:Brokerage   10 AAPL {150.00 USD}
```

### Cost with Date

```beancount
; Specify acquisition date
Assets:Brokerage   10 AAPL {150.00 USD, 2024-01-15}
```

### Cost with Label

```beancount
; Label for specific lot identification
Assets:Brokerage   10 AAPL {150.00 USD, "lot1"}
```

### Price Conversion

Convert at a specific price:

```beancount
; Per-unit price
Assets:EUR    100 EUR @ 1.08 USD

; Total price
Assets:EUR    100 EUR @@ 108 USD
```

### Cost and Price Together

For capital gains transactions:

```beancount
; Sell shares bought at $150, now worth $175
Assets:Brokerage  -10 AAPL {150.00 USD} @ 175.00 USD
Assets:Bank      1750.00 USD
Income:CapitalGains
```

### Reducing Positions

```beancount
; Automatic lot matching (FIFO/LIFO based on account)
Assets:Brokerage  -10 AAPL {}

; Match specific cost
Assets:Brokerage  -10 AAPL {150.00 USD}

; Match specific date
Assets:Brokerage  -10 AAPL {2024-01-15}

; Match specific label
Assets:Brokerage  -10 AAPL {"lot1"}
```

## Metadata

Add key-value pairs to any directive or posting.

### On Directives

```beancount
2024-01-15 * "Coffee Shop"
  category: "discretionary"
  receipt: "/receipts/2024/coffee.jpg"
  Expenses:Food   4.50 USD
  Assets:Cash
```

### On Postings

```beancount
2024-01-15 * "Mixed Purchase"
  Expenses:Food      20.00 USD
    item: "groceries"
  Expenses:Supplies  15.00 USD
    item: "cleaning"
  Assets:Cash
```

### Value Types

```beancount
string-value: "text in quotes"
number-value: 123.45
date-value: 2024-01-15
account-value: Assets:Bank
currency-value: USD
tag-value: #tagname
boolean-value: TRUE
```

## Account Names

### Structure

```
Type:Category:Subcategory:Detail
```

### Root Types

The defaults are English, but can be customized to any language via options:

| Type | Purpose |
|------|---------|
| `Assets` | What you own (positive = good) |
| `Liabilities` | What you owe (negative = debt) |
| `Equity` | Net worth adjustments |
| `Income` | Money coming in (negative in ledger) |
| `Expenses` | Money going out (positive in ledger) |

Account names support full Unicode — Cyrillic, CJK, Arabic, etc.:

```beancount
option "name_equity" "Капитал"
option "name_assets" "资产"

2024-01-01 open Капитал:Opening-Balances
2024-01-01 open 资产:银行:支票 CNY
```

### Naming Conventions

```beancount
; By institution
Assets:Bank:Chase:Checking
Assets:Bank:Chase:Savings

; By purpose
Expenses:Food:Groceries
Expenses:Food:Restaurants
Expenses:Food:Coffee

; By geography
Assets:Bank:US:Chase
Assets:Bank:EU:Deutsche
```

## Include Files

Split your ledger across multiple files:

```beancount
include "accounts.beancount"
include "2024/*.beancount"
include "prices/2024.beancount"
```

## Options

Configure beancount behavior:

```beancount
option "title" "Personal Finances"
option "operating_currency" "USD"
option "booking_method" "FIFO"
```

See [Options Reference](options.md) for all options.

## Plugins

Enable plugins for validation or transformation:

```beancount
plugin "beancount.plugins.auto_accounts"
plugin "beancount.plugins.implicit_prices"
```

See [Plugins Reference](plugins.md) for available plugins.

## Complete Example

```beancount
; main.beancount - Personal Finance Ledger
option "title" "Personal Finances 2024"
option "operating_currency" "USD"

plugin "beancount.plugins.auto_accounts"

; === Accounts ===
2020-01-01 open Assets:Bank:Checking      USD
2020-01-01 open Assets:Bank:Savings       USD
2020-01-01 open Assets:Brokerage          USD,AAPL,VTI
2020-01-01 open Liabilities:CreditCard    USD
2020-01-01 open Expenses:Food
2020-01-01 open Expenses:Transport
2020-01-01 open Income:Salary             USD
2020-01-01 open Equity:Opening-Balances

; === Opening Balance ===
2024-01-01 pad Assets:Bank:Checking Equity:Opening-Balances
2024-01-01 balance Assets:Bank:Checking  5000.00 USD

; === Transactions ===
2024-01-15 * "Employer" "January salary" #income
  Assets:Bank:Checking   3500.00 USD
  Income:Salary         -3500.00 USD

2024-01-16 * "Grocery Store" "Weekly groceries"
  Expenses:Food:Groceries   85.50 USD
  Assets:Bank:Checking

2024-01-17 * "Gas Station" "Fuel"
  Expenses:Transport:Gas   45.00 USD
  Liabilities:CreditCard

2024-01-20 * "Brokerage" "Buy index fund"
  Assets:Brokerage         10 VTI {450.00 USD}
  Assets:Bank:Checking  -4500.00 USD

; === Month End ===
2024-01-31 balance Assets:Bank:Checking  -1130.50 USD
```

## See Also

- [Quick Start](../getting-started/quick-start.md) - Get started with rustledger
- [Options Reference](options.md) - All configuration options
- [Error Codes](errors.md) - Understanding validation errors
