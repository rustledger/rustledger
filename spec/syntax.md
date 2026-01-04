# Beancount Language Syntax Specification

## Core Concepts

**Beancount** is a declarative text-based double-entry bookkeeping system. Input files contain directives (entries) with dates and types, plus optional global options.

## Date Format

All directives begin with dates in ISO 8601 format: `YYYY-MM-DD` (dashes required). The system supports both dash and slash variants (e.g., `2014-02-03` or `2014/02/03`).

## Accounts

Account names consist of colon-separated capitalized words beginning with one of five root types:

```
Assets | Liabilities | Equity | Income | Expenses
```

**Rules for account components:**
- Must start with a capital letter or number
- Can contain letters, numbers, and dashes only
- No spaces or special characters allowed

Example hierarchy:
```
Assets:US:BofA:Checking
Assets:US:BofA:Savings
Expenses:Food:Groceries
```

## Commodities/Currencies

Currency names are recognized by syntax alone (no pre-declaration required):
- All capital letters
- 1-24 characters long
- Must start and end with capital letters or numbers
- Middle characters: letters, numbers, apostrophes, periods, underscores, dashes

Examples: `USD`, `EUR`, `MSFT`, `VACHR` (vacation hours)

## Comments & Organization

Lines after semicolon (`;`) are ignored:
```beancount
; This is a comment
2015-01-01 * "Transaction"
  Assets:Cash      -20 USD  ; inline comment
  Expenses:Taxi
```

Non-directive lines are silently ignored, enabling org-mode formatting.

## Directives

### Open

Declares account inception before first posting:

```
YYYY-MM-DD open Account [Currency,...] ["BookingMethod"]
```

**Optional features:**
- Currency constraints (comma-separated): restrict postings to specified currencies
- Booking methods: `STRICT` (default, exact lot matching), `FIFO`, `LIFO`, `AVERAGE`, `NONE`

Example:
```beancount
2014-05-01 open Assets:Checking USD
2014-05-01 open Assets:Investments MSFT,AAPL
2014-05-01 open Assets:Stocks "FIFO"
```

### Close

Marks account as inactive:

```
YYYY-MM-DD close Account
```

Prevents subsequent postings; helps filtering in reports. Does not generate implicit zero balance assertion.

### Commodity

Declares currencies with optional metadata (purely informational):

```
YYYY-MM-DD commodity Currency
```

Example:
```beancount
1867-07-01 commodity CAD
  name: "Canadian Dollar"
  asset-class: "cash"
```

### Transaction

Most common directive, representing financial exchanges:

```
YYYY-MM-DD [txn|Flag] [[Payee] Narration] [Metadata] Postings
```

**Flag options:**
- `*` — Completed transaction (default)
- `!` — Incomplete, needs review

**Payee & Narration:**
- Single string becomes narration only
- Two strings: first is payee, second is narration
- Empty string allowed for payee: `"Payee" ""`

**Postings format:**
```
[Flag] Account Amount [{Cost}] [@ Price] [Metadata]
```

Multiple postings per transaction allowed. Amount can use arithmetic expressions: `( ) * / - +`

Example:
```beancount
2014-05-05 * "Cafe Mogador" "Lamb tagine"
  Liabilities:CreditCard     -37.45 USD
  Expenses:Restaurant
```

### Posting Amounts & Costs

**Simple amount:**
```beancount
Assets:Checking  100.00 USD
```

**With price (currency conversion):**
```beancount
Assets:Checking  -400.00 USD @ 1.09 CAD
```
Per-unit conversion rate specified with `@`; total conversion with `@@`:
```beancount
Assets:Checking  -400.00 USD @@ 436.01 CAD
```

**With cost (for held commodities):**
```beancount
Assets:Stocks  10 MSFT {45.30 USD}
```

Cost held in curly braces `{}`; tracks basis for capital gains.

**With both cost and price:**
```beancount
Assets:Stocks  -10 MSFT {183.07 USD} @ 197.90 USD
```
Cost used for balancing; price generates price entry only.

**Amount interpolation:**
Omit amount from at most one posting per transaction; calculated automatically:
```beancount
2012-11-03 * "Transfer"
  Assets:Checking    -400.00 USD
  Liabilities:CreditCard
```

### Balancing Rule

The "weight" of each posting determines balance. Calculation:
1. **Amount only** → amount + currency
2. **Price only** → amount × price currency
3. **Cost only** → amount × cost currency
4. **Both cost & price** → cost currency (price ignored for balancing)

Sum of all posting weights must equal zero.

### Reducing Positions

When posting a reduction to commodities held at cost:
- Reduction must match existing lot(s)
- Matching via cost specification, date, or label filters available lots
- Ambiguous matches invoke account's booking method

Example lot specification:
```beancount
Assets:Stocks  -20 MSFT {43.40 USD}
Assets:Stocks  -20 MSFT {2014-02-11}
Assets:Stocks  -20 MSFT {"ref-001"}
```

**Negative cost units:** Not allowed by default (prevents entry errors).

### Tags

Mark transactions with hash-prefixed strings for filtering:

```beancount
2014-04-23 * "Flight" #berlin-trip-2014 #germany
  Expenses:Flights  -1230.27 USD
  Liabilities:CreditCard
```

**Tag stack:**
```
pushtag #berlin-trip-2014
2014-04-23 * "Transaction"
  …
poptag #berlin-trip-2014
```

### Links

Group related transactions using caret-prefixed identifiers:

```beancount
2014-02-05 * "Invoice" ^invoice-001
  Income:Clients  -8450.00 USD
  Assets:Receivable

2014-02-20 * "Payment" ^invoice-001
  Assets:Checking  8450.00 USD
  Assets:Receivable
```

### Balance Assertions

Verify account commodity balances at specific date/time:

```
YYYY-MM-DD balance Account Amount
```

Checks at **beginning of day** (midnight). Single assertion per commodity:

```beancount
2014-08-09 balance Assets:Checking  562.00 USD
2014-08-09 balance Assets:Checking  210.00 CAD
```

**Features:**
- Works on parent accounts (includes sub-account totals)
- Aggregates across cost lots
- Local tolerance override: `balance Account Amount ~ Tolerance`

### Pad

Auto-insert transaction to satisfy subsequent balance assertion:

```
YYYY-MM-DD pad Account SourceAccount
```

Example:
```beancount
2002-01-17 open Assets:Checking
2002-01-17 pad Assets:Checking Equity:Opening-Balances
2014-07-09 balance Assets:Checking  987.34 USD
```

Generates:
```
2002-01-17 P "(Padding inserted...)"
  Assets:Checking        987.34 USD
  Equity:Opening-Balances  -987.34 USD
```

**Constraints:**
- Must have subsequent balance assertion
- No multiple pads per account/commodity currently
- No cost basis support

### Notes

Attach dated comment to account journal:

```
YYYY-MM-DD note Account "Description"
```

### Documents

Link external files to account:

```
YYYY-MM-DD document Account "/path/to/file.pdf"
```

**Directory option:**
```
option "documents" "/home/user/stmts"
```

Requires file naming: `YYYY-MM-DD.description.extension`

### Prices

Record commodity exchange rates:

```
YYYY-MM-DD price Commodity PriceAmount
```

Example:
```beancount
2014-07-09 price HOOL  579.18 USD
2014-07-09 price USD  1.08 CAD
```

**Automatic generation:**
Enable `beancount.plugins.implicit_prices` to synthesize from posting costs/prices.

### Events

Track variable values over time (location, address, employer, trading windows):

```
YYYY-MM-DD event "Name" "Value"
```

Example:
```beancount
2014-07-09 event "location" "Paris, France"
2014-08-15 event "location" "Berlin, Germany"
```

### Query

Embed SQL queries for report generation:

```
YYYY-MM-DD query "QueryName" "SELECT ..."
```

### Custom

Prototype new directive types:

```
YYYY-MM-DD custom "TypeName" Value1 Value2 ...
```

Values can be strings, dates, booleans, amounts, numbers.

## Metadata

Attach arbitrary key-value pairs to directives and postings:

**Keys:** Lowercase start, contain letters/numbers/dashes/underscores

**Value types:**
- Strings
- Accounts
- Currency
- Dates
- Tags
- Numbers (Decimal)
- Amounts

```beancount
2013-03-14 open Assets:BTrade:HOOLI
  category: "taxable"

2013-08-26 * "Buying shares"
  statement: "confirmation-826453.pdf"
  Assets:BTrade:HOOLI  10 HOOL @ 498.45 USD
    decision: "scheduled"
  Assets:BTrade:Cash
```

**Automatic metadata:** All directives contain `filename` (string) and `lineno` (integer).

## Strings

Free text enclosed in double quotes; may span multiple lines:

```beancount
2014-05-05 * "Cafe" "Multi-line
narration here"
```

## Options

Global configuration directives (undated):

```
option "Name" "Value"
```

**Notable options:**
- `operating_currency` — Designates main currencies for reporting (multiple allowed)
- `title` — Ledger title
- `name_assets`, `name_liabilities`, etc. — Root account name overrides
- `booking_method` — Default booking method for accounts

## Plugins

Load modules for entry transformation:

```
plugin "module_name"
plugin "module_name" "config_string"
```

## Includes

Split files across multiple documents:

```
include "path/to/file.beancount"
```

Relative paths resolve to including file's directory.

## Entry Ordering

Directives are automatically sorted chronologically after parsing, regardless of file order. Within the same date:
1. Balance assertions and other non-transaction directives first
2. Transactions after
