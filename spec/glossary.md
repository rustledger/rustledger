# Glossary

Definitions of terms used throughout the rustledger specification.

## A

### Account
A named container for tracking financial positions. Consists of colon-separated components starting with a root type (Assets, Liabilities, Equity, Income, Expenses).

Example: `Assets:Bank:Checking`

### Amount
A quantity paired with a currency. Represents a specific value in a specific denomination.

Example: `100.00 USD`

### Assertion (Balance Assertion)
A directive that verifies an account's balance matches an expected value at a specific date.

Example: `2024-01-15 balance Assets:Checking 1000 USD`

### Augmentation
Adding units to an inventory. The opposite of reduction. Creates a new lot or merges with an existing identical lot.

## B

### Booking
The process of matching a reduction (sale/withdrawal) against existing lots in an inventory. Methods include STRICT, FIFO, LIFO, AVERAGE, and NONE.

### Booking Method
Algorithm for selecting which lot(s) to reduce when multiple lots match:
- **STRICT**: Requires unambiguous match; error if multiple lots match
- **FIFO**: First In, First Out; oldest lots first
- **LIFO**: Last In, First Out; newest lots first
- **AVERAGE**: Weighted average cost basis
- **NONE**: No matching; allows mixed-sign inventories

## C

### Cost
The acquisition price of a position, including per-unit price, currency, date, and optional label. Stored with positions to track cost basis.

Syntax: `{100.00 USD, 2024-01-15, "lot-1"}`

### Cost Basis
The total acquisition cost of a position. Used for calculating capital gains.

Formula: `units × cost_per_unit`

### Cost Specification (CostSpec)
A pattern for matching lots during reduction. May partially specify cost, date, and/or label.

### Currency
An identifier for a denomination. May represent fiat currency (USD, EUR), stocks (AAPL, GOOG), crypto (BTC), or custom units (VACHR).

## D

### Decimal
An exact decimal number (not floating point). Used for all financial calculations to avoid rounding errors.

### Directive
A dated instruction in a beancount file. Types include: transaction, balance, open, close, commodity, pad, event, query, note, document, price, custom.

## F

### Flag
A character indicating transaction status:
- `*` - Complete/cleared
- `!` - Pending/incomplete

## I

### Interpolation
Automatically calculating a missing posting amount to make a transaction balance. At most one posting per currency may be interpolated.

### Inventory
A collection of positions (lots) held in an account. Tracks units, costs, dates, and labels for each lot.

## L

### Ledger
The complete processed state of a beancount file, including all directives, computed inventories, validation errors, and options.

### Link
A caret-prefixed identifier connecting related transactions.

Example: `^invoice-123`

### Lot
A position with a specific cost basis, acquisition date, and optional label. Lots are tracked separately for tax purposes.

## M

### Metadata
Key-value pairs attached to directives or postings for custom annotations.

Example: `receipt: "photo.jpg"`

## N

### Narration
The description text of a transaction explaining its purpose.

## O

### Operating Currency
A currency designated as primary for reporting. Multiple may be specified.

## P

### Pad
A directive that automatically generates a balancing transaction to satisfy a subsequent balance assertion.

### Payee
The other party in a transaction (merchant, employer, etc.).

### Position
Units of a currency held at a specific cost. The building block of inventories.

Structure: `units: Amount, cost: Option<Cost>`

### Posting
A single line within a transaction, specifying an account and amount change.

### Price
The current market value of a currency in terms of another currency. Used for valuation, not for transaction balancing.

Syntax: `@ 150.00 USD` (per-unit) or `@@ 1500.00 USD` (total)

## R

### Reduction
Removing units from an inventory. Triggers the booking algorithm to match against existing lots.

### Root Type
One of the five account categories: Assets, Liabilities, Equity, Income, Expenses.

## S

### Scale
The number of decimal places in a number. Used for inferring tolerance.

Example: `100.00` has scale 2; `100` has scale 0.

### Span
A range of bytes in source code, used for error reporting.

### Source Location
File path, line number, and column pointing to a position in source code.

## T

### Tag
A hash-prefixed identifier for categorizing transactions.

Example: `#vacation-2024`

### Tolerance
The maximum acceptable difference when checking if values are equal. Inferred from decimal precision.

### Transaction
The primary directive type representing a financial exchange between accounts. Must balance (sum of weights = 0).

## U

### Units
The quantity component of an amount, without the currency.

## W

### Weight
The balancing contribution of a posting to a transaction. Calculated as:
- Simple amount: `units`
- With price: `units × price`
- With cost: `units × cost`
- With both: `units × cost` (price ignored for balancing)

## Symbols

### `*` (Star)
Transaction flag indicating "complete" or "cleared".

### `!` (Bang)
Transaction flag indicating "pending" or "needs review".

### `#` (Hash)
Prefix for tags. Example: `#trip-2024`

### `^` (Caret)
Prefix for links. Example: `^invoice-001`

### `@` (At)
Price annotation (per-unit). Example: `@ 1.20 CAD`

### `@@` (Double At)
Total price annotation. Example: `@@ 120.00 CAD`

### `{}` (Braces)
Cost specification. Example: `{100 USD}`

### `{{}}` (Double Braces)
Total cost specification. Example: `{{1000 USD}}`

### `~` (Tilde)
Explicit tolerance in balance assertions. Example: `1000 USD ~ 0.01`
