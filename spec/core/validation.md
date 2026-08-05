# Beancount Validation Rules Catalog

This document catalogs all validation errors and warnings with their trigger conditions.

## Error Categories

| Category | Description |
|----------|-------------|
| **PARSE** | Syntax errors during parsing |
| **ACCOUNT** | Account lifecycle violations |
| **BALANCE** | Balance assertion failures |
| **BOOKING** | Inventory/lot matching errors |
| **TXN** | Transaction structure errors |
| **CURRENCY** | Currency/commodity violations |
| **META** | Metadata and option errors |

## Account Errors

### ACCOUNT_NOT_OPENED

**Code:** `E1001`

**Condition:** Posting references an account that has no prior `open` directive.

**Message:** `Account "{account}" is not open`

**Severity:** Error

```beancount
; No open directive for Assets:Checking
2024-01-15 * "Deposit"
  Assets:Checking   100 USD   ; ERROR: Account not opened
  Income:Salary
```

### ACCOUNT_ALREADY_OPEN

**Code:** `E1002`

**Condition:** `open` directive for an account that is already open.

**Message:** `Account "{account}" is already open (opened on {date})`

**Severity:** Error

```beancount
2020-01-01 open Assets:Checking
2021-01-01 open Assets:Checking  ; ERROR: Already open
```

### ACCOUNT_ALREADY_CLOSED

**Code:** `E1003`

**Condition:** Posting references an account after its `close` directive.

**Message:** `Account "{account}" was closed on {date}`

**Severity:** Error

```beancount
2020-01-01 open Assets:Checking
2023-12-31 close Assets:Checking
2024-01-15 * "Late deposit"
  Assets:Checking   100 USD   ; ERROR: Account closed
  Income:Salary
```

### ACCOUNT_CLOSE_NOT_EMPTY

**Code:** `E1004`

**Condition:** `close` directive when account has non-zero balance.

**Message:** `Cannot close account "{account}" with non-zero balance: {balance}`

**Severity:** Warning (configurable to Error)

### ACCOUNT_INVALID_NAME

**Code:** `E1005`

**Condition:** Account name doesn't match expected pattern.

**Message:** `Invalid account name "{account}": {reason}`

**Reasons:**

- Does not start with valid root (Assets, Liabilities, Equity, Income, Expenses)
- Contains invalid characters
- Component doesn't start with capital letter

**Severity:** Error

## Balance Errors

### BALANCE_ASSERTION_FAILED

**Code:** `E2001`

**Condition:** Account balance doesn't match assertion.

**Message:** `Balance assertion failed for {account}: expected {expected} {currency}, got {actual} (difference: {diff})`

**Severity:** Error

```beancount
2024-01-01 open Assets:Checking
2024-01-15 * "Deposit"
  Assets:Checking   100 USD
  Income:Salary

2024-01-16 balance Assets:Checking  200 USD  ; ERROR: Actually 100 USD
```

### BALANCE_TOLERANCE_EXCEEDED

**Code:** `E2002`

**Condition:** Balance is within default tolerance but exceeds explicit tolerance.

**Message:** `Balance {actual} exceeds tolerance {tolerance} for assertion {expected}`

**Severity:** Error

### PAD_WITHOUT_BALANCE

**Code:** `E2003`

**Condition:** `pad` directive without subsequent `balance` for same account/currency.

**Message:** `Pad directive for {account} has no subsequent balance assertion for {currency}`

**Severity:** Error

### MULTIPLE_PAD_FOR_BALANCE

**Code:** `E2004`

**Condition:** Multiple `pad` directives between balance assertions for same account/currency.

**Message:** `Multiple pad directives for {account} {currency} before balance assertion`

**Severity:** Error

## Transaction Errors

### TXN_NOT_BALANCED

**Code:** `E3001`

**Condition:** Transaction weights don't sum to zero (per currency).

**Message:** `Transaction does not balance: residual {amount} {currency}`

**Severity:** Error

```beancount
2024-01-15 * "Unbalanced"
  Assets:Checking   100 USD
  Expenses:Food      50 USD  ; ERROR: Missing -150 USD
```

### TXN_MULTIPLE_MISSING_AMOUNTS

**Code:** `E3002`

**Condition:** More than one posting has missing amount for same currency.

**Message:** `Cannot interpolate: multiple postings missing amounts for {currency}`

**Severity:** Error

```beancount
2024-01-15 * "Ambiguous"
  Assets:Checking   100 USD
  Expenses:Food           ; Missing
  Expenses:Drinks         ; ERROR: Also missing same currency
```

### TXN_NO_POSTINGS

**Code:** `E3003`

**Condition:** Transaction has zero postings.

**Message:** `Transaction must have at least one posting`

**Severity:** Error

### TXN_SINGLE_POSTING

**Code:** `E3004`

**Condition:** Transaction has exactly one posting (cannot balance).

**Message:** `Transaction has only one posting`

**Severity:** Warning

## Booking Errors

### BOOKING_NO_MATCHING_LOT

**Code:** `E4001`

**Condition:** Reduction specifies cost that doesn't match any lot.

**Message:** `No lot matching {cost_spec} for {currency} in {account}`

**Severity:** Error

```beancount
2024-01-01 * "Buy"
  Assets:Stock   10 AAPL {150 USD}
  Assets:Cash

2024-06-01 * "Sell"
  Assets:Stock  -5 AAPL {160 USD}  ; ERROR: No lot at 160 USD
  Assets:Cash
```

### BOOKING_INSUFFICIENT_UNITS

**Code:** `E4002`

**Condition:** Reduction requests more units than available in matching lots.

**Message:** `Insufficient units: requested {requested}, available {available}`

**Severity:** Error

### BOOKING_AMBIGUOUS_MATCH

**Code:** `E4003`

**Condition:** Multiple lots match and booking method is STRICT.

**Message:** `Ambiguous lot match for {currency}: {count} lots match. Specify cost, date, or label to disambiguate, or use FIFO/LIFO booking.`

**Severity:** Error

```beancount
2024-01-01 open Assets:Stock "STRICT"

2024-01-01 * "Buy lot 1"
  Assets:Stock   10 AAPL {150 USD}
  Assets:Cash

2024-02-01 * "Buy lot 2"
  Assets:Stock   10 AAPL {160 USD}
  Assets:Cash

2024-06-01 * "Sell"
  Assets:Stock  -5 AAPL {}  ; ERROR: Which lot? 150 or 160?
  Assets:Cash
```

### ARITHMETIC_OVERFLOW

**Code:** `E4004`

**Condition:** An amount, or a running total derived from one, exceeds the range
of rledger's decimal type (a 96-bit type, roughly ±7.9×10²⁸ with ~28 significant
digits).

**Message:** `{currency} amount exceeds the representable range (±7.9e28); split the transaction, or denominate it in larger units (thousands, millions) so the number is smaller`

**Severity:** Error

rledger reports this rather than rounding or clamping the value. Clamping would
be unsound in both directions: a clamped figure is printed as if it were exact,
and because `Decimal::MIN == -Decimal::MAX`, a clamped debit and a clamped credit
cancel to a residual of exactly zero — an arbitrarily unbalanced transaction
would certify as balanced.

Note that a *product* can leave the range while both of its operands are far
inside it, since a product needs roughly the sum of its operands' digits. A
transaction can therefore parse cleanly and still overflow during booking.

Python beancount does not have this limit: its `decimal` context keeps 28
significant digits but has effectively unbounded magnitude. Where rledger can
reach the same answer it does — a transaction whose postings are all explicit is
checked in arbitrary precision, so its imbalance is reported exactly (E3001)
rather than as an overflow. E4004 is emitted where a representable result is
genuinely required: an interpolated posting amount, an inventory total, or a
cost basis.

```beancount
2024-01-01 open Assets:Stock
2024-01-01 open Assets:Cash

2024-02-01 * "cost basis needs 33 digits"
  Assets:Stock  10000000000000000 HOOL {10000000000000.00 USD}
  Assets:Cash   ; ERROR: the interpolated USD amount cannot be represented
```

### BOOKING_NEGATIVE_COST

**Code:** `E4005`

**Condition:** A posting's cost amount is negative (a cost must be non-negative).

**Message:** `Cost is negative: {label} cost ({value} {cost_currency}) for {units} in posting to {account}`

**Severity:** Error

## Currency Errors

### CURRENCY_NOT_DECLARED

**Code:** `E5001`

**Condition:** Currency used but not declared with `commodity` directive (when strict mode enabled).

**Message:** `Currency "{currency}" is not declared`

**Severity:** Warning

### CURRENCY_CONSTRAINT_VIOLATION

**Code:** `E5002`

**Condition:** Posting uses currency not in account's allowed list.

**Message:** `Account {account} does not allow currency {currency} (allowed: {allowed})`

**Severity:** Error

```beancount
2024-01-01 open Assets:USDOnly USD

2024-01-15 * "Wrong currency"
  Assets:USDOnly   100 EUR  ; ERROR: Only USD allowed
  Income:Salary
```

### COMMODITY_INVALID_PRECISION_META

**Code:** `E5003`

**Condition:** A `commodity` directive carries a `precision` metadata value that does not parse as a non-negative integer. The declaration is ignored (display precision falls back to `option "display_precision"`, otherwise to inference).

**Message:** `invalid precision metadata on commodity {currency}: {reason}; this declaration is ignored — display precision falls back to option "display_precision" if set, otherwise to inference`

**Severity:** Warning

## Budget Errors

### MALFORMED_BUDGET

**Code:** `E11001`

**Condition:** A `custom "budget"` directive that rledger is confident IS a budget carries content it cannot use.

Confident is ONE rule, implemented as `rustledger_budget::addressed_to_us`: the interval slot holds a real interval keyword (`daily`, `weekly`, `monthly`, `quarterly`, `yearly`, or the bare noun of each), OR the first value names an account and the payload carries an amount in at most three values.

The amount need not be in the third slot: `custom "budget" Expenses:Food 400.00 USD` is a budget with the interval word forgotten, and requiring the slot left it reported by nobody while `report budget` printed "No budgets declared" over a ledger that plainly declares one. What keeps another tool's payload out is the ARITY — Fava reads three values and tolerates a trailing note, so anything longer is a schema of its own (`custom "budget" Assets:Bank:Checking 1000.00 USD TRUE "monthly"` has four and is left alone). Either half is strong evidence; neither occurs by coincidence in a payload written for something else.

A `custom "budget"` meeting neither test is not reported anywhere — not by `check`, not by the LSP, and not by `report budget`. `custom` is beancount's open extension point and the name is not rledger's alone: beancount's own documented example is `custom "budget" "weekly < 1000.00 USD" 2016-02-28 TRUE 43.03 USD 23`, and an envelope-budgeting tool might write `custom "budget" "envelope-groceries" "rollover" 250.00 USD`. Python accepts both silently, and so does rledger.

A trailing quoted NOTE is not an error — Fava reads only the first three values and real ledgers carry comments there. A trailing FIGURE is reported, but the budget still applies at the first figure, which is what Fava reads.

**Message:** `budget directive has an invalid interval "{interval}" (use daily, weekly, monthly, quarterly or yearly)`, `budget directive names "{value}", which is not a valid account name`, `budget directive carries a second figure; only the first is read, so write one budget per directive`, or `budget directive not understood; expected: custom "budget" <Account> "<interval>" <amount> <CCY>`

**Severity:** Warning — `custom` is beancount's open extension point, so another tool may legitimately use the name `budget` with a different payload. Rledger reports what it cannot use without failing the ledger.

## Option Errors

### UNKNOWN_OPTION

**Code:** `E7001`

**Condition:** Unrecognized option name.

**Message:** `Unknown option "{name}"`

**Severity:** Warning

### INVALID_OPTION_VALUE

**Code:** `E7002`

**Condition:** Option value is invalid for option type.

**Message:** `Invalid value "{value}" for option "{name}": {reason}`

**Severity:** Error

### DUPLICATE_OPTION

**Code:** `E7003`

**Condition:** Non-repeatable option specified multiple times.

**Message:** `Option "{name}" can only be specified once`

**Severity:** Warning (uses last value)

## Document Errors

### DOCUMENT_FILE_NOT_FOUND

**Code:** `E8001`

**Condition:** Document directive references non-existent file.

**Message:** `Document file not found: {path}`

**Severity:** Warning (configurable)

## Include Errors

### INCLUDE_FILE_NOT_FOUND

**Code:** `E9001`

**Condition:** Included file doesn't exist.

**Message:** `Include file not found: {path}`

**Severity:** Error

### INCLUDE_CYCLE_DETECTED

**Code:** `E9002`

**Condition:** Circular include dependency.

**Message:** `Include cycle detected: {path} -> {chain}`

**Severity:** Error

## Date Errors

### DATE_IN_FUTURE

**Code:** `E10002`

**Condition:** Directive date is in the future.

**Message:** `Directive date {date} is in the future`

**Severity:** Warning

## Validation Phases

Validation occurs in multiple phases:

### Phase 1: Syntax (during parsing)

- PARSE errors
- ACCOUNT_INVALID_NAME

### Phase 2: Structure (after parsing, before processing)

- TXN_NO_POSTINGS
- INCLUDE_FILE_NOT_FOUND
- INCLUDE_CYCLE_DETECTED

### Phase 3: Accounts (chronological scan)

- ACCOUNT_NOT_OPENED
- ACCOUNT_ALREADY_OPEN
- ACCOUNT_ALREADY_CLOSED

### Phase 4: Interpolation

- TXN_MULTIPLE_MISSING_AMOUNTS

### Phase 5: Booking

- All BOOKING errors

### Phase 6: Balancing

- TXN_NOT_BALANCED

### Phase 7: Assertions

- BALANCE_ASSERTION_FAILED
- PAD_WITHOUT_BALANCE

### Phase 8: Optional Checks

- DOCUMENT_FILE_NOT_FOUND
- CURRENCY_NOT_DECLARED
- DATE_IN_FUTURE

## Error Structure (Rust)

```rust
#[derive(Debug)]
pub struct ValidationError {
    pub code: ErrorCode,
    pub message: String,
    pub severity: Severity,
    pub location: Option<SourceLocation>,
    pub context: Option<String>,  // Additional context
}

#[derive(Debug)]
pub struct SourceLocation {
    pub file: PathBuf,
    pub line: u32,
    pub column: Option<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,    // Ledger is invalid
    Warning,  // Suspicious but valid
    Info,     // Informational
}
```
