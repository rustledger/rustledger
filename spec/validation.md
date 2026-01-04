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

### BOOKING_NEGATIVE_UNITS

**Code:** `E4004`

**Condition:** Reduction would create negative position (except with NONE booking).

**Message:** `Reduction would result in negative inventory for {currency}`

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

## Metadata Errors

### DUPLICATE_METADATA_KEY

**Code:** `E6001`

**Condition:** Same metadata key specified multiple times on one directive.

**Message:** `Duplicate metadata key "{key}"`

**Severity:** Warning

### INVALID_METADATA_VALUE

**Code:** `E6002`

**Condition:** Metadata value doesn't match expected type.

**Message:** `Invalid value for metadata key "{key}": expected {type}`

**Severity:** Warning

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

### DATE_OUT_OF_ORDER

**Code:** `E10001`

**Condition:** Directive date is before previous directive (informational only).

**Message:** `Directive date {date} is before previous directive {prev_date}`

**Severity:** Info (directives are auto-sorted)

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
