______________________________________________________________________

## title: Error Codes Reference description: Validation errors and how to fix them

# Error Codes Reference

This page documents validation errors that `rledger check` can report.

## Error Format

Errors are displayed as:

```
file.beancount:42: error[E1001]: Account not opened
```

Format: `file:line: error[code]: message`

## Error Code Categories

| Range | Category |
|-------|----------|
| E1xxx | Account errors |
| E2xxx | Balance errors |
| E3xxx | Transaction errors |
| E4xxx | Booking/lot errors |
| E5xxx | Currency errors |
| E6xxx | Metadata errors |
| E7xxx | Option errors |
| E8xxx | Document errors |
| E10xxx | Date warnings/info |

## Account Errors (E1xxx)

### E1001: Account Not Opened

**Cause**: Transaction uses an account without an `open` directive.

**Example**:

```beancount
; No 'open' for Expenses:Food
2024-01-15 * "Coffee"
  Expenses:Food   5.00 USD
  Assets:Cash    -5.00 USD
```

**Fix**: Add an open directive:

```beancount
2020-01-01 open Expenses:Food
2020-01-01 open Assets:Cash  USD
```

Or use `rledger doctor missing-open` to generate them.

### E1002: Account Already Open

**Cause**: Duplicate `open` directive for same account.

**Fix**: Remove the duplicate open directive.

### E1003: Account Used After Close

**Cause**: Transaction on an account after its `close` date.

**Example**:

```beancount
2024-01-01 close Assets:OldBank

2024-02-15 * "Late transaction"
  Assets:OldBank   100.00 USD   ; Account is closed
```

**Fix**: Use correct account or adjust close date.

### E1004: Account Close With Non-Zero Balance (Warning)

**Cause**: Closing an account that still has a balance.

**Fix**: Zero out the account balance before closing.

### E1005: Invalid Account Name

**Cause**: Account name doesn't match required format.

**Example**:

```beancount
2024-01-15 * "Coffee"
  expenses:food   5.00 USD    ; Lowercase not allowed
```

**Fix**: Use Title:Case:Accounts starting with Assets, Liabilities, Equity, Income, or Expenses.

## Balance Errors (E2xxx)

### E2001: Balance Assertion Failed

**Cause**: Account balance doesn't match assertion.

**Example**:

```beancount
2024-01-15 balance Assets:Checking  1000.00 USD
; But actual balance is 950.00 USD
```

**Fix**:

1. Check for missing transactions
1. Verify the expected amount
1. Use `rledger doctor context` to see surrounding transactions

### E2002: Balance Exceeds Tolerance

**Cause**: Balance is off by more than the allowed tolerance.

**Fix**: Adjust the balance assertion or find the discrepancy.

### E2003: Pad Without Balance Assertion

**Cause**: A `pad` directive has no subsequent `balance` assertion.

**Fix**: Add a balance assertion after the pad.

### E2004: Multiple Pads for Same Balance

**Cause**: Multiple pad directives for the same balance assertion.

**Fix**: Remove duplicate pad directives.

## Transaction Errors (E3xxx)

### E3001: Transaction Does Not Balance

**Cause**: Postings don't sum to zero.

**Example**:

```beancount
2024-01-15 * "Coffee"
  Expenses:Food    5.00 USD
  Assets:Cash     -4.00 USD   ; Doesn't balance
```

**Fix**: Ensure postings sum to zero:

```beancount
2024-01-15 * "Coffee"
  Expenses:Food    5.00 USD
  Assets:Cash     -5.00 USD
```

### E3002: Multiple Missing Amounts

**Cause**: More than one posting is missing an amount for the same currency.

**Fix**: Only one posting per currency can have an inferred amount.

### E3003: Transaction Has No Postings

**Cause**: Transaction has no posting lines.

**Fix**: Add at least two postings to the transaction.

### E3004: Transaction Has Single Posting (Warning)

**Cause**: Transaction has only one posting line.

**Fix**: Add a second posting to complete the transaction.

## Booking Errors (E4xxx)

### E4001: No Matching Lot

**Cause**: Can't find a lot to reduce when selling/removing inventory.

**Example**:

```beancount
2024-01-15 * "Sell AAPL"
  Assets:Brokerage  -10 AAPL {150.00 USD}  ; No lot at this cost
```

**Fix**: Check cost basis matches existing lot, or use `{}` for automatic matching.

### E4002: Insufficient Units

**Cause**: Trying to reduce more units than available in the lot.

**Fix**: Check the quantity being sold matches available holdings.

### E4003: Ambiguous Lot Match

**Cause**: In STRICT booking mode, multiple lots could match.

**Fix**: Specify the exact lot using cost basis `{cost}` or date `{date}`.

### E4005: Negative Cost

**Cause**: A cost specification resolves to a negative amount.

**Fix**: Ensure cost values are non-negative (e.g., `{10 USD}` not `{-10 USD}`). Zero cost is allowed.

## Currency Errors (E5xxx)

### E5001: Currency Not Declared

**Cause**: Using a currency without a `commodity` directive (when strict mode enabled).

**Fix**: Declare the currency:

```beancount
2020-01-01 commodity USD
```

### E5002: Currency Not Allowed in Account

**Cause**: Posting uses currency not allowed for account.

**Example**:

```beancount
2020-01-01 open Assets:Bank  USD  ; Only USD allowed

2024-01-15 * "Deposit"
  Assets:Bank    100.00 EUR       ; EUR not allowed
```

**Fix**: Use allowed currency or update account declaration.

### E5003: Invalid Precision Metadata (Warning)

**Cause**: A `commodity` directive has invalid `precision` metadata.

**Fix**: Correct the `precision` metadata value on the commodity directive.

## Option Errors (E7xxx)

### E7001: Unknown Option

**Cause**: Unrecognized option name.

**Fix**: Check option spelling. Use `rledger doctor list-options` to see valid options.

### E7002: Invalid Option Value

**Cause**: Option value is invalid.

**Fix**: Check the expected format for the option.

### E7003: Duplicate Option

**Cause**: Non-repeatable option specified multiple times.

**Fix**: Remove duplicate option directives.

## Document Errors (E8xxx)

### E8001: Document Not Found

**Cause**: Document directive references missing file.

**Fix**: Ensure file exists at specified path.

## Date Warnings (E10xxx)

### E10001: Date Out of Order (Info)

**Cause**: Entries are not in chronological order.

**Note**: This is informational only and does not prevent validation.

### E10002: Entry Dated in Future (Warning)

**Cause**: Entry has a date in the future.

**Note**: This is a warning that may indicate a typo.

## Using Error Information

### Find Context

```bash
# See what's around an error
rledger doctor context ledger.beancount 42
```

### Check Specific Account

```bash
# View account history
rledger query ledger.beancount \
  "SELECT date, narration, position WHERE account = 'Assets:Bank' ORDER BY date"
```

### Generate Missing Opens

```bash
# Auto-generate open directives
rledger doctor missing-open ledger.beancount
```

## See Also

- [check command](../commands/check.md) - Running validation
- [doctor command](../commands/doctor.md) - Debugging tools
- [Plugins](plugins.md) - Plugin-specific errors
