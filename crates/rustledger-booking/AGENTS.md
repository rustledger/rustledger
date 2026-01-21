# Booking Crate Guidelines

This document provides context for AI assistants working on the rustledger-booking crate.

## Overview

This crate handles transaction interpolation, balancing, and padding. It implements the core double-entry bookkeeping logic.

## Architecture

| File | Purpose |
|------|---------|
| `lib.rs` | Public API, tolerance/residual calculations |
| `interpolate.rs` | Fill in missing amounts to balance transactions |
| `pad.rs` | Expand pad directives into balance adjustments |

## Core Concepts

### Interpolation

When a transaction has exactly one posting without an amount per currency, that amount is calculated to balance the transaction:

```
2024-01-15 * "Groceries"
  Expenses:Food  50.00 USD
  Assets:Cash              ; <- Inferred as -50.00 USD
```

### Tolerance

Decimal precision varies by currency. Tolerance is the maximum acceptable rounding error:
- `0.005` for 2-decimal currencies (USD, EUR)
- `0.00005` for 4-decimal currencies (BTC)

### Residual

The imbalance after summing all postings. Must be within tolerance for a valid transaction.

## Critical Rules

### Correctness is Paramount

Booking affects financial calculations. Double-check:
- Sign handling (positive/negative amounts)
- Currency isolation (never mix different currencies)
- Tolerance precision (use `Decimal`, not `f64`)

### Match Python Beancount Behavior

The booking logic MUST match Python beancount exactly. When implementing:
1. Read the Python source in `beancount/parser/booking_full.py`
2. Create test cases comparing both implementations
3. Document any intentional differences

### No Floating Point

Always use `rust_decimal::Decimal`:
```rust
// Good
let amount = Decimal::new(500, 2); // 5.00

// Bad - floating point errors
let amount = 5.00_f64;
```

## Testing

### Required Tests for Booking Changes

1. **Simple transactions**: One currency, two postings
2. **Multi-currency**: Each currency balances independently
3. **Cost basis**: Stock purchases with cost specs
4. **Price annotations**: Currency conversions
5. **Edge cases**: Zero amounts, maximum precision

### Test Commands

```bash
# Unit tests
cargo test -p rustledger-booking

# Run against Python beancount test files
./scripts/compare-with-beancount.sh
```

## Common Tasks

### Adding a New Booking Method

1. Add variant to booking method enum
2. Implement interpolation logic in `interpolate.rs`
3. Add comprehensive test cases
4. Compare with Python beancount output

### Debugging Balance Errors

1. Print residuals: `dbg!(calculate_residual(&transaction))`
2. Check tolerance: `dbg!(calculate_tolerance(&amounts))`
3. Verify signs: positive = debit, negative = credit
