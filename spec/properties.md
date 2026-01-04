# Property-Based Testing Specification

This document defines properties for fuzzing rustledger with `proptest` or `quickcheck`.

## Why Property Testing?

Unit tests check specific cases. Property tests verify **invariants hold for all inputs**:

```rust
// Unit test: checks ONE case
#[test]
fn test_balance() {
    let txn = make_txn(100, -100);
    assert!(txn.balances());
}

// Property test: checks MILLIONS of cases
#[proptest]
fn prop_interpolated_txns_balance(txn: ArbitraryTransaction) {
    let result = interpolate(txn);
    prop_assert!(result.balances());
}
```

## Parser Properties

### P1: Parse-Print Roundtrip

Any parsed ledger, when printed and re-parsed, produces identical AST:

```rust
#[proptest]
fn prop_parse_print_roundtrip(ledger: ArbitraryLedger) {
    let printed = print(&ledger);
    let reparsed = parse(&printed).unwrap();
    prop_assert_eq!(ledger, reparsed);
}
```

### P2: Valid Syntax Never Panics

Parser never panics on any input:

```rust
#[proptest]
fn prop_parser_no_panic(input: String) {
    let _ = parse(&input);  // May error, must not panic
}
```

### P3: Error Messages Have Locations

All parse errors include source location:

```rust
#[proptest]
fn prop_errors_have_locations(input: ArbitraryInvalidInput) {
    if let Err(e) = parse(&input) {
        prop_assert!(e.location.is_some());
    }
}
```

### P4: Comments Are Ignored

Adding comments doesn't change semantics:

```rust
#[proptest]
fn prop_comments_ignored(ledger: ArbitraryLedger, comments: Vec<String>) {
    let with_comments = insert_comments(&ledger, &comments);
    let parsed_original = parse(&print(&ledger)).unwrap();
    let parsed_with_comments = parse(&with_comments).unwrap();
    prop_assert_eq!(parsed_original.directives, parsed_with_comments.directives);
}
```

## Decimal Properties

### P5: Arithmetic Consistency

Decimal operations are consistent:

```rust
#[proptest]
fn prop_addition_commutative(a: Decimal, b: Decimal) {
    prop_assert_eq!(a + b, b + a);
}

#[proptest]
fn prop_addition_associative(a: Decimal, b: Decimal, c: Decimal) {
    prop_assert_eq!((a + b) + c, a + (b + c));
}

#[proptest]
fn prop_multiplication_distributes(a: Decimal, b: Decimal, c: Decimal) {
    prop_assert_eq!(a * (b + c), a * b + a * c);
}
```

### P6: Tolerance Symmetry

Tolerance comparisons are symmetric:

```rust
#[proptest]
fn prop_tolerance_symmetric(a: Decimal, b: Decimal, tol: PositiveDecimal) {
    prop_assert_eq!(
        near_equal(a, b, tol),
        near_equal(b, a, tol)
    );
}
```

### P7: Zero Tolerance Equals Equality

Zero tolerance means exact equality:

```rust
#[proptest]
fn prop_zero_tolerance_is_equality(a: Decimal, b: Decimal) {
    prop_assert_eq!(
        near_equal(a, b, Decimal::ZERO),
        a == b
    );
}
```

## Transaction Properties

### P8: Interpolation Produces Balanced Transactions

Successfully interpolated transactions always balance:

```rust
#[proptest]
fn prop_interpolation_balances(txn: ArbitraryTransactionWithOneMissing) {
    let result = interpolate(txn);
    prop_assert!(result.is_ok());
    prop_assert!(result.unwrap().balances());
}
```

### P9: Balanced Transactions Stay Balanced

Balanced transactions remain balanced through processing:

```rust
#[proptest]
fn prop_balanced_stays_balanced(txn: ArbitraryBalancedTransaction) {
    let processed = process(txn.clone());
    prop_assert!(processed.balances());
}
```

### P10: Weight Calculation Is Deterministic

Same posting always produces same weight:

```rust
#[proptest]
fn prop_weight_deterministic(posting: ArbitraryPosting) {
    let w1 = weight(&posting);
    let w2 = weight(&posting);
    prop_assert_eq!(w1, w2);
}
```

### P11: Transaction Weights Sum to Zero

For balanced transactions, weights sum to zero per currency:

```rust
#[proptest]
fn prop_balanced_weights_zero(txn: ArbitraryBalancedTransaction) {
    let weights = txn.postings.iter().map(weight).collect::<Vec<_>>();
    let by_currency = group_by_currency(&weights);

    for (currency, amounts) in by_currency {
        let sum: Decimal = amounts.iter().sum();
        prop_assert!(sum.abs() <= txn.tolerance(&currency));
    }
}
```

## Inventory Properties

### P12: Augmentation Increases Units

Adding to inventory increases total units:

```rust
#[proptest]
fn prop_augment_increases_units(
    inv: ArbitraryInventory,
    pos: ArbitraryPosition,
) {
    prop_assume!(pos.units.number > Decimal::ZERO);

    let before = inv.total_units(&pos.units.currency);
    let after_inv = inv.augment(pos.clone());
    let after = after_inv.total_units(&pos.units.currency);

    prop_assert_eq!(after, before + pos.units.number);
}
```

### P13: Reduction Decreases Units

Removing from inventory decreases total units:

```rust
#[proptest]
fn prop_reduce_decreases_units(
    inv: NonEmptyInventory,
    reduction: ValidReduction,  // Reduction that matches existing lots
) {
    let before = inv.total_units(&reduction.currency);
    let (after_inv, _) = inv.reduce(reduction.clone()).unwrap();
    let after = after_inv.total_units(&reduction.currency);

    prop_assert_eq!(after, before - reduction.units.abs());
}
```

### P14: Non-Negative Inventory (Non-NONE Booking)

Inventory never goes negative with STRICT/FIFO/LIFO:

```rust
#[proptest]
fn prop_inventory_non_negative(
    operations: Vec<ArbitraryOperation>,
    method: NonNoneBookingMethod,
) {
    let mut inv = Inventory::new();

    for op in operations {
        match op {
            Op::Augment(pos) => { inv.augment(pos); }
            Op::Reduce(spec) => {
                // May fail, that's OK
                let _ = inv.reduce(spec, method);
            }
        }
    }

    for pos in inv.positions() {
        prop_assert!(pos.units.number >= Decimal::ZERO);
    }
}
```

### P15: FIFO Takes Oldest First

FIFO reduction always takes from oldest matching lot:

```rust
#[proptest]
fn prop_fifo_takes_oldest(inv: InventoryWithMultipleLots) {
    let oldest_date = inv.oldest_lot_date();
    let (_, matched) = inv.reduce_fifo(any_matching_spec()).unwrap();

    prop_assert_eq!(matched.first().unwrap().date, oldest_date);
}
```

### P16: LIFO Takes Newest First

LIFO reduction always takes from newest matching lot:

```rust
#[proptest]
fn prop_lifo_takes_newest(inv: InventoryWithMultipleLots) {
    let newest_date = inv.newest_lot_date();
    let (_, matched) = inv.reduce_lifo(any_matching_spec()).unwrap();

    prop_assert_eq!(matched.first().unwrap().date, newest_date);
}
```

## Booking Properties

### P17: Cost Basis Preserved

Total cost basis is preserved through booking:

```rust
#[proptest]
fn prop_cost_basis_preserved(
    inv: ArbitraryInventory,
    reduction: ValidReduction,
    method: BookingMethod,
) {
    let before_cost = inv.total_cost_basis();
    let (after_inv, matched) = inv.reduce(reduction, method).unwrap();
    let matched_cost: Decimal = matched.iter().map(|m| m.cost_basis()).sum();

    prop_assert_eq!(before_cost, after_inv.total_cost_basis() + matched_cost);
}
```

### P18: STRICT Rejects Ambiguity

STRICT booking fails when multiple lots match:

```rust
#[proptest]
fn prop_strict_rejects_ambiguous(inv: InventoryWithAmbiguousLots) {
    let result = inv.reduce_strict(ambiguous_spec());
    prop_assert!(matches!(result, Err(BookingError::AmbiguousMatch)));
}
```

## Validation Properties

### P19: Account Lifecycle Consistency

Accounts cannot be used before open or after close:

```rust
#[proptest]
fn prop_account_lifecycle(ledger: ArbitraryLedger) {
    let errors = validate(&ledger);

    for txn in &ledger.transactions {
        for posting in &txn.postings {
            let open_date = ledger.open_date(&posting.account);
            let close_date = ledger.close_date(&posting.account);

            if let Some(open) = open_date {
                if txn.date < open {
                    prop_assert!(errors.iter().any(|e|
                        matches!(e.code, ErrorCode::AccountNotOpened)));
                }
            }
            if let Some(close) = close_date {
                if txn.date > close {
                    prop_assert!(errors.iter().any(|e|
                        matches!(e.code, ErrorCode::AccountClosed)));
                }
            }
        }
    }
}
```

### P20: Balance Assertions Checked

Failed balance assertions produce errors:

```rust
#[proptest]
fn prop_balance_assertions_checked(ledger: ArbitraryLedgerWithAssertions) {
    let (_, errors) = process(&ledger);

    for assertion in &ledger.balance_assertions {
        let actual = compute_balance(&ledger, &assertion.account, assertion.date);
        if !near_equal(actual, assertion.amount, tolerance) {
            prop_assert!(errors.iter().any(|e|
                matches!(e.code, ErrorCode::BalanceAssertionFailed)));
        }
    }
}
```

## Include Properties

### P21: Include Expansion Is Deterministic

Including files produces deterministic result:

```rust
#[proptest]
fn prop_include_deterministic(files: ArbitraryFileSet) {
    let result1 = load_with_includes(&files);
    let result2 = load_with_includes(&files);
    prop_assert_eq!(result1, result2);
}
```

### P22: Cycle Detection

Include cycles are detected:

```rust
#[proptest]
fn prop_include_cycle_detected(files: FilesWithCycle) {
    let result = load_with_includes(&files);
    prop_assert!(matches!(result, Err(LoadError::IncludeCycle(_))));
}
```

## Arbitrary Generators

### Generating Valid Transactions

```rust
fn arb_balanced_transaction() -> impl Strategy<Value = Transaction> {
    (arb_date(), arb_narration(), arb_postings())
        .prop_map(|(date, narration, postings)| {
            let mut txn = Transaction { date, narration, postings, .. };
            balance_transaction(&mut txn);  // Adjust last posting
            txn
        })
}
```

### Generating Inventories

```rust
fn arb_inventory() -> impl Strategy<Value = Inventory> {
    prop::collection::vec(arb_position(), 0..10)
        .prop_map(|positions| Inventory { positions })
}

fn arb_position() -> impl Strategy<Value = Position> {
    (arb_positive_amount(), prop::option::of(arb_cost()))
        .prop_map(|(units, cost)| Position { units, cost })
}
```

### Shrinking

Property test frameworks automatically shrink failing cases to minimal examples:

```rust
// If this fails with a 50-posting transaction,
// proptest will find minimal failing case (maybe 2-3 postings)
#[proptest]
fn prop_something(txn: Transaction) {
    // ...
}
```

## Running Property Tests

```bash
# Run with default iterations (256)
cargo test --features proptest

# Run with more iterations
PROPTEST_CASES=10000 cargo test --features proptest

# Run with seed for reproducibility
PROPTEST_SEED=12345 cargo test --features proptest
```

## Regression Tests

Failed property tests become regression tests:

```rust
// Discovered by proptest on 2024-01-15
#[test]
fn regression_interpolation_with_cost() {
    let txn = Transaction {
        postings: vec![
            Posting { units: Some(amount!(10 AAPL)), cost: Some(cost!(150 USD)), .. },
            Posting { units: None, .. },  // Should interpolate to -1500 USD
        ],
        ..
    };
    assert!(interpolate(txn).is_ok());
}
```
