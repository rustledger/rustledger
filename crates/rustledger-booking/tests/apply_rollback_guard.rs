//! `apply`'s rollback guard must predict every way a posting can fail.
//!
//! The guard is a plain `assert!`, not a `debug_assert!`, so an unsound
//! prediction is a process abort in release rather than a reported error.
//! #2345 was exactly that: `add_headroom_for` bounded the per-currency NET and
//! the cost-less merge slot, but #2118 had made cost-bearing lots merge too, so
//! two opposite lots netted to zero while the lot the next add joined sat at
//! `Decimal::MAX`.
//!
//! The crash input is kept at
//! `rustledger-booking/fuzz/regressions/fuzz_booking/headroom-net-hides-ceiling-lot-2345`,
//! but nothing in `cargo test` replays the fuzz corpus — so the panic path
//! needs a test of its own here, or it is only covered while the fuzz job runs.

use rustledger_booking::BookingEngine;
use rustledger_core::{Amount, BookingMethod, CostNumber, CostSpec, Decimal, Posting, Transaction};

/// A cost-bearing buy. The cost spec carries no explicit date, so the lot's
/// acquisition date is the transaction's — which is what decides whether two
/// buys MERGE into one lot or stay separate.
fn buy(day: u32, units: Decimal, per_unit: Decimal) -> Transaction {
    let cost = CostSpec::empty()
        .with_number(CostNumber::PerUnit { value: per_unit })
        .with_currency("USD");
    Transaction::new(
        rustledger_core::naive_date(2024, 1, day).expect("valid date"),
        "ceiling lot",
    )
    .with_synthesized_posting(
        Posting::new("Assets:Stock", Amount::new(units, "CORP")).with_cost(cost),
    )
    .with_synthesized_posting(Posting::new(
        "Assets:Cash",
        Amount::new(-(units * per_unit), "USD"),
    ))
}

#[test]
fn an_overflow_into_a_ceiling_lot_is_reported_and_rolled_back() {
    // NONE never matches a lot, so every posting accumulates as an
    // augmentation and opposite-signed cost-bearing lots can coexist. That is
    // the state in which the per-currency net stops bounding the lots.
    let mut engine = BookingEngine::with_method(BookingMethod::None);

    engine
        .apply(&buy(1, Decimal::MAX, Decimal::new(1, 2)))
        .expect("a single MAX lot fits");
    engine
        .apply(&buy(2, -Decimal::MAX, Decimal::new(2, 2)))
        .expect("a second, opposite lot fits - the net is now zero");

    let before = engine
        .inventory(&"Assets:Stock".into())
        .cloned()
        .expect("the account holds two lots");

    // Day 1 again, and the same cost: this MERGES into the lot at MAX rather
    // than opening a third one. Merging needs agreement on cost, currency,
    // date and label, so the date is what makes this the reproducer.
    let err = engine
        .apply(&buy(1, Decimal::ONE, Decimal::new(1, 2)))
        .expect_err("merging one more unit into the lot at MAX must be reported");

    // On the typed fields, not a substring of the message: a message match is
    // satisfied by any error that happens to mention the account.
    match &err {
        rustledger_booking::BookingError::Inventory(inner) => {
            assert!(
                matches!(inner.error, rustledger_core::BookingError::Overflow(_)),
                "expected an Overflow, got {:?}",
                inner.error
            );
            assert_eq!(
                inner.account.as_str(),
                "Assets:Stock",
                "the error must name the account whose lot overflowed"
            );
        }
        other => panic!("expected an inventory error, got {other:?}"),
    }

    // The substance of the guard: a failed transaction leaves NOTHING applied.
    // Without the prediction, `apply` skips its snapshot, and the assertion it
    // then trips exists precisely because there is nothing left to restore
    // from.
    let after = engine
        .inventory(&"Assets:Stock".into())
        .cloned()
        .expect("the account still exists");
    assert_eq!(
        before.units("CORP"),
        after.units("CORP"),
        "a transaction that failed to apply must not move the running balance"
    );
}
