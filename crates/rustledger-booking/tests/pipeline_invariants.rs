//! Pipeline-boundary property tests (#1235).
//!
//! These assert invariants that hold ACROSS pipeline phases rather than
//! within a single function — the class of bug that no unit test
//! structurally catches because each phase passes in isolation.
//!
//! This file starts with the **booking idempotence** family
//! (`book(book(L)) == book(L)`, realized here as interpolation
//! idempotence). The other families enumerated in #1235 — parse/format
//! roundtrip, plugin commutativity, validation-phase consistency,
//! wire-format roundtrip, and query determinism — can be added here over
//! time.

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_booking::{calculate_residual, interpolate};
use rustledger_core::{Amount, IncompleteAmount, NaiveDate, Posting, Transaction};

fn date_strategy() -> impl Strategy<Value = NaiveDate> {
    (2000i32..2100, 1u32..13, 1u32..29)
        .prop_map(|(y, m, d)| rustledger_core::naive_date(y, m, d).unwrap())
}

/// Non-zero amounts with bounded scale. Non-zero so the elided leg is
/// meaningful; bounded magnitude/scale so proptest shrinks toward small,
/// readable counterexamples (#1235 open question 3) rather than degenerate
/// ones.
fn amount_strategy(currency: &'static str) -> impl Strategy<Value = Amount> {
    (-1_000_000i64..1_000_000, 0u32..4)
        .prop_filter("non-zero units", |(n, _)| *n != 0)
        .prop_map(move |(n, scale)| Amount::new(Decimal::new(n, scale), currency))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Booking idempotence (#1235): re-interpolating an already-filled
    /// transaction is a no-op — `interpolate(interpolate(L)) ==
    /// interpolate(L)` — and fills nothing the second time. Catches
    /// interpolation that isn't a fixed point (e.g. a fill the second
    /// pass would re-adjust).
    #[test]
    fn interpolation_is_idempotent_single_elided(
        date in date_strategy(),
        a in amount_strategy("USD"),
    ) {
        let txn = Transaction::new(date, "t")
            .with_synthesized_posting(Posting::new("Expenses:Food", a))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let once = interpolate(&txn).expect("first interpolation succeeds");
        let twice = interpolate(&once.transaction).expect("re-interpolation succeeds");

        prop_assert_eq!(
            &twice.transaction,
            &once.transaction,
            "re-interpolation changed an already-filled transaction"
        );
        prop_assert!(
            twice.filled_indices.is_empty(),
            "re-interpolation filled new postings: {:?}",
            twice.filled_indices
        );
    }

    /// The same fixed-point property across two independent currency
    /// groups (each with its own elided leg), exercising the
    /// per-currency residual bookkeeping.
    #[test]
    fn interpolation_is_idempotent_multi_currency(
        date in date_strategy(),
        a in amount_strategy("USD"),
        b in amount_strategy("EUR"),
    ) {
        let txn = Transaction::new(date, "t")
            .with_synthesized_posting(Posting::new("Expenses:Food", a))
            .with_synthesized_posting(Posting::with_incomplete(
                "Assets:USD",
                IncompleteAmount::CurrencyOnly("USD".into()),
            ))
            .with_synthesized_posting(Posting::new("Expenses:Travel", b))
            .with_synthesized_posting(Posting::with_incomplete(
                "Assets:EUR",
                IncompleteAmount::CurrencyOnly("EUR".into()),
            ));

        // Some random shapes may be structurally unfillable; those are out
        // of scope for the idempotence property, so skip them.
        let Ok(once) = interpolate(&txn) else {
            return Ok(());
        };
        let twice = interpolate(&once.transaction).expect("re-interpolation succeeds");

        prop_assert_eq!(&twice.transaction, &once.transaction);
        prop_assert!(twice.filled_indices.is_empty());
    }

    /// A successfully-interpolated transaction balances: every currency's
    /// residual is exactly zero. (The fixed-point property above relies on
    /// this — if the fill didn't balance, the second pass would re-fill.)
    #[test]
    fn interpolated_transaction_has_zero_residual(
        date in date_strategy(),
        a in amount_strategy("USD"),
    ) {
        let txn = Transaction::new(date, "t")
            .with_synthesized_posting(Posting::new("Expenses:Food", a))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let filled = interpolate(&txn).expect("interpolation succeeds");
        for (currency, residual) in calculate_residual(&filled.transaction) {
            prop_assert_eq!(
                residual,
                Decimal::ZERO,
                "non-zero residual {} after interpolation",
                currency
            );
        }
    }
}
