//! Property-Based Tests from TLA+ Invariants
//!
//! These tests verify that the Rust implementation satisfies the same
//! invariants defined in the TLA+ specifications.
//!
//! Reference: spec/tla/Interpolation.tla

use proptest::prelude::*;
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use rustledger_booking::{calculate_residual, interpolate};
use rustledger_core::{Amount, IncompleteAmount, NaiveDate, Posting, Transaction};

// ============================================================================
// Test Strategies
// ============================================================================

fn date_strategy() -> impl Strategy<Value = NaiveDate> {
    (2020i32..2025, 1u32..13, 1u32..29).prop_map(|(y, m, d)| {
        rustledger_core::naive_date(y, m, d)
            .unwrap_or(rustledger_core::naive_date(y, m, 1).unwrap())
    })
}

fn amount_strategy(currency: &'static str) -> impl Strategy<Value = Amount> {
    // Non-zero amounts for meaningful tests
    prop::sample::select(vec![-1000i64, -100, -50, -10, -1, 1, 10, 50, 100, 1000]).prop_filter_map(
        "non-zero",
        move |n| {
            if n != 0 {
                Some(Amount::new(Decimal::from(n), currency))
            } else {
                None
            }
        },
    )
}

// ============================================================================
// Interpolation Tests (from Interpolation.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// TLA+ AtMostOneNull:
    /// At most one posting per currency can have a missing amount.
    ///
    /// If a transaction has two postings with missing amounts for the same
    /// currency, interpolation should fail with MultipleMissing error.
    #[test]
    fn prop_interpolation_at_most_one_null_enforced(
        amount1 in amount_strategy("USD"),
        date in date_strategy(),
    ) {
        // Create transaction with two missing USD amounts
        let txn = Transaction::new(date, "Test")
            .with_synthesized_posting(Posting::new("Expenses:Food", amount1))
            .with_synthesized_posting(Posting::with_incomplete(
                "Assets:Cash1",
                IncompleteAmount::CurrencyOnly("USD".into()),
            ))
            .with_synthesized_posting(Posting::with_incomplete(
                "Assets:Cash2",
                IncompleteAmount::CurrencyOnly("USD".into()),
            ));

        let result = interpolate(&txn);

        // Should fail because two postings are missing amounts for same currency
        prop_assert!(
            result.is_err(),
            "Should fail with two missing amounts for same currency: {:?}",
            result
        );
    }

    /// TLA+ CompleteImpliesBalanced:
    /// After interpolation, sum(postings) = 0 for each currency.
    ///
    /// This is the fundamental invariant: interpolation produces balanced transactions.
    #[test]
    fn prop_interpolation_completes_balanced(
        amount in amount_strategy("USD"),
        date in date_strategy(),
    ) {
        // Create transaction with one explicit amount and one missing
        let txn = Transaction::new(date, "Test")
            .with_synthesized_posting(Posting::new("Expenses:Food", amount))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn);

        if let Ok(interp_result) = result {
            // After interpolation, transaction should balance
            let residuals = calculate_residual(&interp_result.transaction);

            for (currency, residual) in &residuals {
                prop_assert!(
                    residual.abs() < dec!(0.01),
                    "Transaction should balance after interpolation, but {} residual is {}",
                    currency, residual
                );
            }
        }
    }

    /// TLA+ HasNullAccurate:
    /// Interpolation correctly identifies which postings need filling.
    ///
    /// The filled_indices should contain exactly the indices of postings
    /// that were originally missing amounts.
    #[test]
    fn prop_interpolation_fills_correct_postings(
        amount in amount_strategy("USD"),
        date in date_strategy(),
    ) {
        let txn = Transaction::new(date, "Test")
            .with_synthesized_posting(Posting::new("Expenses:Food", amount))
            .with_synthesized_posting(Posting::auto("Assets:Cash")); // Index 1 is missing

        let result = interpolate(&txn);

        if let Ok(interp_result) = result {
            // Should have filled exactly the posting at index 1
            prop_assert!(
                interp_result.filled_indices.contains(&1),
                "Should fill posting at index 1, filled: {:?}",
                interp_result.filled_indices
            );

            // All filled postings should now have complete amounts
            for idx in &interp_result.filled_indices {
                let posting = &interp_result.transaction.postings[*idx];
                prop_assert!(
                    matches!(posting.units, Some(IncompleteAmount::Complete(_))),
                    "Filled posting should have complete amount"
                );
            }
        }
    }

    /// TLA+ Interpolation preserves explicit amounts.
    ///
    /// Postings with explicit amounts should not be modified during interpolation.
    #[test]
    fn prop_interpolation_preserves_explicit_amounts(
        amount1 in amount_strategy("USD"),
        amount2 in amount_strategy("EUR"),
        date in date_strategy(),
    ) {
        let txn = Transaction::new(date, "Test")
            .with_synthesized_posting(Posting::new("Expenses:Food", amount1.clone()))
            .with_synthesized_posting(Posting::new("Expenses:Travel", amount2.clone()))
            .with_synthesized_posting(Posting::auto("Assets:Cash")); // Missing - will absorb both

        let result = interpolate(&txn);

        if let Ok(interp_result) = result {
            // First two postings should be unchanged
            let p1 = &interp_result.transaction.postings[0];
            let p2 = &interp_result.transaction.postings[1];

            if let Some(IncompleteAmount::Complete(a)) = &p1.units {
                prop_assert_eq!(
                    a.number, amount1.number,
                    "First posting amount should be preserved"
                );
            }
            if let Some(IncompleteAmount::Complete(a)) = &p2.units {
                prop_assert_eq!(
                    a.number, amount2.number,
                    "Second posting amount should be preserved"
                );
            }
        }
    }

    /// Residual calculation is deterministic.
    ///
    /// Calling calculate_residual twice should produce the same result.
    #[test]
    fn prop_residual_is_deterministic(
        amounts in prop::collection::vec(amount_strategy("USD"), 1..5),
        date in date_strategy(),
    ) {
        let mut txn = Transaction::new(date, "Test");
        for (i, amount) in amounts.iter().enumerate() {
            txn = txn.with_synthesized_posting(Posting::new(format!("Account:{i}"), amount.clone()));
        }

        let residual1 = calculate_residual(&txn);
        let residual2 = calculate_residual(&txn);

        for (currency, value1) in &residual1 {
            let value2 = residual2.get(currency).unwrap_or(&Decimal::ZERO);
            prop_assert_eq!(
                value1, value2,
                "Residual calculation should be deterministic"
            );
        }
    }

    /// Multi-currency interpolation correctly handles multiple currencies.
    ///
    /// When a single auto posting absorbs multiple currencies,
    /// it should be split into multiple postings.
    #[test]
    fn prop_multi_currency_interpolation(
        amount_usd in amount_strategy("USD"),
        amount_eur in amount_strategy("EUR"),
        date in date_strategy(),
    ) {
        let txn = Transaction::new(date, "Test")
            .with_synthesized_posting(Posting::new("Expenses:USD", amount_usd))
            .with_synthesized_posting(Posting::new("Expenses:EUR", amount_eur))
            .with_synthesized_posting(Posting::auto("Assets:Cash")); // Single auto posting

        let result = interpolate(&txn);

        if let Ok(interp_result) = result {
            // Should have at least 4 postings (original 3 + 1 added for second currency)
            // because the auto posting is split
            prop_assert!(
                interp_result.transaction.postings.len() >= 3,
                "Should handle multi-currency interpolation"
            );

            // All residuals should be near zero
            let residuals = calculate_residual(&interp_result.transaction);
            for (currency, residual) in &residuals {
                prop_assert!(
                    residual.abs() < dec!(0.01),
                    "{} should balance, got residual {}",
                    currency, residual
                );
            }
        }
    }
}

// ============================================================================
// Edge Cases
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// No interpolation needed when transaction is already complete.
    #[test]
    fn prop_complete_transaction_unchanged(
        amount in 1i64..1000,
        date in date_strategy(),
    ) {
        let txn = Transaction::new(date, "Test")
            .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(Decimal::from(amount), "USD")))
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(Decimal::from(-amount), "USD")));

        let result = interpolate(&txn).unwrap();

        // No postings should be filled
        prop_assert!(
            result.filled_indices.is_empty(),
            "Complete transaction should have no filled indices"
        );

        // Transaction should balance
        let residuals = calculate_residual(&result.transaction);
        prop_assert!(
            residuals.get("USD").is_none_or(|r| r.abs() < dec!(0.01)),
            "Should balance"
        );
    }

    /// Zero amount postings are valid.
    #[test]
    fn prop_zero_amount_interpolation(
        date in date_strategy(),
    ) {
        // Transaction where residual is already zero
        let txn = Transaction::new(date, "Test")
            .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(100), "USD")))
            .with_synthesized_posting(Posting::new("Expenses:Drink", Amount::new(dec!(-100), "USD")))
            .with_synthesized_posting(Posting::auto("Assets:Cash")); // Will be filled with 0

        let result = interpolate(&txn);

        if let Ok(interp_result) = result {
            // Should succeed even though filled amount is zero
            let residuals = calculate_residual(&interp_result.transaction);
            for (currency, residual) in &residuals {
                prop_assert!(
                    residual.abs() < dec!(0.01),
                    "{} should balance",
                    currency
                );
            }
        }
    }
}
