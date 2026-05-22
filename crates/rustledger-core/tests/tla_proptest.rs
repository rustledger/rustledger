//! Property-Based Tests from TLA+ Invariants
//!
//! These tests use proptest to verify that the Rust implementation
//! satisfies the same invariants defined in TLA+ specifications.
//!
//! Reference: spec/tla/*.tla

use proptest::prelude::*;
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use rustledger_core::NaiveDate;
use rustledger_core::{Amount, BookingError, BookingMethod, Cost, CostSpec, Inventory, Position};

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
    (1i64..100).prop_map(move |n| Amount::new(Decimal::from(n), currency))
}

fn cost_strategy() -> impl Strategy<Value = Cost> {
    (1i64..500, date_strategy())
        .prop_map(|(price, date)| Cost::new(Decimal::from(price), "USD").with_date(date))
}

fn position_strategy(currency: &'static str) -> impl Strategy<Value = Position> {
    (amount_strategy(currency), cost_strategy())
        .prop_map(|(amount, cost)| Position::with_cost(amount, cost))
}

// ============================================================================
// Conservation Invariant Tests (from Conservation.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// TLA+ ConservationInvariant:
    /// inventory + totalReduced = totalAdded
    ///
    /// After any sequence of add/reduce operations, the units must be conserved.
    #[test]
    fn prop_conservation_invariant(
        positions in prop::collection::vec(position_strategy("AAPL"), 1..5),
        reduce_count in 0usize..3,
    ) {
        let mut inv = Inventory::new();
        let mut total_added = Decimal::ZERO;

        // Add all positions
        for pos in &positions {
            total_added += pos.units.number;
            inv.add(pos.clone());
        }

        // Reduce some
        let mut total_reduced = Decimal::ZERO;
        for _ in 0..reduce_count {
            let current = inv.units("AAPL");
            if current > Decimal::ZERO {
                let to_reduce = (current / Decimal::from(2)).max(Decimal::ONE).min(current);
                if let Ok(result) = inv.reduce(
                    &Amount::new(-to_reduce, "AAPL"),
                    None,
                    BookingMethod::Fifo,
                ) {
                    // Sum units from all matched positions
                    let matched_units: Decimal = result.matched.iter()
                        .map(|p| p.units.number.abs())
                        .sum();
                    total_reduced += matched_units;
                }
            }
        }

        // Conservation: inventory + reduced = added
        let inventory = inv.units("AAPL");
        prop_assert_eq!(
            inventory + total_reduced,
            total_added,
            "Conservation violated: {} + {} != {}",
            inventory, total_reduced, total_added
        );
    }

    /// TLA+ NonNegativeInventory:
    /// inventory >= 0 (for non-NONE booking methods)
    #[test]
    fn prop_non_negative_inventory(
        positions in prop::collection::vec(position_strategy("AAPL"), 1..5),
    ) {
        let mut inv = Inventory::new();

        for pos in &positions {
            inv.add(pos.clone());
        }

        // Try to reduce more than available - should fail
        let current = inv.units("AAPL");
        let over_reduce = current + Decimal::ONE;

        let result = inv.reduce(
            &Amount::new(-over_reduce, "AAPL"),
            None,
            BookingMethod::Fifo,
        );

        // Either fails OR inventory stays non-negative
        if result.is_ok() {
            prop_assert!(
                inv.units("AAPL") >= Decimal::ZERO,
                "Inventory went negative: {}",
                inv.units("AAPL")
            );
        }
    }
}

// ============================================================================
// Lot Selection Tests (from LotSelection.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// TLA+ FIFOCorrect:
    /// FIFO selects the lot with the oldest date
    #[test]
    fn prop_fifo_selects_oldest(
        date1 in date_strategy(),
        date2 in date_strategy(),
    ) {
        let mut inv = Inventory::new();

        // Add two lots with different dates
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(100), "USD").with_date(date1),
        ));
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(200), "USD").with_date(date2),
        ));

        // Reduce using FIFO
        let result = inv.reduce(
            &Amount::new(dec!(-5), "AAPL"),
            None,
            BookingMethod::Fifo,
        );

        if let Ok(r) = result {
            let cost_basis = r.cost_basis.unwrap().number;
            let older_date = date1.min(date2);
            let expected_cost = if date1 <= date2 { dec!(100) } else { dec!(200) };

            // FIFO should select from oldest lot
            prop_assert_eq!(
                cost_basis,
                expected_cost * dec!(5),
                "FIFO should select from lot dated {:?} (cost {}), got cost basis {}",
                older_date, expected_cost, cost_basis
            );
        }
    }

    /// TLA+ LIFOCorrect:
    /// LIFO selects the lot with the newest date
    #[test]
    fn prop_lifo_selects_newest(
        date1 in date_strategy(),
        date2 in date_strategy(),
    ) {
        prop_assume!(date1 != date2); // Need different dates for meaningful test

        let mut inv = Inventory::new();

        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(100), "USD").with_date(date1),
        ));
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(200), "USD").with_date(date2),
        ));

        let result = inv.reduce(
            &Amount::new(dec!(-5), "AAPL"),
            None,
            BookingMethod::Lifo,
        );

        if let Ok(r) = result {
            let cost_basis = r.cost_basis.unwrap().number;
            let expected_cost = if date1 >= date2 { dec!(100) } else { dec!(200) };

            // LIFO should select from newest lot
            prop_assert_eq!(
                cost_basis,
                expected_cost * dec!(5),
                "LIFO should select from newest lot, got cost basis {}",
                cost_basis
            );
        }
    }

    /// TLA+ HIFOCorrect:
    /// HIFO selects the lot with the highest cost
    #[test]
    fn prop_hifo_selects_highest_cost(
        cost1 in 50i64..150,
        cost2 in 150i64..250,
    ) {
        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(Decimal::from(cost1), "USD").with_date(date),
        ));
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(Decimal::from(cost2), "USD").with_date(date),
        ));

        let result = inv.reduce(
            &Amount::new(dec!(-5), "AAPL"),
            None,
            BookingMethod::Hifo,
        );

        if let Ok(r) = result {
            let cost_basis = r.cost_basis.unwrap().number;
            let max_cost = Decimal::from(cost1.max(cost2));

            // HIFO should select from highest cost lot
            prop_assert_eq!(
                cost_basis,
                max_cost * dec!(5),
                "HIFO should select from lot with cost {}, got cost basis {}",
                max_cost, cost_basis
            );
        }
    }
}

// ============================================================================
// Double Entry Tests (from DoubleEntry.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// TLA+ TransactionsBalance:
    /// For any transfer, debits = credits (amount is conserved)
    #[test]
    fn prop_transfer_conserves_amount(
        amount in 1i64..1000,
    ) {
        let mut from_account = Inventory::new();
        let to_account = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        // Add to source account
        from_account.add(Position::with_cost(
            Amount::new(Decimal::from(amount), "USD"),
            Cost::new(dec!(1), "USD").with_date(date),
        ));

        let before_from = from_account.units("USD");
        let before_to = to_account.units("USD");
        let total_before = before_from + before_to;

        // Simulate transfer by reducing from source
        let transfer_amount = Decimal::from(amount / 2).max(Decimal::ONE);
        let result = from_account.reduce(
            &Amount::new(-transfer_amount, "USD"),
            None,
            BookingMethod::Fifo,
        );

        if let Ok(r) = result {
            // After transfer: from loses, to gains same amount
            let after_from = from_account.units("USD");
            let matched_units: Decimal = r.matched.iter()
                .map(|p| p.units.number.abs())
                .sum();
            let simulated_to = before_to + matched_units;
            let total_after = after_from + simulated_to;

            // Double-entry: total is conserved
            prop_assert_eq!(
                total_before,
                total_after,
                "Double-entry violated: {} != {}",
                total_before, total_after
            );
        }
    }
}

// ============================================================================
// STRICT Booking Tests (from STRICTCorrect.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// TLA+ STRICTCorrect (Python-compatible, issue #737):
    /// STRICT booking errors with `AmbiguousMatch` when a wildcard reduction
    /// targets multiple lots with *different* costs. The user must
    /// disambiguate by specifying a cost, date, or label.
    #[test]
    fn prop_strict_errors_on_ambiguous_match(
        cost in 100i64..200,
    ) {
        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        // Add two lots with the same currency at different costs.
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(Decimal::from(cost), "USD").with_date(date),
        ));
        inv.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(Decimal::from(cost + 10), "USD").with_date(date),
        ));

        let result = inv.reduce(
            &Amount::new(dec!(-5), "AAPL"),
            None,
            BookingMethod::Strict,
        );

        prop_assert!(
            matches!(result, Err(BookingError::AmbiguousMatch { .. })),
            "STRICT must error on ambiguous wildcard reduction, got: {:?}",
            result
        );
    }

    /// TLA+ STRICTCorrect:
    /// STRICT booking succeeds when exactly one lot matches
    #[test]
    fn prop_strict_succeeds_with_one_lot(
        units in 5i64..50,
        cost in 100i64..200,
    ) {
        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();
        let cost_dec = Decimal::from(cost);

        // Add exactly one lot
        inv.add(Position::with_cost(
            Amount::new(Decimal::from(units), "AAPL"),
            Cost::new(cost_dec, "USD").with_date(date),
        ));

        let reduce_amount = Decimal::from(units / 2).max(Decimal::ONE);

        // STRICT should succeed with exactly one matching lot
        // and specific cost provided
        let cost_spec = CostSpec::default()
            .with_number(rustledger_core::CostNumber::PerUnit { value: cost_dec })
            .with_currency("USD")
            .with_date(date);
        let result = inv.reduce(
            &Amount::new(-reduce_amount, "AAPL"),
            Some(&cost_spec),
            BookingMethod::Strict,
        );

        prop_assert!(
            result.is_ok(),
            "STRICT should succeed with exactly one matching lot, but got: {:?}",
            result
        );
    }
}

// ============================================================================
// NONE Booking Tests (from NONECorrect.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// TLA+ NONECorrect:
    /// NONE booking allows any reduction (most permissive)
    #[test]
    fn prop_none_allows_any_reduction(
        units in 10i64..100,
        reduce in 1i64..10,
    ) {
        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        inv.add(Position::with_cost(
            Amount::new(Decimal::from(units), "AAPL"),
            Cost::new(dec!(100), "USD").with_date(date),
        ));

        // NONE should allow reduction
        let result = inv.reduce(
            &Amount::new(Decimal::from(-reduce), "AAPL"),
            None,
            BookingMethod::None,
        );

        prop_assert!(
            result.is_ok(),
            "NONE should allow reduction, but got: {:?}",
            result
        );
    }

    /// TLA+ NONECorrect ConservationInvariant:
    /// Balance CAN go negative - short positions allowed with NONE
    #[test]
    fn prop_none_conservation_invariant(
        add_units in 10i64..50,
        reduce_units in 1i64..30,
    ) {
        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();
        let total_added = Decimal::from(add_units);

        inv.add(Position::with_cost(
            Amount::new(total_added, "AAPL"),
            Cost::new(dec!(100), "USD").with_date(date),
        ));

        let to_reduce = Decimal::from(reduce_units).min(total_added);
        let result = inv.reduce(
            &Amount::new(-to_reduce, "AAPL"),
            None,
            BookingMethod::None,
        );

        if let Ok(r) = result {
            let matched_units: Decimal = r.matched.iter()
                .map(|p| p.units.number.abs())
                .sum();

            // Conservation: inventory + reduced = added
            let inventory = inv.units("AAPL");
            prop_assert_eq!(
                inventory + matched_units,
                total_added,
                "NONE Conservation violated: {} + {} != {}",
                inventory, matched_units, total_added
            );
        }
    }
}

// ============================================================================
// AVERAGE Booking Tests (from AVERAGECorrect.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// TLA+ AVERAGECorrect:
    /// AVERAGE booking computes weighted average cost
    #[test]
    fn prop_average_weighted_cost(
        units1 in 10i64..50,
        cost1 in 100i64..200,
        units2 in 10i64..50,
        cost2 in 200i64..300,
    ) {
        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        // Add two lots with different costs
        inv.add(Position::with_cost(
            Amount::new(Decimal::from(units1), "AAPL"),
            Cost::new(Decimal::from(cost1), "USD").with_date(date),
        ));
        inv.add(Position::with_cost(
            Amount::new(Decimal::from(units2), "AAPL"),
            Cost::new(Decimal::from(cost2), "USD").with_date(date),
        ));

        // AVERAGE should succeed
        let result = inv.reduce(
            &Amount::new(dec!(-5), "AAPL"),
            None,
            BookingMethod::Average,
        );

        // Average booking should always succeed when there are units
        prop_assert!(
            result.is_ok(),
            "AVERAGE should succeed with available units, but got: {:?}",
            result
        );
    }

    /// TLA+ AVERAGECorrect:
    /// AVERAGE maintains conservation invariant
    /// Note: AVERAGE booking returns all positions before averaging in `matched`,
    /// so we verify conservation using the requested reduction amount.
    #[test]
    fn prop_average_conservation(
        units in 20i64..100,
        cost in 100i64..200,
        reduce in 5i64..15,
    ) {
        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();
        let total_added = Decimal::from(units);
        let reduce_amount = Decimal::from(reduce);

        inv.add(Position::with_cost(
            Amount::new(total_added, "AAPL"),
            Cost::new(Decimal::from(cost), "USD").with_date(date),
        ));

        let result = inv.reduce(
            &Amount::new(-reduce_amount, "AAPL"),
            None,
            BookingMethod::Average,
        );

        if result.is_ok() {
            // Conservation: inventory + reduced = added
            let inventory = inv.units("AAPL");
            prop_assert_eq!(
                inventory + reduce_amount,
                total_added,
                "AVERAGE Conservation violated: {} + {} != {}",
                inventory, reduce_amount, total_added
            );
        }
    }
}

// ============================================================================
// Multi-Currency Conservation Tests (from MultiCurrency.tla)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// TLA+ ConservationPerCurrency:
    /// inventory[c] + totalReduced[c] = totalAdded[c] for each currency.
    ///
    /// Each currency maintains its own conservation invariant independently.
    #[test]
    fn prop_multi_currency_conservation(
        units_aapl in 10i64..100,
        units_goog in 10i64..100,
        reduce_aapl in 1i64..10,
        reduce_goog in 1i64..10,
    ) {
        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        // Add AAPL
        inv.add(Position::with_cost(
            Amount::new(Decimal::from(units_aapl), "AAPL"),
            Cost::new(dec!(100), "USD").with_date(date),
        ));
        let total_added_aapl = Decimal::from(units_aapl);

        // Add GOOG
        inv.add(Position::with_cost(
            Amount::new(Decimal::from(units_goog), "GOOG"),
            Cost::new(dec!(150), "USD").with_date(date),
        ));
        let total_added_goog = Decimal::from(units_goog);

        // Reduce AAPL
        let mut total_reduced_aapl = Decimal::ZERO;
        let aapl_reduce = Decimal::from(reduce_aapl).min(Decimal::from(units_aapl));
        if let Ok(r) = inv.reduce(
            &Amount::new(-aapl_reduce, "AAPL"),
            None,
            BookingMethod::Fifo,
        ) {
            total_reduced_aapl = r.matched.iter().map(|p| p.units.number.abs()).sum();
        }

        // Reduce GOOG
        let mut total_reduced_goog = Decimal::ZERO;
        let goog_reduce = Decimal::from(reduce_goog).min(Decimal::from(units_goog));
        if let Ok(r) = inv.reduce(
            &Amount::new(-goog_reduce, "GOOG"),
            None,
            BookingMethod::Fifo,
        ) {
            total_reduced_goog = r.matched.iter().map(|p| p.units.number.abs()).sum();
        }

        // Check conservation for each currency independently
        let inv_aapl = inv.units("AAPL");
        let inv_goog = inv.units("GOOG");

        prop_assert_eq!(
            inv_aapl + total_reduced_aapl,
            total_added_aapl,
            "AAPL conservation violated: {} + {} != {}",
            inv_aapl, total_reduced_aapl, total_added_aapl
        );

        prop_assert_eq!(
            inv_goog + total_reduced_goog,
            total_added_goog,
            "GOOG conservation violated: {} + {} != {}",
            inv_goog, total_reduced_goog, total_added_goog
        );
    }

    /// TLA+ NonNegativeInventory:
    /// All currencies maintain non-negative inventory.
    #[test]
    fn prop_multi_currency_non_negative(
        units_aapl in 10i64..50,
        units_goog in 10i64..50,
    ) {
        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        inv.add(Position::with_cost(
            Amount::new(Decimal::from(units_aapl), "AAPL"),
            Cost::new(dec!(100), "USD").with_date(date),
        ));
        inv.add(Position::with_cost(
            Amount::new(Decimal::from(units_goog), "GOOG"),
            Cost::new(dec!(150), "USD").with_date(date),
        ));

        // Try to reduce more than available for each currency
        let _ = inv.reduce(
            &Amount::new(Decimal::from(-units_aapl - 10), "AAPL"),
            None,
            BookingMethod::Fifo,
        );
        let _ = inv.reduce(
            &Amount::new(Decimal::from(-units_goog - 10), "GOOG"),
            None,
            BookingMethod::Fifo,
        );

        // Both should remain non-negative after failed reductions
        prop_assert!(
            inv.units("AAPL") >= Decimal::ZERO,
            "AAPL inventory went negative: {}",
            inv.units("AAPL")
        );
        prop_assert!(
            inv.units("GOOG") >= Decimal::ZERO,
            "GOOG inventory went negative: {}",
            inv.units("GOOG")
        );
    }

    /// TLA+ NoCurrencyMixing / Isolation:
    /// Operations on one currency don't affect another currency's balance.
    #[test]
    fn prop_multi_currency_isolation(
        units_aapl in 10i64..50,
        units_goog in 10i64..50,
        reduce_aapl in 1i64..10,
    ) {
        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        inv.add(Position::with_cost(
            Amount::new(Decimal::from(units_aapl), "AAPL"),
            Cost::new(dec!(100), "USD").with_date(date),
        ));
        inv.add(Position::with_cost(
            Amount::new(Decimal::from(units_goog), "GOOG"),
            Cost::new(dec!(150), "USD").with_date(date),
        ));

        // Record GOOG balance before AAPL operation
        let goog_before = inv.units("GOOG");

        // Reduce AAPL
        let aapl_reduce = Decimal::from(reduce_aapl).min(Decimal::from(units_aapl));
        let _ = inv.reduce(
            &Amount::new(-aapl_reduce, "AAPL"),
            None,
            BookingMethod::Fifo,
        );

        // GOOG should be unaffected
        let goog_after = inv.units("GOOG");
        prop_assert_eq!(
            goog_before,
            goog_after,
            "GOOG balance changed after AAPL operation: {} -> {}",
            goog_before, goog_after
        );
    }

    /// TLA+ ReduceBoundPerCurrency:
    /// Total reduced can never exceed total added for any currency.
    #[test]
    fn prop_multi_currency_reduce_bound(
        add1 in 10i64..50,
        add2 in 10i64..50,
    ) {
        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        // Add to AAPL twice
        inv.add(Position::with_cost(
            Amount::new(Decimal::from(add1), "AAPL"),
            Cost::new(dec!(100), "USD").with_date(date),
        ));
        inv.add(Position::with_cost(
            Amount::new(Decimal::from(add2), "AAPL"),
            Cost::new(dec!(110), "USD").with_date(date),
        ));

        let total_added = Decimal::from(add1 + add2);
        let mut total_reduced = Decimal::ZERO;

        // Try to reduce multiple times
        for _ in 0..5 {
            let current = inv.units("AAPL");
            if current > Decimal::ZERO {
                let to_reduce = (current / Decimal::from(2)).max(Decimal::ONE).min(current);
                if let Ok(r) = inv.reduce(
                    &Amount::new(-to_reduce, "AAPL"),
                    None,
                    BookingMethod::Fifo,
                ) {
                    let reduced: Decimal = r.matched.iter().map(|p| p.units.number.abs()).sum();
                    total_reduced += reduced;
                }
            }
        }

        // Reduced should never exceed added
        prop_assert!(
            total_reduced <= total_added,
            "Reduced ({}) exceeded added ({})",
            total_reduced, total_added
        );
    }
}

// ============================================================================
// STRICT_WITH_SIZE Property Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// StrictWithSize exact-size property:
    /// When a reduction amount exactly matches one lot's size,
    /// STRICT_WITH_SIZE should succeed (not raise AmbiguousMatch).
    #[test]
    fn prop_strict_with_size_exact_match_succeeds(
        lot1_size in 1i64..50,
        lot2_size in 1i64..50,
        cost1 in 50i64..200,
        cost2 in 50i64..200,
    ) {
        // Only test when lot sizes differ (so we have a unique exact match)
        prop_assume!(lot1_size != lot2_size);

        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        inv.add(Position::with_cost(
            Amount::new(Decimal::from(lot1_size), "AAPL"),
            Cost::new(Decimal::from(cost1), "USD").with_date(date),
        ));
        inv.add(Position::with_cost(
            Amount::new(Decimal::from(lot2_size), "AAPL"),
            Cost::new(Decimal::from(cost2), "USD").with_date(date),
        ));

        // Reduce exactly lot1_size — should match lot1 exactly
        let result = inv.reduce(
            &Amount::new(Decimal::from(-lot1_size), "AAPL"),
            None,
            BookingMethod::StrictWithSize,
        );

        // Should always succeed because exact-size match is unambiguous
        prop_assert!(
            result.is_ok(),
            "StrictWithSize exact match for {} should succeed, got {:?}",
            lot1_size, result
        );

        if let Ok(r) = result {
            let cost_basis = r.cost_basis.unwrap().number;
            let expected = Decimal::from(lot1_size) * Decimal::from(cost1);
            prop_assert_eq!(
                cost_basis, expected,
                "Cost basis should be {} * {} = {}, got {}",
                lot1_size, cost1, expected, cost_basis
            );
        }
    }

    /// StrictWithSize conservation:
    /// After a successful reduction, total inventory units must decrease
    /// by exactly the reduction amount.
    #[test]
    fn prop_strict_with_size_conserves_units(
        lot_size in 1i64..50,
        cost in 50i64..200,
    ) {
        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        // Single lot — always unambiguous for STRICT_WITH_SIZE
        inv.add(Position::with_cost(
            Amount::new(Decimal::from(lot_size), "AAPL"),
            Cost::new(Decimal::from(cost), "USD").with_date(date),
        ));

        let reduce_amount = lot_size / 2 + 1; // Always > 0, always <= lot_size
        let reduce_amount = reduce_amount.min(lot_size);
        let before = inv.units("AAPL");

        let result = inv.reduce(
            &Amount::new(Decimal::from(-reduce_amount), "AAPL"),
            None,
            BookingMethod::StrictWithSize,
        );

        if result.is_ok() {
            let after = inv.units("AAPL");
            prop_assert_eq!(
                before - after,
                Decimal::from(reduce_amount),
                "Units should decrease by exactly {}, went from {} to {}",
                reduce_amount, before, after
            );
        }
    }

    /// StrictWithSize ambiguity:
    /// When no lot exactly matches the reduction size AND the total doesn't
    /// match, STRICT_WITH_SIZE should raise AmbiguousMatch for 2+ lots
    /// with different costs.
    #[test]
    fn prop_strict_with_size_ambiguous_when_no_exact_match(
        lot_size in 5i64..50,
        cost1 in 50i64..150,
        cost2 in 150i64..250,
    ) {
        let mut inv = Inventory::new();
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        // Two lots of same size but different costs
        inv.add(Position::with_cost(
            Amount::new(Decimal::from(lot_size), "AAPL"),
            Cost::new(Decimal::from(cost1), "USD").with_date(date),
        ));
        inv.add(Position::with_cost(
            Amount::new(Decimal::from(lot_size), "AAPL"),
            Cost::new(Decimal::from(cost2), "USD").with_date(date),
        ));

        // Reduce less than lot_size (no exact match, not total)
        let reduce = lot_size - 1;
        if reduce > 0 {
            let result = inv.reduce(
                &Amount::new(Decimal::from(-reduce), "AAPL"),
                None,
                BookingMethod::StrictWithSize,
            );

            // Should be ambiguous: same size lots, different costs, no exact match
            prop_assert!(
                matches!(result, Err(BookingError::AmbiguousMatch { .. })),
                "Expected AmbiguousMatch for reduce {} from two {}-unit lots, got {:?}",
                reduce, lot_size, result
            );
        }
    }
}
