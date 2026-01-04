//! Property-based tests for beancount-core.
//!
//! These tests verify invariants hold for arbitrary inputs using proptest.
//!
//! Run with: cargo test -p beancount-core --test `property_tests`

use rustledger_core::{Amount, BookingMethod, Cost, CostSpec, Inventory, Position};
use chrono::NaiveDate;
use proptest::prelude::*;
use rust_decimal::Decimal;

// ============================================================================
// Arbitrary generators
// ============================================================================

fn arb_decimal() -> impl Strategy<Value = Decimal> {
    // Generate reasonable decimals for testing
    (-1_000_000i64..1_000_000i64).prop_map(|n| Decimal::new(n, 2))
}

fn arb_positive_decimal() -> impl Strategy<Value = Decimal> {
    (1i64..1_000_000i64).prop_map(|n| Decimal::new(n, 2))
}

fn arb_currency() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("USD".to_string()),
        Just("EUR".to_string()),
        Just("GBP".to_string()),
        Just("AAPL".to_string()),
        Just("BTC".to_string()),
    ]
}

fn arb_amount() -> impl Strategy<Value = Amount> {
    (arb_decimal(), arb_currency()).prop_map(|(n, c)| Amount::new(n, c))
}

fn arb_positive_amount() -> impl Strategy<Value = Amount> {
    (arb_positive_decimal(), arb_currency()).prop_map(|(n, c)| Amount::new(n, c))
}

fn arb_date() -> impl Strategy<Value = NaiveDate> {
    (2020u32..2025u32, 1u32..13u32, 1u32..29u32)
        .prop_map(|(y, m, d)| NaiveDate::from_ymd_opt(y as i32, m, d).unwrap())
}

fn arb_cost() -> impl Strategy<Value = Cost> {
    (arb_positive_decimal(), arb_currency(), prop::option::of(arb_date())).prop_map(
        |(n, c, date)| {
            let mut cost = Cost::new(n, c);
            if let Some(d) = date {
                cost = cost.with_date(d);
            }
            cost
        },
    )
}

fn arb_position() -> impl Strategy<Value = Position> {
    (arb_positive_amount(), prop::option::of(arb_cost())).prop_map(|(units, cost)| {
        if let Some(c) = cost {
            Position::with_cost(units, c)
        } else {
            Position::simple(units)
        }
    })
}

fn arb_inventory() -> impl Strategy<Value = Inventory> {
    prop::collection::vec(arb_position(), 0..10).prop_map(|positions| {
        let mut inv = Inventory::new();
        for pos in positions {
            inv.add(pos);
        }
        inv
    })
}

// ============================================================================
// Decimal Properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// P5: Addition is commutative
    #[test]
    fn prop_decimal_addition_commutative(a in arb_decimal(), b in arb_decimal()) {
        prop_assert_eq!(a + b, b + a);
    }

    /// P5: Addition is associative
    #[test]
    fn prop_decimal_addition_associative(
        a in arb_decimal(),
        b in arb_decimal(),
        c in arb_decimal()
    ) {
        // Use a tolerance for floating-point-like edge cases
        let left = (a + b) + c;
        let right = a + (b + c);
        prop_assert_eq!(left, right);
    }

    /// P5: Multiplication distributes over addition
    #[test]
    fn prop_decimal_distributive(
        a in arb_decimal(),
        b in arb_decimal(),
        c in arb_decimal()
    ) {
        let left = a * (b + c);
        let right = a * b + a * c;
        prop_assert_eq!(left, right);
    }

    /// Zero is additive identity
    #[test]
    fn prop_decimal_zero_identity(a in arb_decimal()) {
        prop_assert_eq!(a + Decimal::ZERO, a);
        prop_assert_eq!(Decimal::ZERO + a, a);
    }

    /// Negation is its own inverse
    #[test]
    fn prop_decimal_negation_inverse(a in arb_decimal()) {
        prop_assert_eq!(-(-a), a);
    }
}

// ============================================================================
// Amount Properties
// ============================================================================

proptest! {
    /// Amount negation is its own inverse
    #[test]
    fn prop_amount_negation_inverse(amount in arb_amount()) {
        let double_neg = -(-amount.clone());
        prop_assert_eq!(double_neg.number, amount.number);
        prop_assert_eq!(double_neg.currency, amount.currency);
    }

    /// Amount addition produces same currency
    #[test]
    fn prop_amount_same_currency_add(
        n1 in arb_decimal(),
        n2 in arb_decimal(),
        currency in arb_currency()
    ) {
        let a1 = Amount::new(n1, &currency);
        let a2 = Amount::new(n2, &currency);
        let sum = a1 + a2;
        prop_assert_eq!(sum.currency, currency);
        prop_assert_eq!(sum.number, n1 + n2);
    }
}

// ============================================================================
// Inventory Properties
// ============================================================================

proptest! {
    /// P12: Adding positions increases units
    #[test]
    fn prop_inventory_add_increases_units(
        inv in arb_inventory(),
        pos in arb_position()
    ) {
        let currency = pos.units.currency.clone();
        let before = inv.units(&currency);
        let mut after_inv = inv;
        after_inv.add(pos.clone());
        let after = after_inv.units(&currency);

        prop_assert_eq!(after, before + pos.units.number);
    }

    /// Inventory merge is associative in terms of units
    #[test]
    fn prop_inventory_merge_units(
        inv1 in arb_inventory(),
        inv2 in arb_inventory()
    ) {
        let mut merged = inv1.clone();
        merged.merge(&inv2);

        // Check that units match for common currencies
        for currency in ["USD", "EUR", "GBP", "AAPL", "BTC"] {
            let expected = inv1.units(currency) + inv2.units(currency);
            let actual = merged.units(currency);
            prop_assert_eq!(actual, expected, "Currency {} mismatch", currency);
        }
    }

    /// Empty inventory has zero units for any currency
    #[test]
    fn prop_empty_inventory_zero_units(currency in arb_currency()) {
        let inv = Inventory::new();
        prop_assert_eq!(inv.units(&currency), Decimal::ZERO);
    }

    /// Inventory units is always consistent after operations
    #[test]
    fn prop_inventory_units_consistency(positions in prop::collection::vec(arb_position(), 1..5)) {
        let mut inv = Inventory::new();
        let mut expected_units: std::collections::HashMap<String, Decimal> = std::collections::HashMap::new();

        for pos in &positions {
            inv.add(pos.clone());
            *expected_units.entry(pos.units.currency.clone()).or_default() += pos.units.number;
        }

        for (currency, expected) in expected_units {
            prop_assert_eq!(inv.units(&currency), expected);
        }
    }
}

// ============================================================================
// Booking Properties
// ============================================================================

proptest! {
    /// P14: Inventory stays non-negative with proper booking (FIFO/LIFO/STRICT)
    #[test]
    fn prop_inventory_non_negative_after_add(positions in prop::collection::vec(arb_position(), 0..10)) {
        let mut inv = Inventory::new();

        for pos in positions {
            inv.add(pos);
        }

        // All positions should have non-negative units
        for pos in inv.positions() {
            prop_assert!(pos.units.number >= Decimal::ZERO,
                "Found negative position: {:?}", pos);
        }
    }

    /// Reduction cannot exceed available units (STRICT should fail)
    #[test]
    fn prop_reduce_fails_when_insufficient(
        positions in prop::collection::vec(arb_position(), 1..5),
    ) {
        let mut inv = Inventory::new();
        for pos in &positions {
            inv.add(pos.clone());
        }

        // Pick a currency and try to reduce more than available
        if let Some(pos) = positions.first() {
            let currency = &pos.units.currency;
            let available = inv.units(currency);
            let over_reduction = Amount::new(-(available + Decimal::ONE), currency);

            let result = inv.reduce(&over_reduction, None, BookingMethod::Strict);

            // STRICT should fail or result in insufficient units
            prop_assert!(result.is_err() || inv.units(currency) >= Decimal::ZERO);
        }
    }
}

// ============================================================================
// Cost Properties
// ============================================================================

proptest! {
    /// CostSpec matching is reflexive (a spec matches its own cost)
    #[test]
    fn prop_cost_spec_matches_self(cost in arb_cost()) {
        let spec = CostSpec::empty()
            .with_number_per(cost.number)
            .with_currency(&cost.currency);

        prop_assert!(spec.matches(&cost));
    }

    /// Empty cost spec matches any cost
    #[test]
    fn prop_empty_spec_matches_any(cost in arb_cost()) {
        let empty_spec = CostSpec::empty();
        prop_assert!(empty_spec.matches(&cost));
    }

    /// Cost with date requires matching date
    #[test]
    fn prop_cost_date_matching(
        n in arb_positive_decimal(),
        c in arb_currency(),
        d1 in arb_date(),
        d2 in arb_date()
    ) {
        let cost = Cost::new(n, &c).with_date(d1);
        let spec_with_date = CostSpec::empty().with_date(d2);

        let matches = spec_with_date.matches(&cost);

        // Should match only if dates are equal
        prop_assert_eq!(matches, d1 == d2);
    }
}

// ============================================================================
// Parser-related Properties (roundtrip)
// ============================================================================

proptest! {
    /// Amount Display/parsing roundtrip
    #[test]
    fn prop_amount_display_roundtrip(amount in arb_amount()) {
        let display = format!("{amount}");

        // Display format is "number currency"
        let parts: Vec<&str> = display.split_whitespace().collect();
        prop_assert_eq!(parts.len(), 2);

        let parsed_number: Decimal = parts[0].parse().unwrap();
        let parsed_currency = parts[1];

        prop_assert_eq!(parsed_number, amount.number);
        prop_assert_eq!(parsed_currency, amount.currency);
    }

    /// Cost Display contains key components
    #[test]
    fn prop_cost_display_contains_components(cost in arb_cost()) {
        let display = format!("{cost}");

        // Display should contain the number and currency
        prop_assert!(display.contains(&cost.number.to_string()));
        prop_assert!(display.contains(&cost.currency));
    }
}
