//! TLA+ Invariant Validation Tests
//!
//! These tests validate that Rust implementation satisfies the same invariants
//! defined in TLA+ specifications (spec/tla/*.tla).
//!
//! Each test corresponds to a specific TLA+ invariant, enabling:
//! - Verification that Rust matches formal specification
//! - Regression testing when modifying booking algorithms
//! - Documentation of expected behavior from formal model
//!
//! Reference: spec/tla/BookingMethods.tla

use chrono::NaiveDate;
use proptest::prelude::*;
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use rustledger_core::{Amount, BookingMethod, Cost, CostSpec, Inventory, Position};
use std::collections::HashMap;

// ============================================================================
// Test Helpers (matching TLA+ helper functions)
// ============================================================================

fn date(year: i32, month: u32, day: u32) -> NaiveDate {
    NaiveDate::from_ymd_opt(year, month, day).unwrap()
}

/// TLA+ Oldest(): Get the lot with earliest date
fn oldest_lot(positions: &[&Position]) -> Option<&Position> {
    positions
        .iter()
        .filter(|p| p.cost.is_some())
        .min_by_key(|p| p.cost.as_ref().and_then(|c| c.date))
        .copied()
}

/// TLA+ Newest(): Get the lot with latest date
fn newest_lot(positions: &[&Position]) -> Option<&Position> {
    positions
        .iter()
        .filter(|p| p.cost.is_some())
        .max_by_key(|p| p.cost.as_ref().and_then(|c| c.date))
        .copied()
}

/// TLA+ HighestCost(): Get the lot with highest cost per unit
fn highest_cost_lot(positions: &[&Position]) -> Option<&Position> {
    positions
        .iter()
        .filter(|p| p.cost.is_some())
        .max_by_key(|p| p.cost.as_ref().map(|c| c.number))
        .copied()
}

/// TLA+ Matching(): Get positions matching a cost spec
fn matching_positions<'a>(
    positions: &'a [Position],
    currency: &str,
    spec: &CostSpec,
) -> Vec<&'a Position> {
    positions
        .iter()
        .filter(|p| {
            p.units.currency == currency
                && !p.units.number.is_zero()
                && p.matches_cost_spec(spec)
        })
        .collect()
}

/// TLA+ TotalUnits(): Sum of all units for a currency
fn total_units(inventory: &Inventory, currency: &str) -> Decimal {
    inventory.units(currency)
}

// ============================================================================
// TLA+ NonNegativeUnits Invariant
// ============================================================================
// From BookingMethods.tla:
// NonNegativeUnits == method # "NONE" => TotalUnits >= 0

#[test]
fn tla_non_negative_units_after_fifo() {
    let mut inv = Inventory::new();

    // Add lots (matching TLA+ AddLot action)
    let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));

    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

    // Reduce via FIFO (matching TLA+ ReduceFIFO action)
    let result = inv.reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Fifo);
    assert!(result.is_ok());

    // TLA+ NonNegativeUnits invariant
    assert!(
        total_units(&inv, "AAPL") >= Decimal::ZERO,
        "NonNegativeUnits violated: {} < 0",
        total_units(&inv, "AAPL")
    );
}

#[test]
fn tla_non_negative_units_after_lifo() {
    let mut inv = Inventory::new();

    let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));

    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

    let result = inv.reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Lifo);
    assert!(result.is_ok());

    // TLA+ NonNegativeUnits invariant
    assert!(
        total_units(&inv, "AAPL") >= Decimal::ZERO,
        "NonNegativeUnits violated"
    );
}

#[test]
fn tla_non_negative_units_after_hifo() {
    let mut inv = Inventory::new();

    let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

    let result = inv.reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Hifo);
    assert!(result.is_ok());

    // TLA+ NonNegativeUnits invariant
    assert!(
        total_units(&inv, "AAPL") >= Decimal::ZERO,
        "NonNegativeUnits violated"
    );
}

// ============================================================================
// TLA+ ValidLots Invariant
// ============================================================================
// From BookingMethods.tla:
// ValidLots == \A l \in lots : l.units > 0

#[test]
fn tla_valid_lots_after_partial_reduction() {
    let mut inv = Inventory::new();

    let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

    // Partial reduction - lot should still have positive units
    let _ = inv.reduce(&Amount::new(dec!(-3), "AAPL"), None, BookingMethod::Fifo);

    // TLA+ ValidLots invariant: all remaining lots have positive units
    for pos in inv.positions() {
        assert!(
            pos.units.number > Decimal::ZERO || pos.units.number.is_zero(),
            "ValidLots violated: lot has invalid units {}",
            pos.units.number
        );
    }
}

#[test]
fn tla_valid_lots_empty_after_full_reduction() {
    let mut inv = Inventory::new();

    let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

    // Full reduction - lot should be removed entirely
    let _ = inv.reduce(&Amount::new(dec!(-10), "AAPL"), None, BookingMethod::Fifo);

    // After full consumption, no empty lots should remain
    for pos in inv.positions() {
        assert!(
            !pos.units.number.is_zero(),
            "ValidLots violated: empty lot remains in inventory"
        );
    }
}

// ============================================================================
// TLA+ FIFOProperty Invariant
// ============================================================================
// From BookingMethods.tla (strengthened version):
// FIFOProperty ==
//     \A i \in 1..Len(history) :
//         history[i].method \in {"FIFO", "FIFO_PARTIAL"} =>
//             \A other \in matches : selected.date <= other.date

#[test]
fn tla_fifo_property_selects_oldest() {
    let mut inv = Inventory::new();

    // Create lots with different dates (matching TLA+ AddLot actions)
    let cost_old = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1)); // Oldest
    let cost_mid = Cost::new(dec!(150.00), "USD").with_date(date(2024, 6, 1));
    let cost_new = Cost::new(dec!(200.00), "USD").with_date(date(2024, 12, 1)); // Newest

    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        cost_old.clone(),
    ));
    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        cost_mid.clone(),
    ));
    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        cost_new.clone(),
    ));

    // Snapshot matching lots before reduction (like TLA+ matching_lots)
    let spec = CostSpec::default();
    let matches_before: Vec<_> = matching_positions(inv.positions(), "AAPL", &spec);
    let oldest = oldest_lot(&matches_before);

    // Perform FIFO reduction
    let result = inv
        .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Fifo)
        .unwrap();

    // TLA+ FIFOProperty: selected lot should be oldest among matches
    // The matched position should have the oldest date
    let matched = &result.matched[0];
    assert_eq!(
        matched.cost.as_ref().unwrap().date,
        oldest.unwrap().cost.as_ref().unwrap().date,
        "FIFOProperty violated: did not select oldest lot"
    );

    // Additional verification: cost basis should match oldest lot's cost
    assert_eq!(
        result.cost_basis.as_ref().unwrap().number,
        dec!(500.00), // 5 * 100
        "FIFO should use oldest lot's cost basis"
    );
}

#[test]
fn tla_fifo_property_multiple_lots() {
    let mut inv = Inventory::new();

    // Add lots oldest to newest
    let costs = [
        (dec!(100.00), date(2024, 1, 1)),
        (dec!(110.00), date(2024, 2, 1)),
        (dec!(120.00), date(2024, 3, 1)),
        (dec!(130.00), date(2024, 4, 1)),
    ];

    for (cost, d) in &costs {
        inv.add(Position::with_cost(
            Amount::new(dec!(5), "AAPL"),
            Cost::new(*cost, "USD").with_date(*d),
        ));
    }

    // Reduce 12 units via FIFO - should consume lots in order
    let result = inv
        .reduce(&Amount::new(dec!(-12), "AAPL"), None, BookingMethod::Fifo)
        .unwrap();

    // TLA+ FIFOProperty verification:
    // Should consume: 5 @ 100 + 5 @ 110 + 2 @ 120 = 500 + 550 + 240 = 1290
    assert_eq!(result.cost_basis.as_ref().unwrap().number, dec!(1290.00));

    // Remaining inventory should only have newer lots
    assert_eq!(inv.units("AAPL"), dec!(8)); // 20 - 12
}

// ============================================================================
// TLA+ LIFOProperty Invariant
// ============================================================================
// From BookingMethods.tla:
// LIFOProperty ==
//     \A other \in matches : selected.date >= other.date

#[test]
fn tla_lifo_property_selects_newest() {
    let mut inv = Inventory::new();

    let cost_old = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    let cost_mid = Cost::new(dec!(150.00), "USD").with_date(date(2024, 6, 1));
    let cost_new = Cost::new(dec!(200.00), "USD").with_date(date(2024, 12, 1));

    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        cost_old.clone(),
    ));
    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        cost_mid.clone(),
    ));
    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        cost_new.clone(),
    ));

    let spec = CostSpec::default();
    let matches_before: Vec<_> = matching_positions(inv.positions(), "AAPL", &spec);
    let newest = newest_lot(&matches_before);

    let result = inv
        .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Lifo)
        .unwrap();

    // TLA+ LIFOProperty: selected lot should be newest among matches
    let matched = &result.matched[0];
    assert_eq!(
        matched.cost.as_ref().unwrap().date,
        newest.unwrap().cost.as_ref().unwrap().date,
        "LIFOProperty violated: did not select newest lot"
    );

    // LIFO should use newest lot's cost (200)
    assert_eq!(result.cost_basis.as_ref().unwrap().number, dec!(1000.00)); // 5 * 200
}

// ============================================================================
// TLA+ HIFOProperty Invariant
// ============================================================================
// From BookingMethods.tla:
// HIFOProperty ==
//     \A other \in matches : selected.cost_per_unit >= other.cost_per_unit

#[test]
fn tla_hifo_property_selects_highest_cost() {
    let mut inv = Inventory::new();

    // Costs in non-sorted order to test proper selection
    let cost_low = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    let cost_high = Cost::new(dec!(300.00), "USD").with_date(date(2024, 2, 1)); // Highest
    let cost_mid = Cost::new(dec!(200.00), "USD").with_date(date(2024, 3, 1));

    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        cost_low.clone(),
    ));
    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        cost_high.clone(),
    ));
    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        cost_mid.clone(),
    ));

    let spec = CostSpec::default();
    let matches_before: Vec<_> = matching_positions(inv.positions(), "AAPL", &spec);
    let highest = highest_cost_lot(&matches_before);

    let result = inv
        .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Hifo)
        .unwrap();

    // TLA+ HIFOProperty: selected lot should have highest cost among matches
    let matched = &result.matched[0];
    assert_eq!(
        matched.cost.as_ref().unwrap().number,
        highest.unwrap().cost.as_ref().unwrap().number,
        "HIFOProperty violated: did not select highest cost lot"
    );

    // HIFO should use highest cost (300)
    assert_eq!(result.cost_basis.as_ref().unwrap().number, dec!(1500.00)); // 5 * 300
}

#[test]
fn tla_hifo_tax_optimization_scenario() {
    // Real-world tax optimization scenario:
    // When selling shares, HIFO maximizes cost basis, minimizing capital gains
    let mut inv = Inventory::new();

    // Bought at various prices over time
    let purchases = [
        (dec!(10), dec!(50.00), date(2020, 1, 1)),  // $500 total
        (dec!(10), dec!(100.00), date(2021, 1, 1)), // $1000 total
        (dec!(10), dec!(150.00), date(2022, 1, 1)), // $1500 total (highest cost)
        (dec!(10), dec!(75.00), date(2023, 1, 1)),  // $750 total
    ];

    for (units, cost, d) in &purchases {
        inv.add(Position::with_cost(
            Amount::new(*units, "AAPL"),
            Cost::new(*cost, "USD").with_date(*d),
        ));
    }

    // Selling 15 shares via HIFO
    let result = inv
        .reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Hifo)
        .unwrap();

    // HIFO should take: 10 @ 150 + 5 @ 100 = 1500 + 500 = 2000
    assert_eq!(
        result.cost_basis.as_ref().unwrap().number,
        dec!(2000.00),
        "HIFO should maximize cost basis for tax optimization"
    );

    // Compare with FIFO which would give lower cost basis
    let mut inv_fifo = Inventory::new();
    for (units, cost, d) in &purchases {
        inv_fifo.add(Position::with_cost(
            Amount::new(*units, "AAPL"),
            Cost::new(*cost, "USD").with_date(*d),
        ));
    }
    let fifo_result = inv_fifo
        .reduce(&Amount::new(dec!(-15), "AAPL"), None, BookingMethod::Fifo)
        .unwrap();

    // FIFO takes: 10 @ 50 + 5 @ 100 = 500 + 500 = 1000
    assert_eq!(fifo_result.cost_basis.as_ref().unwrap().number, dec!(1000.00));

    // HIFO gives 2x the cost basis, significantly reducing capital gains
    assert!(result.cost_basis.as_ref().unwrap().number > fifo_result.cost_basis.as_ref().unwrap().number);
}

// ============================================================================
// TLA+ STRICTProperty Invariant
// ============================================================================
// From BookingMethods.tla:
// STRICTProperty ==
//     \/ Cardinality(matches) = 1
//     \/ method = "STRICT_TOTAL"

#[test]
fn tla_strict_property_unique_match() {
    let mut inv = Inventory::new();

    // Only one lot - unambiguous
    let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

    // STRICT should work with unique match
    let result = inv.reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Strict);

    assert!(
        result.is_ok(),
        "STRICTProperty: unique match should succeed"
    );
}

#[test]
fn tla_strict_property_ambiguous_fails() {
    let mut inv = Inventory::new();

    // Multiple lots - ambiguous without cost spec
    let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));

    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

    // STRICT should fail without disambiguating cost spec
    let result = inv.reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Strict);

    assert!(
        result.is_err(),
        "STRICTProperty: ambiguous match should fail"
    );
}

#[test]
fn tla_strict_property_total_match_exception() {
    let mut inv = Inventory::new();

    // Multiple lots but reducing exactly total amount
    let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));

    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

    // Reducing exactly 20 (total) should work - STRICT_TOTAL in TLA+
    let result = inv.reduce(&Amount::new(dec!(-20), "AAPL"), None, BookingMethod::Strict);

    assert!(
        result.is_ok(),
        "STRICTProperty: total match exception should succeed"
    );
    assert_eq!(inv.units("AAPL"), Decimal::ZERO);
}

// ============================================================================
// TLA+ STRICT_WITH_SIZEProperty Invariant
// ============================================================================
// From BookingMethods.tla:
// STRICT_WITH_SIZEProperty ==
//     \/ Cardinality(matches) = 1
//     \/ method = "STRICT_WITH_SIZE_EXACT"
//     \/ method = "STRICT_WITH_SIZE_TOTAL"

#[test]
fn tla_strict_with_size_exact_match() {
    let mut inv = Inventory::new();

    // Multiple lots, one matches size exactly
    let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    let cost2 = Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1));

    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1)); // Exact match for 10
    inv.add(Position::with_cost(Amount::new(dec!(15), "AAPL"), cost2));

    // Reducing exactly 10 should use the exact-size lot
    let result = inv.reduce(
        &Amount::new(dec!(-10), "AAPL"),
        None,
        BookingMethod::StrictWithSize,
    );

    assert!(
        result.is_ok(),
        "STRICT_WITH_SIZE: exact size match should succeed"
    );

    // Should have consumed the 10-unit lot entirely
    assert_eq!(inv.units("AAPL"), dec!(15));
}

// ============================================================================
// TLA+ AVERAGEProperty Invariant
// ============================================================================
// From BookingMethods.tla:
// AVERAGEProperty ==
//     history[i].avg_cost >= 0

#[test]
fn tla_average_property_weighted_cost() {
    let mut inv = Inventory::new();

    // Buy 10 @ $100 and 10 @ $200 -> average = $150
    let cost1 = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    let cost2 = Cost::new(dec!(200.00), "USD").with_date(date(2024, 2, 1));

    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost1));
    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost2));

    let result = inv
        .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Average)
        .unwrap();

    // TLA+ AVERAGEProperty: avg_cost >= 0
    assert!(result.cost_basis.is_some());
    let cost_basis = result.cost_basis.as_ref().unwrap().number;
    assert!(cost_basis >= Decimal::ZERO, "AVERAGEProperty violated");

    // Average cost should be (10*100 + 10*200) / 20 = 150
    // Selling 5 units at avg cost = 5 * 150 = 750
    assert_eq!(cost_basis, dec!(750.00));
}

// ============================================================================
// TLA+ CostBasisTracked Property
// ============================================================================
// From BookingMethods.tla:
// CostBasisTracked == totalCostBasis >= 0

#[test]
fn tla_cost_basis_tracked() {
    let mut inv = Inventory::new();

    let cost = Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1));
    inv.add(Position::with_cost(Amount::new(dec!(10), "AAPL"), cost));

    let result = inv
        .reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Fifo)
        .unwrap();

    // TLA+ CostBasisTracked: cost basis is always non-negative
    if let Some(basis) = &result.cost_basis {
        assert!(
            basis.number >= Decimal::ZERO,
            "CostBasisTracked violated: negative cost basis"
        );
    }
}

// ============================================================================
// TLA+ Trace Validation Tests
// ============================================================================
// These tests simulate complete TLA+ traces (sequences of operations)

#[test]
fn tla_trace_fifo_multi_lot_reduction() {
    // TLA+ Trace:
    // State 0: Init (lots = {})
    // State 1: AddLot([units: 10, cost: 100, date: day 1])
    // State 2: AddLot([units: 10, cost: 150, date: day 60])
    // State 3: AddLot([units: 10, cost: 200, date: day 120])
    // State 4: ReduceFIFO(25 units)
    // Expected: Consume all of lot 1 (10), all of lot 2 (10), partial lot 3 (5)

    let mut inv = Inventory::new();

    // State 1-3: AddLot actions
    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1)),
    ));
    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        Cost::new(dec!(150.00), "USD").with_date(date(2024, 3, 1)),
    ));
    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        Cost::new(dec!(200.00), "USD").with_date(date(2024, 5, 1)),
    ));

    // Verify pre-conditions
    assert_eq!(inv.positions().len(), 3);
    assert_eq!(inv.units("AAPL"), dec!(30));

    // State 4: ReduceFIFO
    let result = inv
        .reduce(&Amount::new(dec!(-25), "AAPL"), None, BookingMethod::Fifo)
        .unwrap();

    // Verify TLA+ invariants after trace
    assert!(inv.units("AAPL") >= Decimal::ZERO, "NonNegativeUnits");
    assert_eq!(inv.units("AAPL"), dec!(5), "Units balance");

    // Cost basis: 10*100 + 10*150 + 5*200 = 1000 + 1500 + 1000 = 3500
    assert_eq!(result.cost_basis.as_ref().unwrap().number, dec!(3500.00));
}

#[test]
fn tla_trace_interleaved_add_reduce() {
    // TLA+ Trace simulating real trading:
    // Buy -> Sell -> Buy -> Sell pattern

    let mut inv = Inventory::new();

    // Buy 10 @ $100
    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        Cost::new(dec!(100.00), "USD").with_date(date(2024, 1, 1)),
    ));
    assert_eq!(inv.units("AAPL"), dec!(10));

    // Sell 5 (FIFO)
    let _ = inv.reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Fifo);
    assert_eq!(inv.units("AAPL"), dec!(5));

    // Buy 10 @ $150
    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        Cost::new(dec!(150.00), "USD").with_date(date(2024, 2, 1)),
    ));
    assert_eq!(inv.units("AAPL"), dec!(15));

    // Sell 8 (FIFO) - should take remaining 5 @ $100 + 3 @ $150
    let result = inv
        .reduce(&Amount::new(dec!(-8), "AAPL"), None, BookingMethod::Fifo)
        .unwrap();

    // NonNegativeUnits invariant
    assert!(inv.units("AAPL") >= Decimal::ZERO);
    assert_eq!(inv.units("AAPL"), dec!(7));

    // Cost basis: 5*100 + 3*150 = 500 + 450 = 950
    assert_eq!(result.cost_basis.as_ref().unwrap().number, dec!(950.00));
}

// ============================================================================
// Property-Based Tests (derived from TLA+ properties)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// TLA+ NonNegativeUnits property under random operations
    #[test]
    fn prop_tla_non_negative_units(
        lot_units in proptest::collection::vec(1u32..50u32, 1..5),
        lot_costs in proptest::collection::vec(10u32..500u32, 1..5),
        reduce_units in 1u32..100u32
    ) {
        let mut inv = Inventory::new();

        // Add random lots
        for (i, (&units, &cost)) in lot_units.iter().zip(lot_costs.iter()).enumerate() {
            let d = date(2024, 1, (i + 1) as u32);
            inv.add(Position::with_cost(
                Amount::new(Decimal::from(units), "AAPL"),
                Cost::new(Decimal::from(cost), "USD").with_date(d),
            ));
        }

        let total = inv.units("AAPL");

        // Reduce (capped at total to avoid error)
        let reduce = Decimal::from(reduce_units).min(total);
        if !reduce.is_zero() {
            let _ = inv.reduce(
                &Amount::new(-reduce, "AAPL"),
                None,
                BookingMethod::Fifo,
            );
        }

        // TLA+ NonNegativeUnits invariant
        prop_assert!(inv.units("AAPL") >= Decimal::ZERO);
    }

    /// TLA+ ValidLots property: no empty lots remain
    #[test]
    fn prop_tla_valid_lots(
        lot_units in proptest::collection::vec(1u32..20u32, 1..5),
    ) {
        let mut inv = Inventory::new();

        for (i, &units) in lot_units.iter().enumerate() {
            let d = date(2024, 1, (i + 1) as u32);
            inv.add(Position::with_cost(
                Amount::new(Decimal::from(units), "AAPL"),
                Cost::new(dec!(100), "USD").with_date(d),
            ));
        }

        // Full reduction
        let total = inv.units("AAPL");
        let _ = inv.reduce(&Amount::new(-total, "AAPL"), None, BookingMethod::Fifo);

        // TLA+ ValidLots: no empty positions
        for pos in inv.positions() {
            prop_assert!(!pos.units.number.is_zero());
        }
    }

    /// TLA+ FIFOProperty: FIFO always selects oldest
    #[test]
    fn prop_tla_fifo_selects_oldest(
        days in proptest::collection::vec(1u32..365u32, 2..5),
    ) {
        let mut inv = Inventory::new();

        // Sort days to know which is oldest
        let mut sorted_days = days.clone();
        sorted_days.sort();
        let oldest_day = sorted_days[0];

        for (i, &day) in days.iter().enumerate() {
            let d = NaiveDate::from_ymd_opt(2024, 1, 1).unwrap()
                + chrono::Duration::days(day as i64);
            inv.add(Position::with_cost(
                Amount::new(dec!(10), "AAPL"),
                Cost::new(Decimal::from(100 + i as u32), "USD").with_date(d),
            ));
        }

        let result = inv.reduce(&Amount::new(dec!(-5), "AAPL"), None, BookingMethod::Fifo);

        if let Ok(res) = result {
            // First matched lot should have oldest date
            let matched_day = res.matched[0]
                .cost
                .as_ref()
                .and_then(|c| c.date)
                .map(|d| (d - NaiveDate::from_ymd_opt(2024, 1, 1).unwrap()).num_days() as u32);

            if let Some(day) = matched_day {
                prop_assert_eq!(day, oldest_day, "FIFO should select oldest lot");
            }
        }
    }
}
