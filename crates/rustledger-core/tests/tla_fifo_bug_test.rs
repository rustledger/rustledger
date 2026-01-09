//! Test derived from TLA+ counterexample in FIFOCheck.tla
//!
//! TLC found that if lots are added out of chronological order,
//! FIFO incorrectly selects based on insertion order rather than date.

use chrono::NaiveDate;
use rust_decimal_macros::dec;
use rustledger_core::{Amount, BookingMethod, Cost, CostSpec, Inventory, Position};

/// Reproduction of TLA+ counterexample:
/// 1. Add lot with date=2024-01-02
/// 2. Add lot with date=2024-01-01 (OLDER but added second)
/// 3. `ReduceFIFO` should select the older lot (date=2024-01-01)
#[test]
fn tla_fifo_should_select_oldest_by_date_not_insertion_order() {
    let mut inv = Inventory::new();

    // State 2: Add lot with date=2 (newer)
    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        Cost::new(dec!(150), "USD").with_date(NaiveDate::from_ymd_opt(2024, 1, 2).unwrap()),
    ));

    // State 3: Add lot with date=1 (OLDER, but added second)
    inv.add(Position::with_cost(
        Amount::new(dec!(10), "AAPL"),
        Cost::new(dec!(100), "USD").with_date(NaiveDate::from_ymd_opt(2024, 1, 1).unwrap()),
    ));

    // State 4: Reduce using FIFO
    let result = inv
        .reduce(
            &Amount::new(dec!(-5), "AAPL"),
            Some(&CostSpec::default()),
            BookingMethod::Fifo,
        )
        .expect("reduction should succeed");

    // FIFO should select the OLDEST lot (date=2024-01-01, cost=$100)
    // But the current implementation selects by insertion order (date=2024-01-02, cost=$150)
    let cost_basis = result.cost_basis.expect("should have cost basis");

    // This assertion currently FAILS because the code picks insertion order
    // Expected: 5 units * $100 = $500 (from oldest lot)
    // Actual:   5 units * $150 = $750 (from first-inserted lot)
    assert_eq!(
        cost_basis.number,
        dec!(500),
        "FIFO should select oldest lot by DATE, not insertion order. \
         Got cost basis ${}, expected $500 (5 units @ $100 from 2024-01-01 lot)",
        cost_basis.number
    );
}
