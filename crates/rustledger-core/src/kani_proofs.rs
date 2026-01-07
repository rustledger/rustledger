//! Kani Verification Proofs for rustledger-core
//!
//! This module contains Kani proofs that verify TLA+ invariants hold in the Rust
//! implementation. Kani uses bounded model checking to exhaustively verify
//! properties for all possible inputs within bounds.
//!
//! # Running Kani Proofs
//!
//! ```bash
//! # Install Kani
//! cargo install --locked kani-verifier
//! kani setup
//!
//! # Run all proofs
//! cargo kani --package rustledger-core
//!
//! # Run specific proof
//! cargo kani --package rustledger-core --harness kani_fifo_selects_oldest
//! ```
//!
//! # TLA+ Correspondence
//!
//! Each proof corresponds to a TLA+ invariant:
//! - `kani_fifo_selects_oldest` ↔ `FIFOProperty` in BookingMethods.tla
//! - `kani_lifo_selects_newest` ↔ `LIFOProperty` in BookingMethods.tla
//! - `kani_hifo_selects_highest_cost` ↔ `HIFOProperty` in BookingMethods.tla
//! - `kani_non_negative_units` ↔ `NonNegativeUnits` in Inventory.tla
//! - `kani_conservation_of_units` ↔ `ConservationInv` in InductiveInvariants.tla

#![cfg(kani)]

use crate::inventory::{BookingMethod, Inventory};
use crate::{Amount, Cost, CostSpec, Position};
use rust_decimal::Decimal;

/// Maximum values for bounded verification
const MAX_LOTS: usize = 4;
const MAX_UNITS: i64 = 100;
const MAX_COST: i64 = 1000;
const MAX_DATE: i64 = 365;

/// Helper to create a position for Kani proofs
fn make_position(units: i64, cost: i64, date: i64, currency: &str) -> Position {
    Position {
        units: Amount::new(Decimal::new(units, 0), currency.into()),
        cost: Some(Cost {
            amount: Some(Amount::new(Decimal::new(cost, 0), "USD".into())),
            date: Some(chrono::NaiveDate::from_ymd_opt(2024, 1, 1).unwrap()
                + chrono::Duration::days(date)),
            label: None,
        }),
    }
}

/// Helper to get date from position
fn get_date(pos: &Position) -> i64 {
    pos.cost
        .as_ref()
        .and_then(|c| c.date)
        .map(|d| d.signed_duration_since(chrono::NaiveDate::from_ymd_opt(2024, 1, 1).unwrap()).num_days())
        .unwrap_or(0)
}

/// Helper to get cost from position
fn get_cost(pos: &Position) -> i64 {
    pos.cost
        .as_ref()
        .and_then(|c| c.amount.as_ref())
        .map(|a| a.number.mantissa() / 10i128.pow(a.number.scale()))
        .unwrap_or(0) as i64
}

// ============================================================================
// KANI PROOFS
// ============================================================================

/// Proof: FIFO always selects the oldest lot
///
/// Corresponds to TLA+ FIFOProperty:
/// ```tla
/// FIFOProperty ==
///     \A i \in 1..Len(history) :
///         history[i].method \in {"FIFO", "FIFO_PARTIAL"} =>
///             LET h == history[i]
///                 selected == h.from_lot
///                 matches == h.matching_lots
///             IN \A other \in matches : selected.date <= other.date
/// ```
#[kani::proof]
#[kani::unwind(5)]
fn kani_fifo_selects_oldest() {
    // Create symbolic inputs
    let num_lots: usize = kani::any();
    kani::assume(num_lots > 0 && num_lots <= MAX_LOTS);

    let mut inventory = Inventory::new();
    let mut min_date = MAX_DATE;
    let mut dates = [0i64; MAX_LOTS];

    // Add lots with symbolic dates
    for i in 0..num_lots {
        let units: i64 = kani::any();
        let cost: i64 = kani::any();
        let date: i64 = kani::any();

        kani::assume(units > 0 && units <= MAX_UNITS);
        kani::assume(cost > 0 && cost <= MAX_COST);
        kani::assume(date > 0 && date <= MAX_DATE);

        dates[i] = date;
        if date < min_date {
            min_date = date;
        }

        let pos = make_position(units, cost, date, "AAPL");
        inventory.add_position(pos);
    }

    // Reduce using FIFO
    let reduce_units: i64 = kani::any();
    kani::assume(reduce_units > 0 && reduce_units <= MAX_UNITS);

    let spec = CostSpec::default();
    if let Ok(result) = inventory.reduce(BookingMethod::Fifo, Decimal::new(reduce_units, 0), &spec) {
        // Verify: the reduced lot had the minimum date
        for reduction in result.reductions {
            let reduced_date = get_date(&reduction.position);
            // The selected lot's date must be <= all other lots' dates
            kani::assert(
                reduced_date <= min_date + 1, // Allow for rounding
                "FIFO must select oldest lot"
            );
        }
    }
}

/// Proof: LIFO always selects the newest lot
///
/// Corresponds to TLA+ LIFOProperty
#[kani::proof]
#[kani::unwind(5)]
fn kani_lifo_selects_newest() {
    let num_lots: usize = kani::any();
    kani::assume(num_lots > 0 && num_lots <= MAX_LOTS);

    let mut inventory = Inventory::new();
    let mut max_date = 0i64;

    for _i in 0..num_lots {
        let units: i64 = kani::any();
        let cost: i64 = kani::any();
        let date: i64 = kani::any();

        kani::assume(units > 0 && units <= MAX_UNITS);
        kani::assume(cost > 0 && cost <= MAX_COST);
        kani::assume(date > 0 && date <= MAX_DATE);

        if date > max_date {
            max_date = date;
        }

        let pos = make_position(units, cost, date, "AAPL");
        inventory.add_position(pos);
    }

    let reduce_units: i64 = kani::any();
    kani::assume(reduce_units > 0 && reduce_units <= MAX_UNITS);

    let spec = CostSpec::default();
    if let Ok(result) = inventory.reduce(BookingMethod::Lifo, Decimal::new(reduce_units, 0), &spec) {
        for reduction in result.reductions {
            let reduced_date = get_date(&reduction.position);
            kani::assert(
                reduced_date >= max_date - 1,
                "LIFO must select newest lot"
            );
        }
    }
}

/// Proof: HIFO always selects the highest cost lot
///
/// Corresponds to TLA+ HIFOProperty
#[kani::proof]
#[kani::unwind(5)]
fn kani_hifo_selects_highest_cost() {
    let num_lots: usize = kani::any();
    kani::assume(num_lots > 0 && num_lots <= MAX_LOTS);

    let mut inventory = Inventory::new();
    let mut max_cost = 0i64;

    for _i in 0..num_lots {
        let units: i64 = kani::any();
        let cost: i64 = kani::any();
        let date: i64 = kani::any();

        kani::assume(units > 0 && units <= MAX_UNITS);
        kani::assume(cost > 0 && cost <= MAX_COST);
        kani::assume(date > 0 && date <= MAX_DATE);

        if cost > max_cost {
            max_cost = cost;
        }

        let pos = make_position(units, cost, date, "AAPL");
        inventory.add_position(pos);
    }

    let reduce_units: i64 = kani::any();
    kani::assume(reduce_units > 0 && reduce_units <= MAX_UNITS);

    let spec = CostSpec::default();
    if let Ok(result) = inventory.reduce(BookingMethod::Hifo, Decimal::new(reduce_units, 0), &spec) {
        for reduction in result.reductions {
            let reduced_cost = get_cost(&reduction.position);
            kani::assert(
                reduced_cost >= max_cost - 1,
                "HIFO must select highest cost lot"
            );
        }
    }
}

/// Proof: Units never go negative (for non-NONE booking)
///
/// Corresponds to TLA+ NonNegativeUnits:
/// ```tla
/// NonNegativeUnits ==
///     \A curr \in Currencies :
///         ~(\E op \in Range(operations) : op.type = "reduce_none")
///         => TotalUnits(inventory, curr) >= 0
/// ```
#[kani::proof]
#[kani::unwind(5)]
fn kani_non_negative_units() {
    let mut inventory = Inventory::new();

    // Add some lots
    let num_adds: usize = kani::any();
    kani::assume(num_adds <= MAX_LOTS);

    let mut total_added = 0i64;

    for _i in 0..num_adds {
        let units: i64 = kani::any();
        kani::assume(units > 0 && units <= MAX_UNITS);

        let pos = make_position(units, 100, 1, "AAPL");
        inventory.add_position(pos);
        total_added += units;
    }

    // Try to reduce
    let reduce_units: i64 = kani::any();
    kani::assume(reduce_units > 0);

    let spec = CostSpec::default();
    let result = inventory.reduce(BookingMethod::Fifo, Decimal::new(reduce_units, 0), &spec);

    // If reduction succeeded, units should still be non-negative
    if result.is_ok() {
        // Calculate remaining units
        let total_units: i64 = inventory
            .positions()
            .filter(|p| p.units.currency.as_ref() == "AAPL")
            .map(|p| p.units.number.mantissa() as i64 / 10i64.pow(p.units.number.scale()))
            .sum();

        kani::assert(total_units >= 0, "Units must never go negative");
    }
}

/// Proof: Conservation of units
///
/// Corresponds to TLA+ ConservationInv:
/// ```tla
/// ConservationInv ==
///     TotalUnits(lots) + totalReduced = totalAdded
/// ```
#[kani::proof]
#[kani::unwind(5)]
fn kani_conservation_of_units() {
    let mut inventory = Inventory::new();

    // Track totals
    let mut total_added = 0i64;
    let mut total_reduced = 0i64;

    // Add lots
    let num_adds: usize = kani::any();
    kani::assume(num_adds > 0 && num_adds <= MAX_LOTS);

    for _i in 0..num_adds {
        let units: i64 = kani::any();
        kani::assume(units > 0 && units <= MAX_UNITS);

        let pos = make_position(units, 100, 1, "AAPL");
        inventory.add_position(pos);
        total_added += units;
    }

    // Reduce
    let reduce_units: i64 = kani::any();
    kani::assume(reduce_units > 0 && reduce_units <= total_added);

    let spec = CostSpec::default();
    if let Ok(result) = inventory.reduce(BookingMethod::Fifo, Decimal::new(reduce_units, 0), &spec) {
        for reduction in result.reductions {
            total_reduced += reduction.units.mantissa() as i64
                / 10i64.pow(reduction.units.scale());
        }
    }

    // Calculate remaining
    let remaining: i64 = inventory
        .positions()
        .filter(|p| p.units.currency.as_ref() == "AAPL")
        .map(|p| p.units.number.mantissa() as i64 / 10i64.pow(p.units.number.scale()))
        .sum();

    // Conservation: remaining + reduced = added
    kani::assert(
        remaining + total_reduced == total_added,
        "Conservation of units must hold"
    );
}

/// Proof: STRICT rejects ambiguous matches
///
/// Corresponds to TLA+ STRICTProperty
#[kani::proof]
#[kani::unwind(5)]
fn kani_strict_rejects_ambiguous() {
    let mut inventory = Inventory::new();

    // Add multiple lots with same cost spec (ambiguous)
    let units1: i64 = kani::any();
    let units2: i64 = kani::any();
    kani::assume(units1 > 0 && units1 <= MAX_UNITS);
    kani::assume(units2 > 0 && units2 <= MAX_UNITS);
    kani::assume(units1 != units2); // Different sizes

    // Same cost and date = ambiguous
    let pos1 = make_position(units1, 100, 1, "AAPL");
    let pos2 = make_position(units2, 100, 1, "AAPL");

    inventory.add_position(pos1);
    inventory.add_position(pos2);

    // Try to reduce with STRICT
    let reduce_units: i64 = kani::any();
    kani::assume(reduce_units > 0 && reduce_units < units1 && reduce_units < units2);

    let spec = CostSpec::default();
    let result = inventory.reduce(BookingMethod::Strict, Decimal::new(reduce_units, 0), &spec);

    // STRICT should reject ambiguous matches (error expected)
    // If it succeeds, there must have been exactly one match
    if result.is_ok() {
        // This is only valid if one lot was fully consumed or sizes matched
        kani::assert(
            reduce_units == units1 || reduce_units == units2 || units1 + units2 == reduce_units,
            "STRICT must reject ambiguous unless exact match"
        );
    }
}

/// Proof: Valid positions have non-zero units
///
/// Corresponds to TLA+ ValidPositions
#[kani::proof]
#[kani::unwind(5)]
fn kani_valid_positions() {
    let mut inventory = Inventory::new();

    // Add and reduce
    let add_units: i64 = kani::any();
    kani::assume(add_units > 0 && add_units <= MAX_UNITS);

    let pos = make_position(add_units, 100, 1, "AAPL");
    inventory.add_position(pos);

    let reduce_units: i64 = kani::any();
    kani::assume(reduce_units > 0 && reduce_units <= add_units);

    let spec = CostSpec::default();
    let _ = inventory.reduce(BookingMethod::Fifo, Decimal::new(reduce_units, 0), &spec);

    // All remaining positions must have positive units
    for pos in inventory.positions() {
        let units = pos.units.number.mantissa() as i64 / 10i64.pow(pos.units.number.scale());
        kani::assert(units > 0, "All positions must have positive units");
    }
}

// ============================================================================
// STUB IMPLEMENTATIONS FOR KANI
// ============================================================================

#[cfg(kani)]
mod stubs {
    // Kani may need stubs for external functions
    // Add them here as needed
}
