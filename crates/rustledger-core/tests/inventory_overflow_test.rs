//! Decimal overflow must report, never panic (#1863).
//!
//! `Decimal` is 96-bit (~7.9e28) and its `+` / `*` PANIC on overflow. Inventory
//! arithmetic runs in the loader's booking phase, so a ledger holding amounts
//! near the ceiling aborted EVERY command — including `check`, the command a
//! user runs to find out what is wrong with their file. CLAUDE.md's rule is
//! that ledger input never panics the CLI.
//!
//! Each test drives one arithmetic site directly. The end-to-end diagnostic is
//! covered by the CLI suite; these pin the layer where the panic lived, so a
//! regression is attributed to the operation rather than to "check aborts".

use rustledger_core::cost::Cost;
use rustledger_core::{Amount, Decimal, Inventory, Position};
use std::str::FromStr;

/// Units large enough that `units * cost` leaves `Decimal`'s range while
/// neither operand is near it on its own — the case that a `checked_add`-only
/// fix would have missed.
fn big_units() -> Decimal {
    Decimal::from_str("10000000000000000").expect("literal")
}

fn big_cost() -> Decimal {
    Decimal::from_str("10000000000000").expect("literal")
}

/// `add` — the running units cache (the site in the original report).
#[test]
fn add_saturates_and_flags_instead_of_panicking() {
    let mut inv = Inventory::new();
    inv.add(Position::simple(Amount::new(Decimal::MAX, "USD")));
    assert!(!inv.overflowed(), "one MAX position fits");

    inv.add(Position::simple(Amount::new(Decimal::MAX, "USD")));
    assert!(
        inv.overflowed(),
        "the sum of two MAX positions cannot be represented and must be marked"
    );
}

/// `try_add` — the same operation, reported rather than merely recorded.
///
/// This is what the booking engine calls, so this is the assertion that
/// connects the saturation to a user-visible diagnostic.
#[test]
fn try_add_reports_the_overflow() {
    let mut inv = Inventory::new();
    inv.try_add(Position::simple(Amount::new(Decimal::MAX, "USD")))
        .expect("first add fits");

    let err = inv
        .try_add(Position::simple(Amount::new(Decimal::MAX, "USD")))
        .expect_err("the second must report, not saturate silently");
    let msg = err.to_string();
    assert!(
        msg.contains("overflow") && msg.contains("USD"),
        "the message must name the overflow and the currency: {msg}"
    );
}

/// `add` merging into an existing simple position (the second site in `add`).
#[test]
fn merging_into_an_existing_position_saturates() {
    let mut inv = Inventory::new();
    // Two adds of the same currency with no cost merge in place.
    inv.add(Position::simple(Amount::new(Decimal::MAX, "USD")));
    inv.add(Position::simple(Amount::new(Decimal::MAX, "USD")));
    assert!(inv.overflowed());
    // And the process is still alive to assert it.
    assert_eq!(inv.units("USD"), Decimal::MAX, "clamped, not wrapped");
}

/// `at_cost` — a MULTIPLICATION, not an addition.
///
/// Fixing only the additions would have moved the panic here rather than
/// removing it: this overflows on inputs far below `Decimal::MAX`.
#[test]
fn at_cost_multiplication_saturates() {
    let mut inv = Inventory::new();
    inv.add(Position::with_cost(
        Amount::new(big_units(), "HOOL"),
        Cost::new(big_cost(), "USD"),
    ));
    let at = inv.at_cost();
    assert!(
        at.overflowed(),
        "units * cost leaves the range and must be marked"
    );
}

/// `book_value` — reaches `Cost::total_cost`, a further multiplication site.
#[test]
fn book_value_multiplication_saturates() {
    let mut inv = Inventory::new();
    inv.add(Position::with_cost(
        Amount::new(big_units(), "HOOL"),
        Cost::new(big_cost(), "USD"),
    ));
    // The assertion is simply that this returns rather than aborting; the
    // figure it returns is clamped and is not meaningful.
    let totals = inv.book_value("HOOL");
    assert_eq!(totals.len(), 1, "one cost currency");
}

/// Ordinary amounts are untouched — the checked arithmetic must not perturb
/// any value that fits, which is every real ledger.
#[test]
fn normal_arithmetic_is_unchanged_and_unflagged() {
    let mut inv = Inventory::new();
    inv.add(Position::simple(Amount::new(
        Decimal::from_str("100.50").expect("literal"),
        "USD",
    )));
    inv.add(Position::simple(Amount::new(
        Decimal::from_str("-40.25").expect("literal"),
        "USD",
    )));
    assert_eq!(
        inv.units("USD"),
        Decimal::from_str("60.25").expect("literal")
    );
    assert!(
        !inv.overflowed(),
        "a ledger that fits must never be marked — the flag is what makes a \
         clamped figure detectable, so a false positive would condemn good data"
    );

    let mut costed = Inventory::new();
    costed.add(Position::with_cost(
        Amount::new(Decimal::from_str("10").expect("literal"), "HOOL"),
        Cost::new(Decimal::from_str("150.00").expect("literal"), "USD"),
    ));
    let at = costed.at_cost();
    assert!(!at.overflowed());
    assert_eq!(
        at.units("USD"),
        Decimal::from_str("1500.00").expect("literal"),
        "10 * 150.00"
    );
}

/// Negative overflow clamps downward, not upward.
///
/// A sign error here would turn a huge liability into a huge asset — worse
/// than the panic, since nothing would look wrong.
#[test]
fn negative_overflow_clamps_to_min() {
    let mut inv = Inventory::new();
    inv.add(Position::simple(Amount::new(Decimal::MIN, "USD")));
    inv.add(Position::simple(Amount::new(Decimal::MIN, "USD")));
    assert!(inv.overflowed());
    assert_eq!(
        inv.units("USD"),
        Decimal::MIN,
        "two large negatives must clamp to MIN, not MAX"
    );
}
