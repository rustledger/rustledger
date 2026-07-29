//! `Decimal` overflow is REPORTED at the API level, never clamped (#1863).
//!
//! `rust_decimal` is 96-bit with a ~±7.9e28 ceiling and its `+`/`*` panic on
//! overflow. The CLI-level behavior is pinned in
//! `rustledger/tests/decimal_overflow_test.rs`; this file pins the core API
//! contracts those depend on, including the ones no ledger can currently
//! reach through the CLI.
//!
//! # Why not saturate
//!
//! Saturation was implemented and rejected (PR #1890). `Decimal::MIN` is
//! exactly `-Decimal::MAX`, so clamped opposite-sign values cancel to zero and
//! an arbitrarily unbalanced ledger certifies as clean. The assertion in
//! `min_is_exactly_negative_max` pins the property that makes clamping unsound,
//! so anyone reaching for `saturating_*` here meets the reason first.

use rustledger_core::cost::Cost;
use rustledger_core::{Amount, Decimal, Inventory, Position};
use std::str::FromStr;

/// Units and cost that each fit comfortably but whose PRODUCT does not — a
/// product needs roughly the sum of its operands' digits. A `checked_add`-only
/// fix would sail past this.
fn big_units() -> Decimal {
    Decimal::from_str("10000000000000000").expect("literal")
}

fn big_cost() -> Decimal {
    Decimal::from_str("10000000000000").expect("literal")
}

/// The property that makes saturation unsound. If this ever fails, clamping
/// would become merely lossy rather than actively misleading — but it holds
/// for `rust_decimal` and is the reason this whole fix is `checked_*`.
#[test]
fn min_is_exactly_negative_max() {
    assert_eq!(
        Decimal::MIN,
        -Decimal::MAX,
        "clamped debits and credits cancel to exactly zero, so a saturating \
         residual cannot distinguish a real balance from an overflowed one"
    );
    assert_eq!(
        Decimal::MAX.saturating_add(Decimal::MIN),
        Decimal::ZERO,
        "this is the sum that made a 1e40 imbalance pass `check` in PR #1890"
    );
}

#[test]
fn add_reports_overflow_instead_of_panicking() {
    let mut inv = Inventory::new();
    inv.add(Position::simple(Amount::new(Decimal::MAX, "USD")))
        .expect("one MAX position fits");

    let err = inv
        .add(Position::simple(Amount::new(Decimal::MAX, "USD")))
        .expect_err("the second cannot be represented and must be reported");
    assert_eq!(
        err.currency.as_str(),
        "USD",
        "the message must name the currency"
    );
}

/// A rejected `add` must not half-apply: BOTH running totals are computed
/// before either is committed.
///
/// The two can fail independently. `units_cache` tracks every position of the
/// currency; the merge target holds only the uncosted ones. A costed `+MAX`
/// against an uncosted `-MAX` nets the cache to zero while the merge target
/// sits at `-MAX`, so adding `-1` more overflows the MERGE while the cache
/// still fits — the ordering this test exists to pin. (Written after an
/// earlier version of it passed with the commit deliberately moved before the
/// check, because the cache happened to fail first in that fixture.)
#[test]
fn a_rejected_add_leaves_the_inventory_unchanged() {
    let one = Decimal::from_str("1").expect("literal");
    let mut inv = Inventory::new();
    inv.add(Position::with_cost(
        Amount::new(Decimal::MAX, "HOOL"),
        Cost::new(one, "USD"),
    ))
    .expect("costed position fits");
    inv.add(Position::simple(Amount::new(Decimal::MIN, "HOOL")))
        .expect("cache nets to zero, uncosted total is MIN");

    assert_eq!(inv.units("HOOL"), Decimal::ZERO, "precondition: cache is 0");
    let positions_before = inv.positions().count();

    // Cache: 0 + (-1) fits. Merge target: MIN + (-1) overflows.
    inv.add(Position::simple(Amount::new(-one, "HOOL")))
        .expect_err("the uncosted merge leaves the range");

    assert_eq!(
        inv.units("HOOL"),
        Decimal::ZERO,
        "the units cache must not be committed when the merge fails"
    );
    assert_eq!(
        inv.positions().count(),
        positions_before,
        "no position may be appended by a failed add"
    );
}

/// `at_cost` multiplies, so it overflows on inputs far below the ceiling.
#[test]
fn at_cost_reports_the_product_overflow() {
    let mut inv = Inventory::new();
    inv.add(Position::with_cost(
        Amount::new(big_units(), "HOOL"),
        Cost::new(big_cost(), "USD"),
    ))
    .expect("the position itself fits");

    let err = inv.at_cost().expect_err("units * cost leaves the range");
    assert_eq!(
        err.currency.as_str(),
        "USD",
        "reported in the COST currency"
    );
}

/// `book_value` must not confuse "no cost" with "out of range".
///
/// It deliberately does not go through `Position::book_value`, whose `None`
/// means both. Skipping an overflowing position would silently drop it from
/// the total — the same class of defect as clamping it.
#[test]
fn book_value_distinguishes_uncosted_from_unrepresentable() {
    let mut costed = Inventory::new();
    costed
        .add(Position::with_cost(
            Amount::new(big_units(), "HOOL"),
            Cost::new(big_cost(), "USD"),
        ))
        .expect("fits");
    costed
        .book_value("HOOL")
        .expect_err("an out-of-range product must be reported");

    // An uncosted position is not an error — it contributes nothing.
    let mut uncosted = Inventory::new();
    uncosted
        .add(Position::simple(Amount::new(big_units(), "HOOL")))
        .expect("fits");
    let totals = uncosted
        .book_value("HOOL")
        .expect("no cost is not an overflow");
    assert!(totals.is_empty(), "an uncosted position has no book value");
}

/// `Cost::total_cost` is the shared multiplication behind book values and
/// reduction cost bases.
#[test]
fn total_cost_reports_rather_than_panicking() {
    let cost = Cost::new(big_cost(), "USD");
    assert!(
        cost.total_cost(big_units()).is_none(),
        "the product leaves the range"
    );
    let ok = cost
        .total_cost(Decimal::from_str("10").expect("literal"))
        .expect("an ordinary quantity fits");
    assert_eq!(
        ok.number,
        Decimal::from_str("100000000000000").expect("literal")
    );
}

/// The subtree sum behind balance assertions and pads. `Decimal`'s `Sum` impl
/// panics, so this had to stop using it.
#[test]
fn subtree_sum_reports_overflow() {
    use rustledger_core::{Account, Currency};

    let mut a = Inventory::new();
    a.add(Position::simple(Amount::new(Decimal::MAX, "USD")))
        .expect("fits");
    let mut b = Inventory::new();
    b.add(Position::simple(Amount::new(Decimal::MAX, "USD")))
        .expect("fits");

    let accounts = [
        (Account::from("Assets:Bank"), a),
        (Account::from("Assets:Bank:Sub"), b),
    ];
    let usd = Currency::from("USD");

    assert!(
        rustledger_core::sum_account_and_subaccounts(
            accounts.iter().map(|(k, v)| (k, v)),
            "Assets:Bank",
            &usd,
        )
        .is_none(),
        "two MAX sub-balances cannot be summed and must report, not panic"
    );
}

/// Ordinary ledgers — every real one — must be completely unaffected.
///
/// Without this, "report an overflow" would be satisfiable by reporting one
/// unconditionally.
#[test]
fn ordinary_arithmetic_is_untouched() {
    let mut inv = Inventory::new();
    inv.add(Position::simple(Amount::new(
        Decimal::from_str("100.50").expect("literal"),
        "USD",
    )))
    .expect("fits");
    inv.add(Position::simple(Amount::new(
        Decimal::from_str("-40.25").expect("literal"),
        "USD",
    )))
    .expect("fits");
    assert_eq!(
        inv.units("USD"),
        Decimal::from_str("60.25").expect("literal")
    );

    let mut costed = Inventory::new();
    costed
        .add(Position::with_cost(
            Amount::new(Decimal::from_str("10").expect("literal"), "HOOL"),
            Cost::new(Decimal::from_str("150.00").expect("literal"), "USD"),
        ))
        .expect("fits");
    let at = costed.at_cost().expect("an ordinary product fits");
    assert_eq!(
        at.units("USD"),
        Decimal::from_str("1500.00").expect("literal"),
        "10 * 150.00"
    );
}
