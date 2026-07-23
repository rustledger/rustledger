//! Returns over **imperfect / imported** ledgers — the net-units capability that
//! #1850 targets (beangrow parity, and where we exceed it).
//!
//! Money-weighted (XIRR) and time-weighted returns depend on cash flows and
//! terminal **market** value (`net units × price`), never on cost-basis lots. So a
//! cost-basis / lot error — an over-sell, an empty-cost `{}` sale with no matching
//! lot, a missing opening buy — must NOT block the report: net-units simply sums
//! the units (possibly negative) and values at market, like beancount + beangrow.
//! `rledger check` remains the validator. These tests exercise that through the
//! shared [`scope_returns`] / [`scopes_returns`] composition (the exact path the
//! CLI `report returns` and the component `session.returns` take), so they also
//! pin the real `PriceDatabase` price resolution.
//!
//! Where we deliberately **exceed** beangrow: it crashes on falling prices /
//! negative returns ("complex rate of return", beangrow#4 / beangrow#16); our
//! Newton+Brent `xirr` returns a real `Option<f64>`. Those cases are marked below.

use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use rustledger_core::{
    Amount, CostNumber, CostSpec, Directive, NaiveDate, Posting, Price, Transaction, naive_date,
};
use rustledger_query::{scope_returns, scopes_returns};
use rustledger_returns::{ExtractError, Scope};

fn d(y: i32, m: u32, day: u32) -> NaiveDate {
    naive_date(y, m, day).unwrap()
}

fn amt(n: Decimal, ccy: &str) -> Amount {
    Amount::new(n, ccy)
}

/// A `{per_unit USD}` cost spec (also seeds an implicit price at the txn date).
fn cost(per_unit: Decimal) -> CostSpec {
    CostSpec::empty()
        .with_number(CostNumber::PerUnit { value: per_unit })
        .with_currency("USD")
}

fn txn(date: NaiveDate, postings: Vec<Posting>) -> Directive {
    let mut t = Transaction::new(date, "");
    for p in postings {
        t = t.with_synthesized_posting(p);
    }
    Directive::Transaction(t)
}

fn broker_scope() -> Scope {
    Scope::new(vec!["Assets:Broker".to_string()], vec![])
}

/// Over-selling an empty-cost `{}` lot (the common "No position matches" state of
/// imported brokerage data) is tolerated: buying 5 then reducing 10 nets to −5
/// units, valued at the terminal market price (−5 × 120 = −600). No trap, no
/// refusal — `rledger check` is the validator, not the returns report.
#[test]
fn over_sell_nets_negative_and_values_at_market() {
    let dirs = vec![
        txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(5), "AAPL"))
                    .with_cost(cost(dec!(100))),
                Posting::new("Assets:Bank", amt(dec!(-500), "USD")),
            ],
        ),
        txn(
            d(2020, 6, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(-10), "AAPL"))
                    .with_cost(CostSpec::empty()),
                Posting::new("Assets:Bank", amt(dec!(1000), "USD")),
            ],
        ),
        Directive::Price(Price::new(d(2020, 12, 31), "AAPL", amt(dec!(120), "USD"))),
    ];
    let r = scope_returns(&dirs, &broker_scope(), "USD", d(2020, 12, 31))
        .expect("over-sell is tolerated by net-units valuation");
    assert_eq!(r.current_value, dec!(-600), "net −5 AAPL × 120");
    assert_eq!(r.invested, dec!(500));
    assert_eq!(r.distributions, dec!(1000));
}

/// A **missing opening buy** — an importer that started mid-history, so only the
/// sale is in the ledger — leaves a short net position, valued at market. beangrow
/// handles this (net `add_position`); the strict-clean design (#1849) blocked it.
#[test]
fn missing_opening_buy_yields_short_position() {
    let dirs = vec![
        // Sell 10 with no prior buy: net −10 AAPL, +1200 cash.
        txn(
            d(2020, 3, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(-10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(1200), "USD")),
            ],
        ),
        Directive::Price(Price::new(d(2020, 12, 31), "AAPL", amt(dec!(100), "USD"))),
    ];
    let r = scope_returns(&dirs, &broker_scope(), "USD", d(2020, 12, 31))
        .expect("a missing opening buy nets short, valued at market");
    assert_eq!(r.current_value, dec!(-1000), "net −10 AAPL × 100");
    assert_eq!(r.invested, dec!(0));
    assert_eq!(r.distributions, dec!(1200));
}

/// An empty-cost `{}` sale that DOES reduce a held lot cleanly values identically
/// under net-units (which never lot-matches): buy 10, sell 4 → net 6 × 130 = 780.
#[test]
fn empty_cost_sale_reducing_cleanly_values_net_units() {
    let dirs = vec![
        txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL"))
                    .with_cost(cost(dec!(100))),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        ),
        txn(
            d(2020, 6, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(-4), "AAPL"))
                    .with_cost(CostSpec::empty()),
                Posting::new("Assets:Bank", amt(dec!(520), "USD")),
            ],
        ),
        Directive::Price(Price::new(d(2020, 12, 31), "AAPL", amt(dec!(130), "USD"))),
    ];
    let r = scope_returns(&dirs, &broker_scope(), "USD", d(2020, 12, 31))
        .expect("a clean empty-cost reduction values via net units");
    assert_eq!(r.current_value, dec!(780), "net 6 AAPL × 130");
}

/// **Falling prices → a real negative return.** beangrow *crashes* here ("complex
/// rate of return", beangrow#4 / beangrow#16); our Newton+Brent `xirr` returns a
/// genuine negative rate. Buy 10 @ 100 (−1000), worth 50 a year later (+500) →
/// ≈ −50%/yr, money- and time-weighted alike. This is a place we exceed beangrow.
#[test]
fn falling_prices_give_a_real_negative_return_not_a_crash() {
    let dirs = vec![
        txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL"))
                    .with_cost(cost(dec!(100))),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        ),
        Directive::Price(Price::new(d(2021, 1, 1), "AAPL", amt(dec!(50), "USD"))),
    ];
    let r = scope_returns(&dirs, &broker_scope(), "USD", d(2021, 1, 1))
        .expect("falling prices compute, they do not crash");
    assert_eq!(r.current_value, dec!(500), "net 10 AAPL × 50");
    let mwr = r
        .money_weighted
        .expect("a real negative money-weighted rate");
    assert!((-0.55..=-0.45).contains(&mwr), "≈ −50%/yr, got {mwr}");
    let twr = r.time_weighted.expect("a real negative time-weighted rate");
    assert!((-0.55..=-0.45).contains(&twr), "≈ −50%/yr, got {twr}");
}

/// A **near-total loss** stays defined (large negative), never a crash: buy 10 @
/// 100 (−1000), worth 0.01 each at the horizon (+0.10) → ≈ −100%/yr.
#[test]
fn near_total_loss_returns_a_defined_rate() {
    let dirs = vec![
        txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL"))
                    .with_cost(cost(dec!(100))),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        ),
        Directive::Price(Price::new(d(2021, 1, 1), "AAPL", amt(dec!(0.01), "USD"))),
    ];
    let r = scope_returns(&dirs, &broker_scope(), "USD", d(2021, 1, 1))
        .expect("a near-total loss computes");
    assert_eq!(r.current_value, dec!(0.10));
    let mwr = r.money_weighted.expect("defined, not a crash");
    assert!(mwr < -0.9, "near-total loss ≈ −100%, got {mwr}");
}

/// **Missing-price policy (§5):** a commodity with no price until a *late* explicit
/// `price` directive still yields a money-weighted return (terminal is priced), but
/// the time-weighted chain — which needs a price at every flow date — degrades to
/// `None` rather than erroring the whole summary. The buy carries no cost, so it
/// seeds no implicit price; AAPL is unpriced before the terminal date.
#[test]
fn missing_intermediate_price_degrades_twr_not_mwr() {
    let scope = Scope::new(
        vec!["Assets:Broker".to_string()],
        vec!["Income:Dividends".to_string()],
    );
    let dirs = vec![
        // Buy 10 AAPL for 1000 USD cash with NO cost/price → AAPL stays unpriced.
        txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Stock", amt(dec!(10), "AAPL")),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        ),
        txn(
            d(2020, 6, 1),
            vec![
                Posting::new("Assets:Bank", amt(dec!(20), "USD")),
                Posting::new("Income:Dividends", amt(dec!(-20), "USD")),
            ],
        ),
        // The FIRST (and only) AAPL price is at the horizon.
        Directive::Price(Price::new(d(2020, 12, 31), "AAPL", amt(dec!(130), "USD"))),
    ];
    let r = scope_returns(&dirs, &scope, "USD", d(2020, 12, 31))
        .expect("the terminal is priced, so the summary is well-defined");
    assert_eq!(r.current_value, dec!(1300), "net 10 AAPL × 130");
    assert!(
        r.money_weighted.is_some_and(|m| m > 0.0),
        "money-weighted computes from cash flows + priced terminal: {:?}",
        r.money_weighted
    );
    assert!(
        r.time_weighted.is_none(),
        "a missing intermediate price degrades TWR to None, got {:?}",
        r.time_weighted
    );
}

/// Per-scope isolation at the shared-composition level (what `--by-group` relies
/// on, #1850 §4): one scope with an elided in-scope posting fails alone
/// (`UnvaluableInput`), while a clean scope computes — over ONE shared accumulation.
/// A cost-basis/lot error in one scope never touches another.
#[test]
fn scopes_are_isolated_one_unvaluable_others_compute() {
    let dirs = vec![
        // Clean group: buy 10 @ 100, worth 130.
        txn(
            d(2020, 1, 1),
            vec![
                Posting::new("Assets:Broker:Clean", amt(dec!(10), "AAPL"))
                    .with_cost(cost(dec!(100))),
                Posting::new("Assets:Bank", amt(dec!(-1000), "USD")),
            ],
        ),
        // Broken group: an elided in-scope leg → net units unknown → unvaluable.
        txn(
            d(2020, 3, 1),
            vec![
                Posting::auto("Assets:Broker:Broken"),
                Posting::new("Assets:Bank", amt(dec!(-500), "USD")),
            ],
        ),
        Directive::Price(Price::new(d(2020, 12, 31), "AAPL", amt(dec!(130), "USD"))),
    ];
    let clean = Scope::new(vec!["Assets:Broker:Clean".to_string()], vec![]);
    let broken = Scope::new(vec!["Assets:Broker:Broken".to_string()], vec![]);
    let results = scopes_returns(&dirs, &[clean, broken], "USD", d(2020, 12, 31));
    assert_eq!(
        results[0]
            .as_ref()
            .expect("clean scope computes")
            .current_value,
        dec!(1300),
    );
    assert!(
        matches!(results[1], Err(ExtractError::UnvaluableInput(_))),
        "the elided scope fails alone: {:?}",
        results[1]
    );
}
