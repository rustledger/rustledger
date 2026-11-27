//! A lot bought at a total or compound cost (`{{T}}`, `{a # b}`) is weighed
//! at its exact total when it is sold whole, as a total price is (#2831): the
//! balance is checked exactly, never against the rounded per-unit cost.
//!
//! Both pinned here are documented in `docs/reference/compatibility.md`
//! ("Total Prices and Total Costs That Do Not Divide Evenly").

use rustledger_core::Directive;
use rustledger_loader::{Ledger, LoadOptions, load};
use std::io::Write;

fn load_source(source: &str) -> Ledger {
    let mut f = tempfile::Builder::new()
        .prefix("exact-lot-total-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    load(f.path(), &LoadOptions::default()).expect("the ledger loads")
}

/// A whole sale of a compound-cost lot whose exact residual is `-0.005`,
/// exactly the transaction's tolerance: balanced, as bean-check 3.2.3 finds
/// it. The per-unit cost `95.13896103896103896103896104` is rounded up, and
/// the balance weighed `19.25` of it, `1831.42500000000000000000000002`, so
/// the residual went `2e-26` past the tolerance and rledger reported
/// `E3001`. The sale now carries the lot's exact total, and the residual is
/// computed exactly.
#[test]
fn a_whole_sale_of_a_compound_lot_balances_at_the_tolerance_edge() {
    let ledger = load_source(
        "2024-01-01 open Assets:Cash
2024-01-01 open Income:Gains
2024-01-02 open Assets:Broker
2024-01-02 *
  Assets:Broker  4 VTI {125.51 USD, \"lot1\"}
  Assets:Broker  19.25 VTI {94.94 # 3.83 USD}
  Assets:Cash
2024-01-05 *
  Assets:Broker  -23.25 VTI {} @ 163.92 USD
  Assets:Cash  3811.14 USD
  Income:Gains
",
    );
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);
}

/// A residual just past the tolerance is still refused: the check is exact,
/// not lax. The same sale with the gain stated a cent short is off by `0.015`.
#[test]
fn an_exact_residual_past_the_tolerance_is_still_an_error() {
    let ledger = load_source(
        "2024-01-01 open Assets:Cash
2024-01-01 open Income:Gains
2024-01-02 open Assets:Broker
2024-01-02 *
  Assets:Broker  4 VTI {125.51 USD, \"lot1\"}
  Assets:Broker  19.25 VTI {94.94 # 3.83 USD}
  Assets:Cash
2024-01-05 *
  Assets:Broker  -23.25 VTI {} @ 163.92 USD
  Assets:Cash  3811.14 USD
  Income:Gains  -1477.66 USD
",
    );
    let codes: Vec<&str> = ledger.errors.iter().map(|e| e.code.as_str()).collect();
    assert_eq!(codes, ["E3001"], "{:?}", ledger.errors);
}

/// The deliberate half: an elided gain interpolated from the exact total.
/// `17.125 ACME {286.04 # 2.75 USD}` sold whole at `80.23` against `1373.94`
/// cash leaves a gain of exactly `3527.245`, which rounds half-even to
/// `3527.24`. Beancount weighs its rounded per-unit cost, making the gain
/// `3527.245000000000000000000001`, and books `3527.25`.
#[test]
fn an_interpolated_gain_at_a_half_cent_tie_rounds_the_exact_total() {
    let ledger = load_source(
        "2024-01-01 open Assets:Cash
2024-01-01 open Income:Gains
2024-01-09 open Assets:Broker
2024-01-09 *
  Assets:Broker  17.125 ACME {286.04 # 2.75 USD}
  Assets:Cash
2024-01-12 *
  Assets:Broker  -17.125 ACME {} @ 80.23 USD
  Assets:Cash  1373.94 USD
  Income:Gains
",
    );
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);
    let gain = ledger
        .directives
        .iter()
        .filter_map(|s| match &s.value {
            Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .next_back()
        .and_then(|t| {
            t.postings
                .iter()
                .find(|p| p.value.account.as_str() == "Income:Gains")
        })
        .and_then(|p| p.value.units.as_ref())
        .map(ToString::to_string);
    assert_eq!(gain.as_deref(), Some("3527.24 USD"));
}
