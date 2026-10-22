//! Under `option "infer_tolerance_from_cost"`, each cost or price contributes
//! at most beancount's `MAXIMUM_TOLERANCE` (0.5) to its currency's tolerance
//! (#2717).
//!
//! Beancount's `interpolate.infer_tolerances` caps every contribution,
//! `min(tolerance * number, MAXIMUM_TOLERANCE)`, before summing them per
//! currency. rledger summed them uncapped, so `10.0 X {100000 USD}` allowed
//! 5,000 USD of imbalance where beancount allows 0.5. Every verdict below is
//! bean-check's (beancount 3.2.3) on the same ledger, and every interpolated
//! number is what `bean-query` prints for it.

use rust_decimal::Decimal;
use rustledger_core::Directive;
use rustledger_loader::{Ledger, LoadOptions, load};
use std::io::Write;
use std::str::FromStr;

fn load_source(source: &str) -> Ledger {
    let mut f = tempfile::Builder::new()
        .prefix("tolerance-cost-cap-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    load(f.path(), &LoadOptions::default()).expect("the ledger loads")
}

const FROM_COST: &str = "option \"infer_tolerance_from_cost\" \"TRUE\"\n";

const OPENS: &str = "\
2026-01-01 open Assets:Broker
2026-01-01 open Assets:Cash
";

/// Whether the one transaction `postings` make balances, under `options`
/// (on top of `infer_tolerance_from_cost`).
fn balances(options: &str, postings: &str) -> bool {
    let ledger = load_source(&format!(
        "{FROM_COST}{options}{OPENS}\n2026-01-02 * \"t\"\n{postings}"
    ));
    let other: Vec<&str> = ledger
        .errors
        .iter()
        .map(|e| e.message.as_str())
        .filter(|m| !m.contains("does not balance"))
        .collect();
    assert!(other.is_empty(), "unexpected errors: {other:#?}");
    ledger.errors.is_empty()
}

/// The issue's ledger: a 5,000 USD uncapped tolerance, 0.5 capped.
#[test]
fn a_cost_contribution_is_capped() {
    assert!(!balances(
        "",
        "  Assets:Broker  10.0 X {100000 USD}\n  Assets:Cash  -999900 USD\n"
    ));
    assert!(balances(
        "",
        "  Assets:Broker  10.0 X {100000 USD}\n  Assets:Cash  -999999.6 USD\n"
    ));
}

#[test]
fn a_price_contribution_is_capped() {
    assert!(!balances(
        "",
        "  Assets:Broker  10.0 X @ 100000 USD\n  Assets:Cash  -999900 USD\n"
    ));
}

/// The cap is per contribution, not on the sum: three capped 0.5s are 1.5.
#[test]
fn capped_contributions_still_sum() {
    let three = |cash: &str| {
        format!(
            "  Assets:Broker  1.0 X {{100 USD}}\n  Assets:Broker  1.0 Y {{100 USD}}\n\
             \x20 Assets:Broker  1.0 Z {{100 USD}}\n  Assets:Cash  {cash} USD\n"
        )
    };
    assert!(balances("", &three("-298.8")));
    assert!(!balances("", &three("-298.4")));
    // A cost and a price in one currency: 0.5 + 0.5.
    assert!(balances(
        "",
        "  Assets:Broker  1.5 X {100 USD} @ 120 USD\n  Assets:Cash  -149.1 USD\n"
    ));
}

/// Under the cap nothing changes: `0.05 x 2 = 0.1`.
#[test]
fn a_small_contribution_is_unchanged() {
    assert!(balances(
        "",
        "  Assets:Broker  1.5 X {2 USD}\n  Assets:Cash  -2.92 USD\n"
    ));
    assert!(!balances(
        "",
        "  Assets:Broker  1.5 X {2 USD}\n  Assets:Cash  -2.88 USD\n"
    ));
}

#[test]
fn the_cap_applies_after_the_multiplier() {
    let three = "option \"tolerance_multiplier\" \"3\"\n";
    // 0.3 x 1 = 0.3, under the cap.
    assert!(balances(
        three,
        "  Assets:Broker  1.5 X {1 USD}\n  Assets:Cash  -1.25 USD\n"
    ));
    // 0.3 x 10 = 3, capped to 0.5.
    assert!(!balances(
        three,
        "  Assets:Broker  1.5 X {10 USD}\n  Assets:Cash  -14.4 USD\n"
    ));
}

#[test]
fn inferred_tolerance_default_is_not_capped() {
    // A named default is a floor of its own, past the cap.
    assert!(balances(
        "option \"inferred_tolerance_default\" \"USD:2\"\n",
        "  Assets:Broker  10.0 X {100000 USD}\n  Assets:Cash  -999998.5 USD\n"
    ));
    // `*` is only a fallback: the capped 0.5 is USD's tolerance.
    assert!(!balances(
        "option \"inferred_tolerance_default\" \"*:2\"\n",
        "  Assets:Broker  10.0 X {100000 USD}\n  Assets:Cash  -999999 USD\n"
    ));
}

/// Beancount's parser turns `@@ 3 USD` over 1.5 units into `@ 2 USD`, so the
/// price contributes `0.05 x 2 = 0.1`; rledger used the total, 0.15.
#[test]
fn a_total_price_contributes_its_per_unit_price() {
    assert!(!balances(
        "",
        "  Assets:Broker  1.5 X @@ 3 USD\n  Assets:Cash  -2.88 USD\n"
    ));
    assert!(balances(
        "",
        "  Assets:Broker  1.5 X @@ 3 USD\n  Assets:Cash  -2.92 USD\n"
    ));
}

/// A total or compound cost is checked by its booked per-unit cost, capped.
#[test]
fn total_and_compound_costs_are_capped() {
    assert!(!balances(
        "",
        "  Assets:Broker  1.5 X {{300 USD}}\n  Assets:Cash  -299.4 USD\n"
    ));
    assert!(balances(
        "",
        "  Assets:Broker  1.5 X {{300 USD}}\n  Assets:Cash  -299.6 USD\n"
    ));
    assert!(!balances(
        "",
        "  Assets:Broker  1.5 X {100 # 10 USD}\n  Assets:Cash  -159.4 USD\n"
    ));
}

/// Interpolation rounds to the grid of the capped tolerance: 0.5 rounds to
/// whole USD where the uncapped 10.000005 rounded nothing. A total cost as
/// written contributes `min(0, 0.05 x total)` (beancount's parser reads
/// `{{T}}` as `number_per = 0`), so it leaves its currency unrounded.
#[test]
fn interpolation_rounds_to_the_capped_tolerance() {
    let ledger = load_source(&format!(
        "{FROM_COST}{OPENS}\
         2026-01-02 * \"capped\"\n  Assets:Broker  1.5 X {{200.0001 USD}}\n  Assets:Cash\n\
         2026-01-02 * \"uncapped\"\n  Assets:Broker  1.5 Y {{2.0001 USD}}\n  Assets:Cash\n\
         2026-01-02 * \"total cost\"\n  Assets:Broker  1.5 Z {{{{300.00015 USD}}}}\n  Assets:Cash\n\
         2026-01-02 * \"total price\"\n  Assets:Broker  1.5 W @@ 300.00015 USD\n  Assets:Cash\n\
         2026-01-02 * \"unit price\"\n  Assets:Broker  1.5 V @ 200.0001 USD\n  Assets:Cash\n"
    ));
    assert!(ledger.errors.is_empty(), "{:#?}", ledger.errors);
    let filled: Vec<(String, Decimal)> = ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .map(|t| {
            let cash = t
                .postings
                .iter()
                .find(|p| p.account.as_str() == "Assets:Cash")
                .and_then(|p| p.amount())
                .expect("Assets:Cash filled");
            (t.narration.to_string(), cash.number)
        })
        .collect();
    let d = |s: &str| Decimal::from_str(s).unwrap();
    assert_eq!(
        filled,
        vec![
            ("capped".to_string(), d("-300")),
            ("uncapped".to_string(), d("-3.00015")),
            ("total cost".to_string(), d("-300.00015")),
            ("total price".to_string(), d("-300")),
            ("unit price".to_string(), d("-300")),
        ]
    );
}

/// A cost spec naming only its currency is beancount's `CostSpec` with no
/// number, which contributes the cap itself, 0.5, before booking. So the
/// elided cash of a `{USD}` sale rounds to whole USD, `11` where the lot's
/// cost is 11.00055, as bean-query shows; `{}` names no currency and leaves
/// it exact.
#[test]
fn a_currency_only_cost_spec_contributes_the_cap() {
    let ledger = load_source(&format!(
        "{FROM_COST}{OPENS}\
         2026-01-01 * \"buy\"\n  Assets:Broker  10.5 X {{2.0001 USD}}\n  Assets:Cash  -21.00105 USD\n\
         2026-01-01 * \"buy\"\n  Assets:Broker  10.5 Y {{2.0001 USD}}\n  Assets:Cash  -21.00105 USD\n\
         2026-01-02 * \"currency only\"\n  Assets:Broker  -5.5 X {{USD}}\n  Assets:Cash\n\
         2026-01-02 * \"empty\"\n  Assets:Broker  -5.5 Y {{}}\n  Assets:Cash\n"
    ));
    assert!(ledger.errors.is_empty(), "{:#?}", ledger.errors);
    let sold: Vec<(String, Decimal)> = ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Transaction(t) if t.narration.as_str() != "buy" => Some(t),
            _ => None,
        })
        .map(|t| {
            let cash = t
                .postings
                .iter()
                .find(|p| p.account.as_str() == "Assets:Cash")
                .and_then(|p| p.amount())
                .expect("Assets:Cash filled");
            (t.narration.to_string(), cash.number)
        })
        .collect();
    let d = |s: &str| Decimal::from_str(s).unwrap();
    assert_eq!(
        sold,
        vec![
            ("currency only".to_string(), d("11")),
            ("empty".to_string(), d("11.00055")),
        ]
    );
}
