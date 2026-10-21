//! A `{{total}}` cost spread over very many units books (#2689).
//!
//! `1.00 USD` over `30000000000` units is `3.333…E-11` a unit: 28 significant
//! digits to beancount, but only 17 in a `Decimal`'s 28 decimal places, so
//! `per-unit × units` misses the total by ~1e-18. `BookedCost`'s consistency
//! check read that as an inconsistent pair and booking refused the posting as
//! "amount exceeds the representable range". The booked cost keeps the exact
//! total beside the per-unit (#2427), so nothing is lost by accepting it.
//!
//! Verdicts are bean-check's (beancount 3.2.3) except where noted, and the
//! cost and weight figures are what bean-query prints for the same ledger.

use rust_decimal::Decimal;
use rustledger_core::{CostNumber, Directive, Transaction};
use rustledger_loader::{Ledger, LoadOptions, load};
use std::io::Write;
use std::str::FromStr;

fn load_source(source: &str) -> Ledger {
    let mut f = tempfile::Builder::new()
        .prefix("tiny-per-unit-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    load(f.path(), &LoadOptions::default()).expect("the ledger loads")
}

const OPENS: &str = "\
2026-01-01 open Assets:Broker
2026-01-01 open Assets:Cash
";

fn ledger(body: &str) -> Ledger {
    load_source(&format!("{OPENS}{body}"))
}

fn messages(ledger: &Ledger) -> Vec<String> {
    ledger.errors.iter().map(|e| e.message.clone()).collect()
}

fn d(s: &str) -> Decimal {
    Decimal::from_str(s).unwrap()
}

fn transactions(ledger: &Ledger) -> impl Iterator<Item = &Transaction> {
    ledger.directives.iter().filter_map(|d| match &d.value {
        Directive::Transaction(t) => Some(t),
        _ => None,
    })
}

/// The `(per_unit, total)` booked on the first transaction's first posting.
fn booked_cost(ledger: &Ledger) -> (Decimal, Decimal) {
    let txn = transactions(ledger).next().expect("a transaction");
    match txn.postings[0].cost.as_deref().and_then(|c| c.number) {
        Some(CostNumber::PerUnitFromTotal(b)) => (b.per_unit, b.total),
        other => panic!("expected a booked total, got {other:?}"),
    }
}

const BUY: &str = "2026-01-02 * \"buy\"\n  Assets:Broker  30000000000 GGG {{1.00 USD}}\n  Assets:Cash  -1.00 USD\n";

#[test]
fn a_total_over_very_many_units_books_with_its_exact_total() {
    let l = ledger(BUY);
    assert!(l.errors.is_empty(), "{:#?}", messages(&l));
    let (per_unit, total) = booked_cost(&l);
    // The nearest `Decimal` to beancount's 3.333333333333333333333333333E-11.
    assert_eq!(per_unit, d("0.0000000000333333333333333333"));
    assert_eq!(total.to_string(), "1.00");
}

#[test]
fn every_shape_that_derives_a_tiny_per_unit_books() {
    for body in [
        // The cash elided: the total is still written.
        "2026-01-02 * \"t\"\n  Assets:Broker  30000000000 GGG {{1.00 USD}}\n  Assets:Cash\n",
        // A cost currency alone, solved from the cash.
        "2026-01-02 * \"t\"\n  Assets:Broker  30000000000 GGG {USD}\n  Assets:Cash  -1.00 USD\n",
        // A compound cost.
        "2026-01-02 * \"t\"\n  Assets:Broker  30000000000 GGG {0 # 1.00 USD}\n  Assets:Cash  -1.00 USD\n",
        // Fractional units.
        "2026-01-02 * \"t\"\n  Assets:Broker  12345678901.2345678 GGG {{1.00 USD}}\n  Assets:Cash  -1.00 USD\n",
    ] {
        let l = ledger(body);
        assert!(l.errors.is_empty(), "{body}\n{:#?}", messages(&l));
    }
}

#[test]
fn such_a_lot_is_matched_and_sold_at_its_exact_total() {
    for sale in [
        "2026-01-03 * \"sell all\"\n  Assets:Broker  -30000000000 GGG {}\n  Assets:Cash  1.00 USD\n\
         2026-01-04 balance Assets:Cash  0.00 USD\n",
        "2026-01-03 * \"sell half\"\n  Assets:Broker  -15000000000 GGG {}\n  Assets:Cash  0.50 USD\n\
         2026-01-04 balance Assets:Cash  -0.50 USD\n\
         2026-01-04 balance Assets:Broker  15000000000 GGG\n",
        // A total spec names the lot: the same division, the same per-unit.
        "2026-01-03 * \"sell by total\"\n  Assets:Broker  -30000000000 GGG {{1.00 USD}}\n  Assets:Cash  1.00 USD\n",
    ] {
        let l = ledger(&format!("{BUY}{sale}"));
        assert!(l.errors.is_empty(), "{sale}\n{:#?}", messages(&l));
    }
}

/// Deliberate divergence (correctness first): bean-check rejects the integer
/// form, `Transaction does not balance: (-1E-28 USD)`, only because its own
/// per-unit times the units misses `1` in the 28th place and integers give
/// no tolerance. The lot's exact total is `1 USD`, so the transaction
/// balances exactly, and rledger accepts it. See `BookedCost`'s invariant.
#[test]
fn the_integer_form_balances_exactly_and_books() {
    let l = ledger(
        "2026-01-02 * \"t\"\n  Assets:Broker  30000000000 GGG {{1 USD}}\n  Assets:Cash  -1 USD\n",
    );
    assert!(l.errors.is_empty(), "{:#?}", messages(&l));
    assert_eq!(booked_cost(&l).1, d("1"));
}

/// Below 1e-28 a unit there is no per-unit to record, and it is refused, by
/// name: the per-unit is too small, not an amount out of range. (beancount,
/// with unbounded exponents, accepts it; a lot at a per-unit of zero would be
/// a cost nobody wrote.)
#[test]
fn a_per_unit_below_the_smallest_decimal_is_refused_by_name() {
    for body in [
        "2026-01-02 * \"t\"\n  Assets:Broker  50000000000000000000000000000 GGG {{1 USD}}\n  Assets:Cash  -1 USD\n",
        "2026-01-02 * \"t\"\n  Assets:Broker  50000000000000000000000000000 GGG {USD}\n  Assets:Cash  -1 USD\n",
    ] {
        let l = ledger(body);
        let errors = messages(&l);
        assert_eq!(errors.len(), 1, "{body}\n{errors:#?}");
        assert!(
            errors[0].contains("per-unit cost of 1 USD over 50000000000000000000000000000 units")
                && errors[0].contains("below 1e-28"),
            "{errors:#?}"
        );
        assert!(!errors[0].contains("representable range"), "{errors:#?}");
    }
}
