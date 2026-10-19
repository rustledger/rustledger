//! A per-unit number booking derives from a total is beancount's (#2652).
//!
//! beancount divides `total / |units|` with Python's `decimal` (28
//! significant digits, half to even, the ideal exponent for an exact
//! quotient); booking divided with `rust_decimal`, so `4 X {{10 USD}}` booked
//! `2.50` where beancount books `2.5`, and `3 X {{10 USD}}` booked
//! `3.3333333333333333333333333333` where beancount books
//! `3.333333333333333333333333333`. Every expected string below is what
//! `bean-query` (beancount 3.2.3) prints for `str(cost_number)` /
//! `str(number(price))` on the same ledger, except where noted.
//!
//! What must NOT move is checked too: a lot's exact total, the sums its sales
//! add up to, and lot matching, which compares by value (`2.5 == 2.50`).

use rustledger_core::{CostNumber, Directive, PriceKind, Transaction};
use rustledger_loader::{Ledger, LoadOptions, load};
use std::io::Write;

fn load_source(source: &str) -> Ledger {
    let mut f = tempfile::Builder::new()
        .prefix("per-unit-python-division-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    load(f.path(), &LoadOptions::default()).expect("the ledger loads")
}

fn no_errors(ledger: &Ledger) {
    let errors: Vec<String> = ledger.errors.iter().map(|e| format!("{e:?}")).collect();
    assert!(errors.is_empty(), "{errors:#?}");
}

fn transactions(ledger: &Ledger) -> impl Iterator<Item = &Transaction> {
    ledger.directives.iter().filter_map(|d| match &d.value {
        Directive::Transaction(t) => Some(t),
        _ => None,
    })
}

/// The booked per-unit cost and per-unit price of the transaction's first
/// posting in `currency`, as `str()` renders them.
fn booked(ledger: &Ledger, narration: &str, currency: &str) -> (Option<String>, Option<String>) {
    let txn = transactions(ledger)
        .find(|t| t.narration.as_str() == narration)
        .unwrap_or_else(|| panic!("no transaction {narration:?}"));
    let posting = txn
        .postings
        .iter()
        .find(|p| p.amount().is_some_and(|a| a.currency.as_str() == currency))
        .unwrap_or_else(|| panic!("{narration}: no {currency} posting"));
    let cost = posting.cost.as_deref().and_then(|c| match c.number? {
        CostNumber::PerUnit { value } => Some(value.to_string()),
        CostNumber::PerUnitFromTotal(b) => Some(b.per_unit.to_string()),
        CostNumber::Total { .. } | CostNumber::Compound { .. } => {
            panic!("{narration}: cost left unbooked: {c:?}")
        }
    });
    let price = posting.price.as_deref().map(|p| {
        assert_eq!(
            p.kind,
            PriceKind::Unit,
            "{narration}: price left as a total"
        );
        p.amount
            .as_ref()
            .and_then(|a| a.as_amount())
            .expect("a complete price")
            .number
            .to_string()
    });
    (cost, price)
}

const LEDGER: &str = r#"
2026-01-01 open Assets:Broker
2026-01-01 open Assets:Cash
2026-01-01 open Income:Gains
2026-01-02 * "t1"
  Assets:Broker  4 AAA {{10 USD}}
  Assets:Cash
2026-01-02 * "t2"
  Assets:Broker  4 BBB {{10.00 USD}}
  Assets:Cash
2026-01-02 * "t3"
  Assets:Broker  3 CCC {{10 USD}}
  Assets:Cash
2026-01-02 * "t4"
  Assets:Broker  3 DDD {{7.5 USD}}
  Assets:Cash
2026-01-02 * "t5"
  Assets:Broker  0.5 EEE {{10 USD}}
  Assets:Cash
2026-01-02 * "t6"
  Assets:Broker  7.0 FFF {{100 USD}}
  Assets:Cash
2026-01-02 * "c1"
  Assets:Broker  3 HHH {1 # 1 USD}
  Assets:Cash
2026-01-02 * "c2"
  Assets:Broker  2 III {1.50 # 1 USD}
  Assets:Cash
2026-01-02 * "c4"
  Assets:Broker  4 KKK {0 # 10 USD}
  Assets:Cash
2026-01-02 * "c6"
  Assets:Broker  0.3 MMM {1.1 # 1 USD}
  Assets:Cash
2026-01-02 * "p1"
  Assets:Cash  4 NNN @@ 10 USD
  Assets:Cash
2026-01-02 * "p2"
  Assets:Cash  3 OOO @@ 10 USD
  Assets:Cash
2026-01-02 * "p3"
  Assets:Cash  4 PPP @@ 10.00 USD
  Assets:Cash
2026-01-02 * "p4"
  Assets:Cash  0.5 QQQ @@ 10 USD
  Assets:Cash
2026-01-02 * "p5"
  Assets:Cash  -3 RRR @@ 10 USD
  Assets:Cash
2026-01-02 * "i1"
  Assets:Broker  10 TTT {USD}
  Assets:Cash  -25.00 USD
2026-01-02 * "i2"
  Assets:Broker  3 UUU {USD}
  Assets:Cash  -10 USD
2026-01-02 * "i3"
  Assets:Cash  10 VVV @ USD
  Assets:Cash  -25.00 USD
2026-01-02 * "i4"
  Assets:Cash  3 WWW @ USD
  Assets:Cash  -10 USD
2026-01-02 * "i5"
  Assets:Cash  4 XXX @ USD
  Assets:Cash  -10 USD
2026-01-03 * "s1"
  Assets:Broker  -3 CCC {{10 USD}}
  Assets:Cash
2026-01-03 * "s2"
  Assets:Broker  -4 AAA {} @@ 13 USD
  Assets:Cash  13 USD
  Income:Gains
"#;

#[test]
fn per_unit_numbers_derived_from_totals_are_beancounts() {
    let ledger = load_source(LEDGER);
    no_errors(&ledger);
    let cost = |n, c| booked(&ledger, n, c).0;
    let price = |n, c| booked(&ledger, n, c).1;
    let s = |v: &str| Some(v.to_string());

    // `{{T}}`: the issue's four, then a positive ideal exponent and a
    // fractional divisor.
    assert_eq!(cost("t1", "AAA"), s("2.5"));
    assert_eq!(cost("t2", "BBB"), s("2.50"));
    assert_eq!(cost("t3", "CCC"), s("3.333333333333333333333333333"));
    assert_eq!(cost("t4", "DDD"), s("2.5"));
    assert_eq!(cost("t5", "EEE"), s("20"));
    assert_eq!(cost("t6", "FFF"), s("14.28571428571428571428571429"));
    // `{per # total}`: `(total + per × N) / N`, each step rounded in turn.
    assert_eq!(cost("c1", "HHH"), s("1.333333333333333333333333333"));
    assert_eq!(cost("c2", "III"), s("2.00"));
    assert_eq!(cost("c4", "KKK"), s("2.5"));
    assert_eq!(cost("c6", "MMM"), s("4.433333333333333333333333333"));
    // `@@`. p4 is beancount's `2E+1`: `Decimal` has no exponent, same value.
    assert_eq!(price("p1", "NNN"), s("2.5"));
    assert_eq!(price("p2", "OOO"), s("3.333333333333333333333333333"));
    assert_eq!(price("p3", "PPP"), s("2.50"));
    assert_eq!(price("p4", "QQQ"), s("20"));
    assert_eq!(price("p5", "RRR"), s("3.333333333333333333333333333"));
    // An interpolated `{}` cost.
    assert_eq!(cost("i1", "TTT"), s("2.50"));
    assert_eq!(cost("i2", "UUU"), s("3.333333333333333333333333333"));
    // An interpolated `@` price: Python's scale when exact...
    assert_eq!(price("i3", "VVV"), s("2.50"));
    assert_eq!(price("i5", "XXX"), s("2.5"));
    // ...but deliberately NOT Python's 28 digits when inexact: beancount's
    // `3.333333333333333333333333333` weighs 9.999999999999999999999999999
    // and beancount reports its own interpolation as unbalanced. This one
    // balances (`no_errors` above).
    assert_eq!(price("i4", "WWW"), s("3.3333333333333333333333333333"));
    // A reduction of a `{{T}}` lot names the lot's per-unit cost, and a sale's
    // `@@` is the sale's per-unit price.
    assert_eq!(cost("s1", "CCC"), s("3.333333333333333333333333333"));
    assert_eq!(cost("s2", "AAA"), s("2.5"));
    assert_eq!(price("s2", "AAA"), s("3.25"));
}

/// What a `{{T}}` or compound lot cost, and what the sale that empties it
/// takes, is the total written, whatever the per-unit cost rounds to (#2427).
///
/// The buys keep their total beside the per-unit cost (`PerUnitFromTotal`),
/// as before #2652, and print it as written. The sale is compared by VALUE.
/// Before #2652 it held only a per-unit cost, because
/// `3 × 3.3333333333333333333333333333` (exactly 9.9999999999999999999999999999)
/// is rounded to `10.000000000000000000000000000` by `checked_mul`, which the
/// booker took for "the per-unit reproduces the total"; its exact total was
/// then not 10 (`total_for` gave `None`). Now `3 × 3.333333333333333333333333333`
/// visibly falls short, so the sale carries the lot's exact total, 10.
#[test]
fn lot_totals_stay_exact() {
    use rustledger_core::Decimal;
    use std::str::FromStr;
    let ledger = load_source(LEDGER);
    no_errors(&ledger);
    for (narration, currency, total, written) in [
        ("t1", "AAA", "10", true),
        ("t3", "CCC", "10", true),
        ("t6", "FFF", "100", true),
        ("c1", "HHH", "4", true),
        ("c6", "MMM", "1.33", true),
        ("s1", "CCC", "-10", false),
    ] {
        let txn = transactions(&ledger)
            .find(|t| t.narration.as_str() == narration)
            .expect("transaction");
        let posting = txn
            .postings
            .iter()
            .find(|p| p.amount().is_some_and(|a| a.currency.as_str() == currency))
            .expect("the posting");
        let units = posting.amount().expect("booked units").number;
        let cost = posting
            .cost
            .as_deref()
            .and_then(|c| c.number)
            .expect("a booked cost");
        let got = cost.total_for(units).expect("a representable total");
        assert_eq!(
            got,
            Decimal::from_str(total).unwrap(),
            "{narration}: {cost:?}"
        );
        if written {
            assert_eq!(
                got.to_string(),
                total,
                "{narration} keeps the total as written"
            );
        }
    }
}

/// Lot identity compares the per-unit cost by VALUE: a lot booked at `2.5`
/// from `{{10 USD}}` is reduced by `{2.50 USD}` and by `{{5.00 USD}}` over 2.
#[test]
fn lot_matching_is_by_value() {
    let ledger = load_source(
        r#"
2026-01-01 open Assets:Broker
2026-01-01 open Assets:Cash
2026-01-02 * "buy"
  Assets:Broker  4 AAA {{10 USD}}
  Assets:Cash
2026-01-03 * "sell at 2.50"
  Assets:Broker  -2 AAA {2.50 USD}
  Assets:Cash
2026-01-04 * "sell the rest as a total"
  Assets:Broker  -2 AAA {{5.00 USD}}
  Assets:Cash
2026-01-05 balance Assets:Broker  0 AAA
"#,
    );
    no_errors(&ledger);
}
