//! A transaction that sells past a lot it touches loads as booking read it
//! (#2368).
//!
//! Booking classifies each posting against the inventory before the
//! transaction, threaded with earlier reductions only. Both `apply` and the
//! validator's inventory pass used to add each posting as they reached it, so
//! a later posting could become a reduction booking never saw: these ledgers,
//! which beancount accepts, failed `rledger check` with `Not enough units` and
//! `No matching lot`. The expected holdings are beancount's.

use rustledger_core::{Decimal, Directive, Inventory, Position};
use rustledger_loader::{LoadOptions, load};
use std::io::Write;

/// Load `source` and return the errors plus every `Assets:Stock` position as
/// `(units, per-unit cost)`, sorted.
fn load_stock(source: &str) -> (Vec<String>, Vec<(Decimal, Decimal)>) {
    let mut f = tempfile::Builder::new()
        .prefix("same-txn-short-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    let ledger = load(f.path(), &LoadOptions::default()).expect("the ledger loads");

    let mut inv = Inventory::new();
    for d in &ledger.directives {
        if let Directive::Transaction(txn) = &d.value {
            for p in &txn.postings {
                if p.account.as_str() != "Assets:Stock" {
                    continue;
                }
                let units = p.amount().expect("booked postings are complete");
                inv.add(Position::from_posting(units, p.cost.as_deref(), txn.date))
                    .expect("no overflow");
            }
        }
    }
    let mut held: Vec<(Decimal, Decimal)> = inv
        .positions()
        .filter(|p| !p.units.number.is_zero())
        .map(|p| (p.units.number, p.cost.as_ref().expect("cost").number))
        .collect();
    held.sort();
    (
        ledger.errors.iter().map(|e| format!("{e:?}")).collect(),
        held,
    )
}

#[test]
fn buying_then_selling_past_the_buy_opens_a_short() {
    let (errors, held) = load_stock(
        r#"option "booking_method" "STRICT"
2020-01-01 open Assets:Stock
2020-01-01 open Assets:Cash

2020-01-02 * "buy 10 then sell 20 in one transaction"
  Assets:Stock   10 X {100.00 USD}
  Assets:Stock  -20 X {100.00 USD}
  Assets:Cash   1000.00 USD
"#,
    );
    assert!(
        errors.is_empty(),
        "beancount accepts this ledger; got {errors:?}"
    );
    assert_eq!(held, vec![(Decimal::from(-10), Decimal::new(10000, 2))]);
}

#[test]
fn selling_a_lot_out_then_past_it_opens_a_short() {
    let (errors, held) = load_stock(
        r#"option "booking_method" "STRICT"
2020-01-01 open Assets:Stock
2020-01-01 open Assets:Cash

2020-01-01 * "seed"
  Assets:Stock   2 X {100 USD}
  Assets:Cash  -200 USD

2020-01-13 * "buy 9 at 101, then sell 2 at 100 twice"
  Assets:Stock   9 X {101 USD}
  Assets:Stock  -2 X {100 USD}
  Assets:Stock  -2 X {100 USD}
  Assets:Cash   -509 USD
"#,
    );
    assert!(
        errors.is_empty(),
        "beancount accepts this ledger; got {errors:?}"
    );
    assert_eq!(
        held,
        vec![
            (Decimal::from(-2), Decimal::from(100)),
            (Decimal::from(9), Decimal::from(101)),
        ],
    );
}

/// A cost-less buy written ahead of an `AVERAGE` sale in the same transaction
/// stays out of that sale's pool, as `book` read it.
///
/// Booking sells 4 of the 10 @ 100 and only then adds the 10 cost-less units,
/// leaving 6 @ 100 beside them. The next sale pools all 16 against a basis of
/// 600, so it books at 37.50. Adding the cost-less units first put them in the
/// first sale's pool, left 16 @ 50, and booked the next sale at 50.
#[test]
fn a_cost_less_buy_does_not_join_an_average_sale_in_its_own_transaction() {
    let mut f = tempfile::Builder::new()
        .prefix("same-txn-average-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(
        br#"2020-01-01 open Assets:Stock X "AVERAGE"
2020-01-01 open Assets:Cash
2020-01-01 open Equity:Open

2020-01-02 * "seed"
  Assets:Stock  10 X {100 USD}
  Assets:Cash  -1000 USD

2020-01-03 * "cost-less units in, then an average sale"
  Assets:Stock   10 X
  Equity:Open   -10 X
  Assets:Stock  -4 X {}
  Assets:Cash

2020-01-04 * "read the pool back"
  Assets:Stock  -2 X {}
  Assets:Cash
"#,
    )
    .expect("write fixture");
    let ledger = load(f.path(), &LoadOptions::default()).expect("the ledger loads");
    assert!(ledger.errors.is_empty(), "got {:?}", ledger.errors);

    let read_back = ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Transaction(txn) if txn.narration.as_str() == "read the pool back" => {
                Some(txn)
            }
            _ => None,
        })
        .flat_map(|txn| txn.postings.iter())
        .find(|p| p.account.as_str() == "Assets:Stock")
        .expect("the read-back sale");
    let booked = Position::from_posting(
        read_back.amount().expect("booked"),
        read_back.cost.as_deref(),
        rustledger_core::NaiveDate::default(),
    );
    assert_eq!(
        booked.cost.map(|c| c.number),
        Some(Decimal::new(3750, 2)),
        "the pool the next sale saw included the cost-less buy",
    );
}
