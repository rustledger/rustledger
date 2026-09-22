//! Holding a long and a short in one commodity, a posting whose cost matches
//! only its own side adds to it (#2384).
//!
//! Whether a posting reduces used to be decided by the currency alone: any
//! lot of the opposite sign made it a reduction, which then looked for a lot
//! its cost spec named, found none on that side, and failed with `No matching
//! lot`. Beancount accepts these ledgers, but its lot matching ignores sign,
//! so it merges the new units into the same-sign lot and gives them that
//! lot's older acquisition date. Here they are a new lot at the transaction
//! date, with the same units and cost.

use rustledger_core::{Decimal, Directive, Inventory, NaiveDate, Position};
use rustledger_loader::{LoadOptions, load};
use std::io::Write;

fn load_source(source: &str) -> rustledger_loader::Ledger {
    let mut f = tempfile::Builder::new()
        .prefix("mixed-sign-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    load(f.path(), &LoadOptions::default()).expect("the ledger loads")
}

/// `Assets:Stock` lots as `(units, per-unit cost, acquisition date)`, sorted.
fn stock(ledger: &rustledger_loader::Ledger) -> Vec<(Decimal, Decimal, Option<NaiveDate>)> {
    let mut inv = Inventory::new();
    for d in &ledger.directives {
        if let Directive::Transaction(txn) = &d.value {
            for p in txn
                .postings
                .iter()
                .filter(|p| p.account.as_str() == "Assets:Stock")
            {
                inv.add(Position::from_posting(
                    p.amount().expect("booked"),
                    p.cost.as_deref(),
                    txn.date,
                ))
                .expect("fits");
            }
        }
    }
    let mut lots: Vec<_> = inv
        .positions()
        .filter(|p| !p.units.number.is_zero())
        .map(|p| {
            let c = p.cost.as_ref().expect("cost");
            (p.units.number, c.number, c.date)
        })
        .collect();
    lots.sort();
    lots
}

const HEADER: &str = r#"option "booking_method" "STRICT"
2020-01-01 open Assets:Stock
2020-01-01 open Assets:Cash
"#;

fn day(d: i8) -> Option<NaiveDate> {
    Some(rustledger_core::naive_date(2020, 1, d.try_into().unwrap()).unwrap())
}

#[test]
fn a_buy_at_the_long_side_cost_opens_a_new_lot() {
    let ledger = load_source(&format!(
        r#"{HEADER}
2020-01-01 * "a short at 101, a long at 102"
  Assets:Stock  -2 X {{101 USD}}
  Assets:Stock   5 X {{102 USD}}
  Assets:Cash  -308 USD

2020-01-05 * "buy 3 more at 102"
  Assets:Stock   3 X {{102 USD}}
  Assets:Cash  -306 USD
"#
    ));
    assert!(ledger.errors.is_empty(), "got {:?}", ledger.errors);
    assert_eq!(
        stock(&ledger),
        vec![
            (Decimal::from(-2), Decimal::from(101), day(1)),
            (Decimal::from(3), Decimal::from(102), day(5)),
            (Decimal::from(5), Decimal::from(102), day(1)),
        ],
        "a new lot at the transaction date, not beancount's 8 X {{102, 2020-01-01}}",
    );
}

#[test]
fn a_sale_at_the_short_side_cost_opens_a_new_lot() {
    let ledger = load_source(&format!(
        r#"{HEADER}
2020-01-01 * "a long at 102, a short at 101"
  Assets:Stock   5 X {{102 USD}}
  Assets:Stock  -2 X {{101 USD}}
  Assets:Cash  -308 USD

2020-01-05 * "short 1 more at 101"
  Assets:Stock  -1 X {{101 USD}}
  Assets:Cash   101 USD
"#
    ));
    assert!(ledger.errors.is_empty(), "got {:?}", ledger.errors);
    assert_eq!(
        stock(&ledger),
        vec![
            (Decimal::from(-2), Decimal::from(101), day(1)),
            (Decimal::from(-1), Decimal::from(101), day(5)),
            (Decimal::from(5), Decimal::from(102), day(1)),
        ],
    );
}

#[test]
fn a_mistyped_cost_still_fails() {
    let ledger = load_source(&format!(
        r#"{HEADER}
2020-01-01 * "buy"
  Assets:Stock  10 X {{100 USD}}
  Assets:Cash  -1000 USD

2020-01-05 * "sell at a cost no lot has"
  Assets:Stock  -5 X {{101 USD}}
  Assets:Cash   505 USD
"#
    ));
    assert!(
        ledger
            .errors
            .iter()
            .any(|e| format!("{e:?}").contains("No matching lot")),
        "a cost matching no lot must still be refused, as beancount refuses it; got {:?}",
        ledger.errors,
    );
}
