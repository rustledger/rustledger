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

/// A sale naming only a lot date, on an account holding both sides, still
/// fails when no lot has that date (review of #2384).
///
/// The own-side exception compares cost only, setting the date aside, because
/// on the own side the date is an acquisition date. A spec with no cost has
/// nothing left to compare and would match every own-side lot: here the cash
/// leg implies the short's cost, so the typo booked as a new short lot dated
/// with the mistyped date. Beancount refuses it.
#[test]
fn a_mistyped_lot_date_still_fails_on_a_mixed_account() {
    let ledger = load_source(&format!(
        r#"{HEADER}
2020-01-01 * "a long at 100 and a short at 101"
  Assets:Stock  10 X {{100 USD}}
  Assets:Stock  -2 X {{101 USD}}
  Assets:Cash  -798 USD

2020-01-05 * "sell 1, naming a lot date nothing has"
  Assets:Stock  -1 X {{2020-01-09}}
  Assets:Cash   101 USD
"#
    ));
    assert!(
        ledger
            .errors
            .iter()
            .any(|e| format!("{e:?}").contains("No matching lot")),
        "a lot date matching nothing must be refused; got {:?}",
        ledger.errors,
    );
}

/// A cost spec against an account holding the commodity without a cost
/// reduces it, matches no lot, and is refused, as bean-check 3.2.3 refuses
/// it (`No position matches`). Holding `10 BTC` bought without a cost,
/// `-1 BTC {98.52 USD}` opened a short lot at cost beside the long; and a
/// purchase at cost after a sale without a cost spec (issue #875's ledger)
/// was an augmentation, where beancount refuses it too.
#[test]
fn a_cost_spec_against_an_uncosted_holding_is_refused() {
    for ledger in [
        "2024-01-01 open Assets:Wallet\n2024-01-01 open Assets:Cash\n2024-01-01 open Equity:Opening\n\
         2024-01-04 *\n  Assets:Wallet  10 BTC\n  Equity:Opening  -10 BTC\n\
         2024-01-10 *\n  Assets:Wallet  -1 BTC {98.52 USD}\n  Assets:Cash  98.52 USD\n",
        "option \"operating_currency\" \"EUR\"\n2024-01-01 open Assets:Bank EUR\n2024-01-01 open Assets:Stocks HOOG\n\
         2024-01-10 * \"Buy\"\n  Assets:Stocks  100 HOOG {1.50 EUR}\n  Assets:Bank\n\
         2024-01-15 * \"Sell without cost spec\"\n  Assets:Stocks  -25 HOOG @ 1.60 EUR\n  Assets:Bank\n\
         2024-01-20 * \"Buy again\"\n  Assets:Stocks  50 HOOG {1.70 EUR}\n  Assets:Bank\n",
    ] {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("ledger.beancount");
        std::fs::write(&path, ledger).expect("write ledger");
        let loaded = rustledger_loader::load(&path, &rustledger_loader::LoadOptions::default())
            .expect("load ledger");
        let booking = loaded
            .errors
            .iter()
            .filter(|e| e.is_booking_failure())
            .count();
        assert_eq!(booking, 1, "{:?}", loaded.errors);
    }
}
