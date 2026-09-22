//! A reduction written with a cost spec, even `{}`, sells only lots held at
//! cost; units held without a cost stay as they are (#2396).
//!
//! Holding 10 X at 100 and 10 X that arrived with no cost, selling 4 with
//! `{}` sells 4 of the 100 lot, a gain of 40 at 110, under every method.
//! When `{}` also matched cost-less positions, AVERAGE averaged them in as if
//! they cost nothing (the sale at 50, a gain of 240, and the cost-less units
//! left carrying a cost of 50), and FIFO and STRICT refused a ledger beancount
//! accepts. Beancount's reduction matching skips positions not held at cost.

use rustledger_core::{Decimal, Directive, Position};
use rustledger_loader::{LoadOptions, load};
use std::io::Write;

fn ledger_with_sale(method: &str, spec: &str) -> String {
    format!(
        r#"2020-01-01 open Assets:Stock X "{method}"
2020-01-01 open Assets:Cash
2020-01-01 open Equity:Transfer
2020-01-01 open Income:PnL

2020-01-02 * "buy 10 at 100"
  Assets:Stock  10 X {{100 USD}}
  Assets:Cash  -1000 USD

2020-01-03 * "10 units arrive with no cost stated"
  Assets:Stock   10 X
  Equity:Transfer

2020-01-04 * "sell 4 at 110"
  Assets:Stock  -4 X {spec} @ 110 USD
  Assets:Cash   440 USD
  Income:PnL
"#
    )
}

#[test]
fn a_cost_spec_sale_leaves_cost_less_units_alone_under_every_method() {
    // `{*}` merges the pool it sells from, so it must leave the cost-less
    // units out of the merge the same way.
    let cases = [
        ("AVERAGE", "{}"),
        ("FIFO", "{}"),
        ("LIFO", "{}"),
        ("HIFO", "{}"),
        ("STRICT", "{}"),
        ("STRICT", "{*}"),
    ];
    for (method, spec) in cases {
        let mut f = tempfile::Builder::new()
            .prefix("costless-")
            .suffix(".beancount")
            .tempfile()
            .expect("create tempfile");
        f.write_all(ledger_with_sale(method, spec).as_bytes())
            .expect("write fixture");
        let options = LoadOptions {
            collect_capital_gains: true,
            ..LoadOptions::default()
        };
        let ledger = load(f.path(), &options).expect("the ledger loads");
        assert!(
            ledger.errors.is_empty(),
            "{method} {spec}: got {:?}",
            ledger.errors
        );

        let gains = &ledger.capital_gains;
        assert_eq!(gains.len(), 1, "{method} {spec}: one disposal: {gains:?}");
        assert_eq!(
            gains[0].cost_basis.number,
            Decimal::from(400),
            "{method} {spec}: 4 sold from the lot at 100",
        );

        // What the account holds afterwards: the booked postings' units by
        // cost number. (By number, not full lot identity: an AVERAGE sale is
        // booked at the undated pool, so it would not net against the dated
        // buy as a lot.)
        let mut by_cost: std::collections::BTreeMap<Option<Decimal>, Decimal> =
            std::collections::BTreeMap::new();
        for d in &ledger.directives {
            if let Directive::Transaction(txn) = &d.value {
                for p in txn
                    .postings
                    .iter()
                    .filter(|p| p.account.as_str() == "Assets:Stock")
                {
                    let position = Position::from_posting(
                        p.amount().expect("booked"),
                        p.cost.as_deref(),
                        txn.date,
                    );
                    *by_cost.entry(position.cost.map(|c| c.number)).or_default() +=
                        position.units.number;
                }
            }
        }
        let held: Vec<(Decimal, Option<Decimal>)> = by_cost
            .into_iter()
            .filter(|(_, units)| !units.is_zero())
            .map(|(cost, units)| (units, cost))
            .collect();
        assert_eq!(
            held,
            vec![
                (Decimal::from(10), None),
                (Decimal::from(6), Some(Decimal::from(100))),
            ],
            "{method} {spec}: the cost-less units are untouched",
        );
    }
}
