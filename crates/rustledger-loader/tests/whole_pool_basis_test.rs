//! Selling a whole AVERAGE or `{*}` pool balances exactly (#2417).
//!
//! 1 X at 100 and 2 X at 200 average 166.66…, which `Decimal` rounds. Booking
//! priced a sale of all three at `3 × 166.6666666666666666666666667`, which
//! is 500.00…01, so a sale for `500 USD`, whose whole-dollar amounts infer no
//! tolerance, failed to balance by 1E-26 USD. The lots cost exactly 500, and
//! that is the basis a sale of all of them takes, in the balance and in the
//! realized gain alike.

use rustledger_core::Directive;
use rustledger_loader::{LoadOptions, load};
use std::io::Write;

fn ledger(method: &str, spec: &str) -> String {
    format!(
        r#"2024-01-01 open Assets:B X "{method}"
2024-01-01 open Assets:C
2024-01-01 open Income:G

2024-01-02 * "a"
  Assets:B  1 X {{100 USD}}
  Assets:C

2024-01-03 * "b"
  Assets:B  2 X {{200 USD}}
  Assets:C

2024-02-01 * "sell the whole pool"
  Assets:B  -3 X {spec} @ 200 USD
  Assets:C  600 USD
  Income:G  -100 USD
"#
    )
}

fn load_source(source: &str) -> rustledger_loader::Ledger {
    let mut f = tempfile::Builder::new()
        .prefix("whole-pool-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    let options = LoadOptions {
        collect_capital_gains: true,
        ..LoadOptions::default()
    };
    load(f.path(), &options).expect("the ledger loads")
}

#[test]
fn a_whole_pool_sale_balances_and_realizes_the_exact_basis() {
    for (method, spec) in [("AVERAGE", "{}"), ("FIFO", "{*}")] {
        let ledger = load_source(&ledger(method, spec));
        assert!(
            ledger.errors.is_empty(),
            "{method} {spec}: the lots cost exactly 500; got {:?}",
            ledger.errors
        );

        let sale = ledger
            .directives
            .iter()
            .filter_map(|d| match &d.value {
                Directive::Transaction(t) if t.narration.as_str() == "sell the whole pool" => {
                    Some(t)
                }
                _ => None,
            })
            .flat_map(|t| t.postings.iter())
            .find(|p| p.account.as_str() == "Assets:B")
            .expect("the sale");
        let number = sale
            .cost
            .as_deref()
            .and_then(|c| c.number)
            .expect("booked cost");
        assert_eq!(
            number.total(),
            Some(rustledger_core::Decimal::from(500)),
            "{method} {spec}: the booked cost carries the exact total"
        );

        let basis: Vec<_> = ledger
            .capital_gains
            .iter()
            .map(|g| g.cost_basis.number)
            .collect();
        assert_eq!(
            basis,
            vec![rustledger_core::Decimal::from(500)],
            "{method} {spec}: the realized basis is the exact total"
        );
    }
}
