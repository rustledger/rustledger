//! The loader records the disposal of a sale written with its units elided,
//! exactly as it does for the same sale with its units written (#2647).

use rustledger_loader::{LoadOptions, load};
use std::io::Write;

fn load_sale(units: &str) -> rustledger_loader::Ledger {
    let source = format!(
        r#"2024-01-01 open Assets:B X "FIFO"
2024-01-01 open Assets:C
2024-01-01 open Income:Gains
2024-01-01 open Equity:O

2024-01-02 * "buy"
  Assets:B  1 X {{10.00 EUR}}
  Equity:O

2024-01-03 * "buy"
  Assets:B  3 X {{10.00 EUR}}
  Equity:O

2024-03-01 * "sell across both lots"
  Assets:B  {units} X {{10.00 EUR}} @ 15.00 EUR
  Assets:C  30.00 EUR
  Income:Gains  -10.00 EUR
"#
    );
    let mut f = tempfile::Builder::new()
        .suffix(".beancount")
        .tempfile()
        .expect("tempfile");
    f.write_all(source.as_bytes()).expect("write");
    let options = LoadOptions {
        collect_capital_gains: true,
        ..LoadOptions::default()
    };
    load(f.path(), &options).expect("loads")
}

#[test]
fn an_elided_units_sale_records_the_written_sales_disposals() {
    let gains = |l: &rustledger_loader::Ledger| -> Vec<String> {
        assert!(l.errors.is_empty(), "{:?}", l.errors);
        l.capital_gains
            .iter()
            .map(|g| {
                format!(
                    "{} {} basis {} proceeds {} acquired {:?}",
                    g.units,
                    g.currency,
                    g.cost_basis.number.normalize(),
                    g.proceeds.number.normalize(),
                    g.acquired_date
                )
            })
            .collect()
    };
    let written = gains(&load_sale("-2"));
    let elided = gains(&load_sale(""));
    assert_eq!(
        written.len(),
        2,
        "FIFO sells 1 from the first lot and 1 from the second: {written:?}"
    );
    assert_eq!(written, elided);
}
