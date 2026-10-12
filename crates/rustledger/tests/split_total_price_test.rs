//! A total price (`@@`) on a sale that booking splits across lots, end to end
//! (#2569).
//!
//! 1000 XYZ sold for 6000.00 USD from two FIFO lots of 500 books as two
//! postings. Each used to show `@ 12.00` (the total over its own 500 units):
//! the BQL `price` column, and `implicit_prices` emitted a 12.00 price that
//! later valuation used. Beancount 3.2.0 shows 6.00 on both postings and in
//! `#prices` (`bean-query` on this file).

mod common;

use std::io::Write;
use std::path::Path;
use std::process::Command;

const LEDGER: &str = r#"option "operating_currency" "USD"
option "booking_method" "FIFO"
plugin "beancount.plugins.implicit_prices"

2020-01-01 open Assets:Broker:Cash   USD
2020-01-01 open Assets:Broker:XYZ    XYZ
2020-01-01 open Income:Gains         USD
2020-01-01 open Equity:Opening       USD

2020-01-02 * "Fund"
  Assets:Broker:Cash        20000.00 USD
  Equity:Opening

2020-02-01 * "Buy lot 1"
  Assets:Broker:XYZ         500 XYZ {10.00 USD}
  Assets:Broker:Cash

2020-03-01 * "Buy lot 2"
  Assets:Broker:XYZ         500 XYZ {20.00 USD}
  Assets:Broker:Cash

2020-04-01 * "Sell all 1000 for a total of 6000"
  Assets:Broker:XYZ        -1000 XYZ {} @@ 6000.00 USD
  Assets:Broker:Cash        6000.00 USD
  Income:Gains
"#;

fn query_csv(bin: &Path, file: &Path, bql: &str) -> String {
    let out = Command::new(bin)
        .args(["query", "--no-cache", "-f", "csv"])
        .arg(file)
        .arg(bql)
        .output()
        .expect("run rledger query");
    assert!(
        out.status.success(),
        "rledger query failed: {}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn split_postings_and_implicit_prices_carry_the_whole_sale_price() {
    let bin = require_rledger!();
    let mut f = tempfile::Builder::new()
        .suffix(".beancount")
        .tempfile()
        .expect("tempfile");
    f.write_all(LEDGER.as_bytes()).expect("write ledger");

    let postings = query_csv(
        &bin,
        f.path(),
        "SELECT units(position) AS units, price, weight \
         WHERE account ~ 'XYZ' AND number < 0 ORDER BY weight",
    );
    assert_eq!(
        postings,
        "units,price,weight\n\
         -500 XYZ,6.00 USD,-10000.00 USD\n\
         -500 XYZ,6.00 USD,-5000.00 USD\n",
        "each split posting carries 6000.00 / 1000, not 6000.00 / 500"
    );

    let prices = query_csv(
        &bin,
        f.path(),
        "SELECT date, currency, amount FROM #prices WHERE date = 2020-04-01",
    );
    assert_eq!(prices, "date,currency,amount\n2020-04-01,XYZ,6.00 USD\n");
}
