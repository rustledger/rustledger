//! A price written without a currency on a posting at cost, end to end
//! (#3047, reported by tomelliot).
//!
//! Beancount fills the price currency from the cost currency
//! (`booking_full.categorize_by_currency`), so `-2 STK {5 USD, 2020-01-02} @ 7`
//! has the price `7 USD`. rledger kept a bare number: the BQL `price` column
//! came out empty and `implicit_prices` emitted no price for the posting.
//! The expected outputs below are beancount 3.2.3's (`bean-query` on this
//! file, beanquery 0.2.0).

mod common;

use std::io::Write;
use std::path::Path;
use std::process::Command;

const LEDGER: &str = r#"plugin "beancount.plugins.implicit_prices"

2020-01-01 open Assets:S
2020-01-01 open Assets:C
2020-01-01 open Income:G

2020-01-02 * "buy"
  Assets:S  2 STK {5 USD, 2020-01-02}
  Assets:C  -10 USD

2020-02-01 * "sell, per-unit price"
  Assets:S  -2 STK {5 USD, 2020-01-02} @ 7
  Assets:C  14 USD
  Income:G

2020-03-01 * "buy, cost currency elided too"
  Assets:S  2 STK {5} @ 6
  Assets:C  -10 USD

2020-04-01 * "sell, total price"
  Assets:S  -2 STK {5 USD} @@ 16
  Assets:C  16 USD
  Income:G

2020-05-01 * "buy at a EUR cost"
  Assets:S  2 STK {5 EUR, 2020-05-01}
  Assets:C  -10 EUR

2020-06-01 * "sell, cost currency differs from the cash leg"
  Assets:S  -2 STK {5 EUR, 2020-05-01} @ 9
  Assets:C  14 USD
  Income:G
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
fn test_price_column_and_implicit_prices_take_the_cost_currency() {
    let bin = require_rledger!();
    let mut f = tempfile::Builder::new()
        .suffix(".beancount")
        .tempfile()
        .expect("tempfile");
    f.write_all(LEDGER.as_bytes()).expect("write ledger");

    let check = Command::new(&bin)
        .args(["check", "--no-cache"])
        .arg(f.path())
        .output()
        .expect("run rledger check");
    assert!(
        check.status.success(),
        "rledger check failed: {}{}",
        String::from_utf8_lossy(&check.stdout),
        String::from_utf8_lossy(&check.stderr)
    );

    let postings = query_csv(
        &bin,
        f.path(),
        "SELECT date, units(position) AS units, cost_currency, price \
         WHERE account = 'Assets:S'",
    );
    assert_eq!(
        postings,
        "date,units,cost_currency,price\n\
         2020-01-02,2 STK,USD,\n\
         2020-02-01,-2 STK,USD,7 USD\n\
         2020-03-01,2 STK,USD,6 USD\n\
         2020-04-01,-2 STK,USD,8 USD\n\
         2020-05-01,2 STK,EUR,\n\
         2020-06-01,-2 STK,EUR,9 EUR\n",
    );

    let prices = query_csv(&bin, f.path(), "SELECT date, currency, amount FROM #prices");
    assert_eq!(
        prices,
        "date,currency,amount\n\
         2020-01-02,STK,5 USD\n\
         2020-02-01,STK,7 USD\n\
         2020-03-01,STK,6 USD\n\
         2020-04-01,STK,8 USD\n\
         2020-05-01,STK,5 EUR\n\
         2020-06-01,STK,9 EUR\n",
    );
}

/// With `infer_tolerance_from_cost`, the completed price widens the
/// transaction's tolerance in the cost currency, as the same price written
/// with its currency does: units quantum 0.05 times cost 0.1 plus price 0.2
/// is 0.015 USD, which covers the -0.01 USD residual. Beancount 3.2.3 accepts
/// this file (its balance check reads the booked price) and refuses it with
/// the price removed (tolerance 0.005).
#[test]
fn test_completed_price_widens_the_inferred_tolerance() {
    let bin = require_rledger!();
    let check = |ledger: &str| {
        let mut f = tempfile::Builder::new()
            .suffix(".beancount")
            .tempfile()
            .expect("tempfile");
        f.write_all(ledger.as_bytes()).expect("write ledger");
        Command::new(&bin)
            .args(["check", "--no-cache"])
            .arg(f.path())
            .output()
            .expect("run rledger check")
    };
    let ledger = |price: &str| {
        format!(
            "option \"infer_tolerance_from_cost\" \"TRUE\"\n\
             2020-01-01 open Assets:S\n\
             2020-01-01 open Assets:C\n\
             2020-02-01 * \"buy\"\n  \
               Assets:S  1.5 STK {{0.1 USD}}{price}\n  \
               Assets:C  -0.16 USD\n"
        )
    };
    for price in [" @ 0.2", " @ 0.2 USD"] {
        let out = check(&ledger(price));
        assert!(
            out.status.success(),
            "`{price}` should balance within 0.015 USD: {}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    assert!(
        !check(&ledger("")).status.success(),
        "without the price the tolerance is 0.005 USD and -0.01 USD is an imbalance"
    );
}
