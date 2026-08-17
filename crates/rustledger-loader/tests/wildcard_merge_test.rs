//! `{*}` merge survives the whole load pipeline (#2068).
//!
//! Booking used to resolve `{*}` into the per-unit cost of the pool it would
//! create and clear the marker, so the application pass went looking for a lot
//! at the merged average — a lot that does not exist until the merge has run.
//! A ledger that beancount accepts failed `rledger check` with
//! `No matching lot`, naming holdings the account plainly had.

use rustledger_loader::{LoadOptions, load};
use std::io::Write;

/// Two lots at 100 and 120; `{*}` merges them to a 20-unit pool at 110 and
/// sells 5 out of it.
const MERGE_SOURCE: &str = r#"option "operating_currency" "USD"

2000-01-01 open Assets:Stock X "STRICT"
2000-01-01 open Assets:Cash USD
2000-01-01 open Income:PnL

2024-01-01 * "buy lot 1"
  Assets:Stock  10 X {100.00 USD}
  Assets:Cash  -1000.00 USD

2024-01-02 * "buy lot 2"
  Assets:Stock  10 X {120.00 USD}
  Assets:Cash  -1200.00 USD

2024-02-01 * "sell against the merged pool"
  Assets:Stock  -5 X {*}
  Assets:Cash   600.00 USD
  Income:PnL
"#;

#[test]
fn a_wildcard_merge_loads_without_errors() {
    let mut f = tempfile::Builder::new()
        .prefix("wildcard-merge-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(MERGE_SOURCE.as_bytes()).expect("write fixture");

    let ledger = load(f.path(), &LoadOptions::default()).expect("the ledger loads");
    assert!(
        ledger.errors.is_empty(),
        "`{{*}}` must book AND apply; got: {:?}",
        ledger.errors,
    );
}
