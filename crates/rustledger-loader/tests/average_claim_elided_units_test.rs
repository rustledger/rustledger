//! The full pipeline reports an AVERAGE sale with elided units whose stated
//! cost is not the pool's, once (#2645).

use rustledger_loader::{LoadOptions, load};
use std::io::Write;

fn errors(sale_cost: &str, cash: &str) -> Vec<String> {
    let source = format!(
        r#"2024-01-01 open Assets:B X "AVERAGE"
2024-01-01 open Assets:C

2024-01-02 * "buy"
  Assets:B  10 X {{10.00 EUR}}
  Assets:C

2024-03-01 * "sell, units elided"
  Assets:B  X {{{sale_cost}}}
  Assets:C  {cash}
"#
    );
    let mut f = tempfile::Builder::new()
        .suffix(".beancount")
        .tempfile()
        .expect("tempfile");
    f.write_all(source.as_bytes()).expect("write");
    let ledger = load(f.path(), &LoadOptions::default()).expect("loads");
    ledger.errors.iter().map(|e| e.message.clone()).collect()
}

#[test]
fn the_issue_case_is_reported_once() {
    assert_eq!(
        errors("99.00 EUR", "99.00 EUR"),
        [
            "Assets:B: AVERAGE pool of X costs 10.00 EUR per unit, not the 99.00 EUR the cost \
          spec states; write the pool's cost or leave the spec empty (2024-03-01, \"sell, \
          units elided\")"
        ]
    );
}

#[test]
fn the_pools_own_cost_still_books() {
    assert_eq!(errors("10.00 EUR", "20.00 EUR"), Vec::<String>::new());
}
