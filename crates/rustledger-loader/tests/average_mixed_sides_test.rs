//! AVERAGE pools only the side a reduction takes from, and realized gains
//! follow (#2393).
//!
//! On an account holding a long at 102 and a short at 101, covering 1 of the
//! short at 95 is a gain of 6 on the short (opened at 101, closed at 95),
//! short-term. Pooling both sides priced the cover from a net long pool at
//! 102.67 and reported a loss of 8 with an unknown holding period, and left
//! the account as `4 X {102.67}`, the short gone.

use rustledger_core::Decimal;
use rustledger_loader::{LoadOptions, load};
use std::io::Write;

#[test]
fn covering_a_short_beside_a_long_realizes_the_shorts_gain() {
    let mut f = tempfile::Builder::new()
        .prefix("average-mixed-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(
        br#"2020-01-01 open Assets:Stock X "AVERAGE"
2020-01-01 open Assets:Cash
2020-01-01 open Income:PnL

2020-01-01 * "a short at 101 and a long at 102"
  Assets:Stock  -2 X {101 USD}
  Assets:Stock   5 X {102 USD}
  Assets:Cash  -308 USD

2020-01-05 * "cover 1 of the short at 95"
  Assets:Stock   1 X {} @ 95 USD
  Assets:Cash   -95 USD
  Income:PnL
"#,
    )
    .expect("write fixture");
    let options = LoadOptions {
        collect_capital_gains: true,
        ..LoadOptions::default()
    };
    let ledger = load(f.path(), &options).expect("the ledger loads");
    assert!(ledger.errors.is_empty(), "got {:?}", ledger.errors);

    let gains = &ledger.capital_gains;
    assert_eq!(gains.len(), 1, "one disposal: {gains:?}");
    let g = &gains[0];
    assert!(g.short_sale, "covering a short is a short-sale disposal");
    assert_eq!(g.units, Decimal::from(1));
    assert_eq!(g.cost_basis.number, Decimal::from(95), "paid 95 to cover");
    assert_eq!(
        g.proceeds.number,
        Decimal::from(101),
        "received 101 opening the short"
    );
}
