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

/// A trailing `*` component is the same merge as `{*}` (#2329).
///
/// Beancount's grammar takes `*` as any component of the cost list, so
/// `{110.00 USD, *}` is a merge. It used to parse as a plain per-unit spec,
/// so this sale looked for a lot at 110, found none, and failed; written
/// `{100.00 USD, *}` it silently sold from the 100 lot instead of the pool.
/// Both now merge. `{110.00 USD, *}` books from the pool at 110 like `{*}`;
/// `{100.00 USD, *}` states a cost the pool does not have, and is refused
/// rather than booked at 110 with the 100 dropped (#2398).
#[test]
fn a_trailing_star_component_merges_like_a_leading_one() {
    use rustledger_core::Directive;
    let load_with = |spec: &str| {
        let source = MERGE_SOURCE.replace("-5 X {*}", &format!("-5 X {spec}"));
        assert!(
            source.contains(&format!("-5 X {spec}")),
            "fixture edit must apply"
        );
        let mut f = tempfile::Builder::new()
            .prefix("trailing-merge-")
            .suffix(".beancount")
            .tempfile()
            .expect("create tempfile");
        f.write_all(source.as_bytes()).expect("write fixture");
        load(f.path(), &LoadOptions::default()).expect("the ledger loads")
    };

    let refused = load_with("{100.00 USD, *}");
    assert!(
        refused.errors.iter().any(|e| e
            .message
            .contains("the merged pool costs 110.00 USD per unit")),
        "a merge of a 110 pool stating 100 must be refused: {:?}",
        refused.errors,
    );

    for spec in ["{*}", "{110.00 USD, *}"] {
        let ledger = load_with(spec);
        assert!(ledger.errors.is_empty(), "{spec}: got {:?}", ledger.errors);

        let sale = ledger
            .directives
            .iter()
            .filter_map(|d| match &d.value {
                Directive::Transaction(t)
                    if t.narration.as_str() == "sell against the merged pool" =>
                {
                    Some(t)
                }
                _ => None,
            })
            .flat_map(|t| t.postings.iter())
            .find(|p| p.account.as_str() == "Assets:Stock")
            .expect("the sale");
        let cost = sale.cost.as_deref().expect("booked cost");
        assert!(cost.merge, "{spec}: booked as a merge");
        assert_eq!(
            cost.number.and_then(|n| n.per_unit()),
            Some(rustledger_core::Decimal::new(11000, 2)),
            "{spec}: sold from the merged pool at 110",
        );
    }
}
