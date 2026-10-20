//! `option "inferred_tolerance_default" "*:…"` is beancount's fallback, not a
//! floor (#2685).
//!
//! Beancount's `infer_tolerances` pops `*` off its tolerance table and makes
//! it the table's default value, so it reaches only a currency the
//! transaction gives no tolerance at all. rledger applied it as a minimum on
//! every units currency, which passed transactions bean-check rejects. Every
//! verdict below is bean-check's (beancount 3.2.3) on the same ledger, and
//! every interpolated number is what `bean-query` prints for it.

use rust_decimal::Decimal;
use rustledger_core::Directive;
use rustledger_loader::{Ledger, LoadOptions, load};
use std::io::Write;
use std::str::FromStr;

fn load_source(source: &str) -> Ledger {
    let mut f = tempfile::Builder::new()
        .prefix("tolerance-wildcard-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    load(f.path(), &LoadOptions::default()).expect("the ledger loads")
}

const OPENS: &str = "\
2026-01-01 open Assets:A
2026-01-01 open Assets:B
2026-01-01 open Assets:Eur
2026-01-01 open Assets:Stock
";

/// The residual messages of the ledger's unbalanced transactions.
fn imbalances(options: &str, body: &str) -> Vec<String> {
    let ledger = load_source(&format!("{options}\n{OPENS}{body}"));
    let other: Vec<String> = ledger
        .errors
        .iter()
        .filter(|e| !e.message.contains("does not balance"))
        .map(|e| e.message.clone())
        .collect();
    assert!(other.is_empty(), "unexpected errors: {other:#?}");
    ledger.errors.iter().map(|e| e.message.clone()).collect()
}

const STAR: &str = "option \"inferred_tolerance_default\" \"*:0.05\"";

#[test]
fn the_wildcard_does_not_loosen_a_currency_written_to_cents() {
    let off_by_four_cents = "2026-01-02 * \"t\"\n  Assets:A  10.00 USD\n  Assets:B  -9.96 USD\n";
    let errors = imbalances(STAR, off_by_four_cents);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("0.04 USD"), "{errors:?}");
    // A named default is a floor, as before.
    assert_eq!(
        imbalances(
            "option \"inferred_tolerance_default\" \"USD:0.05\"",
            off_by_four_cents
        ),
        Vec::<String>::new()
    );
}

#[test]
fn the_wildcard_is_the_tolerance_of_a_currency_with_none() {
    // Integers only: no tolerance is inferred, so `*` is the tolerance.
    let off_by_one = "2026-01-02 * \"t\"\n  Assets:A  10 USD\n  Assets:B  -9 USD\n";
    assert_eq!(imbalances(STAR, off_by_one).len(), 1);
    assert!(imbalances("option \"inferred_tolerance_default\" \"*:2\"", off_by_one).is_empty());
    // A currency mentioned only as a price and cost currency gets it too
    // (the floor skipped any currency that was not a units currency).
    let price_only = |cost: &str| {
        format!(
            "2026-01-02 * \"t\"\n  Assets:Eur  -5 EUR @ 2.00 USD\n  Assets:Stock  1 GGG {{{cost} USD}}\n"
        )
    };
    assert!(imbalances(STAR, &price_only("10.04")).is_empty());
    assert_eq!(imbalances(STAR, &price_only("10.06")).len(), 1);
}

#[test]
fn a_named_default_beats_the_wildcard() {
    let options = "option \"inferred_tolerance_default\" \"*:0.05\"\n\
                   option \"inferred_tolerance_default\" \"USD:0.02\"";
    let off = |n: &str| format!("2026-01-02 * \"t\"\n  Assets:A  10.00 USD\n  Assets:B  {n} USD\n");
    assert_eq!(imbalances(options, &off("-9.97")).len(), 1);
    assert!(imbalances(options, &off("-9.99")).is_empty());
    // Smaller than the wildcard, on integers: the named default still wins.
    let options = "option \"inferred_tolerance_default\" \"*:0.05\"\n\
                   option \"inferred_tolerance_default\" \"USD:0.001\"";
    let whole = "2026-01-02 * \"t\"\n  Assets:A  10 USD\n  Assets:B  -9.99 USD\n";
    assert_eq!(imbalances(options, whole).len(), 1);
}

#[test]
fn interpolation_rounds_with_the_wildcard_only_where_nothing_else_applies() {
    let ledger = load_source(&format!(
        "{STAR}\n{OPENS}\
         2026-01-02 * \"cents\"\n  Assets:A  10.00 USD\n  Assets:Eur  3 EUR @ 1.1111 USD\n  Assets:B\n\
         2026-01-02 * \"whole\"\n  Assets:A  10 USD\n  Assets:Eur  3 EUR @ 1.1111 USD\n  Assets:B\n"
    ));
    assert!(ledger.errors.is_empty(), "{:#?}", ledger.errors);
    let filled: Vec<(String, Decimal)> = ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .map(|t| {
            let b = t
                .postings
                .iter()
                .find(|p| p.account.as_str() == "Assets:B")
                .and_then(|p| p.amount())
                .expect("Assets:B filled");
            (t.narration.to_string(), b.number)
        })
        .collect();
    let d = |s| Decimal::from_str(s).unwrap();
    assert_eq!(
        filled,
        [
            ("cents".to_string(), d("-13.33")),
            ("whole".to_string(), d("-13.3"))
        ]
    );
    // The scale too: beancount prints `-13.33` and `-13.3`.
    assert_eq!(filled[0].1.to_string(), "-13.33");
    assert_eq!(filled[1].1.to_string(), "-13.3");
}
