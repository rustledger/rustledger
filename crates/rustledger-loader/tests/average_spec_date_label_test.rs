//! A date or label on an AVERAGE sale's cost spec is refused, not dropped
//! (#2627).
//!
//! An AVERAGE sale takes from the account's pool, which is one undated,
//! unlabeled lot, so a date or label written on the sale's spec describes no
//! lot. It used to book from the pool without a word. A `{*}` sale already
//! refuses one (#2398); AVERAGE now does the same. Beancount has no AVERAGE
//! booking to compare with (bean-check 3.2.3: `AVERAGE method is not
//! supported`).

use rustledger_loader::{LoadOptions, load};
use std::io::Write;

/// Two lots in an AVERAGE account (the first dated and labeled on its buy),
/// then a sale of 1 X written with `spec`.
fn ledger(spec: &str) -> String {
    format!(
        r#"2024-01-01 open Assets:B X "AVERAGE"
2024-01-01 open Assets:C
2024-01-01 open Income:G

2024-01-02 * "a"
  Assets:B  10 X {{10.00 EUR, 2024-01-02, "lot-a"}}
  Assets:C

2024-01-03 * "b"
  Assets:B  10 X {{12.00 EUR}}
  Assets:C

2024-03-01 * "sell"
  Assets:B  -1 X {spec} @ 15 EUR
  Assets:C  15 EUR
  Income:G
"#
    )
}

fn errors(source: &str) -> Vec<String> {
    let mut f = tempfile::Builder::new()
        .prefix("average-date-label-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    let ledger = load(f.path(), &LoadOptions::default()).expect("the ledger loads");
    ledger.errors.iter().map(|e| e.message.clone()).collect()
}

#[test]
fn a_date_or_label_on_an_average_sale_is_reported_once() {
    for (spec, stated) in [
        // The date the first lot was bought on: still no lot, the pool is
        // undated.
        ("{2024-01-02}", "2024-01-02"),
        // A date no lot has.
        ("{2024-01-05}", "2024-01-05"),
        // The label the first lot was bought with.
        (r#"{"lot-a"}"#, r#""lot-a""#),
        // Beside a correct cost and currency.
        ("{11.00 EUR, 2024-01-02}", "2024-01-02"),
        (r#"{EUR, "lot-a"}"#, r#""lot-a""#),
    ] {
        let errors = errors(&ledger(spec));
        assert_eq!(
            errors,
            [format!(
                "Assets:B: AVERAGE pool of X is one lot with no date or label, so the cost \
                 spec's {stated} describes no lot; remove it (2024-03-01, \"sell\")"
            )],
            "{spec}"
        );
    }
}

#[test]
fn an_average_sale_without_a_date_or_label_books_as_before() {
    for spec in ["{}", "{EUR}", "{11.00 EUR}"] {
        assert_eq!(errors(&ledger(spec)), Vec::<String>::new(), "{spec}");
    }
}

/// `{*}` keeps its own words for the same claim (#2398).
#[test]
fn a_merge_spec_keeps_its_own_message() {
    let errors = errors(&ledger("{*, 2024-01-02}"));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].contains("the merge builds one lot with no date or label"),
        "{errors:?}"
    );
}

/// A single-lot pool, a buy with a date and label, and covering a short:
/// buys keep theirs, and a sale or cover writing one is refused even when the
/// pool is the one lot bought on that date.
#[test]
fn buys_keep_their_date_and_label_and_every_reduction_refuses_one() {
    let base = r#"2024-01-01 open Assets:B X "AVERAGE"
2024-01-01 open Assets:S X "AVERAGE"
2024-01-01 open Assets:C
2024-01-01 open Income:G

2024-01-02 * "buy, dated and labeled"
  Assets:B  10 X {10.00 EUR, 2024-01-02, "lot-a"}
  Assets:C

2024-03-02 * "open a short"
  Assets:S  -20 X {15.00 EUR, 2024-03-02}
  Assets:C  300 EUR
"#;
    assert_eq!(errors(base), Vec::<String>::new());

    let sale = format!(
        "{base}\n2024-03-03 * \"sell\"\n  Assets:B  -1 X {{2024-01-02}} @ 15 EUR\n  \
         Assets:C  15 EUR\n  Income:G\n"
    );
    assert_eq!(errors(&sale).len(), 1, "{:?}", errors(&sale));

    let cover = format!(
        "{base}\n2024-03-03 * \"cover\"\n  Assets:S  5 X {{2024-03-02}} @ 14 EUR\n  \
         Assets:C  -70 EUR\n  Income:G\n"
    );
    let errors = errors(&cover);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("Assets:S: AVERAGE pool of X"),
        "{errors:?}"
    );
}

/// A sale written with its units elided never reaches booking's lot matching:
/// interpolation solves the units and `apply` reduces the pool. It used to
/// drop the date there too.
#[test]
fn an_elided_units_sale_refuses_a_date_too() {
    let source = r#"2024-01-01 open Assets:B X "AVERAGE"
2024-01-01 open Assets:C

2024-01-02 * "buy"
  Assets:B  10 X {10.00 EUR, 2024-01-02}
  Assets:C

2024-03-01 * "sell, units elided"
  Assets:B  X {10.00 EUR, 2024-01-02}
  Assets:C  10.00 EUR
"#;
    let reported = errors(source);
    assert_eq!(reported.len(), 1, "{reported:?}");
    assert!(
        reported[0].starts_with(
            "Assets:B: AVERAGE pool of X is one lot with no date or label, so the cost \
             spec's 2024-01-02 describes no lot"
        ),
        "{reported:?}"
    );
    // Without the date it books, as before.
    let undated = source.replace(
        "X {10.00 EUR, 2024-01-02}\n  Assets:C  10",
        "X {10.00 EUR}\n  Assets:C  10",
    );
    assert_ne!(undated, source);
    assert_eq!(errors(&undated), Vec::<String>::new());
}
