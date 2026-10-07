//! A units number written without its currency takes the currency the
//! account holds when nothing else in the transaction names one (#2465).
//!
//! End-to-end through `load`, so the loader's booking pass, the running
//! balances it books against, and the validator after it all take part. The
//! rule itself is pinned case by case in
//! `rustledger-booking/tests/elided_units_currency_2465.rs`.

use rustledger_core::Directive;
use rustledger_loader::{LoadOptions, load};
use std::io::Write;

/// Load `source`, returning the error messages and the booked postings of
/// every transaction dated `2026-10-01` as `account number currency`.
fn load_ledger(source: &str) -> (Vec<String>, Vec<String>) {
    let mut f = tempfile::Builder::new()
        .prefix("elided-units-currency-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    let ledger = load(f.path(), &LoadOptions::default()).expect("the ledger loads");
    let errors = ledger.errors.iter().map(|e| e.message.clone()).collect();
    let mut booked = Vec::new();
    for d in &ledger.directives {
        if let Directive::Transaction(txn) = &d.value
            && txn.date.to_string() == "2026-10-01"
        {
            for p in &txn.postings {
                booked.push(match p.amount() {
                    Some(units) => format!("{} {} {}", p.account, units.number, units.currency),
                    None => format!("{} (unbooked)", p.account),
                });
            }
        }
    }
    (errors, booked)
}

const OPENS: &str = "2026-01-01 open Assets:Foo
2026-01-01 open Assets:Bar
2026-01-01 open Equity:Opening
";

/// The issue's ledger verbatim. Beancount 3.2.3 accepts it and books
/// `42.50 USD` / `-42.50 USD`; rledger refused it with "cannot infer currency
/// for posting to account Assets:Foo".
#[test]
fn the_issue_ledger_books_in_the_accounts_currency() {
    let (errors, booked) = load_ledger(&format!(
        "{OPENS}
2026-01-02 *
    Assets:Foo       100.00 USD
    Equity:Opening

2026-10-01 !
    Assets:Foo    42.50
    Assets:Bar
"
    ));
    assert!(errors.is_empty(), "beancount accepts this: {errors:?}");
    assert_eq!(booked, ["Assets:Foo 42.50 USD", "Assets:Bar -42.50 USD"]);
}

/// An `open` directive's currency list is NOT a source, in beancount or here:
/// with an empty balance, the posting is refused.
#[test]
fn an_open_constraint_is_not_a_source() {
    let (errors, _) = load_ledger(
        "2026-01-01 open Assets:Foo USD
2026-01-01 open Assets:Bar

2026-10-01 *
    Assets:Foo    42.50
    Assets:Bar
",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("cannot infer currency for posting to account Assets:Foo")),
        "{errors:?}"
    );
}

/// A pad is expanded after booking, in beancount and here, so an account
/// funded only by a pad holds nothing when the transaction books. Beancount:
/// "Failed to categorize posting 1".
#[test]
fn a_pad_does_not_count_as_a_balance() {
    let (errors, _) = load_ledger(&format!(
        "{OPENS}
2026-01-02 pad Assets:Foo Equity:Opening
2026-01-03 balance Assets:Foo 100.00 USD

2026-10-01 *
    Assets:Foo    42.50
    Assets:Bar
"
    ));
    assert!(
        errors
            .iter()
            .any(|e| e.contains("cannot infer currency for posting to account Assets:Foo")),
        "{errors:?}"
    );
}

/// The currency is resolved, the number is kept, and an imbalance is still
/// reported (#1920's guarantee survives the new source).
#[test]
fn a_resolved_posting_that_does_not_balance_is_reported() {
    let (errors, booked) = load_ledger(&format!(
        "{OPENS}
2026-01-02 *
    Assets:Foo       100.00 USD
    Equity:Opening

2026-10-01 *
    Assets:Foo    42.50
    Assets:Bar    40.00
    Equity:Opening -100.00 USD
"
    ));
    // Bar holds nothing, but Foo and Bar are two undetermined postings, so the
    // group rule is out for both and Bar has no balance: refused.
    assert!(
        errors
            .iter()
            .any(|e| e.contains("cannot infer currency for posting to account Assets:Bar")),
        "{errors:?} {booked:?}"
    );

    let (errors, booked) = load_ledger(&format!(
        "{OPENS}
2026-01-02 *
    Assets:Foo       100.00 USD
    Equity:Opening

2026-10-01 *
    Assets:Foo    42.50
    Assets:Bar   -50.00 USD
"
    ));
    assert_eq!(booked, ["Assets:Foo 42.50 USD", "Assets:Bar -50.00 USD"]);
    assert!(
        errors.iter().any(|e| e.contains("does not balance")),
        "{errors:?}"
    );
}
