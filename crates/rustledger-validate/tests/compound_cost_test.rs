//! Compound cost `{a # b}` — weight and booked-cost conformance (#1700).
//!
//! Beancount's `compound_amount`: `{a # b}` on N units costs `N*a + b` total,
//! booking per-unit `(N*a + b)/N`. Pre-#1700 the parser folded the form
//! into `{{b}}` (dropping `a`) and mis-read `{# b}` as `PerUnit{b}`, so
//! valid ledgers errored, invalid ones passed, and lots booked at wrong
//! cost bases. These tests pin the full table from the issue plus the
//! booked-cost case the coincidental example there masked.

mod common;

use rustledger_parser::parse;

/// Parse + validate a ledger, returning balance-error residual messages.
fn balance_errors(src: &str) -> Vec<String> {
    let parsed = parse(src);
    assert!(
        parsed.errors.is_empty(),
        "parse errors: {:?}",
        parsed.errors
    );
    let directives: Vec<_> = parsed.directives.into_iter().map(|d| d.value).collect();
    common::validate(&directives)
        .into_iter()
        .map(|e| e.to_string())
        .filter(|m| m.contains("balance"))
        .collect()
}

const HEADER: &str = "2024-01-01 open Assets:B\n2024-01-01 open Assets:Cash\n\n";

/// `{5.00 USD}` on 2 units weighs 10.00 — balances against −10.
#[test]
fn per_unit_form_balances() {
    let errors = balance_errors(&format!(
        "{HEADER}2024-01-10 * \"buy\"\n  Assets:B  2 VTI {{5.00 USD}}\n  Assets:Cash  -10.00 USD\n"
    ));
    assert!(errors.is_empty(), "{errors:?}");
}

/// `{5.00 # 0.00 USD}` weighs 2*5 + 0 = 10.00 — balances (pre-#1700:
/// weighed 0, false E3001).
#[test]
fn compound_zero_total_balances() {
    let errors = balance_errors(&format!(
        "{HEADER}2024-01-10 * \"buy\"\n  Assets:B  2 VTI {{5.00 # 0.00 USD}}\n  Assets:Cash  -10.00 USD\n"
    ));
    assert!(errors.is_empty(), "{errors:?}");
}

/// `{# 10.00 USD}` weighs 2*0 + 10 = 10.00 — balances (pre-#1700: parsed
/// as PerUnit{10}, weighed 20, false E3001).
#[test]
fn compound_total_only_balances() {
    let errors = balance_errors(&format!(
        "{HEADER}2024-01-10 * \"buy\"\n  Assets:B  2 VTI {{# 10.00 USD}}\n  Assets:Cash  -10.00 USD\n"
    ));
    assert!(errors.is_empty(), "{errors:?}");
}

/// `{5.00 # 10.00 USD}` weighs 2*5 + 10 = 20.00 — does NOT balance −10
/// (pre-#1700: weighed 10, the invalid ledger passed silently).
#[test]
fn compound_both_detects_imbalance() {
    let errors = balance_errors(&format!(
        "{HEADER}2024-01-10 * \"buy\"\n  Assets:B  2 VTI {{5.00 # 10.00 USD}}\n  Assets:Cash  -10.00 USD\n"
    ));
    assert!(
        !errors.is_empty(),
        "an unbalanced compound-cost transaction must be rejected"
    );
}

/// The valid version of the both-components form: −20 balances 2*5 + 10.
#[test]
fn compound_both_balances_at_full_weight() {
    let errors = balance_errors(&format!(
        "{HEADER}2024-01-10 * \"buy\"\n  Assets:B  2 VTI {{5.00 # 10.00 USD}}\n  Assets:Cash  -20.00 USD\n"
    ));
    assert!(errors.is_empty(), "{errors:?}");
}

/// The booked cost basis derives from the COMBINED total: `2 VTI
/// {6.00 # 10.00}` books at (2*6 + 10)/2 = 11.00/unit. The issue's
/// example (`{5.00 # 10.00}` on 2 units) coincidentally booked the right
/// per-unit under the old `{{10}}` misreading (10/2 = 5.00 = the written
/// 5.00); this asymmetric case pins the real derivation.
#[test]
fn compound_books_combined_per_unit() {
    use rustledger_core::{BookingMethod, Decimal};

    let src = format!(
        "{HEADER}2024-01-10 * \"buy\"\n  Assets:B  2 VTI {{6.00 # 10.00 USD}}\n  Assets:Cash  -22.00 USD\n"
    );
    let parsed = parse(&src);
    let directives: Vec<_> = parsed.directives.into_iter().map(|d| d.value).collect();
    let result = rustledger_booking::book(&directives, BookingMethod::Strict);
    assert!(
        result.failed.is_empty(),
        "booking failures: {:?}",
        result.failed
    );
    let txn = result
        .booked
        .iter()
        .find_map(|d| match d {
            rustledger_core::Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .expect("transaction present");
    let cost = txn.postings[0]
        .cost
        .as_ref()
        .and_then(|c| c.number)
        .expect("booked cost number");
    assert_eq!(
        cost.per_unit(),
        Some(Decimal::new(1100, 2)),
        "booked per-unit must be (2*6 + 10)/2 = 11.00, got {cost:?}"
    );
    assert_eq!(
        cost.total(),
        Some(Decimal::new(2200, 2)),
        "preserved total must be the combined 22.00, got {cost:?}"
    );
}

/// Reductions with compound specs (the case the FFI parity corpus caught):
/// the spec normalizes to an effective per-unit for lot matching, WITHOUT
/// injecting the sell date as a match filter, and `apply()` re-reduces from
/// the booked posting cleanly.
#[test]
fn compound_reduction_matches_and_books() {
    let src = format!(
        "{HEADER}2024-01-10 * \"buy\"\n  Assets:B  2 VTI {{6.00 # 10.00 USD}}\n  Assets:Cash  -22.00 USD\n\n\
         2024-02-10 * \"sell by resolved per-unit\"\n  Assets:B  -2 VTI {{11.00 USD}}\n  Assets:Cash  22.00 USD\n\n\
         2024-03-10 * \"buy again\"\n  Assets:B  2 VTI {{5.00 # 0.00 USD}}\n  Assets:Cash  -10.00 USD\n\n\
         2024-04-10 * \"sell filtering by compound spec\"\n  Assets:B  -2 VTI {{5.00 # 0.00 USD}}\n  Assets:Cash  10.00 USD\n"
    );
    let errors = balance_errors(&src);
    assert!(errors.is_empty(), "{errors:?}");
}
