//! Regression: the string-input load surface (`load_source`, backing
//! `ledger.load`/`validate`/`query`) must run the canonical pipeline — the
//! post-booking *regular* plugin pass AND the date sort — not a hand-rolled
//! parse+book subset. Previously file-declared regular plugins silently no-oped
//! and directives booked in file order. See the FFI pipeline collapse.

use rustledger_core::Directive;
use rustledger_ffi_wasi::helpers::load_source;

/// A file-declared regular plugin (`rename_accounts`) rewrites postings when a
/// ledger is loaded from source text.
#[test]
fn load_source_runs_file_declared_regular_plugin() {
    let src = "plugin \"rename_accounts\" \"{'Expenses:Old': 'Expenses:New'}\"\n\
               2020-01-01 open Assets:Cash\n2020-01-01 open Expenses:New\n\
               2020-01-02 * \"x\"\n  Assets:Cash  -10.00 USD\n  Expenses:Old  10.00 USD\n";
    let r = load_source(src);
    let posting_accounts: Vec<String> = r
        .directives
        .iter()
        .filter_map(|d| match d {
            Directive::Transaction(t) => Some(
                t.postings
                    .iter()
                    .map(|p| p.account.to_string())
                    .collect::<Vec<_>>()
                    .join(","),
            ),
            _ => None,
        })
        .collect();
    assert!(
        posting_accounts.iter().any(|a| a.contains("Expenses:New"))
            && !posting_accounts.iter().any(|a| a.contains("Expenses:Old")),
        "rename_accounts must run through load_source; got {posting_accounts:?}"
    );
}

/// Directives are date-sorted before they reach consumers, regardless of file
/// order — the canonical pipeline sorts; the old hand-rolled path did not.
#[test]
fn load_source_sorts_directives_by_date() {
    // Later-dated transaction appears FIRST in file order.
    let src = "2020-01-01 open Assets:Cash\n2020-01-01 open Expenses:Food\n\
               2020-03-01 * \"later\"\n  Assets:Cash  -2.00 USD\n  Expenses:Food  2.00 USD\n\
               2020-02-01 * \"earlier\"\n  Assets:Cash  -1.00 USD\n  Expenses:Food  1.00 USD\n";
    let r = load_source(src);
    let narrations: Vec<String> = r
        .directives
        .iter()
        .filter_map(|d| match d {
            Directive::Transaction(t) => Some(t.narration.to_string()),
            _ => None,
        })
        .collect();
    assert_eq!(
        narrations,
        vec!["earlier".to_string(), "later".to_string()],
        "load_source must emit date-sorted directives; got {narrations:?}"
    );
}

/// A bare source declaring an `include` lists it without resolving it, and must
/// NOT emit a parse-phase "file not found" error (which would suppress
/// `ledger.validate`).
#[test]
fn load_source_lists_includes_without_resolution_error() {
    let src = "include \"accounts.beancount\"\n\
               2020-01-02 * \"x\"\n  Assets:Cash  -10.00 USD\n  Expenses:Food  10.00 USD\n";
    let r = load_source(src);
    let include_paths: Vec<String> = r.includes.iter().map(|i| i.path.clone()).collect();
    assert!(
        include_paths.iter().any(|p| p == "accounts.beancount"),
        "declared include should be listed; got {include_paths:?}"
    );
    assert!(
        !r.errors.iter().any(|e| e.message.contains("not found")),
        "unresolved include must not produce a not-found error; got {:?}",
        r.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}

/// Plugin *warnings* (e.g. `unrealized`'s gain/loss notices), which now flow
/// through the full pipeline, must surface to FFI consumers as warnings — not
/// errors.
#[test]
fn load_source_preserves_warning_severity() {
    let src = "plugin \"unrealized\" \"Equity:Unrealized\"\n\
               2020-01-01 open Assets:Stock\n2020-01-01 open Assets:Cash\n\
               2020-01-01 open Equity:Unrealized\n\
               2020-01-02 * \"buy\"\n  Assets:Stock  10 AAPL {100.00 USD}\n  Assets:Cash  -1000.00 USD\n\
               2020-06-01 price AAPL 150.00 USD\n";
    let r = load_source(src);
    assert!(
        r.errors.iter().any(|e| e.severity == "warning"),
        "unrealized gain must surface as a warning; got {:?}",
        r.errors
            .iter()
            .map(|e| (&e.severity, &e.message))
            .collect::<Vec<_>>()
    );
    assert!(
        !r.errors.iter().any(|e| e.severity == "error"),
        "the unrealized notice must not be reported as an error; got {:?}",
        r.errors
            .iter()
            .map(|e| (&e.severity, &e.message))
            .collect::<Vec<_>>()
    );
}

/// A glob `include` path that cannot be resolved on the string surface must not
/// error either (the literal-stub approach could not match a glob pattern).
#[test]
fn load_source_glob_include_does_not_error() {
    let src = "include \"[ab].beancount\"\n\
               2020-01-02 * \"x\"\n  Assets:Cash  -10.00 USD\n  Expenses:Food  10.00 USD\n";
    let r = load_source(src);
    assert!(
        !r.errors
            .iter()
            .any(|e| e.message.contains("does not match") || e.message.contains("not found")),
        "unresolved glob include must not produce an error; got {:?}",
        r.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}
