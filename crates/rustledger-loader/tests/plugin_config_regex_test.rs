//! Regular expressions in native plugin configs mean what they mean in
//! Python's `re`, or are refused with an error naming the plugin and the
//! construct, never matched differently (#2601).
//!
//! Each "as beancount" case was checked against beancount 3.2 with
//! `beancount_reds_plugins`; the comment on each gives what beancount does.

use rustledger_core::Directive;
use rustledger_loader::{Ledger, LoadOptions, load};

fn load_source(source: &str) -> Ledger {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join("main.beancount");
    std::fs::write(&path, source).expect("write fixture");
    load(&path, &LoadOptions::default()).expect("the ledger loads")
}

fn posting_accounts(ledger: &Ledger) -> Vec<String> {
    ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .flat_map(|t| t.postings.iter().map(|p| p.account.to_string()))
        .collect()
}

fn messages(ledger: &Ledger) -> Vec<&str> {
    ledger.errors.iter().map(|e| e.message.as_str()).collect()
}

/// beancount: `\1` in a `rename_accounts` replacement is group 1 (`$1` would
/// be literal text). The beancount string and the Python literal each take
/// one level of backslashes. rledger used Rust's replacement syntax and
/// produced `Expenses:Dining:\1`.
#[test]
fn rename_accounts_replacement_uses_python_group_references() {
    let ledger = load_source(
        "plugin \"beancount_reds_plugins.rename_accounts.rename_accounts\" \
         \"{'Expenses:Food:(.*)': 'Expenses:Dining:\\\\\\\\1'}\"\n\
         2024-01-01 open Assets:Cash\n2024-01-01 open Expenses:Food:Lunch\n\
         2024-01-02 * \"x\"\n  Expenses:Food:Lunch  1 USD\n  Assets:Cash\n",
    );
    assert_eq!(
        posting_accounts(&ledger),
        ["Expenses:Dining:Lunch", "Assets:Cash"],
        "{:?}",
        messages(&ledger)
    );
}

/// beancount: `long_short` matches its pattern with `re.match`, at the start
/// of the account, so `Capital-Gains` does not match `Income:Capital-Gains`
/// and nothing is reclassified. rledger searched anywhere in the account and
/// split the gain into `:Short`.
#[test]
fn long_short_matches_at_the_start_of_the_account() {
    let ledger = load_source(
        "plugin \"beancount_reds_plugins.capital_gains_classifier.long_short\" \
         \"{'Capital-Gains': [':Capital-Gains', ':Capital-Gains:Short', ':Capital-Gains:Long']}\"\n\
         2020-01-01 open Assets:Cash\n2020-01-01 open Assets:Stock\n\
         2020-01-01 open Income:Capital-Gains\n\
         2024-01-02 * \"buy\"\n  Assets:Stock  10 AAA {10 USD}\n  Assets:Cash\n\
         2024-02-01 * \"sell\"\n  Assets:Stock  -10 AAA {10 USD} @ 20 USD\n  \
         Assets:Cash  200 USD\n  Income:Capital-Gains  -100 USD\n",
    );
    let accounts = posting_accounts(&ledger);
    assert!(
        accounts
            .iter()
            .all(|a| !a.contains("Short") && !a.contains("Long")),
        "{accounts:?}"
    );
    assert!(ledger.errors.is_empty(), "{:?}", messages(&ledger));
}

/// beancount: `&&` in a character class is two literal `&`s, so `[A&&B]BC`
/// matches `ABC` and `check_commodity` ignores it. To Rust's `regex` it was a
/// class intersection matching nothing, and rledger reported the commodity.
#[test]
fn check_commodity_class_reads_double_ampersand_as_literal() {
    let ledger = load_source(
        "plugin \"beancount.plugins.check_commodity\" \"{'Assets:Stock': '[A&&B]BC'}\"\n\
         2024-01-01 commodity USD\n\
         2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Stock\n\
         2024-01-02 * \"buy\"\n  Assets:Stock  1 ABC {1 USD}\n  Assets:Cash  -1 USD\n",
    );
    assert!(ledger.errors.is_empty(), "{:?}", messages(&ledger));
}

/// beancount renames with the lookbehind; rledger cannot express one, so it
/// renames nothing and says so, naming the plugin and the construct.
#[test]
fn rename_accounts_reports_a_lookbehind_it_cannot_express() {
    let ledger = load_source(
        "plugin \"beancount_reds_plugins.rename_accounts.rename_accounts\" \
         \"{'(?<=Expenses:)Food': 'Dining'}\"\n\
         2024-01-01 open Assets:Cash\n2024-01-01 open Expenses:Food\n\
         2024-01-02 * \"x\"\n  Expenses:Food  1 USD\n  Assets:Cash\n",
    );
    let errors = messages(&ledger);
    assert!(
        errors
            .iter()
            .any(|m| m.contains("rename_accounts") && m.contains("lookbehind")),
        "{errors:?}"
    );
    assert_eq!(posting_accounts(&ledger), ["Expenses:Food", "Assets:Cash"]);
}

/// beancount checks `Assets:Mixed` (the negative lookahead excludes only
/// `Assets:Cash`); rledger cannot express it and says so.
#[test]
fn onecommodity_reports_a_lookahead_it_cannot_express() {
    let ledger = load_source(
        "plugin \"beancount.plugins.onecommodity\" \"Assets:(?!Cash)\"\n\
         2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Mixed\n\
         2024-01-02 * \"x\"\n  Assets:Mixed  1 AAA\n  Assets:Mixed  1 BBB\n  \
         Assets:Cash  -1 AAA\n  Assets:Cash  -1 BBB\n",
    );
    let errors = messages(&ledger);
    assert!(
        errors
            .iter()
            .any(|m| m.contains("onecommodity") && m.contains("negative lookahead")),
        "{errors:?}"
    );
}

/// beancount renames `Assets:Cash` to `Assets:Bank:Bank` with
/// `'(:Cash)?$': ':Bank'`: `re.sub` also replaces the empty match at the end
/// after the non-empty one, which rledger's engine does not. A pattern that
/// can match empty is refused, by name, rather than renamed differently.
#[test]
fn rename_accounts_refuses_a_pattern_that_can_match_empty() {
    let ledger = load_source(
        "plugin \"beancount_reds_plugins.rename_accounts.rename_accounts\" \
         \"{'(:Cash)?$': ':Bank'}\"\n\
         2024-01-01 open Assets:Cash\n2024-01-01 open Expenses:Food\n\
         2024-01-02 * \"x\"\n  Expenses:Food  1 USD\n  Assets:Cash\n",
    );
    let errors = messages(&ledger);
    assert!(
        errors
            .iter()
            .any(|m| m.contains("rename_accounts") && m.contains("empty string")),
        "{errors:?}"
    );
    assert_eq!(posting_accounts(&ledger), ["Expenses:Food", "Assets:Cash"]);
}

/// A `$1` is literal text to `re.sub`, as to beancount; a config written for
/// rledger's old reading gets a warning pointing at `\1`.
#[test]
fn rename_accounts_warns_about_a_dollar_group_reference() {
    let ledger = load_source(
        "plugin \"beancount_reds_plugins.rename_accounts.rename_accounts\" \
         \"{'Expenses:Food:(.*)': 'Expenses:Dining:$1'}\"\n\
         2024-01-01 open Assets:Cash\n2024-01-01 open Expenses:Food:Lunch\n\
         2024-01-02 * \"x\"\n  Expenses:Food:Lunch  1 USD\n  Assets:Cash\n",
    );
    let errors = messages(&ledger);
    assert!(
        errors
            .iter()
            .any(|m| m.contains("rename_accounts") && m.contains("literal text")),
        "{errors:?}"
    );
}

/// beancount's `gain_loss` fails (it removes the posting twice) when a
/// second rule matches what the first rewrote; rledger reports it and
/// rewrites nothing, rather than chaining the rules.
#[test]
fn gain_loss_reports_two_rules_matching_one_posting() {
    let ledger = load_source(
        "plugin \"beancount_reds_plugins.capital_gains_classifier.gain_loss\" \
         \"{'Income:.*': [':CG', ':CG:Gains', ':CG:Losses'], 'Income:CG:.*': [':Gains', ':G', ':L']}\"\n\
         2024-01-01 open Assets:Cash\n2024-01-01 open Income:CG\n\
         2024-01-02 * \"x\"\n  Income:CG  -10 USD\n  Assets:Cash\n",
    );
    let errors = messages(&ledger);
    assert!(
        errors.iter().any(|m| m.contains("more than one rule")),
        "{errors:?}"
    );
    assert_eq!(posting_accounts(&ledger), ["Income:CG", "Assets:Cash"]);
}

/// beancount's `long_short` reads only its config's first entry, so a second
/// one it cannot use (a lookahead here) is ignored, not an error.
#[test]
fn long_short_reads_only_the_first_entry() {
    let ledger = load_source(
        "plugin \"beancount_reds_plugins.capital_gains_classifier.long_short\" \
         \"{'Income:Capital-Gains': [':Capital-Gains', ':Capital-Gains:Short', ':Capital-Gains:Long'], \
         'Income(?=x)': [':a', ':b', ':c']}\"\n\
         2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Stock\n\
         2024-01-01 open Income:Capital-Gains\n\
         2024-01-02 * \"buy\"\n  Assets:Stock  10 AAA {10 USD}\n  Assets:Cash\n\
         2024-02-01 * \"sell\"\n  Assets:Stock  -10 AAA {10 USD} @ 20 USD\n  \
         Assets:Cash  200 USD\n  Income:Capital-Gains  -100 USD\n",
    );
    assert!(ledger.errors.is_empty(), "{:?}", messages(&ledger));
    assert!(
        posting_accounts(&ledger)
            .iter()
            .any(|a| a == "Income:Capital-Gains:Short"),
        "{:?}",
        posting_accounts(&ledger)
    );
}
