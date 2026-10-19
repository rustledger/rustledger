//! Plugins get the ledger's tolerance options and booking's interpolation
//! marks, and the marks are gone from the ledger once they have run
//! (#2653). Each `sellgains` case was checked against beancount 3.2's
//! bean-check; the comment on each gives what it reports.

use rustledger_core::Directive;
use rustledger_loader::{Ledger, LoadOptions, load};

fn load_source(source: &str) -> Ledger {
    let dir = tempfile::tempdir().expect("temp dir");
    let path = dir.path().join("main.beancount");
    std::fs::write(&path, source).expect("write fixture");
    load(&path, &LoadOptions::default()).expect("the ledger loads")
}

fn messages(ledger: &Ledger) -> Vec<&str> {
    ledger.errors.iter().map(|e| e.message.as_str()).collect()
}

/// Every posting of the loaded ledger still carrying the mark.
fn marked(ledger: &Ledger) -> Vec<String> {
    ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .flat_map(|t| t.postings.iter())
        .filter(|p| p.meta.contains_key(rustledger_core::AUTOMATIC_META))
        .map(|p| p.account.to_string())
        .collect()
}

const OPEN: &str = "2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Stock\n\
                    2024-01-01 open Income:Gains\n";

/// beancount: cash booking computes as `40.0` gives no slack (it skips an
/// `__automatic__` posting), so 39.99 against 40.0 fails; the same cash
/// written allows 0.1 and passes. Plugins saw no mark before #2653, so
/// rledger passed both.
#[test]
fn sellgains_reads_the_interpolation_mark() {
    let ledger = load_source(&format!(
        "plugin \"beancount.plugins.sellgains\"\n{OPEN}\
         2024-01-02 * \"buy\"\n  Assets:Stock  10 AAA {{10.0 USD}}\n  Assets:Cash  -100.0 USD\n\
         2024-01-05 * \"interpolated cash\"\n  Assets:Stock  -3 AAA {{10.0 USD}} @ 13.33 USD\n  \
         Assets:Cash\n  Income:Gains  -10 USD\n\
         2024-01-06 * \"written cash\"\n  Assets:Stock  -3 AAA {{10.0 USD}} @ 13.33 USD\n  \
         Assets:Cash  40.0 USD\n  Income:Gains  -10 USD\n"
    ));
    assert_eq!(
        messages(&ledger),
        ["Invalid price vs. proceeds/gains: (39.99 USD) vs. (40.0 USD); difference: (-0.01 USD)"]
    );
    assert_eq!(ledger.errors[0].location.as_ref().map(|l| l.line), Some(8));
    // The marks went with the plugins.
    assert!(marked(&ledger).is_empty(), "{:?}", marked(&ledger));
}

/// beancount: a `tolerance_multiplier` of 5 lets proceeds 4 cents off pass
/// and fails 11 cents off; plugins got the default 0.5 before #2653, which
/// failed both.
#[test]
fn sellgains_reads_the_ledgers_tolerance_options() {
    let ledger = load_source(&format!(
        "option \"tolerance_multiplier\" \"5\"\nplugin \"beancount.plugins.sellgains\"\n{OPEN}\
         2024-01-02 * \"buy\"\n  Assets:Stock  10 AAA {{100 USD}}\n  Assets:Cash  -1000 USD\n\
         2024-01-05 * \"within\"\n  Assets:Stock  -2 AAA {{100 USD}} @ 150 USD\n  \
         Assets:Cash  300.04 USD\n  Income:Gains\n\
         2024-01-06 * \"beyond\"\n  Assets:Stock  -2 AAA {{100 USD}} @ 150 USD\n  \
         Assets:Cash  300.11 USD\n  Income:Gains\n"
    ));
    assert_eq!(
        messages(&ledger),
        ["Invalid price vs. proceeds/gains: (300 USD) vs. (300.11 USD); difference: (-0.11 USD)"]
    );
}

/// `Options::plugin_options` carries every tolerance option, the defaults
/// sorted by currency, so a plugin sees the same input on every run.
#[test]
fn plugin_options_carry_the_tolerance_options() {
    let ledger = load_source(
        "option \"inferred_tolerance_default\" \"USD:0.003\"\n\
         option \"inferred_tolerance_default\" \"*:0.5\"\n\
         option \"inferred_tolerance_default\" \"EUR:0.01\"\n\
         option \"tolerance_multiplier\" \"0.6\"\n\
         option \"infer_tolerance_from_cost\" \"TRUE\"\n",
    );
    let options = ledger.options.plugin_options();
    assert_eq!(
        options.inferred_tolerance_default,
        [
            ("*".to_string(), "0.5".to_string()),
            ("EUR".to_string(), "0.01".to_string()),
            ("USD".to_string(), "0.003".to_string()),
        ]
    );
    assert_eq!(options.tolerance_multiplier, "0.6");
    assert!(options.infer_tolerance_from_cost);

    let defaults = load_source("").options.plugin_options();
    assert!(defaults.inferred_tolerance_default.is_empty());
    assert_eq!(defaults.tolerance_multiplier, "0.5");
    assert!(!defaults.infer_tolerance_from_cost);
}

/// A plugin that sets the mark itself loses it too: `split_expenses` marks
/// the postings it adds, which reached the ledger, and `PRINT` could not
/// re-parse them.
#[test]
fn a_plugins_own_marks_are_removed() {
    let ledger = load_source(
        "plugin \"beancount.plugins.split_expenses\" \"Martin Caroline\"\n\
         2024-01-01 open Assets:Cash\n2024-01-01 open Expenses:Food\n\
         2024-01-01 open Expenses:Food:Martin\n2024-01-01 open Expenses:Food:Caroline\n\
         2024-01-02 * \"dinner\"\n  Expenses:Food  10.00 USD\n  Assets:Cash\n",
    );
    let accounts: Vec<String> = ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .flat_map(|t| t.postings.iter().map(|p| p.account.to_string()))
        .collect();
    assert!(
        accounts.iter().any(|a| a.ends_with(":Caroline")),
        "split_expenses ran: {accounts:?} {:?}",
        messages(&ledger)
    );
    assert!(marked(&ledger).is_empty(), "{:?}", marked(&ledger));
}
