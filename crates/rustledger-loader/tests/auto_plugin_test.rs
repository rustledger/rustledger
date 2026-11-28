//! `plugin "beancount.plugins.auto"` runs `auto_accounts` and then
//! `implicit_prices`, as beancount's does (`loader.combine_plugins`).
//!
//! Both parts run after booking, where the plugin is declared, as beancount
//! runs them; the reference is expanded into both by
//! `rustledger_plugin::plugin_parts`.
//! It used to be refused as an unsupported Python module (E8004), and then
//! every account it would have opened was reported as never opened.

#![cfg(all(feature = "validation", feature = "plugins"))]

use rustledger_core::Directive;
use rustledger_loader::{Ledger, LoadOptions, VirtualFileSystem, load_with_fs};
use std::path::Path;

fn load_source(text: &str) -> Ledger {
    let mut vfs = VirtualFileSystem::new();
    vfs.add_file("main.beancount", text);
    load_with_fs(
        Path::new("main.beancount"),
        &LoadOptions::default(),
        Box::new(vfs),
    )
    .expect("loads")
}

/// No `open`s, and one priced posting: `auto_accounts` must open the
/// accounts the booked transaction names and `implicit_prices` must add the
/// price. `Income:Gains` is elided and books to zero, which booking drops,
/// so after booking (where beancount runs the plugin, and so does rledger)
/// nothing names it: bean-check 3.2.3 opens `Assets:Cash` and
/// `Assets:Stock` only.
const LEDGER: &str = "2024-01-02 * \"buy\"\n  Assets:Stock  2 HOOL {10 USD} @ 11 USD\n  \
    Assets:Cash  -20 USD\n  Income:Gains\n";

#[test]
fn test_auto_plugin_runs_auto_accounts_and_implicit_prices() {
    for name in ["beancount.plugins.auto", "auto"] {
        let ledger = load_source(&format!("plugin \"{name}\"\n{LEDGER}"));
        let errors: Vec<_> = ledger
            .errors
            .iter()
            .map(|e| format!("{}: {}", e.code, e.message))
            .collect();
        assert!(errors.is_empty(), "{name}: {errors:?}");
        let opens = ledger
            .directives
            .iter()
            .filter(|d| matches!(d.value, Directive::Open(_)))
            .count();
        assert_eq!(opens, 2, "{name}: auto_accounts opens the booked accounts");
        let prices: Vec<_> = ledger
            .directives
            .iter()
            .filter_map(|d| match &d.value {
                Directive::Price(p) => Some(format!("{} {}", p.currency, p.amount)),
                _ => None,
            })
            .collect();
        assert_eq!(
            prices,
            ["HOOL 11 USD"],
            "{name}: implicit_prices adds the price"
        );
    }
}

/// Without the plugin, the same ledger fails: the test above is not passing
/// for some other reason.
#[test]
fn test_auto_plugin_ledger_needs_the_plugin() {
    let ledger = load_source(LEDGER);
    assert!(
        ledger.errors.iter().any(|e| e.code == "E1001"),
        "{:?}",
        ledger.errors
    );
}

/// `check --auto` (`LoadOptions::auto_accounts`) loads the same plugin as
/// `bean-check --auto` (`beancount.plugins.auto`): it opened the accounts but
/// added no implicit price.
#[test]
fn test_auto_flag_runs_auto_accounts_and_implicit_prices() {
    let mut vfs = VirtualFileSystem::new();
    vfs.add_file("main.beancount", LEDGER);
    let options = LoadOptions {
        auto_accounts: true,
        ..LoadOptions::default()
    };
    let ledger = load_with_fs(Path::new("main.beancount"), &options, Box::new(vfs)).expect("loads");
    assert!(ledger.errors.is_empty(), "{:?}", ledger.errors);
    let opens = ledger
        .directives
        .iter()
        .filter(|d| matches!(d.value, Directive::Open(_)))
        .count();
    let prices = ledger
        .directives
        .iter()
        .filter(|d| matches!(d.value, Directive::Price(_)))
        .count();
    assert_eq!((opens, prices), (2, 1));
}

fn opened(ledger: &Ledger) -> Vec<String> {
    ledger
        .directives
        .iter()
        .filter_map(|s| match &s.value {
            Directive::Open(o) => Some(o.account.to_string()),
            _ => None,
        })
        .collect()
}

/// `auto_accounts` runs after booking, as beancount runs it, so it opens
/// nothing for a transaction booking refused: beancount's plugin never sees
/// one. It ran before booking, and opened `Assets:Broker`, which only the
/// refused sale below names; bean-check 3.2.3 opens `Assets:Cash` and
/// `Assets:Stock` and reports the sale's booking error alone. No account of
/// the sale is reported as never opened either: Early judges against the
/// opens the plugin would insert (`early_validation_view`).
#[test]
fn test_auto_accounts_opens_nothing_for_a_transaction_booking_refuses() {
    let ledger = load_source(
        "plugin \"beancount.plugins.auto_accounts\"\n\
         2024-01-02 * \"buy\"\n  Assets:Stock  2 HOOL {10 USD}\n  Assets:Cash  -20 USD\n\
         2024-01-03 * \"oversell\"\n  Assets:Stock  -5 HOOL {}\n  Assets:Broker  50 USD\n",
    );
    let codes: Vec<&str> = ledger.errors.iter().map(|e| e.code.as_str()).collect();
    assert!(!codes.contains(&"E1001"), "{:?}", ledger.errors);
    assert_eq!(
        codes.len(),
        1,
        "the booking error alone: {:?}",
        ledger.errors
    );
    assert_eq!(opened(&ledger), ["Assets:Cash", "Assets:Stock"]);
}
