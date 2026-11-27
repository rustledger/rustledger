//! `plugin "beancount.plugins.auto"` runs `auto_accounts` and then
//! `implicit_prices`, as beancount's does (`loader.combine_plugins`).
//!
//! The two parts run in different passes here (`auto_accounts` opens
//! accounts before booking, `implicit_prices` reads booked costs), so the
//! reference is expanded into both by `rustledger_plugin::plugin_parts`.
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

/// No `open`s, and one priced posting: `auto_accounts` must open all three
/// accounts and `implicit_prices` must add the price.
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
        assert_eq!(opens, 3, "{name}: auto_accounts opens every account");
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
