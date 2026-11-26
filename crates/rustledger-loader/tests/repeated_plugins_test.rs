//! A plugin declared in more than one file of a ledger runs once.
//!
//! beancount 3.2.3 runs the top-level file's plugins only and ignores a
//! `plugin` in an included file. rledger runs an included file's plugins
//! too (a sub-ledger that declares `auto_accounts` for itself still works
//! when included), and so it runs each distinct `(name, config)` from the
//! first file that declares it only, in beancount's breadth-first file
//! order (`rustledger_loader::plugins_in_run_order`). Before, a plugin
//! declared in the main file and again in an include ran twice, and a
//! plugin that adds entries added them twice. A repeat within that one
//! file runs as written, as beancount runs a top-level file's repeat.
//!
//! The plugins here are not idempotent, so a second run shows:
//! `implicit_prices` adds a `price` per priced posting each time it runs,
//! and `check_commodity` reports a missing commodity each time it runs.

#![cfg(all(feature = "validation", feature = "plugins"))]

use rustledger_core::Directive;
use rustledger_loader::{Ledger, LoadOptions, VirtualFileSystem, load_with_fs};
use std::path::Path;

/// A transaction with one priced posting, so `implicit_prices` adds one
/// `price` each time it runs, in a commodity no `commodity` declares, so
/// `check_commodity` reports it each time it runs.
const BUY: &str = "2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Stock\n\
    2024-01-01 commodity USD\n\
    2024-01-02 * \"buy\"\n  Assets:Stock  1 HOOL @ 10 USD\n  Assets:Cash\n";

const IMPLICIT_PRICES: &str = "plugin \"beancount.plugins.implicit_prices\"\n";
const CHECK_COMMODITY: &str = "plugin \"beancount.plugins.check_commodity\"\n";

fn load_files(files: &[(&str, &str)]) -> Ledger {
    let mut vfs = VirtualFileSystem::new();
    for (name, text) in files {
        vfs.add_file(*name, *text);
    }
    load_with_fs(
        Path::new("main.beancount"),
        &LoadOptions::default(),
        Box::new(vfs),
    )
    .expect("loads")
}

fn prices(ledger: &Ledger) -> usize {
    ledger
        .directives
        .iter()
        .filter(|d| matches!(d.value, Directive::Price(_)))
        .count()
}

fn missing_commodity(ledger: &Ledger) -> usize {
    ledger
        .errors
        .iter()
        .filter(|e| {
            e.message
                .starts_with("Missing Commodity directive for 'HOOL'")
        })
        .count()
}

/// The plugins as they run: `(name, config)`.
fn run_order(ledger: &Ledger) -> Vec<(String, Option<String>)> {
    rustledger_loader::plugins_in_run_order(&ledger.plugins, &ledger.source_map)
        .into_iter()
        .map(|p| (p.name.clone(), p.config.clone()))
        .collect()
}

/// The plugins declared in the main file and again in an include run once:
/// one `price`, one missing-commodity error. Before, two of each.
#[test]
fn test_load_plugin_in_main_and_include_runs_once() {
    let main = format!("{IMPLICIT_PRICES}{CHECK_COMMODITY}include \"sub.beancount\"\n{BUY}");
    let sub = format!("{IMPLICIT_PRICES}{CHECK_COMMODITY}");
    let ledger = load_files(&[("main.beancount", &main), ("sub.beancount", &sub)]);
    assert_eq!(prices(&ledger), 1, "{:?}", ledger.directives);
    assert_eq!(missing_commodity(&ledger), 1, "{:?}", ledger.errors);
    // The declarations are all kept; the run takes each once.
    assert_eq!(ledger.plugins.len(), 4);
    assert_eq!(
        run_order(&ledger),
        [
            ("beancount.plugins.implicit_prices".to_string(), None),
            ("beancount.plugins.check_commodity".to_string(), None),
        ]
    );
}

/// A repeat two includes deep, and one in a sibling include, run once too:
/// `main` includes `x` then `y`, `x` includes `z`, and all four declare the
/// plugins.
#[test]
fn test_load_plugin_in_nested_includes_runs_once() {
    let main = format!(
        "{IMPLICIT_PRICES}include \"x.beancount\"\ninclude \"y.beancount\"\n{CHECK_COMMODITY}{BUY}"
    );
    let x = format!("include \"z.beancount\"\n{IMPLICIT_PRICES}{CHECK_COMMODITY}");
    let both = format!("{CHECK_COMMODITY}{IMPLICIT_PRICES}");
    let ledger = load_files(&[
        ("main.beancount", &main),
        ("x.beancount", &x),
        ("y.beancount", &both),
        ("z.beancount", &both),
    ]);
    assert_eq!(prices(&ledger), 1, "{:?}", ledger.directives);
    assert_eq!(missing_commodity(&ledger), 1, "{:?}", ledger.errors);
}

/// A plugin declared only in an included file still runs: the deliberate
/// difference from bean-check 3.2.3, which ignores it (no `price`, no
/// error there).
#[test]
fn test_load_plugin_only_in_include_still_runs_once() {
    let main = format!("include \"sub.beancount\"\n{BUY}");
    let sub = format!("{IMPLICIT_PRICES}{CHECK_COMMODITY}");
    let ledger = load_files(&[("main.beancount", &main), ("sub.beancount", &sub)]);
    assert_eq!(prices(&ledger), 1, "{:?}", ledger.directives);
    assert_eq!(missing_commodity(&ledger), 1, "{:?}", ledger.errors);
}

/// The same name with another config is another plugin, and runs: two
/// `price`s for two distinct configs (`implicit_prices` reads none), the
/// repeat of either config in a later file not run.
#[test]
fn test_load_plugin_with_different_config_runs_once_per_config() {
    let other = "plugin \"beancount.plugins.implicit_prices\" \"other\"\n";
    let main = format!("{IMPLICIT_PRICES}include \"sub.beancount\"\n{BUY}");
    let sub = format!("include \"deep.beancount\"\n{other}{IMPLICIT_PRICES}");
    let deep = format!("{other}{IMPLICIT_PRICES}");
    let ledger = load_files(&[
        ("main.beancount", &main),
        ("sub.beancount", &sub),
        ("deep.beancount", &deep),
    ]);
    assert_eq!(prices(&ledger), 2, "{:?}", ledger.directives);
    assert_eq!(
        run_order(&ledger),
        [
            ("beancount.plugins.implicit_prices".to_string(), None),
            (
                "beancount.plugins.implicit_prices".to_string(),
                Some("other".to_string())
            ),
        ]
    );
}

/// A repeat within one file runs as written: beancount runs every
/// declaration of the top-level file, a repeat again (two `price`s in
/// bean-check 3.2.3), and rledger keeps that, in the file a plugin runs
/// from. The same repeat in a later file still does not run.
#[test]
fn test_load_plugin_repeated_in_one_file_runs_as_written() {
    let main = format!("{IMPLICIT_PRICES}{IMPLICIT_PRICES}{BUY}");
    let ledger = load_files(&[("main.beancount", &main)]);
    assert_eq!(prices(&ledger), 2, "{:?}", ledger.directives);

    let main = format!("{IMPLICIT_PRICES}{IMPLICIT_PRICES}include \"sub.beancount\"\n{BUY}");
    let sub = format!("{IMPLICIT_PRICES}{IMPLICIT_PRICES}");
    let ledger = load_files(&[("main.beancount", &main), ("sub.beancount", &sub)]);
    assert_eq!(prices(&ledger), 2, "{:?}", ledger.directives);

    // Declared only in an include, twice: it runs from there, twice.
    let main = format!("include \"sub.beancount\"\n{BUY}");
    let ledger = load_files(&[("main.beancount", &main), ("sub.beancount", &sub)]);
    assert_eq!(prices(&ledger), 2, "{:?}", ledger.directives);
}

/// The files' plugins run in beancount's breadth-first file order, not the
/// depth-first order the files are read in: `main` includes `x` then `y`,
/// and `x` includes `z`, so `y`'s plugins run before `z`'s. `y` renames
/// `Assets:A` to `Assets:B` and `z` renames `Assets:B` to `Assets:C`: in
/// that order the account ends as `Assets:C`; depth first, `z`'s rename
/// ran first, found no `Assets:B`, and the account ended as `Assets:B`.
#[test]
fn test_load_included_plugins_run_in_breadth_first_order() {
    let rename = |from: &str, to: &str| {
        format!(
            "plugin \"beancount_reds_plugins.rename_accounts.rename_accounts\" \
             \"{{'{from}': '{to}'}}\"\n"
        )
    };
    let main = "include \"x.beancount\"\ninclude \"y.beancount\"\n\
        2024-01-01 open Assets:A\n2024-01-01 open Equity:O\n\
        2024-01-02 * \"t\"\n  Assets:A  1 USD\n  Equity:O\n";
    let y = rename("Assets:A", "Assets:B");
    let z = rename("Assets:B", "Assets:C");
    let ledger = load_files(&[
        ("main.beancount", main),
        ("x.beancount", "include \"z.beancount\"\n"),
        ("y.beancount", &y),
        ("z.beancount", &z),
    ]);
    let opened: Vec<&str> = ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Open(open) => Some(open.account.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(opened, ["Assets:C", "Equity:O"], "{:?}", ledger.errors);
}
