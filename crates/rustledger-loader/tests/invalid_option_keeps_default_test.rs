//! An option value its converter rejects is reported and NOT applied (#2911).
//!
//! beancount 3.2.3's `grammar.option` returns on the converter's `ValueError`
//! without assigning the option, so the option keeps its default (or an
//! earlier valid setting) and the bad value has no effect past its own error.
//! rledger reported the error and applied the value anyway, so
//! `option "name_equity" "capital"` also failed `open Equity:A` with E1005.
//!
//! These run the whole pipeline (load, book, plugins, validate), because the
//! bug's visible half was a DOWNSTREAM error, which a unit test on `Options`
//! cannot see.

use std::io::Write as _;

/// Load `src` through the full pipeline and return every error code: the
/// option errors first (`rledger check` reports them from `options.warnings`,
/// as `bean-check` reports option errors at the option), then the ledger's.
fn codes(src: &str) -> (Vec<String>, rustledger_loader::Options) {
    let dir = tempfile::Builder::new()
        .prefix("rledger_2911_")
        .tempdir()
        .expect("temp dir");
    let path = dir.path().join("main.beancount");
    let mut f = std::fs::File::create(&path).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    let ledger =
        rustledger_loader::load(&path, &rustledger_loader::LoadOptions::default()).expect("load");
    let codes = ledger
        .options
        .warnings
        .iter()
        .filter(|w| w.is_error())
        .map(|w| w.code.to_string())
        .chain(ledger.errors.iter().map(|e| e.code.clone()))
        .collect();
    (codes, ledger.options)
}

/// The issue's shape: only the option error, and `Equity:A` stays valid. (The
/// issue's own `"A😀"` is an invalid root only under #2908's strict account
/// check, which this shares through `is_valid_account_root`.)
#[test]
fn test_load_invalid_name_option_keeps_default_root() {
    let (codes, options) = codes("option \"name_equity\" \"capital\"\n2024-01-01 open Equity:A\n");
    assert_eq!(codes, ["E7008"]);
    assert_eq!(options.name_equity, "Equity");
}

/// A valid rename followed by an invalid one keeps the valid rename, so
/// accounts under the old default root are the ones rejected, as in beancount.
#[test]
fn test_load_invalid_name_option_keeps_earlier_valid_root() {
    let (codes, options) = codes(
        "option \"name_equity\" \"Capital\"\n\
         option \"name_equity\" \"bad\"\n\
         2024-01-01 open Capital:A\n\
         2024-01-01 open Equity:B\n",
    );
    assert_eq!(codes, ["E7008", "E1005"]);
    assert_eq!(options.name_equity, "Capital");
}

/// An invalid `account_*` value is one error and leaves the default, so the
/// pad into the default opening-balances account is not disturbed, and an
/// earlier valid leaf survives a later invalid one.
#[test]
fn test_load_invalid_account_option_keeps_earlier_valid_leaf() {
    let (codes, options) = codes(
        "option \"account_previous_balances\" \"Anfang\"\n\
         option \"account_previous_balances\" \"x\"\n\
         option \"account_rounding\" \"bad:leaf\"\n\
         2024-01-01 open Assets:A\n\
         2024-01-01 open Equity:Anfang\n\
         2024-01-02 pad Assets:A Equity:Anfang\n\
         2024-01-03 balance Assets:A 10 USD\n",
    );
    assert_eq!(codes, ["E7002", "E7002"]);
    assert_eq!(options.previous_balances_account(), "Equity:Anfang");
    assert_eq!(options.account_rounding, None);
}
