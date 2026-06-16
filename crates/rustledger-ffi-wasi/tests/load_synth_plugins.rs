//! Integration tests pinning that the FFI load surface runs the pre-booking
//! SYNTH plugin pass (`auto_accounts`, `document_discovery`).
//!
//! ## Why this file exists
//!
//! The FFI `load_file` / `load_source` helpers used to hand-roll a *partial*
//! loader (parse + a manual booking loop) that ran in parallel to the canonical
//! `rustledger_loader::process::load` pipeline. That hand-rolled path skipped
//! the pre-booking synth pass entirely, so `auto_accounts` never generated
//! `Open` directives through ANY FFI surface — even though the native loader
//! did (proven by `rustledger-loader`'s `test_plugin_execution_auto_accounts`).
//! No FFI/component test asserted synth behavior, so the divergence shipped
//! green. These tests close that gap and guard against the duplicated pipeline
//! drifting again.
//!
//! ## Assertion strategy
//!
//! Each synth test pins TWO properties:
//!  1. the synth `Open` directives are present, AND
//!  2. they carry NO real source position (lineno 0 / `<unknown>` file) — the
//!     "generated entry" fingerprint that embedders (rustfava) key on to forbid
//!     editing synthesized directives.

use rustledger_core::Directive;
use rustledger_ffi_wasi::helpers::{load_file, load_source};
use rustledger_ffi_wasi::jsonrpc::process_request;
use std::fs;
use tempfile::TempDir;

/// Ledger that declares `plugin "auto_accounts"` and contains NO explicit
/// `open` directives — the synth pass must generate one per used account.
const AUTO_ACCOUNTS_LEDGER: &str = "\
option \"operating_currency\" \"USD\"
plugin \"auto_accounts\"

2024-01-15 * \"Paycheck\"
  Assets:Bank:Checking                    5000 USD
  Income:Salary                          -5000 USD

2024-01-20 * \"Groceries\"
  Expenses:Food                            50 USD
  Assets:Bank:Checking                    -50 USD
";

/// A valid ledger with explicit opens and no synth plugin — used to prove the
/// fix does NOT fabricate generated directives for ordinary ledgers.
const EXPLICIT_OPENS_LEDGER: &str = "\
option \"operating_currency\" \"USD\"
2024-01-01 open Assets:Bank:Checking USD
2024-01-01 open Income:Salary USD

2024-01-15 * \"Paycheck\"
  Assets:Bank:Checking                    5000 USD
  Income:Salary                          -5000 USD
";

const EXPECTED_ACCOUNTS: [&str; 3] = ["Assets:Bank:Checking", "Income:Salary", "Expenses:Food"];

fn open_accounts(dirs: &[Directive]) -> Vec<String> {
    dirs.iter()
        .filter_map(|d| match d {
            Directive::Open(o) => Some(o.account.to_string()),
            _ => None,
        })
        .collect()
}

/// `helpers::load_file` must run `auto_accounts` and surface the generated
/// Opens with no real source position.
#[test]
fn load_file_runs_auto_accounts_synth() {
    let dir = TempDir::new().expect("tempdir");
    let path = dir.path().join("main.beancount");
    fs::write(&path, AUTO_ACCOUNTS_LEDGER).expect("write ledger");

    let fl = load_file(&path, true).expect("load_file should succeed");
    let opens = open_accounts(&fl.directives);
    for acct in EXPECTED_ACCOUNTS {
        assert!(
            opens.iter().any(|a| a == acct),
            "auto_accounts should synthesize an Open for {acct} via load_file; got opens: {opens:?}"
        );
    }

    // Each synthesized Open carries no real file/line (the generated marker).
    for (i, d) in fl.directives.iter().enumerate() {
        if let Directive::Open(o) = d {
            let acct = o.account.to_string();
            if EXPECTED_ACCOUNTS.contains(&acct.as_str()) {
                assert_eq!(
                    fl.directive_lines[i], 0,
                    "synth Open {acct} must have lineno 0"
                );
                assert_eq!(
                    fl.directive_files[i], "<unknown>",
                    "synth Open {acct} must have <unknown> originating file"
                );
            }
        }
    }

    // Synth runs before booking, so no "account not opened" diagnostic fires.
    assert!(
        !fl.errors
            .iter()
            .any(|e| e.message.to_lowercase().contains("not opened")),
        "no account-not-opened error expected; got: {:?}",
        fl.errors
            .iter()
            .map(|e| e.message.clone())
            .collect::<Vec<_>>()
    );
}

/// `helpers::load_source` (string surface, used by `ledger.load` and the
/// component crate) must also run the synth pass.
#[test]
fn load_source_runs_auto_accounts_synth() {
    let lr = load_source(AUTO_ACCOUNTS_LEDGER);
    let opens = open_accounts(&lr.directives);
    for acct in EXPECTED_ACCOUNTS {
        assert!(
            opens.iter().any(|a| a == acct),
            "auto_accounts should synthesize an Open for {acct} via load_source; got opens: {opens:?}"
        );
    }
    for (i, d) in lr.directives.iter().enumerate() {
        if let Directive::Open(o) = d
            && EXPECTED_ACCOUNTS.contains(&o.account.to_string().as_str())
        {
            assert_eq!(lr.directive_lines[i], 0, "synth Open must have lineno 0");
        }
    }
}

/// End-to-end through the JSON-RPC `ledger.loadFile` handler: the synth Opens
/// must appear in `result.entries[]` with `meta.lineno == 0` (the generated
/// fingerprint a JSON consumer sees).
#[test]
fn jsonrpc_load_file_emits_synth_opens() {
    let dir = TempDir::new().expect("tempdir");
    let path = dir.path().join("main.beancount");
    fs::write(&path, AUTO_ACCOUNTS_LEDGER).expect("write ledger");
    let path_str = path.to_str().expect("utf-8 path");

    let req = serde_json::json!({
        "jsonrpc": "2.0", "id": 1, "method": "ledger.loadFile",
        "params": { "path": path_str },
    })
    .to_string();
    let response = serde_json::to_value(process_request(&req)).unwrap();

    let entries = response
        .pointer("/result/entries")
        .and_then(|v| v.as_array())
        .unwrap_or_else(|| panic!("expected entries array; response: {response}"));

    for acct in EXPECTED_ACCOUNTS {
        let synth_open = entries.iter().find(|e| {
            e.get("account").and_then(|a| a.as_str()) == Some(acct)
                && e.pointer("/meta/lineno")
                    .and_then(serde_json::Value::as_u64)
                    == Some(0)
        });
        assert!(
            synth_open.is_some(),
            "expected a generated Open for {acct} with meta.lineno==0; entries: {entries:?}"
        );
    }
}

/// End-to-end through `ledger.load` (string surface).
#[test]
fn jsonrpc_load_emits_synth_opens() {
    let req = serde_json::json!({
        "jsonrpc": "2.0", "id": 1, "method": "ledger.load",
        "params": { "source": AUTO_ACCOUNTS_LEDGER },
    })
    .to_string();
    let response = serde_json::to_value(process_request(&req)).unwrap();

    let entries = response
        .pointer("/result/entries")
        .and_then(|v| v.as_array())
        .unwrap_or_else(|| panic!("expected entries array; response: {response}"));

    for acct in EXPECTED_ACCOUNTS {
        assert!(
            entries.iter().any(|e| {
                e.get("account").and_then(|a| a.as_str()) == Some(acct)
                    && e.pointer("/meta/lineno")
                        .and_then(serde_json::Value::as_u64)
                        == Some(0)
            }),
            "expected a generated Open for {acct} with meta.lineno==0 via ledger.load"
        );
    }
}

/// Regression guard: a plain ledger with explicit opens and no synth plugin
/// must NOT gain spurious generated directives, and its real opens keep their
/// true source positions.
#[test]
fn load_file_no_synth_for_plain_ledger() {
    let dir = TempDir::new().expect("tempdir");
    let path = dir.path().join("main.beancount");
    fs::write(&path, EXPLICIT_OPENS_LEDGER).expect("write ledger");

    let fl = load_file(&path, true).expect("load_file should succeed");
    let opens = open_accounts(&fl.directives);
    assert_eq!(
        opens.len(),
        2,
        "plain ledger should keep exactly its 2 explicit opens, got: {opens:?}"
    );
    // Every directive has a real (>0) line and a concrete originating file.
    for (i, line) in fl.directive_lines.iter().enumerate() {
        assert!(
            *line > 0,
            "explicit directive {i} should have a real lineno, got 0"
        );
        assert_ne!(
            fl.directive_files[i], "<unknown>",
            "explicit directive {i} should have a real file"
        );
    }
}
