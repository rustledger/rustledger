//! `recompute_balance_discrepancies` gives exactly the list a validating load
//! returns (#2823).
//!
//! The WASM and FFI query paths load without validation and recompute
//! discrepancies from the source map only when a query reads them. The
//! recomputation re-runs the loader's own validating pipeline, so it cannot
//! drift from `Ledger::balance_discrepancies`; this pins that it does not, on
//! every in-tree ledger and on a ledger spread over an include.

use rustledger_loader::{
    BalanceDiscrepancy, LoadOptions, Loader, VirtualFileSystem, load, process,
    recompute_balance_discrepancies,
};
use std::path::{Path, PathBuf};

fn render(list: &[BalanceDiscrepancy]) -> Vec<String> {
    list.iter()
        .map(|d| format!("{} {} {} {}", d.date, d.account, d.asserted, d.amount))
        .collect()
}

fn options(validate: bool) -> LoadOptions {
    LoadOptions {
        validate,
        ..Default::default()
    }
}

/// The validating load's list, and the list recomputed from a load that did
/// not validate.
fn both(path: &Path) -> Option<(Vec<String>, Vec<String>)> {
    let validated = load(path, &options(true)).ok()?;
    let plain = load(path, &options(false)).ok()?;
    let recomputed = recompute_balance_discrepancies(&plain.source_map, &options(false));
    Some((
        render(&validated.balance_discrepancies),
        render(&recomputed),
    ))
}

fn ledgers(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            ledgers(&path, out);
        } else if path.extension().is_some_and(|e| e == "beancount") {
            out.push(path);
        }
    }
}

#[test]
fn test_recompute_balance_discrepancies_agrees_with_a_validating_load_in_tree() {
    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut files = Vec::new();
    ledgers(&crates, &mut files);
    files.retain(|p| p.components().any(|c| c.as_os_str() == "tests"));
    assert!(
        files.len() > 20,
        "found only {} in-tree ledgers",
        files.len()
    );

    for path in &files {
        if let Some((validated, recomputed)) = both(path) {
            assert_eq!(recomputed, validated, "{}", path.display());
        }
    }
}

/// The in-tree ledgers hold no failing assertion, so the sweep above compares
/// empty lists. This ledger fails several, in the shapes that identify an
/// assertion (two on one account and date with different amounts, a pad, a
/// passing one within its tolerance, two currencies), so the comparison is
/// not vacuous.
#[test]
fn test_recompute_balance_discrepancies_agrees_on_failing_assertions() {
    let ledger = "2024-01-01 open Assets:Bank\n2024-01-01 open Assets:Other\n2024-01-01 open Equity:Opening\n2024-01-02 *\n  Assets:Bank     10 USD\n  Assets:Bank      5 EUR\n  Equity:Opening\n2024-01-03 pad Assets:Other Equity:Opening\n2024-01-05 balance Assets:Bank 999.00 USD\n2024-01-05 balance Assets:Bank 7.00 USD\n2024-01-05 balance Assets:Bank 5.001 EUR\n2024-01-05 balance Assets:Bank 9 EUR\n2024-01-06 balance Assets:Other 3 USD\n2024-01-07 balance Assets:Other 4 USD\n";
    let file = tempfile::Builder::new()
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    std::fs::write(file.path(), ledger).expect("write the ledger");
    let (validated, recomputed) = both(file.path()).expect("loads");
    assert!(
        validated.len() >= 4,
        "expected several failing assertions, got {validated:?}"
    );
    assert_eq!(recomputed, validated);
}

/// The issue's ledger, with the assertion in an included file: the
/// recomputation reads every file from the source map, not just the entry.
#[test]
fn test_recompute_balance_discrepancies_reads_included_files() {
    let mut vfs = VirtualFileSystem::new();
    vfs.add_file(
        "main.beancount",
        "include \"assert.beancount\"\n2024-01-01 open Assets:Bank\n2024-01-01 open Equity:Opening\n2024-01-02 *\n  Assets:Bank     10 USD\n  Equity:Opening\n",
    );
    vfs.add_file(
        "assert.beancount",
        "2024-01-05 balance Assets:Bank 999.00 USD\n",
    );
    let raw = Loader::new()
        .with_filesystem(Box::new(vfs))
        .load(Path::new("main.beancount"))
        .expect("loads");
    let ledger = process(raw, &options(false)).expect("processes");
    assert!(ledger.balance_discrepancies.is_empty(), "no validation ran");

    let recomputed = recompute_balance_discrepancies(&ledger.source_map, &options(false));
    // bean-query: `Assets:Bank, -989.00 USD`.
    assert_eq!(
        render(&recomputed),
        vec!["2024-01-05 Assets:Bank 999.00 -989.00 USD".to_string()]
    );
}

/// No file, nothing to validate: an empty list, so the column reads NULL.
#[test]
fn test_recompute_balance_discrepancies_is_empty_without_sources() {
    let empty = rustledger_loader::SourceMap::new();
    assert!(recompute_balance_discrepancies(&empty, &options(false)).is_empty());
}
