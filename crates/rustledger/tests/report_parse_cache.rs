//! `rledger report` reuses the on-disk parse cache (shared with
//! `check`) so a repeated report on an unchanged file skips the
//! expensive parse. These tests pin two guarantees:
//!
//! 1. A report writes the cache and a subsequent report hits it.
//! 2. Cached, uncached, and cache-disabled runs produce byte-identical
//!    output (the cache must never change what a report prints).

mod common;

use std::process::Command;

const SRC: &str = r#"option "operating_currency" "USD"

2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank

2024-01-20 * "Lunch"
  Expenses:Food  12.00 USD
  Assets:Bank
"#;

#[test]
fn report_uses_parse_cache_with_identical_output() {
    let bin = require_rledger!();

    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("ledger.beancount");
    std::fs::write(&file, SRC).expect("write ledger");

    let run = |verbose: bool, disable_cache: bool| {
        let mut cmd = Command::new(&bin);
        cmd.arg("report")
            .arg(&file)
            .arg("balances")
            .arg("--no-pager")
            // Hermetic: ignore any cache env the developer/CI may have
            // set, so the cache lands at the default path next to the
            // source (`.ledger.beancount.cache`) and is actually written.
            .env_remove("BEANCOUNT_DISABLE_LOAD_CACHE")
            .env_remove("BEANCOUNT_LOAD_CACHE_FILENAME");
        if verbose {
            cmd.arg("--verbose");
        }
        if disable_cache {
            cmd.env("BEANCOUNT_DISABLE_LOAD_CACHE", "1");
        }
        cmd.output().expect("run rledger report")
    };

    // Cold run: parses and writes the cache.
    let cold = run(false, false);
    assert!(
        cold.status.success(),
        "cold report failed: {}",
        String::from_utf8_lossy(&cold.stderr)
    );
    let cold_out = String::from_utf8_lossy(&cold.stdout).into_owned();

    // The cache is written alongside the source as `.<name>.cache`.
    let cache_file = dir.path().join(".ledger.beancount.cache");
    assert!(
        cache_file.exists(),
        "a cold report should have written the parse cache at {}",
        cache_file.display()
    );

    // Warm run (verbose): must hit the cache and print identical output.
    let warm = run(true, false);
    assert!(
        warm.status.success(),
        "warm report failed: {}",
        String::from_utf8_lossy(&warm.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&warm.stdout),
        cold_out,
        "cached report output must match the cold run"
    );
    let warm_err = String::from_utf8_lossy(&warm.stderr);
    assert!(
        warm_err.contains("from cache"),
        "a verbose warm run should report a cache hit; stderr was:\n{warm_err}"
    );

    // Cache-disabled run: must still produce the same output.
    let nocache = run(false, true);
    assert!(nocache.status.success());
    assert_eq!(
        String::from_utf8_lossy(&nocache.stdout),
        cold_out,
        "cache-disabled report output must match the cached run"
    );
}
