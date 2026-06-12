//! `rledger query` reuses the on-disk parse cache (shared with `check`
//! / `report`) so a repeated query on an unchanged file skips the
//! expensive parse. These tests pin two guarantees:
//!
//! 1. A query writes the cache and a subsequent query hits it.
//! 2. Cached, uncached, and cache-disabled runs produce byte-identical
//!    output. The query outputs summed amounts, which depend on the
//!    `DisplayContext` (per-currency precision); a cache hit rebuilds
//!    that context, so this would catch an empty-context regression.

mod common;

use std::process::Command;

const SRC: &str = r#"option "operating_currency" "USD"

2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank

2024-01-20 * "Lunch"
  Expenses:Food  12.50 USD
  Assets:Bank
"#;

const QUERY: &str = "SELECT account, sum(position) GROUP BY account ORDER BY account";

#[test]
fn query_uses_parse_cache_with_identical_output() {
    let bin = require_rledger!();

    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("ledger.beancount");
    std::fs::write(&file, SRC).expect("write ledger");

    let run = |verbose: bool, disable_cache: bool| {
        let mut cmd = Command::new(&bin);
        cmd.arg("query");
        // `--verbose` must precede the positionals: the QUERY arg is
        // `trailing_var_arg`, so anything after the file is captured as
        // query text.
        if verbose {
            cmd.arg("--verbose");
        }
        cmd.arg(&file).arg(QUERY);
        // Hermetic: ignore any cache env the developer/CI may have set,
        // so the cache lands at the default path next to the source and
        // is actually written.
        cmd.env_remove("BEANCOUNT_DISABLE_LOAD_CACHE")
            .env_remove("BEANCOUNT_LOAD_CACHE_FILENAME");
        if disable_cache {
            cmd.env("BEANCOUNT_DISABLE_LOAD_CACHE", "1");
        }
        cmd.output().expect("run rledger query")
    };

    // Cold run: parses and writes the cache.
    let cold = run(false, false);
    assert!(
        cold.status.success(),
        "cold query failed: {}",
        String::from_utf8_lossy(&cold.stderr)
    );
    let cold_out = String::from_utf8_lossy(&cold.stdout).into_owned();

    // The cache is written alongside the source as `.<name>.cache`.
    let cache_file = dir.path().join(".ledger.beancount.cache");
    assert!(
        cache_file.exists(),
        "a cold query should have written the parse cache at {}",
        cache_file.display()
    );

    // Warm run (verbose): must hit the cache and print identical output.
    let warm = run(true, false);
    assert!(
        warm.status.success(),
        "warm query failed: {}",
        String::from_utf8_lossy(&warm.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&warm.stdout),
        cold_out,
        "cached query output must match the cold run (incl. amount precision)"
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
        "cache-disabled query output must match the cached run"
    );
}

/// The `--no-cache` flag must disable the cache entirely: a query run
/// with it set must not write a cache file (and must still succeed).
/// `--no-cache` precedes the positionals (QUERY is `trailing_var_arg`).
#[test]
fn query_no_cache_flag_skips_cache() {
    let bin = require_rledger!();

    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("ledger.beancount");
    std::fs::write(&file, SRC).expect("write ledger");

    let out = std::process::Command::new(&bin)
        .arg("query")
        .arg("--no-cache")
        .arg(&file)
        .arg(QUERY)
        .env_remove("BEANCOUNT_DISABLE_LOAD_CACHE")
        .env_remove("BEANCOUNT_LOAD_CACHE_FILENAME")
        .output()
        .expect("run rledger query --no-cache");
    assert!(
        out.status.success(),
        "query --no-cache failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let cache_file = dir.path().join(".ledger.beancount.cache");
    assert!(
        !cache_file.exists(),
        "--no-cache must not write the parse cache, but {} exists",
        cache_file.display()
    );
}
