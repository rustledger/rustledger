//! Differential test harness: `rledger price` vs `bean-price` symbol discovery.
//!
//! Drives both binaries against a fixture beancount file and asserts that the set of
//! `(symbol, quote_currency)` pairs they would fetch is identical. This is the keystone
//! deliverable for issue #967 (acceptance criterion #1) — every per-candidate audit
//! item from the bean-price compat sweep can hang off this harness.
//!
//! `bean-price` is provided by the nix dev shell (added in #976). When it is missing
//! (e.g., a contributor running `cargo test` directly), the test is skipped with a
//! warning rather than failed, so non-nix workflows aren't broken.

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::Command;
use tempfile::{NamedTempFile, TempDir};

/// Returns true if `bean-price` is on PATH and runnable.
fn bean_price_available() -> bool {
    Command::new("bean-price")
        .arg("--help")
        .output()
        .is_ok_and(|o| o.status.success())
}

/// Parse `bean-price -n` output. Lines look like:
///   `AAPL /USD                        @ latest     [ beanprice.sources.yahoo(AAPL) ]`
fn extract_bean_price_jobs(stdout: &str) -> BTreeSet<(String, String)> {
    stdout
        .lines()
        .filter_map(|line| {
            let mut parts = line.split_whitespace();
            let sym = parts.next()?;
            let cur = parts.next()?.strip_prefix('/')?;
            // Sanity check: the next field should be `@`. Lines that don't match
            // (blank, log noise, etc.) are silently skipped.
            if parts.next()? != "@" {
                return None;
            }
            Some((sym.to_string(), cur.to_string()))
        })
        .collect()
}

/// Parse `rledger price` stdout. Each fetched price emits a line like
///   `AAPL: 1.00 USD`
/// where the value comes from the stub `--source-cmd`.
fn extract_rledger_jobs(stdout: &str) -> BTreeSet<(String, String)> {
    stdout
        .lines()
        .filter_map(|line| {
            let mut parts = line.split_whitespace();
            let sym = parts.next()?.strip_suffix(':')?;
            let _value = parts.next()?;
            let cur = parts.next()?;
            Some((sym.to_string(), cur.to_string()))
        })
        .collect()
}

// `TempDir` (not `NamedTempFile`) so the script file has no open write handle — exec on Linux fails with ETXTBSY otherwise.
fn stub_source() -> (TempDir, PathBuf) {
    use std::os::unix::fs::PermissionsExt;
    let dir = TempDir::new().unwrap();
    let path = dir.path().join("stub-source.sh");
    std::fs::write(&path, "#!/usr/bin/env bash\necho 1.00\n").unwrap();
    let mut perms = std::fs::metadata(&path).unwrap().permissions();
    perms.set_mode(0o755);
    std::fs::set_permissions(&path, perms).unwrap();
    (dir, path)
}

fn write_fixture(content: &str) -> NamedTempFile {
    let f = tempfile::Builder::new()
        .suffix(".beancount")
        .tempfile()
        .unwrap();
    std::fs::write(f.path(), content).unwrap();
    f
}

fn run_bean_price(fixture: &std::path::Path) -> BTreeSet<(String, String)> {
    let out = Command::new("bean-price")
        .args(["-n", fixture.to_str().unwrap()])
        .output()
        .expect("bean-price -n should execute");
    assert!(
        out.status.success(),
        "bean-price exited non-zero: stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    extract_bean_price_jobs(&String::from_utf8_lossy(&out.stdout))
}

fn run_rledger(fixture: &std::path::Path) -> BTreeSet<(String, String)> {
    let (_dir, stub_path) = stub_source();
    let out = Command::new(env!("CARGO_BIN_EXE_rledger"))
        .args([
            "price",
            "-f",
            fixture.to_str().unwrap(),
            "--source-cmd",
            stub_path.to_str().unwrap(),
        ])
        .output()
        .expect("rledger price should execute");
    assert!(
        out.status.success(),
        "rledger price exited non-zero: stderr={}\nstdout={}",
        String::from_utf8_lossy(&out.stderr),
        String::from_utf8_lossy(&out.stdout),
    );
    extract_rledger_jobs(&String::from_utf8_lossy(&out.stdout))
}

const FIXTURE_BASIC: &str = "\
2024-01-01 commodity AAPL
  price: \"USD:yahoo/AAPL\"

2024-01-01 commodity SPY
  price: \"USD:yahoo/SPY\"

2024-01-01 open Assets:Brokerage
2024-01-01 open Equity:Open

2024-01-15 * \"buy\"
  Assets:Brokerage  10 AAPL {150 USD}
  Assets:Brokerage  5 SPY {500 USD}
  Equity:Open
";

#[test]
fn rledger_and_bean_price_discover_same_symbols_basic() {
    if !bean_price_available() {
        eprintln!(
            "skipping bean-price compat test: bean-price not on PATH \
             (run inside `nix develop` to enable)"
        );
        return;
    }

    let fixture = write_fixture(FIXTURE_BASIC);

    let bean_jobs = run_bean_price(fixture.path());
    let rledger_jobs = run_rledger(fixture.path());

    assert_eq!(
        bean_jobs, rledger_jobs,
        "bean-price and rledger price disagreed on the symbol-set to fetch.\n\
         bean-price = {bean_jobs:?}\n\
         rledger    = {rledger_jobs:?}"
    );
}
