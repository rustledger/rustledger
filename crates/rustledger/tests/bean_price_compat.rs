//! Differential test harness: `rledger price` vs `bean-price`.
//!
//! Two layers of comparison against fixture beancount files:
//!
//! 1. **Commodity discovery** — `bean-price -n` vs `rledger price --source-cmd`,
//!    asserting the same `(symbol, quote_currency)` set is discovered.
//!
//! 2. **Source resolution** — `bean-price -n` vs `rledger price -n`, asserting
//!    the same `(symbol, currency, source, ticker)` tuples are produced. This
//!    covers source-precedence (audit item 5), per-spec ticker preservation (#970),
//!    and fallback chains (#963/#970) that the discovery-only layer can't see.
//!
//! `bean-price` ships in the nix dev shell (#976). On non-nix workflows the test
//! skips with a notice rather than failing; CI doesn't currently use the dev
//! shell, so the harness is enforced via the pre-push hook.

#![cfg(unix)]

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::Command;
use tempfile::{NamedTempFile, TempDir};

fn bean_price_available() -> bool {
    Command::new("bean-price")
        .arg("--help")
        .output()
        .is_ok_and(|o| o.status.success())
}

// Bean-price -n line shape:
//   `AAPL /USD                        @ latest     [ beanprice.sources.yahoo(AAPL) ]`
// Tighter than split_whitespace: require uppercase ticker, slash-prefixed currency,
// and the literal `@` separator before accepting.
fn extract_bean_price_jobs(stdout: &str) -> BTreeSet<(String, String)> {
    fn is_ticker(s: &str) -> bool {
        !s.is_empty()
            && s.chars().all(|c| {
                c.is_ascii_uppercase() || c.is_ascii_digit() || matches!(c, '.' | '-' | '_')
            })
            && s.chars().next().is_some_and(|c| c.is_ascii_uppercase())
    }
    fn is_currency(s: &str) -> bool {
        !s.is_empty() && s.chars().all(|c| c.is_ascii_uppercase())
    }

    stdout
        .lines()
        .filter_map(|line| {
            let mut parts = line.split_whitespace();
            let sym = parts.next()?;
            let cur = parts.next()?.strip_prefix('/')?;
            if parts.next()? != "@" {
                return None;
            }
            if !is_ticker(sym) || !is_currency(cur) {
                return None;
            }
            Some((sym.to_string(), cur.to_string()))
        })
        .collect()
}

// rledger `--beancount` line shape: `2024-05-02 price AAPL 1.00 USD` — stable, documented.
fn extract_rledger_jobs(stdout: &str) -> BTreeSet<(String, String)> {
    stdout
        .lines()
        .filter_map(|line| {
            let mut parts = line.split_whitespace();
            let _date = parts.next()?;
            if parts.next()? != "price" {
                return None;
            }
            let sym = parts.next()?;
            let _amount = parts.next()?;
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
    // rledger parses --source-cmd via shell_words::split, so a temp path containing
    // whitespace would be word-split into multiple tokens and the exec would fail.
    let stub_arg = shell_words::quote(stub_path.to_str().unwrap()).into_owned();
    let out = Command::new(env!("CARGO_BIN_EXE_rledger"))
        .args([
            "price",
            "-f",
            fixture.to_str().unwrap(),
            "--beancount",
            "--source-cmd",
            &stub_arg,
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

fn assert_same_commodities(fixture: &str, label: &str) {
    if !bean_price_available() {
        eprintln!(
            "skipping bean-price compat ({label}): bean-price not on PATH \
             (run inside `nix develop` to enable)"
        );
        return;
    }
    let f = write_fixture(fixture);
    let bean_jobs = run_bean_price(f.path());
    let rledger_jobs = run_rledger(f.path());
    assert_eq!(
        bean_jobs, rledger_jobs,
        "fixture {label}: bean-price and rledger price disagreed on commodity discovery.\n\
         bean-price = {bean_jobs:?}\n\
         rledger    = {rledger_jobs:?}"
    );
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

const FIXTURE_MIXED_CURRENCIES: &str = "\
2024-01-01 commodity AAPL
  price: \"USD:yahoo/AAPL\"

2024-01-01 commodity SAP
  price: \"EUR:yahoo/SAP.DE\"

2024-01-01 open Assets:US
2024-01-01 open Assets:DE
2024-01-01 open Equity:Open

2024-01-15 * \"buy AAPL\"
  Assets:US  10 AAPL {150 USD}
  Equity:Open

2024-01-16 * \"buy SAP\"
  Assets:DE  20 SAP {120 EUR}
  Equity:Open
";

#[test]
fn rledger_and_bean_price_discover_same_commodities_basic() {
    assert_same_commodities(FIXTURE_BASIC, "basic");
}

#[test]
fn rledger_and_bean_price_discover_same_commodities_mixed_currencies() {
    assert_same_commodities(FIXTURE_MIXED_CURRENCIES, "mixed_currencies");
}

// ===== Layer 2: source-resolution differential (uses both binaries' dry-run) =====

/// Strip bean-price's `beanprice.sources.` module prefix so source names match
/// rledger's bare names (`yahoo`, `ecb`, ...).
fn normalize_source(s: &str) -> String {
    s.strip_prefix("beanprice.sources.")
        .unwrap_or(s)
        .to_string()
}

/// Parse `bean-price -n` output. Each line ends with
///   `[ beanprice.sources.yahoo(AAPL), beanprice.sources.google(VTI) ]`
/// We extract the bracket section and split on commas.
fn extract_bean_price_attempts(stdout: &str) -> BTreeSet<(String, String, String, String)> {
    let mut out = BTreeSet::new();
    for line in stdout.lines() {
        let mut parts = line.split_whitespace();
        let Some(sym) = parts.next() else { continue };
        let Some(cur_raw) = parts.next() else {
            continue;
        };
        let Some(cur) = cur_raw.strip_prefix('/') else {
            continue;
        };
        if parts.next() != Some("@") {
            continue;
        }
        // Locate the bracket payload regardless of how many tokens precede it.
        let Some(open) = line.find('[') else { continue };
        let Some(close) = line.rfind(']') else {
            continue;
        };
        if close <= open {
            continue;
        }
        let inside = line[open + 1..close].trim();
        for entry in inside.split(',') {
            let entry = entry.trim();
            // `module.path.name(TICKER)` — split on the last '(' before ')'.
            let Some(paren_open) = entry.rfind('(') else {
                continue;
            };
            let Some(paren_close) = entry.rfind(')') else {
                continue;
            };
            if paren_close <= paren_open {
                continue;
            }
            let source = normalize_source(entry[..paren_open].trim());
            let ticker = entry[paren_open + 1..paren_close].trim().to_string();
            out.insert((sym.to_string(), cur.to_string(), source, ticker));
        }
    }
    out
}

/// Parse `rledger price -n` output. Format:
///   `<symbol> /<currency> @ <date> <source>(<ticker>)[, <source>(<ticker>)...][  [skip: ...]]`
fn extract_rledger_attempts(stdout: &str) -> BTreeSet<(String, String, String, String)> {
    let mut out = BTreeSet::new();
    for line in stdout.lines() {
        // Drop the trailing skip annotation if present. The two-space prefix
        // is what `dump_fetch_plan` writes; if that ever changes, this strip
        // becomes a no-op and the skip suffix is parsed as a bogus source.
        let line = line.split("  [skip:").next().unwrap_or(line).trim_end();

        let mut parts = line.split_whitespace();
        let Some(sym) = parts.next() else { continue };
        let Some(cur_raw) = parts.next() else {
            continue;
        };
        let Some(cur) = cur_raw.strip_prefix('/') else {
            continue;
        };
        if parts.next() != Some("@") {
            continue;
        }
        let _date = parts.next();
        // Everything left is the source list. Rejoin to handle the
        // ", " separator (split_whitespace would split on it too).
        let rest = parts.collect::<Vec<_>>().join(" ");
        for entry in rest.split(", ") {
            let entry = entry.trim();
            if entry == "<unmapped>" {
                continue;
            }
            let Some(paren_open) = entry.rfind('(') else {
                continue;
            };
            let Some(paren_close) = entry.rfind(')') else {
                continue;
            };
            if paren_close <= paren_open {
                continue;
            }
            let source = entry[..paren_open].trim().to_string();
            let ticker = entry[paren_open + 1..paren_close].trim().to_string();
            out.insert((sym.to_string(), cur.to_string(), source, ticker));
        }
    }
    out
}

fn run_bean_price_attempts(
    fixture: &std::path::Path,
) -> BTreeSet<(String, String, String, String)> {
    let out = Command::new("bean-price")
        .args(["-n", fixture.to_str().unwrap()])
        .output()
        .expect("bean-price -n should execute");
    assert!(
        out.status.success(),
        "bean-price exited non-zero: stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    extract_bean_price_attempts(&String::from_utf8_lossy(&out.stdout))
}

fn run_rledger_attempts(fixture: &std::path::Path) -> BTreeSet<(String, String, String, String)> {
    let out = Command::new(env!("CARGO_BIN_EXE_rledger"))
        .args(["price", "-f", fixture.to_str().unwrap(), "-n"])
        .output()
        .expect("rledger price -n should execute");
    assert!(
        out.status.success(),
        "rledger price -n exited non-zero: stderr={}\nstdout={}",
        String::from_utf8_lossy(&out.stderr),
        String::from_utf8_lossy(&out.stdout),
    );
    extract_rledger_attempts(&String::from_utf8_lossy(&out.stdout))
}

fn assert_same_attempts(fixture: &str, label: &str) {
    if !bean_price_available() {
        eprintln!(
            "skipping bean-price compat ({label}): bean-price not on PATH \
             (run inside `nix develop` to enable)"
        );
        return;
    }
    let f = write_fixture(fixture);
    let bean = run_bean_price_attempts(f.path());
    let rledger = run_rledger_attempts(f.path());
    assert_eq!(
        bean, rledger,
        "fixture {label}: bean-price and rledger price disagreed on (symbol, currency, source, ticker).\n\
         bean-price = {bean:?}\n\
         rledger    = {rledger:?}"
    );
}

#[test]
fn rledger_and_bean_price_resolve_same_attempts_basic() {
    assert_same_attempts(FIXTURE_BASIC, "basic");
}

#[test]
fn rledger_and_bean_price_resolve_same_attempts_mixed_currencies() {
    assert_same_attempts(FIXTURE_MIXED_CURRENCIES, "mixed_currencies");
}

// Sanity check: when we're inside `nix develop`, `bean-price` must be on PATH —
// otherwise removing beanprice from the flake would silently turn every harness
// test into a no-op and we wouldn't notice. CI doesn't currently use the dev
// shell so this guard only fires for local devs; making CI run inside nix is a
// separate workflow change.
#[cfg(target_os = "linux")]
#[test]
fn bean_price_must_be_on_path_in_dev_shell() {
    if std::env::var_os("IN_NIX_SHELL").is_none() {
        eprintln!("skipping: not running inside `nix develop`");
        return;
    }
    assert!(
        bean_price_available(),
        "bean-price not on PATH inside nix dev shell — flake regression?"
    );
}
