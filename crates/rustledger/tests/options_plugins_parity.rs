//! The option plugins report the same thing natively and in Python.
//!
//! `check_option_expiry` has a Python counterpart in beancount-options
//! (rustledger/rustledger#2555). A ledger enables it with one line,
//! `plugin "beancount_options.check_option_expiry"`: `rledger` resolves
//! that to the native plugin by the name's last part, and `bean-check`
//! imports the package. These tests run both on the fixtures in
//! `tests/fixtures/options/` and require the same errors, at the same
//! lines, in the same order.
//!
//! Tool-gated: they need `bean-check` with beancount-options installed.
//! Where it is missing they print [`SKIP_MARKER`] and pass; the
//! `python-gated-cargo-tests` CI job installs both and fails on the marker.

mod common;

use std::path::{Path, PathBuf};
use std::process::Command;

/// Printed when `bean-check` or beancount-options is unavailable; CI
/// fails on it.
const SKIP_MARKER: &str = "Skipping: beancount-options not installed";

/// What a run that started the Python runtime prints. The native plugin
/// must handle these lines, never the sandboxed Python one.
const PYTHON_RAN: &str = "Loading Python plugin runtime";

fn fixture(name: &str) -> PathBuf {
    common::test_fixtures_dir().join("options").join(name)
}

/// Whether `bean-check` can import beancount-options: the clean fixture
/// must pass. Prints [`SKIP_MARKER`] when it cannot.
fn beancount_options_ready() -> bool {
    let ok = Command::new("bean-check")
        .arg(fixture("clean.beancount"))
        .output()
        .is_ok_and(|o| o.status.success());
    if !ok {
        eprintln!("{SKIP_MARKER}");
    }
    ok
}

/// `N: message` for each error line naming `path`, in output order. Both
/// tools start an error with `<path>:<line>:`; rledger adds a column and
/// `error[PLUGIN]:`, bean-check prints the entry on the lines after it.
fn errors(text: &str, path: &Path) -> Vec<String> {
    let name = path.file_name().unwrap().to_str().unwrap();
    text.lines()
        .filter_map(|l| {
            let rest = &l[l.find(&format!("{name}:"))? + name.len() + 1..];
            let (line, rest) = rest.split_once(':')?;
            line.parse::<u32>().ok()?;
            let message = rest
                .trim_start_matches(|c: char| c.is_ascii_digit())
                .trim_start_matches(':')
                .trim_start()
                .trim_start_matches("error[PLUGIN]:")
                .trim_start();
            Some(format!("{line}: {message}"))
        })
        .collect()
}

fn run(program: &Path, args: &[&str], path: &Path) -> (bool, String) {
    let out = Command::new(program)
        .args(args)
        .arg(path)
        .output()
        .unwrap_or_else(|e| panic!("running {}: {e}", program.display()));
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (out.status.success(), text)
}

/// Both tools on one fixture: the same errors, and the native plugin ran.
fn assert_parity(name: &str, expected: usize) {
    let rledger = require_rledger!();
    if !beancount_options_ready() {
        return;
    }
    let path = fixture(name);
    let (rs_ok, rs_text) = run(&rledger, &["check"], &path);
    let (py_ok, py_text) = run(Path::new("bean-check"), &[], &path);
    assert!(!rs_text.contains(PYTHON_RAN), "{rs_text}");
    let rs = errors(&rs_text, &path);
    let py = errors(&py_text, &path);
    assert_eq!(rs.len(), expected, "rledger:\n{rs_text}");
    assert_eq!(py, rs, "bean-check:\n{py_text}\nrledger:\n{rs_text}");
    assert_eq!(py_ok, rs_ok, "exit status differs");
}

/// Partial close, sign change, netting of cancelling legs, adjusted and
/// dotted roots, invalid symbols, a 100-contract long at cost, closes on
/// and after expiry, an unexpired contract, and a `price` as the last
/// entry: eight errors, identical in both tools.
#[test]
fn check_option_expiry_matches_beancount_options() {
    assert_parity("expiry.beancount", 8);
}

/// A ledger with nothing to report passes in both.
#[test]
fn check_option_expiry_clean_ledger_matches() {
    assert_parity("clean.beancount", 0);
}

/// The line parser reads both tools' formats.
#[test]
fn errors_reads_both_formats() {
    let path = Path::new("/x/ledger.beancount");
    let rledger = "/x/ledger.beancount:7:1: error[PLUGIN]: A expired\n✗ 1 error\n";
    let bean_check = "/x/ledger.beancount:7: A expired\n\n   2026-09-02 * \"x\"\n";
    assert_eq!(errors(rledger, path), ["7: A expired"]);
    assert_eq!(errors(bean_check, path), ["7: A expired"]);
}
