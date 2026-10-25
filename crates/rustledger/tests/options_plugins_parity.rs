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
//! The shared cases in beancount-options' `tests/cases/<plugin>/` (each
//! ledger with a `.expected` file of `line: message`) are run too, from the
//! checkout named by `BEANCOUNT_OPTIONS_DIR`, so a rule change lands on
//! both sides. `check_option_assignment`'s own fixture, which exercises
//! what `rledger check`'s booking fills in, is checked against
//! `assignment.expected` with `rledger` alone.
//!
//! Tool-gated: the parity tests need `bean-check` with beancount-options
//! installed, and the shared cases need `BEANCOUNT_OPTIONS_DIR`. Where
//! the first is missing they print [`SKIP_MARKER`], and where the second
//! is unset [`NO_CASES_DIR_MARKER`]; either way they pass. The
//! `python-gated-cargo-tests` CI job provides both and fails on either
//! marker.
//!
//! To run them locally, install beancount-options into the environment
//! whose `bean-check` is first on `PATH` (`pip install -e
//! ~/src/beancount-options`), set `BEANCOUNT_OPTIONS_DIR` to that checkout,
//! and run outside `nix develop`: inside it, `bean-check` is
//! `scripts/bin/bean-check`, the compat-container wrapper, which does not
//! have beancount-options, so the tests always skip there.

mod common;

use std::path::{Path, PathBuf};
use std::process::Command;

/// Printed when `bean-check` or beancount-options is unavailable; CI
/// fails on it.
const SKIP_MARKER: &str = "Skipping: beancount-options not installed";

/// Printed when `BEANCOUNT_OPTIONS_DIR` (the beancount-options checkout
/// holding the shared cases) is unset; CI fails on it.
const NO_CASES_DIR_MARKER: &str =
    "Skipping: BEANCOUNT_OPTIONS_DIR not set (the beancount-options checkout with tests/cases/)";

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

/// `N: message` for each error line naming `path`, in output order, or
/// `file:N: message` when `files` lists more than one file. Both tools
/// start an error with `<path>:<line>:`; rledger adds a column and
/// `error[PLUGIN]:`, bean-check prints the entry on the lines after it.
fn errors(text: &str, files: &[&Path]) -> Vec<String> {
    let names: Vec<&str> = files
        .iter()
        .map(|f| f.file_name().unwrap().to_str().unwrap())
        .collect();
    text.lines()
        .filter_map(|l| {
            let (name, at) = names
                .iter()
                .filter_map(|n| l.find(&format!("{n}:")).map(|at| (*n, at)))
                .min_by_key(|(_, at)| *at)?;
            let rest = &l[at + name.len() + 1..];
            let (line, rest) = rest.split_once(':')?;
            line.parse::<u32>().ok()?;
            let message = rest
                .trim_start_matches(|c: char| c.is_ascii_digit())
                .trim_start_matches(':')
                .trim_start()
                .trim_start_matches("error[PLUGIN]:")
                .trim_start();
            Some(if names.len() == 1 {
                format!("{line}: {message}")
            } else {
                format!("{name}:{line}: {message}")
            })
        })
        .collect()
}

/// The `line: message` lines of a `.expected` file.
fn expected(path: &Path) -> Vec<String> {
    std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("reading {}: {e}", path.display()))
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(str::to_string)
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

/// Both tools on one ledger: the same errors, and the native plugin ran.
/// `files` are the files whose errors are compared (the ledger and any it
/// includes). Returns the errors.
fn assert_parity_of(path: &Path, files: &[&Path], expected: usize) -> Option<Vec<String>> {
    let Some(rledger) = common::rledger_binary() else {
        eprintln!("Skipping: rledger binary not found");
        return None;
    };
    if !beancount_options_ready() {
        return None;
    }
    let (rs_ok, rs_text) = run(&rledger, &["check"], path);
    let (py_ok, py_text) = run(Path::new("bean-check"), &[], path);
    assert!(!rs_text.contains(PYTHON_RAN), "{rs_text}");
    let rs = errors(&rs_text, files);
    let py = errors(&py_text, files);
    assert_eq!(rs.len(), expected, "rledger:\n{rs_text}");
    assert_eq!(py, rs, "bean-check:\n{py_text}\nrledger:\n{rs_text}");
    assert_eq!(py_ok, rs_ok, "exit status differs");
    Some(rs)
}

fn assert_parity(name: &str, expected: usize) {
    let path = fixture(name);
    assert_parity_of(&path, &[&path], expected);
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

/// Same-day trades split across an `include`: both tools take beancount's
/// order (date, type, then line, whatever the file), so both report the position
/// at `includes-other.beancount:1`, not at the buy in the including file.
#[test]
fn check_option_expiry_same_day_across_include_matches() {
    let main = fixture("includes.beancount");
    let other = fixture("includes-other.beancount");
    let Some(errors) = assert_parity_of(&main, &[&main, &other], 1) else {
        return;
    };
    assert_eq!(
        errors,
        [
            "includes-other.beancount:1: AAPL261016P00230000 expired 2026-10-16 but 2 contract(s) remain open in Assets:Broker:Options"
        ]
    );
}

/// beancount-options' shared cases: each `tests/cases/<plugin>/*.beancount`
/// gives its `.expected` errors natively, and the same as `bean-check`.
fn assert_shared_cases_match(plugin: &str) {
    let Some(dir) = std::env::var_os("BEANCOUNT_OPTIONS_DIR") else {
        eprintln!("{NO_CASES_DIR_MARKER}");
        return;
    };
    let cases = PathBuf::from(dir).join("tests/cases").join(plugin);
    let mut ledgers: Vec<PathBuf> = std::fs::read_dir(&cases)
        .unwrap_or_else(|e| panic!("reading {}: {e}", cases.display()))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "beancount"))
        .collect();
    ledgers.sort();
    assert!(!ledgers.is_empty(), "no cases in {}", cases.display());
    for ledger in ledgers {
        let want = expected(&ledger.with_extension("expected"));
        let Some(got) = assert_parity_of(&ledger, &[&ledger], want.len()) else {
            return;
        };
        assert_eq!(got, want, "{}", ledger.display());
    }
}

/// beancount-options' shared `check_option_expiry` cases, both sides.
#[test]
fn check_option_expiry_shared_cases_match() {
    assert_shared_cases_match("expiry");
}

/// beancount-options' shared `check_option_assignment` cases, both sides.
/// Its overflow fixture is not one, for the reason on that test.
#[test]
fn check_option_assignment_shared_cases_match() {
    assert_shared_cases_match("assignment");
}

/// `check_option_assignment` through `rledger check`: booking fills each
/// closing `{}` leg with its lot's cost, which is the premium the plugin
/// reads, so the errors are those in `assignment.expected`.
#[test]
fn check_option_assignment_end_to_end() {
    let rledger = require_rledger!();
    let path = fixture("assignment.beancount");
    let (ok, text) = run(&rledger, &["check"], &path);
    assert!(!text.contains(PYTHON_RAN), "{text}");
    assert!(!ok, "{text}");
    assert_eq!(
        errors(&text, &[&path]),
        expected(&fixture("assignment.expected")),
        "{text}"
    );
}

/// Products past `Decimal`'s range neither panic nor pass silently: the
/// share count still runs, and an assignment whose basis cannot be
/// computed is reported as not checked (#2661 review). Not shared with
/// beancount-options: its Python counterpart has arbitrary-precision
/// decimals and checks these amounts instead.
#[test]
fn check_option_assignment_overflow_is_reported() {
    let rledger = require_rledger!();
    let path = fixture("assignment-overflow.beancount");
    let (ok, text) = run(&rledger, &["check"], &path);
    assert!(!text.contains("panicked"), "{text}");
    assert!(!ok, "{text}");
    assert_eq!(
        errors(&text, &[&path]),
        [
            "12: AAPL261016P99999999 assignment: 1000000000000000000000000 contract(s) but 1 AAPL; expected 100000000000000000000000000",
            "19: MSFT261016P99999999 assignment not checked: amounts exceed the supported decimal range",
        ],
        "{text}"
    );
}

/// `check_option_expiry` skips a position whose net leaves `Decimal`'s
/// range, but through the loader that position never reaches it: booking
/// rejects the inventory first, so `rledger check` still fails.
#[test]
fn check_option_expiry_overflow_is_rejected_by_booking() {
    let rledger = require_rledger!();
    let path = fixture("expiry-overflow.beancount");
    let (ok, text) = run(&rledger, &["check"], &path);
    assert!(!text.contains("panicked"), "{text}");
    assert!(!ok, "{text}");
    assert!(
        text.contains("AAPL261016P00100000 amount exceeds the representable range"),
        "{text}"
    );
}

/// The line parser reads both tools' formats, and names the file when
/// errors from several files are compared.
#[test]
fn errors_reads_both_formats() {
    let path = Path::new("/x/ledger.beancount");
    let rledger = "/x/ledger.beancount:7:1: error[PLUGIN]: A expired\n✗ 1 error\n";
    let bean_check = "/x/ledger.beancount:7: A expired\n\n   2026-09-02 * \"x\"\n";
    assert_eq!(errors(rledger, &[path]), ["7: A expired"]);
    assert_eq!(errors(bean_check, &[path]), ["7: A expired"]);
    let other = Path::new("/x/other.beancount");
    let both = "/x/other.beancount:1: A expired\n/x/ledger.beancount:9:1: error[PLUGIN]: B\n";
    assert_eq!(
        errors(both, &[path, other]),
        ["other.beancount:1: A expired", "ledger.beancount:9: B"]
    );
}
