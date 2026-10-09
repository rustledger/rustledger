//! Integration tests for the agent-native `ag-rledger` binary (#1291).
//!
//! Gated behind the `ag-rledger` feature: the binary (and thus the
//! `CARGO_BIN_EXE_ag-rledger` env var these tests resolve) only exists when
//! that feature is enabled. Without the gate, the default
//! `cargo test -p rustledger` would fail to compile this file (missing env
//! var) even though the binary isn't built. Run with
//! `cargo test -p rustledger --features ag-rledger`.
//!
//! These resolve the binary via `CARGO_BIN_EXE_ag-rledger` (set by cargo
//! for any `[[bin]]` target) and assert on the agcli JSON envelope and the
//! typed process exit code. They mirror the `common` harness conventions
//! used by the `rledger` CLI tests, but the binary is always present under
//! `cargo test --features ag-rledger` so no skip macro is needed.
#![cfg(feature = "ag-rledger")]

use serde_json::Value;
use std::path::PathBuf;
use std::process::Command;

/// Resolve the `ag-rledger` binary built for this test run.
fn ag_rledger() -> PathBuf {
    // `CARGO_BIN_EXE_<name>` is injected by cargo for each bin target.
    PathBuf::from(env!("CARGO_BIN_EXE_ag-rledger"))
}

/// Write a temp beancount file under the test's temp dir and return its path.
fn write_fixture(dir: &std::path::Path, name: &str, contents: &str) -> PathBuf {
    let path = dir.join(name);
    std::fs::write(&path, contents).expect("write fixture");
    path
}

/// Run `ag-rledger <args...>` and return `(exit_code, parsed_envelope)`.
fn run(args: &[&str]) -> (i32, Value) {
    let output = Command::new(ag_rledger())
        .args(args)
        .output()
        .expect("spawn ag-rledger");
    let code = output.status.code().expect("exit code");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let envelope: Value = serde_json::from_str(stdout.trim())
        .unwrap_or_else(|e| panic!("envelope is not JSON ({e}): {stdout}"));
    (code, envelope)
}

const GOOD_LEDGER: &str = "\
2024-01-01 open Assets:Cash
2024-01-01 open Equity:Opening

2024-01-02 * \"Opening balance\"
  Assets:Cash       100.00 USD
  Equity:Opening   -100.00 USD
";

const BAD_LEDGER: &str = "\
2024-01-01 open Assets:Cash
2024-01-02 * \"Unbalanced\"
  Assets:Cash       100.00 USD
  Equity:Opening    -90.00 USD
";

#[test]
fn check_good_file_exits_zero_with_ok_envelope() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "good.beancount", GOOD_LEDGER);

    let (code, env) = run(&["check", file.to_str().unwrap(), "--json"]);

    assert_eq!(code, 0, "good file should exit 0: {env}");
    assert_eq!(env["ok"], Value::Bool(true));
    assert_eq!(env["exit_code"], 0);
    // The buffered check JSON is re-parsed into `result.data`.
    assert_eq!(env["result"]["data"]["error_count"], 0);
}

#[test]
fn check_bad_file_exits_nonzero() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "bad.beancount", BAD_LEDGER);

    let (code, env) = run(&["check", file.to_str().unwrap(), "--json"]);

    assert_ne!(code, 0, "unbalanced file should exit non-zero: {env}");
    assert_eq!(env["exit_code"], 1);
    // Envelope still reports the command ran (ok: true) but carries a
    // non-zero exit code and the diagnostics.
    assert!(
        env["result"]["data"]["error_count"]
            .as_u64()
            .is_some_and(|n| n >= 1),
        "expected at least one error: {env}"
    );
}

#[test]
fn check_missing_file_maps_to_not_found() {
    let tmp = tempfile::tempdir().unwrap();
    let missing = tmp.path().join("nope.beancount");

    let (code, env) = run(&["check", missing.to_str().unwrap(), "--json"]);

    // NOT_FOUND is exit code 3 in agcli's typed-exit-code table.
    assert_eq!(code, 3, "missing file should map to NOT_FOUND: {env}");
    assert_eq!(env["ok"], Value::Bool(false));
    assert_eq!(env["error"]["code"], "FILE_NOT_FOUND");
}

#[test]
fn query_returns_structured_json() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "good.beancount", GOOD_LEDGER);

    let (code, env) = run(&[
        "query",
        file.to_str().unwrap(),
        "SELECT account, sum(position) GROUP BY account",
        "--format",
        "json",
    ]);

    assert_eq!(code, 0, "query should exit 0: {env}");
    assert_eq!(env["ok"], Value::Bool(true));
    let rows = &env["result"]["data"]["rows"];
    assert!(rows.is_array(), "expected rows array: {env}");
    assert_eq!(rows.as_array().unwrap().len(), 2, "two accounts: {env}");
}

#[test]
fn report_balances_returns_json_data() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "good.beancount", GOOD_LEDGER);

    let (code, env) = run(&[
        "report",
        file.to_str().unwrap(),
        "balances",
        "--format",
        "json",
    ]);

    assert_eq!(code, 0, "report should exit 0: {env}");
    assert_eq!(env["ok"], Value::Bool(true));
    assert!(
        env["result"]["data"].is_array(),
        "balances data should be a JSON array: {env}"
    );
}

#[test]
fn check_alias_c_works() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "good.beancount", GOOD_LEDGER);

    let (code, env) = run(&["c", file.to_str().unwrap(), "--json"]);

    assert_eq!(code, 0, "alias `c` should behave like check: {env}");
    assert_eq!(env["ok"], Value::Bool(true));
}

/// M1: a bool flag declared before the positional must NOT swallow the
/// positional. `extract --invert-sign <file.csv>` should treat the CSV as the
/// input file, not error "extract requires a ledger file".
#[test]
fn extract_bool_flag_before_positional_keeps_positional() {
    let tmp = tempfile::tempdir().unwrap();
    let csv = write_fixture(
        tmp.path(),
        "bank.csv",
        "Date,Description,Amount\n2024-01-02,Coffee,-4.50\n",
    );

    let (code, env) = run(&["extract", "--invert-sign", csv.to_str().unwrap()]);

    // The CSV is recognized as the positional input: we must NOT get the
    // MISSING_FILE usage error. Any other outcome (success, or a parse/import
    // error) is acceptable here — the point is the flag didn't eat the file.
    assert_ne!(
        env["error"]["code"], "MISSING_FILE",
        "--invert-sign should not swallow the positional file: {env}"
    );
    // USAGE exit code is 2; a swallowed positional would surface as USAGE.
    assert_ne!(code, 2, "should not be a usage error: {env}");
}

/// M1: the `--no-header` extract bool flag before the positional likewise must
/// not consume the file.
#[test]
fn extract_no_header_flag_before_positional_keeps_positional() {
    let tmp = tempfile::tempdir().unwrap();
    let csv = write_fixture(tmp.path(), "bank.csv", "2024-01-02,Coffee,-4.50\n");

    let (_code, env) = run(&["extract", "--no-header", csv.to_str().unwrap()]);

    assert_ne!(
        env["error"]["code"], "MISSING_FILE",
        "--no-header should not swallow the positional file: {env}"
    );
}

/// M2: `ag-rledger query "SELECT ..."` with no `--file` must target the
/// configured default file, not route the SQL string into `file`. We point
/// the default at a good ledger via `RLEDGER_FILE`/config; here we use the
/// `--file`-less form and confirm the query runs against the default instead
/// of failing with a file-not-found for the SQL text.
#[test]
fn query_without_file_uses_default_not_positional() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "good.beancount", GOOD_LEDGER);

    // Set the default file through the env-driven profile path the binary
    // honors. `default.file` resolution reads config; the simplest robust
    // signal is RLEDGER_FILE if supported, else fall back to asserting the
    // SQL string is not treated as a path.
    let output = Command::new(ag_rledger())
        .args([
            "query",
            "SELECT account, sum(position) GROUP BY account",
            "--format",
            "json",
        ])
        .env("RLEDGER_FILE", file.to_str().unwrap())
        .output()
        .expect("spawn ag-rledger");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let env: Value = serde_json::from_str(stdout.trim())
        .unwrap_or_else(|e| panic!("envelope is not JSON ({e}): {stdout}"));

    // The SQL string must not be interpreted as a file path: a path-shaped
    // misroute would surface FILE_NOT_FOUND for "SELECT ...".
    assert_ne!(
        env["error"]["code"], "FILE_NOT_FOUND",
        "query text must not be treated as a file path: {env}"
    );
    // The leading positional ("SELECT ...") doesn't look like a ledger path,
    // so it is kept as query text rather than swallowed as the file.
}

/// M2: when a ledger-looking path IS the leading positional, query still
/// treats it as the file (heuristic doesn't over-correct).
#[test]
fn query_with_ledger_positional_still_uses_it_as_file() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "good.beancount", GOOD_LEDGER);

    let (code, env) = run(&[
        "query",
        file.to_str().unwrap(),
        "SELECT account, sum(position) GROUP BY account",
        "--format",
        "json",
    ]);

    assert_eq!(
        code, 0,
        "query with explicit ledger positional should run: {env}"
    );
    assert_eq!(env["ok"], Value::Bool(true));
}

/// M3: `ag-rledger add` without `--yes`/`--dry-run` must return a clean USAGE
/// error and must NOT block on stdin or mutate the ledger. We run with a
/// closed stdin; if the binary prompted it would hang (and the test would
/// time out) — instead it should return promptly with the confirmation error.
#[test]
fn add_without_yes_or_dry_run_errors_cleanly() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "ledger.beancount", GOOD_LEDGER);
    let before = std::fs::read_to_string(&file).unwrap();

    let output = Command::new(ag_rledger())
        .args([
            "add",
            file.to_str().unwrap(),
            "--quick",
            "Coffee Shop",
            "Morning coffee",
            "Expenses:Food",
            "4.50 USD",
            "Assets:Cash",
        ])
        .stdin(std::process::Stdio::null())
        .output()
        .expect("spawn ag-rledger");
    let code = output.status.code().expect("exit code");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let env: Value = serde_json::from_str(stdout.trim())
        .unwrap_or_else(|e| panic!("envelope is not JSON ({e}): {stdout}"));

    assert_eq!(
        env["ok"],
        Value::Bool(false),
        "should be an error envelope: {env}"
    );
    assert_eq!(
        code, 2,
        "confirmation-required should map to USAGE (2): {env}"
    );
    assert_eq!(env["error"]["code"], "CONFIRMATION_REQUIRED", "{env}");
    // The ledger must be untouched.
    let after = std::fs::read_to_string(&file).unwrap();
    assert_eq!(
        before, after,
        "ledger must not be mutated without confirmation"
    );
}

/// `ag-rledger add` is quick-mode only: omitting `--quick` (even with
/// `--yes`/`--dry-run`) must return a clean USAGE error, NOT panic. Regression
/// for the `.expect("quick mode args")` panic on agent-controlled input.
#[test]
fn add_without_quick_errors_cleanly_no_panic() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "ledger.beancount", GOOD_LEDGER);
    let before = std::fs::read_to_string(&file).unwrap();

    for confirm in ["--yes", "--dry-run"] {
        let output = Command::new(ag_rledger())
            .args(["add", file.to_str().unwrap(), confirm])
            .stdin(std::process::Stdio::null())
            .output()
            .expect("spawn ag-rledger");
        let code = output.status.code().expect("exit code");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let env: Value = serde_json::from_str(stdout.trim())
            .unwrap_or_else(|e| panic!("envelope is not JSON ({e}): {stdout}"));

        assert!(
            !stderr.contains("panicked"),
            "{confirm}: must not panic; stderr:\n{stderr}"
        );
        assert_eq!(env["ok"], Value::Bool(false), "{confirm}: {env}");
        assert_eq!(
            code, 2,
            "{confirm}: missing --quick should map to USAGE (2): {env}"
        );
        assert_eq!(
            env["error"]["code"], "MISSING_QUICK_ARGS",
            "{confirm}: {env}"
        );
    }
    // The ledger must be untouched.
    assert_eq!(before, std::fs::read_to_string(&file).unwrap());
}

/// M3: `ag-rledger add --dry-run` previews without prompting or mutating.
#[test]
fn add_dry_run_previews_without_mutating() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "ledger.beancount", GOOD_LEDGER);
    let before = std::fs::read_to_string(&file).unwrap();

    let output = Command::new(ag_rledger())
        .args([
            "add",
            file.to_str().unwrap(),
            "--dry-run",
            "--quick",
            "Coffee Shop",
            "Morning coffee",
            "Expenses:Food",
            "4.50 USD",
            "Assets:Cash",
        ])
        .stdin(std::process::Stdio::null())
        .output()
        .expect("spawn ag-rledger");
    let code = output.status.code().expect("exit code");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let env: Value = serde_json::from_str(stdout.trim())
        .unwrap_or_else(|e| panic!("envelope is not JSON ({e}): {stdout}"));

    assert_eq!(code, 0, "dry-run should succeed: {env}");
    assert_eq!(env["ok"], Value::Bool(true));
    let after = std::fs::read_to_string(&file).unwrap();
    assert_eq!(before, after, "dry-run must not mutate the ledger");
}

#[test]
fn root_command_tree_is_self_documenting() {
    let (code, env) = run(&[]);
    assert_eq!(code, 0);
    assert_eq!(env["ok"], Value::Bool(true));
    // The root envelope advertises the reserved agent flags and the
    // command tree, plus our compatibility root field.
    assert_eq!(env["result"]["compatibility"]["engine"], "rustledger");
}

/// `build_extract_args` constructs `extract_cmd::Args` by hand, so it can
/// reintroduce a default the clap definition no longer has — and a default
/// overwrites an `importers.toml` entry's own value (#2304). Checked through
/// the real binary in both directions: an omitted flag keeps the entry's
/// value, and a passed flag replaces it.
///
/// Assertions read `result.stdout`. The envelope's `command` field echoes the
/// command line, which contains the very values being checked, so matching
/// against the whole envelope passes whether or not they were applied.
#[test]
fn extract_adapter_keeps_entry_values_and_lets_flags_override() {
    let tmp = tempfile::tempdir().unwrap();
    let csv = write_fixture(
        tmp.path(),
        "stmt.csv",
        "date;payee;amount\n2025-01-15;SKIPPED;-1.00\n2025-01-16;COFFEE;-3.00\n",
    );
    let config = write_fixture(
        tmp.path(),
        "importers.toml",
        "[[importers]]\nname = \"card\"\naccount = \"Liabilities:Card\"\n\
         currency = \"GBP\"\ndate_column = \"date\"\npayee_column = \"payee\"\n\
         amount_column = \"amount\"\ndelimiter = \";\"\nskip_rows = 1\n",
    );
    let csv = csv.to_str().unwrap();
    let config = config.to_str().unwrap();
    let stdout = |extra: &[&str]| -> String {
        let mut argv = vec!["extract", "--config", config, "--importer", "card"];
        argv.extend_from_slice(extra);
        argv.push(csv);
        let (code, env) = run(&argv);
        assert_eq!(code, 0, "extract failed: {env}");
        env["result"]["stdout"]
            .as_str()
            .unwrap_or_else(|| panic!("no result.stdout in envelope: {env}"))
            .to_string()
    };

    // Omitted flags: every value comes from the entry.
    let entry = stdout(&[]);
    assert!(
        entry.contains("Liabilities:Card"),
        "entry account lost: {entry}"
    );
    assert!(
        entry.contains("GBP") && !entry.contains("USD"),
        "entry currency lost: {entry}"
    );
    assert!(entry.contains("COFFEE"), "entry delimiter lost: {entry}");
    assert!(!entry.contains("SKIPPED"), "entry skip_rows lost: {entry}");

    // Passed flags: each replaces the entry's value, including an explicit 0.
    let flags = stdout(&[
        "--account",
        "Liabilities:FromFlag",
        "--currency",
        "EUR",
        "--skip-rows",
        "0",
    ]);
    assert!(
        flags.contains("Liabilities:FromFlag"),
        "--account did not override the entry: {flags}"
    );
    assert!(
        flags.contains("EUR") && !flags.contains("GBP"),
        "--currency did not override the entry: {flags}"
    );
    assert!(
        flags.contains("SKIPPED"),
        "--skip-rows 0 did not override the entry's 1: {flags}"
    );
}

/// Run `ag-rledger <args...>` with `dir` as the cwd and the only config
/// source; return `(exit_code, envelope, process stderr)`.
fn run_isolated(dir: &std::path::Path, args: &[&str]) -> (i32, Value, String) {
    let output = Command::new(ag_rledger())
        .args(args)
        // `dir` is the user config dir and the cwd, so no stray project
        // config is found above it; PROGRAMDATA covers the Windows system
        // config path. The parse cache is off so `--verbose` reports a
        // fresh load every time.
        .current_dir(dir)
        .env("RLEDGER_CONFIG_DIR", dir)
        .env("PROGRAMDATA", dir)
        .env("BEANCOUNT_DISABLE_LOAD_CACHE", "1")
        .output()
        .expect("spawn ag-rledger");
    let code = output.status.code().expect("exit code");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let envelope: Value = serde_json::from_str(stdout.trim())
        .unwrap_or_else(|e| panic!("envelope is not JSON ({e}): {stdout}"));
    (
        code,
        envelope,
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// An unknown option, a failing balance assertion, and an account closed
/// with money in it: E7001, E2001, and the advisory-only E1004.
const DIAGNOSTICS_LEDGER: &str = "\
option \"not_a_real_option\" \"x\"

2024-01-01 open Assets:Cash
2024-01-01 open Expenses:Food

2024-01-07 * \"lunch\"
  Expenses:Food   12.50 USD
  Assets:Cash

2024-01-08 balance Assets:Cash  0.00 USD

2024-02-20 close Expenses:Food
";

/// #2546: `ag-rledger query` wrote the ledger's diagnostics to the process's
/// stderr, which the envelope does not carry, so an agent saw a clean result
/// for a ledger with a failing balance. They are now the envelope's
/// `warnings`, in the shape `report` uses, and the process's stderr is empty.
#[test]
fn query_diagnostics_are_envelope_warnings_not_stderr() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "diag.beancount", DIAGNOSTICS_LEDGER);
    let file = file.to_str().unwrap();

    let (code, env, stderr) = run_isolated(
        tmp.path(),
        &["query", file, "SELECT account", "--format", "json"],
    );
    assert_eq!(code, 0, "{env}");
    assert!(stderr.is_empty(), "stderr must stay clean, got: {stderr}");

    let warnings = env["result"]["warnings"]
        .as_array()
        .unwrap_or_else(|| panic!("no warnings in the envelope: {env}"));
    let codes: Vec<&str> = warnings
        .iter()
        .map(|w| w["code"].as_str().expect("each warning has a code"))
        .collect();
    // Option diagnostics first, as `rledger query` and bean-query print
    // them; the advisory E1004 is left out, as `check` leaves it out.
    assert_eq!(codes, vec!["E7001", "E2001"], "{env}");
    for w in warnings {
        assert!(
            w["message"].as_str().is_some_and(|m| !m.is_empty()),
            "each warning carries its message: {w}"
        );
    }
    // The query's own answer is untouched.
    assert!(
        env["result"]["data"].is_array() || env["result"]["data"].is_object(),
        "{env}"
    );
}

/// The warnings are exactly what `rledger query` prints, so the two surfaces
/// cannot drift apart.
#[test]
fn query_warnings_match_what_rledger_query_prints() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "diag.beancount", DIAGNOSTICS_LEDGER);
    let file = file.to_str().unwrap();

    let rledger = Command::new(env!("CARGO_BIN_EXE_rledger"))
        .args(["query", file, "SELECT account"])
        .current_dir(tmp.path())
        .env("RLEDGER_CONFIG_DIR", tmp.path())
        .env("PROGRAMDATA", tmp.path())
        .env("BEANCOUNT_DISABLE_LOAD_CACHE", "1")
        .output()
        .expect("spawn rledger");
    let printed: Vec<String> = String::from_utf8_lossy(&rledger.stderr)
        .lines()
        .filter(|l| !l.is_empty())
        .map(str::to_string)
        .collect();
    assert!(
        !printed.is_empty(),
        "rledger printed nothing to compare against"
    );

    let (_, env, _) = run_isolated(tmp.path(), &["query", file, "SELECT account"]);
    let carried: Vec<String> = env["result"]["warnings"]
        .as_array()
        .unwrap_or_else(|| panic!("no warnings: {env}"))
        .iter()
        .map(|w| {
            format!(
                "{}: {}",
                w["code"].as_str().unwrap(),
                w["message"].as_str().unwrap()
            )
        })
        .collect();
    assert_eq!(carried, printed);
}

/// `--no-errors` suppresses the diagnostics in the envelope as it does on
/// the terminal.
#[test]
fn query_no_errors_suppresses_the_warnings() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "diag.beancount", DIAGNOSTICS_LEDGER);
    let (code, env, stderr) = run_isolated(
        tmp.path(),
        &[
            "query",
            file.to_str().unwrap(),
            "SELECT account",
            "--no-errors",
        ],
    );
    assert_eq!(code, 0, "{env}");
    assert!(stderr.is_empty(), "{stderr}");
    assert!(env["result"].get("warnings").is_none(), "{env}");
}

/// #2546's audit: every other command that wrote to the process's stderr
/// now writes to the envelope's `result.stderr`, and the process's stderr
/// stays empty. Each case names what used to be lost.
#[test]
fn no_command_writes_to_the_process_stderr() {
    let tmp = tempfile::tempdir().unwrap();
    let good = write_fixture(tmp.path(), "good.beancount", GOOD_LEDGER);
    let good = good.to_str().unwrap();
    let unformatted = write_fixture(
        tmp.path(),
        "messy.beancount",
        "2024-01-01   open   Assets:Cash\n",
    );
    let unformatted = unformatted.to_str().unwrap();
    let csv = write_fixture(
        tmp.path(),
        "bank.csv",
        "Date,Description,Amount\n2024-01-02,Coffee,-4.50\n2024-01-03,Lunch,not-a-number\n",
    );
    let csv = csv.to_str().unwrap();
    let priced = write_fixture(
        tmp.path(),
        "priced.beancount",
        "2024-01-01 commodity AAPL\n  price: \"garbage\"\n",
    );
    let priced = priced.to_str().unwrap();
    let prefix = tmp.path().join("bin");
    std::fs::create_dir(&prefix).unwrap();
    let wrapper = if cfg!(windows) {
        "bean-check.cmd"
    } else {
        "bean-check"
    };
    std::fs::write(prefix.join(wrapper), "not ours\n").unwrap();
    let prefix = prefix.to_str().unwrap();

    for (args, expected) in [
        // `--verbose` progress from the parse cache.
        (vec!["check", good, "--verbose"], "Loading "),
        (vec!["report", good, "balances", "--verbose"], "Loading "),
        // The diff itself: `--check --diff` returned an exit status and no diff.
        (
            vec!["format", unformatted, "--check", "--diff"],
            "@@ line 1 @@",
        ),
        // A row the importer skipped.
        (
            vec!["extract", csv, "--account", "Assets:Bank"],
            "warning: Row 2",
        ),
        // A malformed `price:` value, found without touching the network.
        (
            vec!["price", "--file", priced, "--dry-run"],
            "malformed `price:` metadata",
        ),
        // A file in the way that is not a wrapper.
        (vec!["compat", "uninstall", "--prefix", prefix], "skip:"),
    ] {
        let (_, env, stderr) = run_isolated(tmp.path(), &args);
        assert!(stderr.is_empty(), "{args:?} wrote to stderr: {stderr}");
        let carried = env["result"]["stderr"]
            .as_str()
            // A failed command's buffer rides on the envelope's `data`.
            .or_else(|| env["data"]["stderr"].as_str())
            .unwrap_or_default();
        assert!(
            carried.contains(expected),
            "{args:?}: {expected:?} missing from the envelope: {env}"
        );
    }
}

/// A command that fails keeps what it wrote before failing: `format`
/// lists each parse error, then refuses the file.
#[test]
fn a_failing_command_carries_its_stderr_on_the_error() {
    let tmp = tempfile::tempdir().unwrap();
    let broken = write_fixture(tmp.path(), "broken.beancount", "2024-01-01 open\n");
    let (code, env, stderr) = run_isolated(tmp.path(), &["format", broken.to_str().unwrap()]);
    assert_ne!(code, 0, "{env}");
    assert!(stderr.is_empty(), "{stderr}");
    assert!(
        env["data"]["stderr"]
            .as_str()
            .is_some_and(|s| s.contains("error: ")),
        "the parse errors must ride on the error: {env}"
    );
}
