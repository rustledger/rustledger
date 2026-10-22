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

/// `ag-rledger extract` and `extract --list-importers` read the `[payees]`
/// and `[importers.payees]` tables (#2550) like `rledger` does: the payee is
/// rewritten (entry table first), and a bad pattern fails the listing.
#[test]
fn extract_adapter_applies_payee_tables() {
    let tmp = tempfile::tempdir().unwrap();
    let csv = write_fixture(
        tmp.path(),
        "stmt.csv",
        "date,payee,desc,amount\n2025-01-15,HOFER DANKT,Card,-1.00\n2025-01-16,AMZN Mktp DE,Order,-3.00\n",
    );
    let config = write_fixture(
        tmp.path(),
        "importers.toml",
        "[payees]\n\"/^amzn/\" = \"Amazon\"\n\"hofer\" = \"Shared\"\n\
         [[importers]]\nname = \"bank\"\naccount = \"Assets:Bank\"\n\
         currency = \"EUR\"\ndate_column = \"date\"\npayee_column = \"payee\"\n\
         narration_column = \"desc\"\namount_column = \"amount\"\n\
         [importers.payees]\n\"hofer dankt\" = \"Hofer\"\n",
    );
    let (code, env) = run(&[
        "extract",
        "--config",
        config.to_str().unwrap(),
        "--importer",
        "bank",
        csv.to_str().unwrap(),
    ]);
    assert_eq!(code, 0, "extract failed: {env}");
    let stdout = env["result"]["stdout"].as_str().unwrap_or_default();
    assert!(
        stdout.contains("2025-01-15 * \"Hofer\" \"Card\""),
        "{stdout}"
    );
    assert!(
        stdout.contains("2025-01-16 * \"Amazon\" \"Order\""),
        "{stdout}"
    );

    let (code, env) = run(&[
        "extract",
        "--config",
        config.to_str().unwrap(),
        "--list-importers",
    ]);
    assert_eq!(code, 0, "list-importers failed: {env}");

    let bad = write_fixture(tmp.path(), "bad.toml", "[payees]\n\"/(/\" = \"X\"\n");
    let (code, env) = run(&[
        "extract",
        "--config",
        bad.to_str().unwrap(),
        "--list-importers",
    ]);
    assert_ne!(code, 0, "a bad pattern must fail the listing: {env}");
    assert!(
        env.to_string().contains("not a valid regular expression"),
        "{env}"
    );
}

/// Run `ag-rledger <args...>` with `dir` as the cwd and the only config
/// source, and return `(exit_code, envelope, stderr)`.
fn run_in(dir: &std::path::Path, args: &[&str]) -> (i32, Value, String) {
    run_in_with(dir, args, &[])
}

/// [`run_in`], with `env` set as well.
fn run_in_with(dir: &std::path::Path, args: &[&str], env: &[(&str, &str)]) -> (i32, Value, String) {
    let output = Command::new(ag_rledger())
        .args(args)
        .envs(env.iter().copied())
        // `dir` is the user config dir and the cwd, so no stray project
        // config is found above it; PROGRAMDATA covers the Windows system
        // config path. The parse cache is off so `--verbose` reports a
        // fresh load every time.
        .current_dir(dir)
        .env("RLEDGER_CONFIG_DIR", dir)
        .env("PROGRAMDATA", dir)
        .env("BEANCOUNT_DISABLE_LOAD_CACHE", "1")
        .env_remove("RLEDGER_PROFILE")
        .env_remove("AG_RLEDGER_PROFILE")
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

    let (code, env, stderr) = run_in(
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

    let (_, env, _) = run_in(tmp.path(), &["query", file, "SELECT account"]);
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
    let (code, env, stderr) = run_in(
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
        // `extract`'s progress. Its warnings, and `price`'s, are
        // `warnings` records now (#2566), covered by
        // `extract_and_price_warnings_are_coded_records`.
        (
            vec!["extract", csv, "--account", "Assets:Bank"],
            "Extracted 1 transactions",
        ),
        // A file in the way that is not a wrapper.
        (vec!["compat", "uninstall", "--prefix", prefix], "skip:"),
    ] {
        let (_, env, stderr) = run_in(tmp.path(), &args);
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
    let (code, env, stderr) = run_in(tmp.path(), &["format", broken.to_str().unwrap()]);
    assert_ne!(code, 0, "{env}");
    assert!(stderr.is_empty(), "{stderr}");
    assert!(
        env["data"]["stderr"]
            .as_str()
            .is_some_and(|s| s.contains("error: ")),
        "the parse errors must ride on the error: {env}"
    );
}

/// #2522: a config file that fails to load was dropped for defaults
/// (`unwrap_or_default()`), so a typo anywhere in it silently reset every
/// setting. It is now an error in the envelope, for every command that reads
/// the config, as `rledger` makes it fatal (#1306).
#[test]
fn a_broken_config_is_an_error_not_silent_defaults() {
    for broken in [
        // Zero is refused at parse time: the sandbox would read it as 1s.
        "[plugins]\nmax_time_secs = 0\n",
        // A typo'd key under `[plugins]` (the table denies unknown fields).
        "[plugins]\nmax_time_sec = 5\n",
        // Not TOML at all.
        "[plugins\n",
    ] {
        let tmp = tempfile::tempdir().unwrap();
        let file = write_fixture(tmp.path(), "good.beancount", GOOD_LEDGER);
        let file = file.to_str().unwrap();
        std::fs::write(tmp.path().join("config.toml"), broken).unwrap();

        for args in [
            vec!["check", file],
            vec!["query", file, "SELECT account"],
            vec!["report", file, "balances"],
            vec!["format", file, "--check"],
            vec!["doctor", "stats", file],
            vec!["lint", "transfers", file],
            vec!["extract", "bank.csv"],
            vec![
                "add",
                file,
                "--quick",
                "p",
                "n",
                "Assets:Cash",
                "1 USD",
                "--dry-run",
            ],
            vec!["compat", "uninstall", "--prefix", "nowhere"],
            vec!["price", "--list-sources"],
        ] {
            let (code, env, _) = run_in(tmp.path(), &args);
            assert_eq!(
                env["ok"],
                Value::Bool(false),
                "{args:?} with {broken:?}: {env}"
            );
            assert_eq!(env["error"]["code"], "CONFIG_ERROR", "{args:?}: {env}");
            assert_eq!(code, 2, "{args:?}: {env}");
            let message = env["error"]["message"].as_str().unwrap_or_default();
            assert!(
                message.contains("Failed to parse config file"),
                "{args:?}: the message must name the config failure: {env}"
            );
        }

        // `config` is exempt, as in `rledger`: it is how a broken file is
        // found and fixed.
        let (code, env, _) = run_in(tmp.path(), &["config", "path"]);
        assert_eq!(code, 0, "config path must still run: {env}");
    }
}

/// The plugin-budget flags are refused when out of range, with the bounds
/// `rledger` applies (one shared definition).
#[test]
fn plugin_budget_flags_are_validated() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "good.beancount", GOOD_LEDGER);
    let file = file.to_str().unwrap();
    for (flag, value) in [
        ("--plugin-max-time-secs", "0"),
        ("--plugin-max-memory-mb", "0"),
        ("--plugin-max-memory-mb", "4097"),
    ] {
        let (code, env, _) = run_in(tmp.path(), &["check", file, flag, value]);
        assert_eq!(code, 2, "{flag} {value}: {env}");
        assert_eq!(
            env["error"]["code"], "INVALID_FLAG",
            "{flag} {value}: {env}"
        );
        assert!(
            env["error"]["message"]
                .as_str()
                .is_some_and(|m| m.contains(flag)),
            "{flag} {value}: {env}"
        );
    }
    // In range, accepted on every command, before or after it.
    let (code, env, _) = run_in(
        tmp.path(),
        &[
            "--plugin-max-time-secs",
            "5",
            "report",
            file,
            "balances",
            "--plugin-max-memory-mb",
            "512",
        ],
    );
    assert_eq!(code, 0, "{env}");
}

/// #2522/#2552: `allow_unknown_flags()` let any flag through unread. A flag
/// the command does not read is now refused, whether it is a typo or a real
/// `rledger` flag the agent surface does not support.
#[test]
fn a_flag_the_command_does_not_read_is_refused() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "good.beancount", GOOD_LEDGER);
    let file = file.to_str().unwrap();
    for args in [
        vec!["check", file, "--frobnicate"],
        vec!["report", file, "balances", "--no-pager"],
        vec!["format", file, "--check", "--no-cache"],
        vec!["check", file, "--plugin-max-mem-mb", "512"],
    ] {
        let (code, env, _) = run_in(tmp.path(), &args);
        assert_eq!(env["error"]["code"], "UNKNOWN_FLAG", "{args:?}: {env}");
        assert_eq!(code, 2, "{args:?}: {env}");
    }
    // agcli's framework flags still pass on every command.
    let (code, env, _) = run_in(
        tmp.path(),
        &["check", file, "--json", "--compact", "--no-color"],
    );
    assert_eq!(code, 0, "{env}");
}

/// `ag-rledger --plugin-max-time-secs 5 <alias>` took `5` for the command
/// and never expanded the alias.
#[test]
fn an_alias_after_a_plugin_budget_flag_still_expands() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "good.beancount", GOOD_LEDGER);
    std::fs::write(
        tmp.path().join("config.toml"),
        "[aliases]\nbal = \"report balances\"\n",
    )
    .unwrap();
    let (code, env, _) = run_in(
        tmp.path(),
        &[
            "--plugin-max-memory-mb",
            "512",
            "bal",
            "--file",
            file.to_str().unwrap(),
            "--format",
            "json",
        ],
    );
    assert_eq!(code, 0, "{env}");
    assert_eq!(env["result"]["command"], "report", "{env}");
}

/// The plugin budget reaches a plugin run by `ag-rledger`, from the flag
/// and from the config file, with the flag winning (#2522, #2552). Before,
/// `ag-rledger` had no flag, and a config-only budget was applied before the
/// flags could be.
#[cfg(feature = "python-plugin-wasm")]
mod plugin_budget {
    use super::*;
    use rustledger_plugin::sandbox::FUEL_PER_SECOND;
    use std::path::Path;

    /// What the plugin's empty output fails with once `process` returns:
    /// proof it ran to completion, not merely that it did not trap.
    const RAN_TO_COMPLETION: &str = "reading marker";
    const FUEL_TRAP: &str = "all fuel consumed";

    /// Write `plugin.wasm` (from `process_body`, a WAT function body ending in
    /// an `i64`) and a ledger that loads it; return the ledger path.
    fn setup(dir: &Path, process_body: &str) -> String {
        let wat = format!(
            r#"(module
                (memory (export "memory") 1)
                (func (export "alloc") (param i32) (result i32) i32.const 0)
                (func (export "__rustledger_abi_version") (result i32) i32.const 3)
                (func (export "process") (param i32 i32) (result i64) (local $n i32)
                    {process_body}))"#
        );
        let wasm = dir.join("plugin.wasm");
        std::fs::write(&wasm, wat::parse_str(wat).expect("WAT parses")).unwrap();
        let ledger = dir.join("ledger.beancount");
        std::fs::write(
            &ledger,
            format!(
                "plugin \"{}\"\n\n2024-01-01 open Assets:Bank USD\n",
                wasm.display()
            ),
        )
        .unwrap();
        ledger.to_str().unwrap().to_string()
    }

    /// About three seconds of fuel: fits the default 30 s, traps on 1 s.
    fn burn(dir: &Path) -> String {
        let iterations = 3 * FUEL_PER_SECOND / 6;
        setup(
            dir,
            &format!(
                "(local.set $n (i32.const {iterations}))
                 (loop
                     (local.set $n (i32.sub (local.get $n) (i32.const 1)))
                     (br_if 0 (local.get $n)))
                 i64.const 0"
            ),
        )
    }

    /// Grows memory to about 300 MiB: refused under the default 256 MiB
    /// cap (the plugin then traps), granted under 1024.
    fn hog(dir: &Path) -> String {
        setup(
            dir,
            "(if (i32.eq (memory.grow (i32.const 4800)) (i32.const -1)) (then unreachable))
             i64.const 0",
        )
    }

    fn result_text(env: &Value) -> String {
        env.to_string()
    }

    #[test]
    fn time_budget_flag_and_config_take_effect() {
        let tmp = tempfile::tempdir().unwrap();
        let ledger = burn(tmp.path());

        let (_, env, _) = run_in(tmp.path(), &["check", &ledger]);
        let out = result_text(&env);
        assert!(out.contains(RAN_TO_COMPLETION), "default budget: {out}");
        assert!(!out.contains(FUEL_TRAP), "default budget: {out}");

        for args in [
            vec!["check", &ledger, "--plugin-max-time-secs", "1"],
            vec!["--plugin-max-time-secs", "1", "check", &ledger],
            // `report` too: the budget is the process's, not `check`'s.
            vec!["report", &ledger, "balances", "--plugin-max-time-secs", "1"],
        ] {
            let (_, env, _) = run_in(tmp.path(), &args);
            assert!(result_text(&env).contains(FUEL_TRAP), "{args:?}: {env}");
        }

        std::fs::write(
            tmp.path().join("config.toml"),
            "[plugins]\nmax_time_secs = 1\n",
        )
        .unwrap();
        let (_, env, _) = run_in(tmp.path(), &["check", &ledger]);
        assert!(result_text(&env).contains(FUEL_TRAP), "config: {env}");

        // The flag beats the config file.
        let (_, env, _) = run_in(
            tmp.path(),
            &["check", &ledger, "--plugin-max-time-secs", "60"],
        );
        let out = result_text(&env);
        assert!(out.contains(RAN_TO_COMPLETION), "flag over config: {out}");
        assert!(!out.contains(FUEL_TRAP), "flag over config: {out}");
    }

    #[test]
    fn memory_cap_flag_and_config_take_effect() {
        let tmp = tempfile::tempdir().unwrap();
        let ledger = hog(tmp.path());

        let (_, env, _) = run_in(tmp.path(), &["check", &ledger]);
        assert!(
            !result_text(&env).contains(RAN_TO_COMPLETION),
            "the default 256 MiB cap must refuse the plugin: {env}"
        );

        let (_, env, _) = run_in(
            tmp.path(),
            &["check", &ledger, "--plugin-max-memory-mb", "1024"],
        );
        assert!(
            result_text(&env).contains(RAN_TO_COMPLETION),
            "--plugin-max-memory-mb 1024 must let it run: {env}"
        );

        std::fs::write(
            tmp.path().join("config.toml"),
            "[plugins]\nmax_memory_mb = 1024\n",
        )
        .unwrap();
        let (_, env, _) = run_in(tmp.path(), &["check", &ledger]);
        assert!(
            result_text(&env).contains(RAN_TO_COMPLETION),
            "config: {env}"
        );

        // The flag beats the config file.
        let (_, env, _) = run_in(
            tmp.path(),
            &["check", &ledger, "--plugin-max-memory-mb", "256"],
        );
        assert!(
            !result_text(&env).contains(RAN_TO_COMPLETION),
            "flag over config: {env}"
        );
    }
}

/// The envelope's `warnings`: `result.warnings`, or `data.warnings` on a
/// failed command.
fn envelope_warnings(env: &Value) -> Vec<Value> {
    env["result"]["warnings"]
        .as_array()
        .or_else(|| env["data"]["warnings"].as_array())
        .cloned()
        .unwrap_or_default()
}

/// The codes of the envelope's `warnings`, in order.
fn warning_codes(env: &Value) -> Vec<String> {
    envelope_warnings(env)
        .iter()
        .map(|w| {
            w["code"]
                .as_str()
                .unwrap_or_else(|| panic!("a warning without a code: {w}"))
                .to_string()
        })
        .collect()
}

/// What `rledger <args...>` writes to stderr, run as [`run_in_with`] runs
/// `ag-rledger`.
fn rledger_stderr(dir: &std::path::Path, args: &[&str], env: &[(&str, &str)]) -> String {
    let output = Command::new(env!("CARGO_BIN_EXE_rledger"))
        .args(args)
        .envs(env.iter().copied())
        .current_dir(dir)
        .env("RLEDGER_CONFIG_DIR", dir)
        .env("PROGRAMDATA", dir)
        .env("BEANCOUNT_DISABLE_LOAD_CACHE", "1")
        .env_remove("RLEDGER_PROFILE")
        .output()
        .expect("spawn rledger");
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// Run `ag-rledger <args...>` in `dir` and assert: nothing on the process's
/// stderr, the warnings carry exactly `expected` codes in order, no warning
/// line is left in `result.stderr`, and each warning's message is what
/// `rledger` prints for the same invocation. Returns the envelope.
#[track_caller]
fn assert_warnings(
    dir: &std::path::Path,
    args: &[&str],
    env: &[(&str, &str)],
    expected: &[&str],
) -> Value {
    let (_, envelope, stderr) = run_in_with(dir, args, env);
    assert!(stderr.is_empty(), "{args:?} wrote to stderr: {stderr}");
    assert_eq!(warning_codes(&envelope), expected, "{args:?}: {envelope}");
    let carried = envelope["result"]["stderr"]
        .as_str()
        .or_else(|| envelope["data"]["stderr"].as_str())
        .unwrap_or_default();
    assert!(
        !carried.contains("warning"),
        "{args:?}: a warning is still prose in result.stderr: {carried}"
    );
    let printed = rledger_stderr(dir, args, env);
    for w in envelope_warnings(&envelope) {
        let message = w["message"].as_str().expect("a warning has a message");
        assert!(
            printed.contains(message),
            "{args:?}: rledger does not print {message:?}:\n{printed}"
        );
    }
    envelope
}

/// #2566: `extract` and `price` warnings were prose in `result.stderr`. They
/// are `warnings` records with codes, in the shape `query` and `report` use,
/// and `rledger` still prints each one.
#[test]
fn extract_and_price_warnings_are_coded_records() {
    let tmp = tempfile::tempdir().unwrap();
    let dir = tmp.path();
    let csv = write_fixture(
        dir,
        "bank.csv",
        "Date,Description,Amount\n2024-01-02,Coffee,-4.50\n\
         2024-01-03,Lunch,not-a-number\n2024-01-04,Tea,-2.00\n",
    );
    let csv = csv.to_str().unwrap();
    let existing = write_fixture(
        dir,
        "existing.beancount",
        "2024-01-01 open Assets:Bank USD\n2024-01-01 open Expenses:Unknown\n\n\
         2024-01-02 * \"Coffee\"\n  Assets:Bank  -4.50 USD\n  Expenses:Unknown\n",
    );
    let existing = existing.to_str().unwrap();

    // A row the importer could not read, and a duplicate `--existing` skipped.
    let env = assert_warnings(
        dir,
        &[
            "extract",
            csv,
            "--account",
            "Assets:Bank",
            "--existing",
            existing,
        ],
        &[],
        &[
            "IMPORTER_WARNING",
            "DUPLICATES_SKIPPED",
            "DUPLICATE_SKIPPED",
        ],
    );
    let warnings = envelope_warnings(&env);
    assert!(
        warnings[0]["message"]
            .as_str()
            .is_some_and(|m| m.starts_with("Row 2")),
        "{env}"
    );
    // A skipped row says which, by date and account.
    assert_eq!(warnings[2]["date"], "2024-01-02", "{env}");
    assert_eq!(warnings[2]["account"], "Assets:Bank", "{env}");
    // The rest of the answer is untouched.
    let stdout = env["result"]["stdout"].as_str().unwrap_or_default();
    assert!(
        stdout.contains("Tea") && !stdout.contains("Coffee"),
        "{env}"
    );

    // A currency the account's `open` does not allow.
    let env = assert_warnings(
        dir,
        &[
            "extract",
            csv,
            "--account",
            "Assets:Bank",
            "--currency",
            "EUR",
            "--existing",
            existing,
        ],
        &[],
        &["CURRENCY_NOT_ALLOWED", "IMPORTER_WARNING"],
    );
    assert_eq!(
        envelope_warnings(&env)[0]["account"],
        "Assets:Bank",
        "{env}"
    );

    // A malformed `price:` value, and nothing left to fetch: found without
    // touching the network.
    let priced = write_fixture(
        dir,
        "priced.beancount",
        "2024-01-01 commodity AAPL\n  price: \"garbage\"\n",
    );
    assert_warnings(
        dir,
        &["price", "--file", priced.to_str().unwrap(), "--dry-run"],
        &[],
        &[
            "PRICE_METADATA_MALFORMED",
            "NO_SYMBOLS",
            "NO_SYMBOLS_HINT",
            "NO_SYMBOLS_HINT",
        ],
    );

    // A price that failed to fetch (a source command that cannot run).
    let env = assert_warnings(
        dir,
        &[
            "price",
            "AAPL",
            "--source-cmd",
            "rledger-test-no-such-command-2566",
        ],
        &[],
        &["PRICE_FETCH_FAILED"],
    );
    assert!(
        envelope_warnings(&env)[0]["message"]
            .as_str()
            .is_some_and(|m| m.starts_with("Failed to fetch AAPL: ")),
        "{env}"
    );
}

/// #2566: an `importers.toml` that does not parse costs the run its payee
/// rewrites and its WASM importer directory, and both are said in
/// `warnings`.
#[test]
fn an_unreadable_importers_config_is_a_coded_warning() {
    let tmp = tempfile::tempdir().unwrap();
    let dir = tmp.path();
    write_fixture(dir, "importers.toml", "[payees\n");
    let csv = write_fixture(
        dir,
        "bank.csv",
        "Date,Description,Amount\n2024-01-02,Coffee,-4.50\n",
    );
    let mut expected = Vec::new();
    // Only a build with the WASM runtime reads `wasm_importer_dir`.
    if cfg!(feature = "python-plugin-wasm") {
        expected.push("IMPORTERS_CONFIG_UNREADABLE");
    }
    expected.push("PAYEES_NOT_APPLIED");
    assert_warnings(
        dir,
        &["extract", csv.to_str().unwrap(), "--account", "Assets:Bank"],
        &[],
        &expected,
    );
}

/// #2566: the `RLEDGER_CONFIG` deprecation warning was written by the config
/// loader straight to the process's stderr. It leads every command's
/// `warnings` now, once even for `config`, which loads the file again.
#[test]
fn the_rledger_config_deprecation_is_a_warning_not_stderr() {
    let tmp = tempfile::tempdir().unwrap();
    let dir = tmp.path();
    let good = write_fixture(dir, "good.beancount", GOOD_LEDGER);
    let env = [("RLEDGER_CONFIG", "/nonexistent/config.toml")];
    for args in [
        vec!["check", good.to_str().unwrap()],
        vec!["config", "path"],
        vec!["report", good.to_str().unwrap(), "accounts"],
        // The commands #2567 added run inside the same capture (#2566).
        vec!["explain", "E2001"],
        vec!["lint", "closed-nonempty", good.to_str().unwrap()],
        vec![
            "report",
            good.to_str().unwrap(),
            "returns",
            "--investments",
            "Assets:Cash",
            "--currency",
            "USD",
            "--end",
            "2024-12-31",
        ],
        vec!["report", good.to_str().unwrap(), "capgains"],
    ] {
        let envelope = assert_warnings(dir, &args, &env, &["RLEDGER_CONFIG_DEPRECATED"]);
        assert!(
            envelope_warnings(&envelope)[0]["message"]
                .as_str()
                .is_some_and(|m| m.starts_with("RLEDGER_CONFIG is no longer supported")),
            "{envelope}"
        );
    }
}

/// The deprecation warning still reaches the envelope when the config then
/// fails to load: no command runs, so it rides on the `CONFIG_ERROR`.
#[test]
fn the_rledger_config_deprecation_rides_on_a_config_error() {
    let tmp = tempfile::tempdir().unwrap();
    let dir = tmp.path();
    let good = write_fixture(dir, "good.beancount", GOOD_LEDGER);
    std::fs::write(dir.join("config.toml"), "[plugins\n").unwrap();
    let (code, env, stderr) = run_in_with(
        dir,
        &["check", good.to_str().unwrap()],
        &[("RLEDGER_CONFIG", "/nonexistent/config.toml")],
    );
    assert_ne!(code, 0, "{env}");
    assert!(stderr.is_empty(), "{stderr}");
    assert_eq!(env["error"]["code"], "CONFIG_ERROR", "{env}");
    assert_eq!(warning_codes(&env), ["RLEDGER_CONFIG_DEPRECATED"], "{env}");
}

/// #2566: a WASM importer whose `identify` fails was reported on the
/// process's stderr by the importer crate. It is a `warnings` record now,
/// with the module's text escaped (#2525).
#[cfg(feature = "python-plugin-wasm")]
#[test]
fn a_failing_wasm_identify_is_a_warning_not_stderr() {
    let tmp = tempfile::tempdir().unwrap();
    let dir = tmp.path();
    let original = r#"(func (export "identify") (param i32 i32) (result i64) i64.const 0)"#;
    let wat = rustledger_importer::test_fixtures::metadata_wat("trp");
    assert!(wat.contains(original), "fixture changed shape");
    let wat = wat.replace(
        original,
        r#"(func (export "identify") (param i32 i32) (result i64) unreachable)"#,
    );
    let wasm = dir.join("trap.wasm");
    std::fs::write(&wasm, wat::parse_str(&wat).expect("WAT parses")).unwrap();
    let csv = write_fixture(
        dir,
        "bank.csv",
        "Date,Description,Amount\n2024-01-02,Coffee,-4.50\n",
    );

    let env = assert_warnings(
        dir,
        &[
            "extract",
            csv.to_str().unwrap(),
            "--account",
            "Assets:Bank",
            "--wasm-importer",
            wasm.to_str().unwrap(),
        ],
        &[],
        &["IMPORTER_IDENTIFY_FAILED"],
    );
    let message = envelope_warnings(&env)[0]["message"]
        .as_str()
        .unwrap_or_default()
        .to_string();
    assert!(
        message.starts_with("WASM importer `trp` identify("),
        "{env}"
    );
    // The CSV importer still read the file.
    assert!(
        env["result"]["stdout"]
            .as_str()
            .is_some_and(|s| s.contains("Coffee")),
        "{env}"
    );
}

/// The subcommand names `rledger --help` lists (clap's `Commands:` section),
/// without `help`.
fn rledger_commands() -> Vec<String> {
    let output = Command::new(env!("CARGO_BIN_EXE_rledger"))
        .arg("--help")
        .output()
        .expect("spawn rledger --help");
    let help = String::from_utf8_lossy(&output.stdout).into_owned();
    let names: Vec<String> = help
        .lines()
        .skip_while(|line| line.trim() != "Commands:")
        .skip(1)
        .take_while(|line| !line.trim().is_empty())
        .filter_map(|line| line.split_whitespace().next())
        .filter(|name| *name != "help")
        .map(str::to_string)
        .collect();
    // The parse is shown able to find commands, or an empty list would pass
    // the guard below vacuously.
    for known in ["check", "query", "report", "explain", "lint"] {
        assert!(
            names.iter().any(|n| n == known),
            "could not read `{known}` out of `rledger --help`:\n{help}"
        );
    }
    names
}

/// The drift guard for #2567: every `rledger` command is an `ag-rledger`
/// command, or is listed in the root envelope's `unsupported_commands` and
/// refused by name. A command added to `rledger` fails here until it is one
/// or the other. Before, `explain` was simply missing.
#[test]
fn every_rledger_command_is_offered_or_listed_as_unsupported() {
    let (_, root) = run(&[]);
    let commands: Vec<String> = root["result"]["commands"]
        .as_array()
        .unwrap_or_else(|| panic!("no command tree: {root}"))
        .iter()
        .filter_map(|c| c["name"].as_str().map(str::to_string))
        .collect();
    let unsupported: Vec<String> = root["result"]["unsupported_commands"]
        .as_array()
        .unwrap_or_else(|| panic!("no unsupported_commands: {root}"))
        .iter()
        .map(|c| {
            assert!(
                c["reason"].as_str().is_some_and(|r| !r.is_empty()),
                "an unsupported command says why: {c}"
            );
            c["command"].as_str().expect("command name").to_string()
        })
        .collect();

    let rledger = rledger_commands();
    for name in &rledger {
        assert!(
            commands.contains(name),
            "`rledger {name}` has no `ag-rledger` counterpart and is not listed as \
             unsupported: offer it, or add it to UNSUPPORTED_COMMANDS"
        );
    }
    for name in &unsupported {
        assert!(
            rledger.contains(name),
            "`{name}` is listed as unsupported but rledger has no such command"
        );
        let (code, env) = run(&[name.as_str(), "bash"]);
        assert_ne!(code, 0, "{env}");
        assert_eq!(env["error"]["code"], "UNSUPPORTED", "{env}");
    }
}

/// What `rledger <args>` prints on stdout, and its exit code, run in `dir`
/// as [`run_in`] runs `ag-rledger`.
fn rledger_stdout(dir: &std::path::Path, args: &[&str]) -> (i32, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_rledger"))
        .args(args)
        .current_dir(dir)
        .env("RLEDGER_CONFIG_DIR", dir)
        .env("PROGRAMDATA", dir)
        .env("BEANCOUNT_DISABLE_LOAD_CACHE", "1")
        .output()
        .expect("spawn rledger");
    (
        output.status.code().expect("exit code"),
        String::from_utf8_lossy(&output.stdout).into_owned(),
    )
}

/// #2567: `report returns`, `report capgains`, `lint closed-nonempty` and
/// `explain` are offered, with `rledger`'s flags; the answer in `result` is
/// what `rledger` prints, and the exit code is `rledger`'s.
#[test]
fn the_commands_from_2567_answer_as_rledger_does() {
    let tmp = tempfile::tempdir().unwrap();
    let returns = write_fixture(
        tmp.path(),
        "returns.beancount",
        "option \"operating_currency\" \"USD\"\n\n\
         2020-01-01 open Assets:Bank\n2020-01-01 open Assets:Broker:Stock\n\
         2020-01-01 open Income:Dividends\n\n\
         2020-01-01 * \"Buy AAPL\"\n  Assets:Broker:Stock  10 AAPL {100 USD}\n  Assets:Bank  -1000 USD\n\n\
         2020-06-01 * \"Dividend\"\n  Assets:Bank  20 USD\n  Income:Dividends  -20 USD\n\n\
         2020-12-31 price AAPL 130 USD\n",
    );
    let returns = returns.to_str().unwrap();
    let gains = write_fixture(
        tmp.path(),
        "gains.beancount",
        "option \"booking_method\" \"FIFO\"\n\n\
         2020-01-01 open Assets:Broker:Stock\n2020-01-01 open Assets:Bank\n\
         2020-01-01 open Income:Gains\n\n\
         2020-01-01 * \"Buy\"\n  Assets:Broker:Stock  10 AAPL {100 USD}\n  Assets:Bank  -1000 USD\n\n\
         2024-03-01 * \"Sell\"\n  Assets:Broker:Stock  -8 AAPL {} @ 150 USD\n  Assets:Bank  1200 USD\n  Income:Gains\n\n\
         2024-06-01 close Assets:Bank\n",
    );
    let gains = gains.to_str().unwrap();

    for (ag, rledger) in [
        (
            vec![
                "report",
                returns,
                "returns",
                "-i",
                "Assets:Broker",
                "--income",
                "Income:Dividends",
                "--end",
                "2020-12-31",
                "--format",
                "json",
            ],
            vec![
                "report",
                returns,
                "returns",
                "-i",
                "Assets:Broker",
                "--income",
                "Income:Dividends",
                "--end",
                "2020-12-31",
                "--format",
                "json",
                "--no-pager",
            ],
        ),
        (
            vec!["report", gains, "capgains", "--year", "2024", "--irr"],
            vec![
                "report",
                gains,
                "capgains",
                "--year",
                "2024",
                "--irr",
                "--no-pager",
            ],
        ),
        (
            vec!["lint", "closed-nonempty", gains, "--format", "json"],
            vec!["lint", "closed-nonempty", gains, "--format", "json"],
        ),
        (vec!["explain", "E2001"], vec!["explain", "E2001"]),
        (vec!["explain"], vec!["explain"]),
        // An unknown code: exit 1 with the pointer, as in rledger.
        (vec!["explain", "E9999"], vec!["explain", "E9999"]),
    ] {
        let (code, env, stderr) = run_in(tmp.path(), &ag);
        assert!(stderr.is_empty(), "{ag:?} wrote to stderr: {stderr}");
        let (rledger_code, printed) = rledger_stdout(tmp.path(), &rledger);
        assert!(
            !printed.is_empty(),
            "{rledger:?} printed nothing to compare"
        );
        assert_eq!(code, rledger_code, "{ag:?}: exit code differs: {env}");
        assert_eq!(
            env["result"]["stdout"].as_str(),
            Some(printed.as_str()),
            "{ag:?}: result differs from rledger's: {env}"
        );
    }

    // The closed-with-a-balance finding is really there, so the comparison
    // above compared a finding and not two empty reports.
    let (_, env, _) = run_in(
        tmp.path(),
        &["lint", "closed-nonempty", gains, "--format", "json"],
    );
    assert!(
        env["result"]["data"]["findings"]
            .as_array()
            .is_some_and(|f| f.len() == 1),
        "{env}"
    );
}

/// A two-year ledger for `split` and `merge` (#2633).
const TWO_YEARS: &str = "\
option \"operating_currency\" \"USD\"

2023-01-01 open Assets:Bank
2023-01-01 open Expenses:Food

2023-05-01 * \"Lunch\"
  Expenses:Food  10 USD
  Assets:Bank

2024-05-01 * \"Lunch\"
  Expenses:Food  11 USD
  Assets:Bank
";

/// Every file under `dir`, with its bytes, `.rledger-backup` included.
fn tree(dir: &std::path::Path) -> Vec<(PathBuf, Vec<u8>)> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).unwrap() {
            let p = e.unwrap().path();
            let meta = std::fs::symlink_metadata(&p).unwrap();
            if meta.is_dir() {
                stack.push(p);
            } else if meta.is_file() {
                out.push((p.clone(), std::fs::read(&p).unwrap()));
            } else {
                out.push((p.clone(), Vec::new()));
            }
        }
    }
    out.sort();
    out
}

/// The paths in a `result` array, as strings.
fn path_list(value: &Value) -> Vec<String> {
    value
        .as_array()
        .unwrap_or_else(|| panic!("not an array: {value}"))
        .iter()
        .map(|p| p.as_str().expect("a path").to_string())
        .collect()
}

/// #2633: `split` and `merge` rewrite and remove ledger files, so without
/// `--yes` or `--dry-run` they refuse, saying how to proceed, and touch
/// nothing. `--no-input` is not a yes.
#[test]
fn split_and_merge_need_yes_or_dry_run() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "ledger.beancount", TWO_YEARS);
    let file = file.to_str().unwrap();
    let before = tree(tmp.path());
    for args in [
        vec!["split", file, "--by", "year"],
        vec!["split", file, "--by", "year", "--no-input"],
        vec!["split", file, "--by", "year", "--yes=false"],
        vec!["merge", file],
    ] {
        let (code, env, stderr) = run_in(tmp.path(), &args);
        assert!(stderr.is_empty(), "{args:?}: {stderr}");
        assert_eq!(code, 2, "{args:?}: {env}");
        assert_eq!(
            env["error"]["code"], "CONFIRMATION_REQUIRED",
            "{args:?}: {env}"
        );
        let fix = env["fix"]
            .as_str()
            .unwrap_or_else(|| panic!("no advice: {env}"));
        assert!(fix.contains("--dry-run") && fix.contains("--yes"), "{env}");
    }
    assert_eq!(tree(tmp.path()), before, "a refused run wrote something");
}

/// `--dry-run` (and `-n`) returns the plan and the equivalence check's
/// verdict, and writes nothing at all: no period files, no backup.
#[test]
fn split_dry_run_returns_the_plan_and_writes_nothing() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "ledger.beancount", TWO_YEARS);
    let canonical = file.canonicalize().unwrap();
    let file = file.to_str().unwrap();
    let before = tree(tmp.path());
    for dry in ["--dry-run", "-n"] {
        // The switch before the file: it must not take the file as a value.
        let (code, env, stderr) = run_in(tmp.path(), &["split", "--by", "year", dry, file]);
        assert!(stderr.is_empty(), "{stderr}");
        assert_eq!(code, 0, "{dry}: {env}");
        let result = &env["result"];
        assert_eq!(result["dry_run"], true, "{env}");
        assert_eq!(result["plan"]["operation"], "split", "{env}");
        assert_eq!(result["plan"]["by"], "year", "{env}");
        let steps = result["plan"]["steps"].as_array().expect("steps");
        let dir = canonical.parent().unwrap().join("ledger");
        let expected = [
            ("create", dir.join("2023.beancount"), Some(3)),
            ("create", dir.join("2024.beancount"), Some(1)),
            ("rewrite", canonical.clone(), None),
        ];
        assert_eq!(steps.len(), expected.len(), "{env}");
        for (step, (action, path, count)) in steps.iter().zip(&expected) {
            assert_eq!(step["action"], *action, "{env}");
            assert_eq!(step["path"].as_str(), path.to_str(), "{env}");
            if let Some(n) = count {
                assert_eq!(step["dated_directives"], *n, "{env}");
            }
        }
        assert_eq!(result["equivalence"]["passed"], true, "{env}");
        assert_eq!(result["equivalence"]["directives"], 4, "{env}");
        assert!(path_list(&result["written"]).is_empty(), "{env}");
        assert_eq!(result["backup_dir"], Value::Null, "{env}");
        assert_eq!(tree(tmp.path()), before, "{dry} wrote something");
    }
}

/// `--yes` writes, and `result` lists every written path, the backup, and,
/// for `merge`, the removed files; the ledger on disk is what was listed.
#[test]
fn yes_writes_and_lists_the_written_paths() {
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(tmp.path(), "ledger.beancount", TWO_YEARS);
    let canonical = file.canonicalize().unwrap();
    let file = file.to_str().unwrap();
    let dir = canonical.parent().unwrap().join("ledger");
    let periods = [dir.join("2023.beancount"), dir.join("2024.beancount")];

    let (code, env, stderr) = run_in(tmp.path(), &["split", file, "--by", "year", "--yes"]);
    assert!(stderr.is_empty(), "{stderr}");
    assert_eq!(code, 0, "{env}");
    let result = &env["result"];
    assert_eq!(result["dry_run"], false, "{env}");
    assert_eq!(result["equivalence"]["passed"], true, "{env}");
    let mut expected: Vec<String> = periods
        .iter()
        .chain(std::iter::once(&canonical))
        .map(|p| p.to_string_lossy().into_owned())
        .collect();
    expected.sort();
    let mut written = path_list(&result["written"]);
    written.sort();
    assert_eq!(written, expected, "{env}");
    for p in &periods {
        assert!(p.is_file(), "{} not written", p.display());
    }
    let backup = result["backup_dir"].as_str().expect("a backup");
    assert!(
        std::path::Path::new(backup).join("manifest.txt").is_file(),
        "{env}"
    );
    // The same text rledger prints is in `stdout`.
    assert!(
        result["stdout"]
            .as_str()
            .is_some_and(|s| s.contains("Done; the ledger was reloaded")),
        "{env}"
    );

    // Merge back: the period files are removed and listed as removed.
    let (code, env, stderr) = run_in(tmp.path(), &["merge", file, "-y"]);
    assert!(stderr.is_empty(), "{stderr}");
    assert_eq!(code, 0, "{env}");
    let result = &env["result"];
    assert_eq!(
        path_list(&result["written"]),
        vec![canonical.to_string_lossy().into_owned()],
        "{env}"
    );
    let mut removed = path_list(&result["removed"]);
    removed.sort();
    let periods: Vec<String> = periods
        .iter()
        .map(|p| p.to_string_lossy().into_owned())
        .collect();
    assert_eq!(removed, periods, "{env}");
    for p in &periods {
        assert!(!std::path::Path::new(p).exists(), "{p} not removed");
    }
    let steps = result["plan"]["steps"].as_array().expect("steps");
    assert!(
        steps[..2]
            .iter()
            .all(|s| s["action"] == "inline" && s["remove"] == true),
        "{env}"
    );
    assert_eq!(
        std::fs::read_to_string(&canonical).unwrap(),
        TWO_YEARS,
        "split then merge must give the original back"
    );
}

/// Each refusal is a coded error, the ledger untouched. The symlink
/// refusals are #2614's (and #2635's for merge).
#[test]
fn each_refusal_maps_to_its_code() {
    let tmp = tempfile::tempdir().unwrap();
    let dir = tmp.path();
    let file = write_fixture(dir, "ledger.beancount", TWO_YEARS);
    let file = file.to_str().unwrap();
    // Moving a relative `document` into `ledger/` points it elsewhere.
    std::fs::write(dir.join("r.pdf"), "%PDF").unwrap();
    let doc = write_fixture(
        dir,
        "doc.beancount",
        &format!("{TWO_YEARS}\n2024-06-01 document Assets:Bank \"r.pdf\"\n"),
    );
    let broken = write_fixture(dir, "broken.beancount", "2024-01-01 open\n");
    let empty = write_fixture(dir, "empty.beancount", "option \"title\" \"x\"\n");
    std::fs::create_dir(dir.join("taken")).unwrap();
    std::fs::write(dir.join("taken/2023.beancount"), "").unwrap();
    let missing_include = write_fixture(dir, "inc.beancount", "include \"gone.beancount\"\n");
    std::fs::write(dir.join("a-file"), "").unwrap();
    let existing_out = write_fixture(dir, "out.beancount", "");
    let parent = write_fixture(dir, "parent.beancount", "include \"child.beancount\"\n");
    write_fixture(dir, "child.beancount", TWO_YEARS);

    let mut cases: Vec<(Vec<String>, &str, i32)> = vec![
        (
            vec![
                "split".into(),
                "nope.beancount".into(),
                "--by".into(),
                "year".into(),
            ],
            "FILE_NOT_FOUND",
            3,
        ),
        (
            vec![
                "split".into(),
                doc.to_str().unwrap().into(),
                "--by".into(),
                "year".into(),
            ],
            "EQUIVALENCE_FAILED",
            1,
        ),
        (
            vec![
                "split".into(),
                broken.to_str().unwrap().into(),
                "--by".into(),
                "year".into(),
            ],
            "PARSE_ERRORS",
            1,
        ),
        (
            vec![
                "split".into(),
                empty.to_str().unwrap().into(),
                "--by".into(),
                "year".into(),
            ],
            "NOTHING_TO_SPLIT",
            1,
        ),
        (
            vec![
                "split".into(),
                file.into(),
                "--by".into(),
                "year".into(),
                "--dir".into(),
                "taken".into(),
            ],
            "TARGET_EXISTS",
            1,
        ),
        (
            vec![
                "split".into(),
                file.into(),
                "--by".into(),
                "year".into(),
                "--dir".into(),
                "a*b".into(),
            ],
            "UNWRITABLE_INCLUDE",
            2,
        ),
        (
            vec![
                "split".into(),
                file.into(),
                "--by".into(),
                "year".into(),
                "--dir".into(),
                "a-file".into(),
            ],
            "NOT_A_DIRECTORY",
            2,
        ),
        (
            vec!["split".into(), file.into(), "--by".into(), "week".into()],
            "INVALID_VALUE",
            2,
        ),
        (vec!["split".into(), file.into()], "MISSING_FLAG", 2),
        (
            vec![
                "split".into(),
                file.into(),
                file.into(),
                "--by".into(),
                "year".into(),
            ],
            "INVALID_ARGS",
            2,
        ),
        (vec!["merge".into(), file.into()], "NOTHING_TO_MERGE", 1),
        (
            vec!["merge".into(), missing_include.to_str().unwrap().into()],
            "INCLUDE_NOT_FOUND",
            3,
        ),
        (
            vec![
                "merge".into(),
                file.into(),
                "-o".into(),
                "x.beancount".into(),
                "--ledger".into(),
                file.into(),
            ],
            "CONFLICTING_FLAGS",
            2,
        ),
        (
            vec![
                "merge".into(),
                parent.to_str().unwrap().into(),
                "-o".into(),
                existing_out.to_str().unwrap().into(),
            ],
            "TARGET_EXISTS",
            1,
        ),
        (
            vec!["merge".into(), file.into(), "--frobnicate".into()],
            "UNKNOWN_FLAG",
            2,
        ),
    ];
    #[cfg(unix)]
    {
        std::fs::create_dir(dir.join("sub")).unwrap();
        std::os::unix::fs::symlink("../ledger.beancount", dir.join("sub/link.beancount")).unwrap();
        for op in ["split", "merge"] {
            let mut args = vec![op.to_string(), "sub/link.beancount".to_string()];
            if op == "split" {
                args.extend(["--by".to_string(), "year".to_string()]);
            }
            cases.push((args, "SYMLINK_ELSEWHERE", 1));
        }
    }

    let before = tree(dir);
    for (args, code, exit) in &cases {
        let mut args: Vec<&str> = args.iter().map(String::as_str).collect();
        // `--dry-run` would hide a refusal that only a write reaches, and
        // `--yes` proves the gate is not what refused.
        args.push("--yes");
        let (got, env, stderr) = run_in(dir, &args);
        assert!(stderr.is_empty(), "{args:?} wrote to stderr: {stderr}");
        assert_eq!(env["ok"], false, "{args:?}: {env}");
        assert_eq!(env["error"]["code"], *code, "{args:?}: {env}");
        assert_eq!(got, *exit, "{args:?}: {env}");
    }
    assert_eq!(tree(dir), before, "a refused run changed the directory");

    // The equivalence refusal carries the plan and the verdict, and names
    // the difference.
    let (_, env, _) = run_in(
        dir,
        &["split", doc.to_str().unwrap(), "--by", "year", "--dry-run"],
    );
    assert_eq!(env["error"]["code"], "EQUIVALENCE_FAILED", "{env}");
    let data = &env["data"];
    assert_eq!(data["equivalence"]["passed"], false, "{env}");
    assert!(
        data["equivalence"]["reason"]
            .as_str()
            .is_some_and(|r| r.contains("document path")),
        "{env}"
    );
    assert_eq!(data["plan"]["operation"], "split", "{env}");
    assert!(
        env["error"]["message"]
            .as_str()
            .is_some_and(|m| m.contains("document path")),
        "{env}"
    );
}

/// `split`/`merge` through ag-rledger print what rledger prints: `stdout`
/// is rledger's stdout, for a dry run and a write alike.
#[test]
fn split_and_merge_answer_as_rledger_does() {
    let ag = tempfile::tempdir().unwrap();
    let native = tempfile::tempdir().unwrap();
    for dir in [ag.path(), native.path()] {
        write_fixture(dir, "ledger.beancount", TWO_YEARS);
    }
    for (ag_args, rledger_args) in [
        (
            vec!["split", "ledger.beancount", "--by", "month", "--dry-run"],
            vec!["split", "ledger.beancount", "--by", "month", "--dry-run"],
        ),
        (
            vec!["split", "ledger.beancount", "--by", "year", "--yes"],
            vec!["split", "ledger.beancount", "--by", "year"],
        ),
        (
            vec![
                "merge",
                "ledger.beancount",
                "--keep-included",
                "-o",
                "all.beancount",
                "--yes",
            ],
            vec![
                "merge",
                "ledger.beancount",
                "--keep-included",
                "-o",
                "all.beancount",
            ],
        ),
    ] {
        let (code, env, stderr) = run_in(ag.path(), &ag_args);
        assert!(stderr.is_empty(), "{stderr}");
        let (native_code, printed) = rledger_stdout(native.path(), &rledger_args);
        assert_eq!(code, native_code, "{ag_args:?}: {env}");
        // The backup directory is named after the second it was made in.
        let stamp = |s: &str| {
            s.lines()
                .map(|l| {
                    if l.starts_with("Backup of the original files:") {
                        "Backup of the original files: <dir>"
                    } else {
                        l
                    }
                })
                .collect::<Vec<_>>()
                .join("\n")
        };
        assert_eq!(
            env["result"]["stdout"].as_str().map(stamp),
            Some(stamp(&printed)),
            "{ag_args:?}: {env}"
        );
    }
}

/// #2633: `split` and `merge` are offered, so the drift guard above now
/// requires them; listing either as unsupported again fails here.
#[test]
fn split_and_merge_are_offered_not_unsupported() {
    let (_, root) = run(&[]);
    let names = |key: &str, field: &str| -> Vec<String> {
        root["result"][key]
            .as_array()
            .unwrap_or_else(|| panic!("no {key}: {root}"))
            .iter()
            .filter_map(|c| c[field].as_str().map(str::to_string))
            .collect()
    };
    let commands = names("commands", "name");
    let unsupported = names("unsupported_commands", "command");
    for name in ["split", "merge"] {
        assert!(commands.iter().any(|c| c == name), "{name} not offered");
        assert!(
            !unsupported.iter().any(|c| c == name),
            "{name} is still listed as unsupported"
        );
    }
}

/// Review of #2633: agcli turns a value flag given nothing (`-o` last,
/// `--dir --yes`) into the value `"true"`, which was taken as a path and
/// written to. It is refused, and nothing is written; a path typed as
/// `true` is still a path.
#[test]
fn a_path_flag_without_a_value_is_refused() {
    let tmp = tempfile::tempdir().unwrap();
    let dir = tmp.path();
    let file = write_fixture(dir, "ledger.beancount", TWO_YEARS);
    let file = file.to_str().unwrap();
    let parent = write_fixture(dir, "parent.beancount", "include \"child.beancount\"\n");
    write_fixture(dir, "child.beancount", TWO_YEARS);
    let parent = parent.to_str().unwrap();
    let before = tree(dir);
    for args in [
        vec!["merge", parent, "--yes", "-o"],
        vec!["merge", parent, "--output", "--yes"],
        vec!["split", file, "--by", "year", "--yes", "--dir"],
        vec!["split", file, "--by", "year", "--dir", "--yes"],
        vec!["split", file, "--by", "year", "--ledger", "--yes"],
        // Another flag's `=true`, or a positional named `true`, is not
        // this flag's value (review round 2).
        vec!["merge", parent, "--yes=true", "-o"],
        vec!["split", file, "--by", "year", "--dry-run=true", "--dir"],
        vec!["merge", "true", "-o", "--yes"],
    ] {
        let (code, env, stderr) = run_in(dir, &args);
        assert!(stderr.is_empty(), "{stderr}");
        assert_eq!(env["error"]["code"], "MISSING_VALUE", "{args:?}: {env}");
        assert_eq!(code, 2, "{args:?}: {env}");
    }
    assert_eq!(tree(dir), before, "a refused run wrote something");

    // Typed, `true` is a directory name like any other.
    let (code, env, _) = run_in(dir, &["split", file, "--by", "year", "--dir", "true", "-n"]);
    assert_eq!(code, 0, "{env}");
    let base = std::path::Path::new(file).canonicalize().unwrap();
    let expected = base.parent().unwrap().join("true").join("2023.beancount");
    assert_eq!(
        env["result"]["plan"]["steps"][0]["path"].as_str(),
        expected.to_str(),
        "{env}"
    );
    let (code, env, _) = run_in(dir, &["split", file, "--by", "year", "--dir=true", "-n"]);
    assert_eq!(code, 0, "{env}");
}

/// `--keep-included=false` does not keep the inlined files, as agcli reads
/// a switch's negation.
#[test]
fn keep_included_false_is_off() {
    let tmp = tempfile::tempdir().unwrap();
    let parent = write_fixture(
        tmp.path(),
        "parent.beancount",
        "include \"child.beancount\"\n",
    );
    write_fixture(tmp.path(), "child.beancount", TWO_YEARS);
    let parent = parent.to_str().unwrap();
    for (flag, remove) in [("--keep-included", false), ("--keep-included=false", true)] {
        let (code, env, _) = run_in(tmp.path(), &["merge", parent, flag, "--dry-run"]);
        assert_eq!(code, 0, "{env}");
        assert_eq!(
            env["result"]["plan"]["steps"][0]["remove"], remove,
            "{flag}: {env}"
        );
    }
}

/// More refusals, each with its code: a FILE outside the `--ledger` root,
/// no FILE and no default, and a file that is not UTF-8.
#[test]
fn more_refusals_map_to_their_codes() {
    let tmp = tempfile::tempdir().unwrap();
    let dir = tmp.path();
    let file = write_fixture(dir, "ledger.beancount", TWO_YEARS);
    let other = write_fixture(dir, "other.beancount", TWO_YEARS);
    let latin1 = dir.join("latin1.beancount");
    std::fs::write(
        &latin1,
        b"2024-01-01 open Assets:Cash\n2024-01-02 * \"bad \xff\"\n  Assets:Cash 1 USD\n  Assets:Cash -1 USD\n",
    )
    .unwrap();
    let before = tree(dir);
    for (args, code, exit) in [
        (
            vec![
                "split",
                file.to_str().unwrap(),
                "--by",
                "year",
                "--ledger",
                other.to_str().unwrap(),
            ],
            "NOT_IN_LEDGER",
            2,
        ),
        (vec!["merge", "--yes"], "MISSING_FILE", 2),
        (
            vec!["split", latin1.to_str().unwrap(), "--by", "year"],
            "NOT_UTF8",
            1,
        ),
    ] {
        let mut args = args.clone();
        args.push("--yes");
        let (got, env, stderr) = run_in(dir, &args);
        assert!(stderr.is_empty(), "{stderr}");
        assert_eq!(env["error"]["code"], code, "{args:?}: {env}");
        assert_eq!(got, exit, "{args:?}: {env}");
    }
    assert_eq!(tree(dir), before);
}
/// #2714: the envelope escapes DEL, C1, bidi controls and line separators
/// from the ledger as `\uXXXX`, so reading it raw is safe, and the values
/// decode unchanged.
#[test]
fn envelope_escapes_display_unsafe_characters_and_keeps_the_values() {
    // Somewhere under `value`, the string `text`.
    fn holds(value: &Value, text: &str) -> bool {
        match value {
            Value::String(s) => s == text,
            Value::Array(items) => items.iter().any(|v| holds(v, text)),
            Value::Object(map) => map.values().any(|v| holds(v, text)),
            _ => false,
        }
    }
    let narration = "a\u{1b}[2Jb\u{7f}c\u{9b}d\u{202e}e\u{2028}f";
    let tmp = tempfile::tempdir().unwrap();
    let file = write_fixture(
        tmp.path(),
        "ledger.beancount",
        &format!(
            "2024-01-01 open Assets:Cash\n\
             2024-01-01 open Equity:Opening\n\
             2024-01-02 * \"{narration}\"\n  \
               Assets:Cash  1 USD\n  \
               Equity:Opening\n"
        ),
    );
    let output = Command::new(ag_rledger())
        .args([
            "query",
            file.to_str().unwrap(),
            "SELECT narration",
            "--format",
            "json",
        ])
        .output()
        .expect("spawn ag-rledger");
    let stdout = String::from_utf8(output.stdout).expect("utf-8 envelope");
    for raw in ['\u{1b}', '\u{7f}', '\u{9b}', '\u{202e}', '\u{2028}'] {
        assert!(
            !stdout.contains(raw),
            "{raw:?} raw in the envelope: {stdout:?}"
        );
    }
    assert!(stdout.contains("\\u009b"), "{stdout}");
    let envelope: Value = serde_json::from_str(stdout.trim()).expect("envelope is JSON");
    // Somewhere in the rows, the narration as it is in the ledger.
    assert!(
        holds(&envelope["result"]["data"]["rows"], narration),
        "the narration decodes unchanged: {envelope}"
    );
}
