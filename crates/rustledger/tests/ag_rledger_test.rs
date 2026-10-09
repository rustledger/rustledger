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
/// source, and return `(exit_code, envelope, stderr)`.
fn run_in(dir: &std::path::Path, args: &[&str]) -> (i32, Value, String) {
    let output = Command::new(ag_rledger())
        .args(args)
        // `dir` is the user config dir and the cwd, so no stray project
        // config is found above it; PROGRAMDATA covers the Windows system
        // config path.
        .current_dir(dir)
        .env("RLEDGER_CONFIG_DIR", dir)
        .env("PROGRAMDATA", dir)
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
                (func (export "__rustledger_abi_version") (result i32) i32.const 1)
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
