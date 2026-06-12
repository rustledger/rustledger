//! Integration tests for the agent-native `ag-rledger` binary (#1291).
//!
//! These resolve the binary via `CARGO_BIN_EXE_ag-rledger` (set by cargo
//! for any `[[bin]]` target) and assert on the agcli JSON envelope and the
//! typed process exit code. They mirror the `common` harness conventions
//! used by the `rledger` CLI tests, but the binary is always present under
//! `cargo test` so no skip macro is needed.

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

#[test]
fn root_command_tree_is_self_documenting() {
    let (code, env) = run(&[]);
    assert_eq!(code, 0);
    assert_eq!(env["ok"], Value::Bool(true));
    // The root envelope advertises the reserved agent flags and the
    // command tree, plus our compatibility root field.
    assert_eq!(env["result"]["compatibility"]["engine"], "rustledger");
}
