//! End-to-end coverage for the `RLEDGER_CONFIG_DIR` env-var wiring.
//!
//! The public `user_config_path()` wrapper reads `RLEDGER_CONFIG_DIR` and its
//! pure `*_with_override` helper does the resolution. The unit tests exercise
//! the helper directly, so they would still pass if the env-var name were
//! typo'd or dropped in the public wrapper. This subprocess test pins the real
//! wiring: set the var, and the config in that directory must actually load.

mod common;

use std::process::Command;

#[test]
fn config_dir_env_var_loads_config_from_that_directory() {
    let bin = require_rledger!();

    // A config.toml with a distinctive marker in a directory that is neither
    // the platform default nor the cwd — it can only be found via the env var.
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        dir.path().join("config.toml"),
        "[default]\nfile = \"ZZ_ENV_OVERRIDE_MARKER.beancount\"\n",
    )
    .expect("write config");

    let output = Command::new(bin)
        .args(["config", "show", "--raw"])
        // cwd holds no `.rledger.toml`, so the marker can only come from the
        // RLEDGER_CONFIG_DIR user config. PROGRAMDATA shields the Windows
        // system-config path from ambient state.
        .current_dir(dir.path())
        .env("PROGRAMDATA", dir.path())
        .env("RLEDGER_CONFIG_DIR", dir.path())
        .output()
        .expect("run rledger config show");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.contains("ZZ_ENV_OVERRIDE_MARKER"),
        "config.toml under RLEDGER_CONFIG_DIR must load via the public wrapper.\n\
         stdout: {stdout}\nstderr: {stderr}"
    );
}

#[test]
fn config_dir_env_var_loads_importers_from_that_directory() {
    let bin = require_rledger!();

    let config_dir = tempfile::tempdir().expect("config tempdir");
    std::fs::write(
        config_dir.path().join("importers.toml"),
        r#"
[[importers]]
name = "envbank"
account = "Assets:Bank:Env"
currency = "USD"
date_column = "Date"
narration_column = "Description"
amount_column = "Amount"
default_expense = "Expenses:Unknown"
"#,
    )
    .expect("write importers config");

    let work_dir = tempfile::tempdir().expect("work tempdir");
    let csv_path = work_dir.path().join("statement.csv");
    std::fs::write(
        &csv_path,
        "Date,Description,Amount\n2024-01-15,COFFEE,-4.25\n",
    )
    .expect("write statement");

    let output = Command::new(bin)
        .args([
            "extract",
            csv_path.to_str().expect("utf-8 path"),
            "--importer",
            "envbank",
        ])
        // cwd holds no importers.toml, so the importer can only come from
        // RLEDGER_CONFIG_DIR/importers.toml.
        .current_dir(work_dir.path())
        .env("PROGRAMDATA", work_dir.path())
        .env("RLEDGER_CONFIG_DIR", config_dir.path())
        .output()
        .expect("run rledger extract");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "extract should succeed with importers.toml under RLEDGER_CONFIG_DIR.\n\
         stdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("Assets:Bank:Env"),
        "configured importer account should appear in extracted output.\n\
         stdout: {stdout}\nstderr: {stderr}"
    );
}
