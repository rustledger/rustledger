//! End-to-end coverage for the host's WASM plugin time budget (#2484):
//! `[plugins] max_time_secs` in the config file and the global
//! `--plugin-max-time-secs` flag, which overrides it.
//!
//! The ledger runs a plugin that burns about three seconds of fuel
//! (`3 * FUEL_PER_SECOND`, measured at 3-4G), so it fits the default
//! 30-second budget and traps on a 1-second one whatever the host's speed. Its
//! output never decodes, so even a run within budget ends in a plugin
//! error; what differs is whether that error is the fuel trap.
#![cfg(feature = "python-plugin-wasm")]

mod common;

use std::path::Path;
use std::process::Command;

use rustledger_plugin::sandbox::FUEL_PER_SECOND;

/// Write `burn.wasm`, a config dir, and a ledger that loads the plugin.
/// Returns the ledger path.
fn setup(dir: &Path, config: Option<&str>) -> std::path::PathBuf {
    let iterations = 3 * FUEL_PER_SECOND / 6;
    let wat = format!(
        r#"(module
            (memory (export "memory") 1)
            (func (export "alloc") (param i32) (result i32) i32.const 0)
            (func (export "__rustledger_abi_version") (result i32) i32.const 1)
            (func (export "process") (param i32 i32) (result i64) (local $n i32)
                (local.set $n (i32.const {iterations}))
                (loop
                    (local.set $n (i32.sub (local.get $n) (i32.const 1)))
                    (br_if 0 (local.get $n)))
                i64.const 0))"#
    );
    let wasm = dir.join("burn.wasm");
    std::fs::write(&wasm, wat::parse_str(wat).expect("WAT parses")).expect("write wasm");
    if let Some(config) = config {
        std::fs::write(dir.join("config.toml"), config).expect("write config");
    }
    let ledger = dir.join("ledger.beancount");
    std::fs::write(
        &ledger,
        format!(
            "plugin \"{}\"\n\n2024-01-01 open Assets:Bank USD\n",
            wasm.display()
        ),
    )
    .expect("write ledger");
    ledger
}

/// Run `rledger <args> <ledger>` with `dir` as the only config source and
/// return stdout + stderr.
fn run(bin: &Path, dir: &Path, args: &[&str], ledger: &Path) -> String {
    let output = Command::new(bin)
        .args(args)
        .arg(ledger)
        // `dir` is the user config dir and the cwd (so no stray project
        // config is found above it); PROGRAMDATA covers the Windows system
        // config path.
        .current_dir(dir)
        .env("RLEDGER_CONFIG_DIR", dir)
        .env("PROGRAMDATA", dir)
        .output()
        .expect("run rledger");
    format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

const TRAP: &str = "all fuel consumed";

#[test]
fn default_budget_covers_the_burn() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let ledger = setup(dir.path(), None);
    let out = run(&bin, dir.path(), &["check"], &ledger);
    assert!(
        out.contains("burn.wasm"),
        "the plugin should run and fail to decode:\n{out}"
    );
    assert!(!out.contains(TRAP), "{out}");
}

#[test]
fn flag_sets_the_budget() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let ledger = setup(dir.path(), None);
    let out = run(
        &bin,
        dir.path(),
        &["--plugin-max-time-secs", "1", "check"],
        &ledger,
    );
    assert!(out.contains(TRAP), "{out}");
}

#[test]
fn config_file_sets_the_budget() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let ledger = setup(dir.path(), Some("[plugins]\nmax_time_secs = 1\n"));
    let out = run(&bin, dir.path(), &["check"], &ledger);
    assert!(out.contains(TRAP), "{out}");
}

#[test]
fn flag_overrides_the_config_file() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let ledger = setup(dir.path(), Some("[plugins]\nmax_time_secs = 1\n"));
    let out = run(
        &bin,
        dir.path(),
        &["check", "--plugin-max-time-secs", "60"],
        &ledger,
    );
    assert!(!out.contains(TRAP), "{out}");
}

#[test]
fn budget_reaches_query_too() {
    // Every command that loads a ledger with plugins reads the setting,
    // not only `check`.
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let ledger = setup(dir.path(), Some("[plugins]\nmax_time_secs = 1\n"));
    let output = Command::new(&bin)
        .args(["query"])
        .arg(&ledger)
        .arg("SELECT account")
        .current_dir(dir.path())
        .env("RLEDGER_CONFIG_DIR", dir.path())
        .env("PROGRAMDATA", dir.path())
        .output()
        .expect("run rledger query");
    let out = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(out.contains(TRAP), "{out}");
}

#[test]
fn zero_is_refused_not_read_as_one_second() {
    // The sandbox floors a budget at one second, so zero would quietly mean
    // "one second" where a user might expect "no limit".
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let ledger = setup(dir.path(), None);
    let out = run(
        &bin,
        dir.path(),
        &["--plugin-max-time-secs", "0", "check"],
        &ledger,
    );
    assert!(out.contains("--plugin-max-time-secs"), "{out}");
    assert!(!out.contains(TRAP), "the plugin must not run:\n{out}");

    let dir = tempfile::tempdir().unwrap();
    let ledger = setup(dir.path(), Some("[plugins]\nmax_time_secs = 0\n"));
    let out = run(&bin, dir.path(), &["check"], &ledger);
    assert!(out.contains("nonzero"), "{out}");
    assert!(!out.contains(TRAP), "the plugin must not run:\n{out}");
}
