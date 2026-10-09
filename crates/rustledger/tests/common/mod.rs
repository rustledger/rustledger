//! Shared test utilities for CLI integration tests.

#![allow(dead_code)]

use std::path::PathBuf;

/// Get the workspace root directory.
pub fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("CARGO_MANIFEST_DIR should have a parent (crates/)")
        .parent()
        .expect("crates/ should have a parent (workspace root)")
        .to_path_buf()
}

/// Get the test fixtures directory.
pub fn test_fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// Find the rledger binary, checking `CARGO_BIN_EXE`, release, and debug paths.
pub fn rledger_binary() -> Option<PathBuf> {
    // Use CARGO_BIN_EXE_rledger if available (set by cargo test)
    if let Ok(path) = std::env::var("CARGO_BIN_EXE_rledger") {
        return Some(PathBuf::from(path));
    }

    // Check target/release first (for --release builds)
    let release_path = project_root().join("target/release/rledger");
    if release_path.exists() {
        return Some(release_path);
    }

    // Fall back to target/debug
    let debug_path = project_root().join("target/debug/rledger");
    if debug_path.exists() {
        return Some(debug_path);
    }

    // Binary not found (Nix builds, not yet built, etc.)
    None
}

/// Skip tests when rledger binary is not available.
///
/// Requires `mod common;` to be declared in the test file.
#[macro_export]
macro_rules! require_rledger {
    () => {
        match common::rledger_binary() {
            Some(path) => path,
            None => {
                eprintln!("Skipping: rledger binary not found");
                return;
            }
        }
    };
}

/// Printed when the `CPython` WASI runtime is unavailable; the
/// `python-gated-cargo-tests` CI job fails on it.
pub const PYTHON_WASI_SKIP_MARKER: &str = "Skipping: CPython WASI runtime unavailable";

/// Whether `rledger` can run Python plugins here: the `CPython` WASI
/// runtime is downloaded and compiled on first use, which needs the
/// network (the offline nix build sandbox has none).
///
/// The first call runs one passthrough plugin, so the one-time download
/// and compile happen once per test binary, not in every parallel test
/// at once. When the runtime is unavailable this prints
/// [`PYTHON_WASI_SKIP_MARKER`] and returns false, unless
/// `RLEDGER_REQUIRE_PYTHON_WASI` is set (as in CI), which panics instead.
pub fn python_wasi_ready(bin: &std::path::Path) -> bool {
    static READY: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let ready = *READY.get_or_init(|| {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir.path().join("warmup.py"),
            "__plugins__ = ['warmup']\ndef warmup(entries, options_map):\n    return entries, []\n",
        )
        .expect("write warmup plugin");
        let ledger = dir.path().join("warmup.beancount");
        std::fs::write(
            &ledger,
            "plugin \"warmup.py\"\n2024-01-01 open Assets:Bank USD\n",
        )
        .expect("write warmup ledger");
        let out = std::process::Command::new(bin)
            .arg("check")
            .arg(&ledger)
            .current_dir(dir.path())
            .env("RLEDGER_CONFIG_DIR", dir.path())
            .output()
            .expect("run rledger");
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        if text.contains("Python runtime unavailable") {
            assert!(
                std::env::var_os("RLEDGER_REQUIRE_PYTHON_WASI").is_none(),
                "RLEDGER_REQUIRE_PYTHON_WASI is set but the CPython WASI runtime is \
                 unavailable:\n{text}"
            );
            return false;
        }
        true
    });
    if !ready {
        eprintln!("{PYTHON_WASI_SKIP_MARKER}");
    }
    ready
}
