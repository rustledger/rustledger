//! Build the stub WASM directive-plugin fixture at
//! `tests/fixtures/sample_stub/` into a `.wasm` file that the
//! integration test in `tests/wasm_plugin_e2e.rs` loads.
//!
//! Sibling to `crates/rustledger-importer/build.rs` — same pattern,
//! same four guards (env-scrub, stale-sentinel, rerun-if-changed for
//! path-deps, panic-not-skip on CI). Documented at length there; this
//! build.rs is intentionally a near-copy so the two stay in lockstep.
//!
//! # Skip-if-wasm32-unavailable (local dev only)
//!
//! On dev machines without `wasm32-unknown-unknown` installed, the
//! cargo invocation fails. We print a `cargo:warning=` and leave the
//! sentinel unwritten — the e2e test detects this and skips itself
//! locally but panics under `CI=true`. CI installs the target.

use std::path::PathBuf;
use std::process::Command;

fn main() {
    // The e2e test that consumes the sentinel is `#[cfg(feature =
    // "wasm-runtime")]`, so under `--no-default-features` (or any
    // feature selection without `wasm-runtime`) the fixture can't be
    // used. Skip the nested cargo build entirely in that case —
    // native-only consumers shouldn't pay for a wasm32 compile or
    // see a `cargo:warning=` for a missing target they don't need.
    //
    // Cargo sets `CARGO_FEATURE_<NAME_UPPERCASED>` env vars for every
    // active feature of the package being built.
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_WASM_RUNTIME");
    if std::env::var_os("CARGO_FEATURE_WASM_RUNTIME").is_none() {
        return;
    }

    let fixture_dir = PathBuf::from("tests/fixtures/sample_stub");
    println!(
        "cargo:rerun-if-changed={}/src/lib.rs",
        fixture_dir.display()
    );
    println!(
        "cargo:rerun-if-changed={}/Cargo.toml",
        fixture_dir.display()
    );
    println!(
        "cargo:rerun-if-changed={}/Cargo.lock",
        fixture_dir.display()
    );
    // Path-dep: the fixture's wire format must stay in lockstep with
    // the plugin-types crate. A new field on `PluginInput` or a macro
    // change should force a fixture rebuild so the e2e test exercises
    // the new ABI.
    println!("cargo:rerun-if-changed=../rustledger-plugin-types/src");
    println!("cargo:rerun-if-changed=../rustledger-plugin-types/Cargo.toml");
    println!("cargo:rerun-if-changed=build.rs");

    let out_dir = PathBuf::from(std::env::var_os("OUT_DIR").expect("OUT_DIR set by cargo"));
    let sentinel = out_dir.join("sample_stub.wasm");

    // Stale-sentinel guard: remove any prior copy before invoking
    // cargo. If the build fails for any reason — wasm32 target
    // missing, ABI break, syntax error — the sentinel stays unwritten
    // and the test detects it.
    if sentinel.exists() {
        std::fs::remove_file(&sentinel).expect("remove stale sample_stub.wasm sentinel");
    }

    let target_dir = out_dir.join("sample_stub_target");

    // Scrub env vars that don't make sense for the inner wasm32 build:
    //
    // - `RUSTFLAGS` / `CARGO_ENCODED_RUSTFLAGS`: under `cargo-llvm-cov`
    //   the outer build sets `-C instrument-coverage`, which has no
    //   wasm32 runtime support and aborts the fixture compile with a
    //   linker error.
    // - `CARGO_BUILD_TARGET` / `CARGO_BUILD_RUSTFLAGS`: same shape,
    //   same risk.
    //
    // Don't scrub `CARGO_TARGET_DIR` — `--target-dir` on the command
    // line takes precedence anyway, and clearing it would defeat
    // caching.
    let status = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .env_remove("CARGO_BUILD_RUSTFLAGS")
        .env_remove("CARGO_BUILD_TARGET")
        .args([
            "build",
            "--release",
            "--target",
            "wasm32-unknown-unknown",
            "--manifest-path",
        ])
        .arg(fixture_dir.join("Cargo.toml"))
        .arg("--target-dir")
        .arg(&target_dir)
        .status();

    match status {
        Ok(s) if s.success() => {
            let built = target_dir
                .join("wasm32-unknown-unknown")
                .join("release")
                .join("sample_stub_wasm_plugin.wasm");
            if !built.exists() {
                println!(
                    "cargo:warning=expected wasm output at {} but it's missing; e2e test will skip (local) or panic (CI)",
                    built.display()
                );
                return;
            }
            std::fs::copy(&built, &sentinel).expect("copy stub wasm to OUT_DIR");
        }
        Ok(s) => {
            println!(
                "cargo:warning=cargo build for sample_stub plugin fixture exited {s}; e2e test will skip (local) or panic (CI)"
            );
        }
        Err(e) => {
            println!(
                "cargo:warning=failed to invoke cargo for sample_stub plugin fixture ({e}); e2e test will skip (local) or panic (CI)"
            );
        }
    }
}
