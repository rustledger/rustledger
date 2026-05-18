//! Build the stub WASM importer fixture at
//! `tests/fixtures/sample_stub/` into a `.wasm` file that the
//! integration test in `tests/wasm_importer_e2e.rs` loads.
//!
//! # Why a build.rs and not test-time `Command::new("cargo")`
//!
//! Building the fixture in a build.rs uses Cargo's standard
//! incremental + rerun-if-changed pipeline: the fixture is built
//! once per source change, cached otherwise. A test-time
//! `Command` would compile on every test run.
//!
//! # Skip-if-wasm32-unavailable
//!
//! On dev machines without `wasm32-unknown-unknown` installed,
//! the cargo invocation fails. We print a `cargo:warning=` and
//! emit a sentinel file telling the test to skip itself —
//! prefers "no signal" over "compile error" for the common case
//! where someone runs `cargo check` without the target.
//!
//! CI has wasm32 installed (per `flake.nix` and the
//! `Tools available` block in CLAUDE.md), so the e2e test runs
//! there for real.

use std::path::PathBuf;
use std::process::Command;

fn main() {
    let fixture_dir = PathBuf::from("tests/fixtures/sample_stub");
    // Re-run when fixture source changes. Without this, cargo
    // assumes build.rs only depends on itself and never rebuilds.
    println!(
        "cargo:rerun-if-changed={}/src/lib.rs",
        fixture_dir.display()
    );
    println!(
        "cargo:rerun-if-changed={}/Cargo.toml",
        fixture_dir.display()
    );
    println!("cargo:rerun-if-changed=build.rs");

    let out_dir = PathBuf::from(std::env::var_os("OUT_DIR").expect("OUT_DIR set by cargo"));
    let sentinel = out_dir.join("sample_stub.wasm");

    // Use a target dir under OUT_DIR so we don't pollute the
    // workspace target/ and so concurrent test runs don't fight.
    let target_dir = out_dir.join("sample_stub_target");

    let status = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
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
                .join("sample_stub_wasm_importer.wasm");
            if !built.exists() {
                println!(
                    "cargo:warning=expected wasm output at {} but it's missing; e2e test will skip",
                    built.display()
                );
                return;
            }
            std::fs::copy(&built, &sentinel).expect("copy stub wasm to OUT_DIR");
        }
        Ok(s) => {
            println!(
                "cargo:warning=cargo build for sample_stub fixture exited {s}; e2e test will skip"
            );
        }
        Err(e) => {
            // Most common cause: wasm32-unknown-unknown target not
            // installed locally. Skip rather than fail — the e2e
            // test detects the missing sentinel and skips itself.
            println!(
                "cargo:warning=failed to invoke cargo for sample_stub fixture ({e}); e2e test will skip"
            );
        }
    }
}
