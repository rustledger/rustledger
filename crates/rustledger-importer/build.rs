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
//! # Skip-if-wasm32-unavailable (local dev only)
//!
//! On dev machines without `wasm32-unknown-unknown` installed,
//! the cargo invocation fails. We print a `cargo:warning=` and
//! leave the sentinel unwritten — the e2e test detects this and
//! skips itself. Prefers "no signal" over "compile error" for the
//! common case where someone runs `cargo check` without the target.
//!
//! **CI must run the e2e test for real.** The `ci` matrix in
//! `.github/workflows/ci.yml` installs `wasm32-unknown-unknown`; the
//! e2e test detects `CI=true` and panics rather than skipping if the
//! sentinel is missing (so green CI can't lie about coverage).
//!
//! # Stale-sentinel guard
//!
//! We delete the sentinel **before** invoking cargo. If the fixture
//! source or the path-dep ABI changes and the new build fails or
//! produces no artifact, the test sees a missing sentinel and either
//! skips (local) or panics (CI). Without this guard, a stale
//! `sample_stub.wasm` from a previous successful build could be
//! loaded against an ABI it no longer matches.

use std::path::PathBuf;
use std::process::Command;

fn main() {
    let fixture_dir = PathBuf::from("tests/fixtures/sample_stub");
    // Re-run when any of these change. Without explicit
    // `rerun-if-changed`, cargo would otherwise watch only build.rs
    // itself, missing both fixture source changes AND the path-dep
    // ABI (rustledger-plugin-types) that the fixture is built against.
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
    // these. A new field on `ImporterOutput` or a macro change should
    // force a fixture rebuild so the e2e test exercises the new ABI.
    println!("cargo:rerun-if-changed=../rustledger-plugin-types/src");
    println!("cargo:rerun-if-changed=../rustledger-plugin-types/Cargo.toml");
    println!("cargo:rerun-if-changed=build.rs");

    let out_dir = PathBuf::from(std::env::var_os("OUT_DIR").expect("OUT_DIR set by cargo"));
    let sentinel = out_dir.join("sample_stub.wasm");

    // Stale-sentinel guard: remove any prior copy before invoking
    // cargo. If the build below fails for any reason — wasm32 target
    // missing, ABI break, syntax error — the sentinel stays unwritten
    // and the test detects it. Without this, a previous success
    // would mask a current regression.
    if sentinel.exists() {
        std::fs::remove_file(&sentinel).expect("remove stale sample_stub.wasm sentinel");
    }

    // Use a target dir under OUT_DIR so we don't pollute the
    // workspace target/ and so concurrent test runs don't fight.
    let target_dir = out_dir.join("sample_stub_target");

    // Scrub env vars that don't make sense for the inner wasm32 build:
    //
    // - `RUSTFLAGS` / `CARGO_ENCODED_RUSTFLAGS`: under `cargo-llvm-cov`
    //   the outer build sets `-C instrument-coverage`, which has no
    //   wasm32 runtime support and aborts the fixture compile with a
    //   linker error. Scrubbing also prevents the host's `-Dwarnings`
    //   from breaking the fixture on a future plugin-types deprecation.
    // - `CARGO_BUILD_TARGET`: would override `--target` (rare, but
    //   propagates from `cargo-llvm-cov` and from some Nix shells).
    // - `CARGO_BUILD_RUSTFLAGS`: same shape, same risk.
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
                .join("sample_stub_wasm_importer.wasm");
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
            // Non-zero exit. Common cause locally: wasm32 target not
            // installed. Other causes (compile error, ABI break) are
            // real bugs — surfaced to the user via CI's panic path
            // when the e2e test sees a missing sentinel.
            println!(
                "cargo:warning=cargo build for sample_stub fixture exited {s}; e2e test will skip (local) or panic (CI)"
            );
        }
        Err(e) => {
            // Spawn failure — cargo binary not on PATH. Rare; treat
            // like other failures: no sentinel, test decides.
            println!(
                "cargo:warning=failed to invoke cargo for sample_stub fixture ({e}); e2e test will skip (local) or panic (CI)"
            );
        }
    }
}
