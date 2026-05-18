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
    // Re-run build.rs when `CARGO_LLVM_COV` is set or unset, so the
    // skip-vs-build decision below is re-evaluated on a coverage →
    // normal transition. Without this, the previous (skipped) build
    // is reused and the sentinel stays missing.
    println!("cargo:rerun-if-env-changed=CARGO_LLVM_COV");

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

    // Skip the sub-cargo entirely under `cargo-llvm-cov`. It injects
    // coverage rustflags via cargo's `--config 'build.rustflags=[...]'`
    // which cannot be overridden by a child cargo invocation (cargo's
    // `--config` array semantics MERGE rather than replace). The
    // wasm32 stable toolchain ships no `profiler_builtins`, so
    // `-Cinstrument-coverage` leaking through fails with
    // `error[E0463]: can't find crate for 'profiler_builtins'`.
    //
    // The Test CI job (`cargo nextest run --all-features`) exercises
    // the e2e test for real — it doesn't run under cargo-llvm-cov.
    // (Doctests runs `cargo test --doc` only; Regression runs a shell
    // script — neither runs integration tests.) Coverage alone
    // skipping this one test is an acceptable trade — the test file
    // itself also checks `CARGO_LLVM_COV` and short-circuits without
    // panicking, so this skip doesn't cause a CI red.
    //
    // `CARGO_LLVM_COV=1` is set by cargo-llvm-cov for every cargo
    // invocation it spawns; it's the documented sentinel for tooling
    // to opt out of coverage-incompatible work.
    if std::env::var_os("CARGO_LLVM_COV").is_some() {
        println!(
            "cargo:warning=skipping sample_stub wasm32 fixture build under cargo-llvm-cov (incompatible with -Cinstrument-coverage); Test job exercises e2e for real"
        );
        return;
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
    // - `CARGO_BUILD_TARGET` / `CARGO_BUILD_RUSTFLAGS`: same shape, same risk.
    // - `RUSTDOCFLAGS`: cargo-llvm-cov sets this in tandem with
    //   `RUSTFLAGS`; harmless for `cargo build` but cleaner not to inherit.
    // - `CARGO_INCREMENTAL`: cargo-llvm-cov forces 0; we want the
    //   fixture's own default.
    // - `LLVM_PROFILE_FILE`: runtime profile output path; doesn't apply
    //   to compilation, but scrubbing keeps the sub-build deterministic.
    //
    // Don't scrub `CARGO_TARGET_DIR` — `--target-dir` on the command
    // line takes precedence anyway, and clearing it would defeat
    // caching.
    //
    // Capture (rather than inherit) stdout/stderr so the actual
    // compile errors from the sub-cargo surface as `cargo:warning=`
    // lines on failure. Cargo's default build-script protocol swallows
    // inherited stderr; we explicitly re-emit it below.
    let output = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .env_remove("CARGO_BUILD_RUSTFLAGS")
        .env_remove("CARGO_BUILD_TARGET")
        .env_remove("RUSTDOCFLAGS")
        .env_remove("CARGO_INCREMENTAL")
        .env_remove("LLVM_PROFILE_FILE")
        // `cargo-llvm-cov` v0.6+ injects coverage rustflags via cargo's
        // `--config 'build.rustflags=[...]'` arg, which propagates to
        // sub-cargos through cargo's config merging (NOT via env vars
        // we scrubbed above). The wasm32 stable toolchain ships no
        // `profiler_builtins` crate, so `-Cinstrument-coverage` leaking
        // through produces `error[E0463]: can't find crate for
        // 'profiler_builtins'`. Counter it at maximum priority: pass
        // our own `--config` that empties the rustflags for the wasm32
        // target. Command-line `--config` beats env beats config file
        // in cargo's merge order.
        .args([
            "--config",
            "target.wasm32-unknown-unknown.rustflags=[]",
            "build",
            "--release",
            "--target",
            "wasm32-unknown-unknown",
            "--manifest-path",
        ])
        .arg(fixture_dir.join("Cargo.toml"))
        .arg("--target-dir")
        .arg(&target_dir)
        .output();

    match output {
        Ok(out) if out.status.success() => {
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
        Ok(out) => {
            // Non-zero exit. Common cause locally: wasm32 target not
            // installed. Other causes (compile error, ABI break,
            // env-leak from coverage tooling) are real bugs — surface
            // the sub-cargo's actual stderr so reviewers can debug
            // without re-running locally.
            for line in String::from_utf8_lossy(&out.stderr).lines() {
                println!("cargo:warning=sample_stub stderr: {line}");
            }
            println!(
                "cargo:warning=cargo build for sample_stub fixture exited {}; e2e test will skip (local) or panic (CI)",
                out.status
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
