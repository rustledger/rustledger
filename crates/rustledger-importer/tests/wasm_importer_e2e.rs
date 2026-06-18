//! End-to-end integration test: load a real `.wasm` module produced by
//! the `wasm_importer_main!` macro and exercise every host ↔ guest
//! entry point.
//!
//! Wave 2.3e — this is the test that earlier waves intentionally
//! deferred. Together with the unit-level WAT tests in
//! `src/wasm.rs`, it closes the loop on three earlier deferrals:
//!
//! 1. **2.3b**: the `MemoryLimiter` is wired through `Store::limiter`
//!    so per-call sandbox enforcement matches `rustledger-plugin`'s
//!    runtime. Unit tests in `rustledger_plugin::sandbox::tests`
//!    cover the limiter in isolation; loading a real wasm32 module
//!    here proves the limiter survives the full instantiate path.
//!
//! 2. **2.3d**: `#[cfg_attr(target_arch = "wasm32", unsafe(export_name = "..."))]`
//!    is the production gate on the `metadata`/`identify`/`extract`/
//!    `extract_enriched` symbol names. The compile-test crate proves
//!    the macro *expands* correctly on the host target; this test
//!    proves the wasm32 linker actually emits those exact symbol
//!    names — `WasmImporter::validate_module` looks them up by name
//!    and would fail loudly here if the cfg gate ever broke.
//!
//! 3. **2.3d**: `default_enriched_from` (guest-side) emits a `"default"`
//!    method string, and host-side `parse_method("default")` maps it
//!    back to `CategorizationMethod::Default`. Both sides have unit
//!    tests for their half; the `extract_enriched` assertion below
//!    is the only place the symmetry is actually proven end to end.
//!
//! # Skip when wasm32 unavailable (local dev only)
//!
//! `build.rs` writes the compiled fixture to `OUT_DIR/sample_stub.wasm`.
//! On dev machines without the `wasm32-unknown-unknown` target it
//! emits a `cargo:warning=` and skips writing the file. This test
//! detects the missing sentinel via `Path::exists()` and bails with an
//! `eprintln!` rather than failing — matches the build.rs design that
//! prefers "no signal" to "compile error" for the common case where
//! someone runs `cargo test` without the wasm32 target installed.
//!
//! **In CI we refuse to skip.** GitHub Actions sets `CI=true`; if the
//! sentinel is missing under CI we panic with an actionable message,
//! because a silent skip there means the wave 2.3e value (real wasm32
//! round-trip) was never exercised. The first revision of this PR fell
//! into exactly that trap — the test passed in 180 ms because cargo
//! couldn't find the wasm32 target and the graceful-skip path ran.
#![cfg(feature = "wasm-importer")]

use std::path::{Path, PathBuf};

use rustledger_core::Directive;
use rustledger_importer::config::{CsvConfig, ImporterType};
use rustledger_importer::{Importer, ImporterConfig, WasmImporter};
use rustledger_ops::enrichment::CategorizationMethod;

/// Absolute path to the fixture wasm produced by `build.rs`. Returns
/// `None` when the sentinel is missing (wasm32 target unavailable on
/// this dev machine — CI always has it).
fn fixture_wasm_path() -> Option<PathBuf> {
    let p = PathBuf::from(env!("OUT_DIR")).join("sample_stub.wasm");
    p.exists().then_some(p)
}

fn minimal_config() -> ImporterConfig {
    ImporterConfig {
        account: "Assets:StubBank".to_string(),
        currency: Some("USD".to_string()),
        importer_type: ImporterType::Csv(CsvConfig::default()),
    }
}

#[test]
fn stub_wasm_module_round_trips_every_entry_point() {
    // `cargo-llvm-cov` injects `-Cinstrument-coverage` via cargo's
    // `--config` which can't be overridden in the wasm32 sub-cargo
    // build that our build.rs runs. build.rs detects `CARGO_LLVM_COV`
    // and skips the fixture compile; we mirror that here so the
    // CI-panic guard below doesn't fire on coverage runs. The Test
    // job (`cargo nextest run --all-features`) exercises this test
    // for real — Doctests runs only doctests, Regression runs a shell
    // script, so neither covers integration tests.
    if std::env::var_os("CARGO_LLVM_COV").is_some() {
        eprintln!(
            "skip: running under cargo-llvm-cov; wasm32 fixture skipped by build.rs (Test job covers e2e)"
        );
        return;
    }

    let Some(wasm_path) = fixture_wasm_path() else {
        // CI must actually exercise the wasm32 path — silent skip there
        // defeats the whole point of the e2e test. Detect GitHub
        // Actions' `CI=true` and panic with an actionable message.
        assert!(
            std::env::var_os("CI").is_none(),
            "sample_stub.wasm sentinel missing in CI — wasm32-unknown-unknown \
             target not installed, build.rs gracefully skipped. Install it via \
             `targets: wasm32-unknown-unknown` on the rust-toolchain step in \
             .github/workflows/ci.yml (already done for the `ci` matrix; add to \
             any new job that runs `cargo test -p rustledger-importer`)."
        );
        eprintln!(
            "skip: sample_stub.wasm sentinel missing — wasm32-unknown-unknown not installed?"
        );
        return;
    };

    let importer = WasmImporter::load(&wasm_path).expect("load stub wasm");

    // ---- metadata: cached at load, exposed via name()/description() ----
    // Pins the strings the stub set via `wasm_importer_main! { name: ..., description: ... }`.
    assert_eq!(importer.name(), "sample-stub");
    assert_eq!(
        importer.description(),
        "minimal stub for the host's e2e test"
    );

    // ---- identify: the stub matches *.stub, rejects everything else ----
    assert!(
        importer.identify(Path::new("statement.stub")),
        "stub should identify *.stub paths"
    );
    assert!(
        !importer.identify(Path::new("statement.csv")),
        "stub should reject non-*.stub paths"
    );

    // extract/extract_enriched both std::fs::read the path; the stub
    // ignores file content, so an empty tempfile suffices.
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    let config = minimal_config();

    // ---- extract: returns the single hardcoded Open directive ----
    let result = importer
        .extract(tmp.path(), &config)
        .expect("extract succeeds");
    assert_eq!(
        result.directives.len(),
        1,
        "stub returns exactly one directive"
    );
    let Directive::Open(open) = &result.directives[0] else {
        panic!(
            "expected Open, got {:?}",
            std::mem::discriminant(&result.directives[0])
        );
    };
    assert_eq!(open.account.as_str(), "Assets:StubBank");
    assert_eq!(open.currencies.len(), 1);
    assert_eq!(open.currencies[0].as_str(), "USD");
    assert_eq!(open.date.to_string(), "2024-01-15");

    // The stub pushes a warning to prove the host's warning-forwarding
    // path actually moves bytes across the ABI boundary.
    assert_eq!(
        result.warnings,
        vec!["stub: synthetic single directive".to_string()],
        "stub's single warning should round-trip verbatim"
    );

    // ---- extract_enriched: macro short-form auto-generates a
    // passthrough via `default_enriched_from`. The host's `parse_method`
    // maps the wire-format `"default"` string back to
    // `CategorizationMethod::Default`. This single assertion is the
    // canary for the cross-crate symmetry guarantee deferred from
    // wave 2.3d.
    let enriched = importer
        .extract_enriched(tmp.path(), &config)
        .expect("extract_enriched succeeds");
    assert_eq!(enriched.entries.len(), 1, "one entry from one directive");
    let (_dir, enr) = &enriched.entries[0];
    assert_eq!(
        enr.method,
        CategorizationMethod::Default,
        "default passthrough should round-trip the `default` method string"
    );
    assert_eq!(enr.directive_index, 0);
    // Bit-equality on the literal 0.0 the default-passthrough sets —
    // it's never the product of arithmetic, so clippy's float-cmp lint
    // doesn't apply here (we silence it by comparing bits).
    assert_eq!(
        enr.confidence.to_bits(),
        0.0_f64.to_bits(),
        "default enrichment is uncategorized"
    );
    assert!(
        enr.alternatives.is_empty(),
        "default enrichment has no alternatives"
    );
    // Warning forwarding survives the enriched path too. (Bridge
    // warnings would be appended first if any; here the "default"
    // method is recognized so the bridge stays quiet.)
    assert_eq!(
        enriched.warnings,
        vec!["stub: synthetic single directive".to_string()],
    );
}
