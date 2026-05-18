//! End-to-end integration test: load a real `.wasm` module produced
//! by the `wasm_plugin_main!` macro and exercise the `process` entry
//! point.
//!
//! Sibling to `rustledger-importer/tests/wasm_importer_e2e.rs`. Same
//! design: a build.rs compiles `tests/fixtures/sample_stub/` to
//! wasm32; this test loads it via `PluginManager::load_bytes`,
//! exercises one round-trip, and asserts the result.
//!
//! Closes the macro-validation gap on the directive-plugin side: the
//! compile-test crate (`plugin_macro_compiles.rs`) proves the macro
//! expands correctly on the host target, but only this test proves
//! the wasm32 linker actually emits `alloc` and `process` exports
//! with the names the host loader looks up. If the
//! `#[cfg_attr(target_arch = "wasm32", unsafe(export_name = "..."))]`
//! gating ever breaks, `validate_plugin_module` rejects the load and
//! this test fails loudly.
//!
//! # Skip when wasm32 unavailable (local dev only)
//!
//! `build.rs` writes the compiled fixture to `OUT_DIR/sample_stub.wasm`.
//! On dev machines without `wasm32-unknown-unknown` installed, it
//! emits a `cargo:warning=` and leaves the sentinel unwritten. This
//! test detects the missing sentinel via `Path::exists()` and bails
//! with an `eprintln!` rather than failing locally.
//!
//! **In CI we refuse to skip.** GitHub Actions sets `CI=true`; if the
//! sentinel is missing under CI we panic with an actionable message,
//! matching the importer e2e test's CI guard.

#![cfg(feature = "wasm-runtime")]

use std::path::PathBuf;

use rustledger_plugin::{PluginManager, RuntimeConfig};
use rustledger_plugin_types::{
    DirectiveData, DirectiveWrapper, OpenData, PluginInput, PluginOp, PluginOptions,
    TransactionData,
};

/// Absolute path to the fixture wasm produced by `build.rs`. Returns
/// `None` when the sentinel is missing (wasm32 target unavailable).
fn fixture_wasm_path() -> Option<PathBuf> {
    let p = PathBuf::from(env!("OUT_DIR")).join("sample_stub.wasm");
    p.exists().then_some(p)
}

fn txn_wrapper(narration: &str) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: String::new(),
        date: "2024-01-15".to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: narration.to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![],
        }),
    }
}

fn open_wrapper(account: &str) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: String::new(),
        date: "2024-01-01".to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Open(OpenData {
            account: account.to_string(),
            currencies: vec![],
            booking: None,
            metadata: vec![],
        }),
    }
}

#[test]
fn stub_wasm_plugin_round_trips_process() {
    let Some(wasm_path) = fixture_wasm_path() else {
        assert!(
            std::env::var_os("CI").is_none(),
            "sample_stub.wasm sentinel missing in CI — wasm32-unknown-unknown \
             target not installed, build.rs gracefully skipped. Install it via \
             `targets: wasm32-unknown-unknown` on the rust-toolchain step in \
             .github/workflows/ci.yml + quality.yml."
        );
        eprintln!(
            "skip: sample_stub.wasm sentinel missing — wasm32-unknown-unknown not installed?"
        );
        return;
    };

    let bytes = std::fs::read(&wasm_path).expect("read stub wasm");
    let mut manager = PluginManager::with_config(RuntimeConfig::default());
    let index = manager
        .load_bytes("sample-stub", &bytes)
        .expect("load stub wasm");

    // Mixed input: one transaction (gets tagged), one Open (passes
    // through). The stub's `process` distinguishes the two arms.
    let input = PluginInput {
        directives: vec![
            txn_wrapper("Coffee shop"),
            open_wrapper("Assets:Bank:Checking"),
        ],
        options: PluginOptions::default(),
        config: None,
    };

    let output = manager.execute(index, &input).expect("execute round-trips");

    assert!(
        output.errors.is_empty(),
        "stub plugin should not emit errors, got: {:?}",
        output.errors,
    );
    assert_eq!(output.ops.len(), 2);

    // Op 0 is the transaction — should be Modify with the tag added.
    match &output.ops[0] {
        PluginOp::Modify(i, wrapper) => {
            assert_eq!(*i, 0);
            let DirectiveData::Transaction(txn) = &wrapper.data else {
                panic!("expected transaction in Modify, got {:?}", wrapper.data);
            };
            assert_eq!(txn.tags, vec!["stub-processed".to_string()]);
            assert_eq!(txn.narration, "Coffee shop");
        }
        other => panic!("expected Modify on transaction, got {other:?}"),
    }

    // Op 1 is the Open — should be Keep (untouched passthrough).
    match &output.ops[1] {
        PluginOp::Keep(i) => assert_eq!(*i, 1),
        other => panic!("expected Keep on non-transaction, got {other:?}"),
    }
}
