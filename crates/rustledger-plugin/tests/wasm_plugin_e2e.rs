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
    AmountData, DirectiveData, DirectiveWrapper, OpenData, PluginInput, PluginOp, PluginOptions,
    PostingData, TransactionData,
};

/// Bytes of the fixture wasm produced by `build.rs`, or `None` when the
/// test must skip: under cargo-llvm-cov, or locally when the sentinel is
/// missing (wasm32 target unavailable). Panics when missing in CI.
fn fixture_wasm_bytes() -> Option<Vec<u8>> {
    // cargo-llvm-cov can't be overridden in our wasm32 sub-cargo (see
    // build.rs). The Test job exercises these tests for real; coverage
    // skips them.
    if std::env::var_os("CARGO_LLVM_COV").is_some() {
        eprintln!(
            "skip: running under cargo-llvm-cov; wasm32 fixture skipped by build.rs (Test job covers e2e)"
        );
        return None;
    }

    let path = PathBuf::from(env!("OUT_DIR")).join("sample_stub.wasm");
    if !path.exists() {
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
        return None;
    }

    Some(std::fs::read(&path).expect("read stub wasm"))
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

fn expense_wrapper(n: usize) -> DirectiveWrapper {
    let posting = |account: &str, number: &str| PostingData {
        account: account.to_string(),
        units: Some(AmountData {
            number: number.to_string(),
            currency: "USD".to_string(),
        }),
        cost: None,
        price: None,
        flag: None,
        metadata: vec![],
        span: None,
    };
    DirectiveWrapper {
        directive_type: String::new(),
        date: "2024-01-15".to_string(),
        filename: Some("ledger.beancount".to_string()),
        lineno: Some(u32::try_from(n).expect("small index")),
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: Some("Grocery store".to_string()),
            narration: format!("Groceries #{n}"),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![
                posting("Liabilities:CreditCard", "-42.10"),
                posting("Expenses:Food:Groceries", "42.10"),
            ],
        }),
    }
}

#[test]
fn stub_wasm_plugin_round_trips_process() {
    let Some(bytes) = fixture_wasm_bytes() else {
        return;
    };
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

/// The default time budget covers a ledger-sized input. It used to be
/// converted to fuel at 1M per second, so the default 30 seconds were
/// 30M fuel; decoding one two-posting transaction costs the stub ~67k
/// fuel, so it trapped on a ledger of a few hundred transactions.
#[test]
fn stub_wasm_plugin_processes_ledger_sized_input_within_default_budget() {
    const TRANSACTIONS: usize = 5_000;

    let Some(bytes) = fixture_wasm_bytes() else {
        return;
    };
    let mut manager = PluginManager::with_config(RuntimeConfig::default());
    let index = manager
        .load_bytes("sample-stub", &bytes)
        .expect("load stub wasm");

    let input = PluginInput {
        directives: (0..TRANSACTIONS).map(expense_wrapper).collect(),
        options: PluginOptions::default(),
        config: None,
    };

    let output = manager
        .execute(index, &input)
        .expect("default budget covers a 5,000-transaction input");

    assert!(
        output.errors.is_empty(),
        "stub plugin should not emit errors, got: {:?}",
        output.errors,
    );
    assert_eq!(output.ops.len(), TRANSACTIONS);
    for (i, op) in output.ops.iter().enumerate() {
        assert!(
            matches!(op, PluginOp::Modify(j, _) if *j == i),
            "expected Modify({i}, _), got {op:?}"
        );
    }
}
