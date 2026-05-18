//! Stub WASM importer for the host's end-to-end integration test.
//!
//! This is the smallest possible importer that exercises every host
//! ↔ guest contract:
//!
//! - `identify` returns true iff the path ends with `.stub` —
//!   exercises the path-string round-trip through msgpack
//! - `extract` returns a single hardcoded `Open` directive — exercises
//!   the `DirectiveWrapper` wire format encode/decode
//! - `extract_enriched` is omitted; the short-form macro arm
//!   auto-generates a passthrough that wraps via
//!   `default_enriched_from`. The host's e2e test asserts the
//!   default `"default"` method string round-trips correctly,
//!   closing the cross-crate symmetry guarantee deferred from wave 2.3d.
//!
//! Not a real importer — exists only to load through `WasmImporter`
//! and prove the macro's wasm32 export-name + symbol contract
//! actually works end to end. The host's e2e test (in
//! `crates/rustledger-importer/tests/wasm_importer_e2e.rs`) is the
//! only consumer.

use rustledger_plugin_types::{
    DirectiveData, DirectiveWrapper, ImporterInput, ImporterOutput, OpenData,
    wasm_importer_main,
};

/// Stub identifier: matches any file path ending with `.stub`.
fn identify(path: &str) -> bool {
    path.ends_with(".stub")
}

/// Stub extractor: ignores input content, returns a single Open
/// directive. The host's e2e test asserts the round-trip preserves
/// the directive's fields (date, account) verbatim.
fn extract(_input: ImporterInput) -> ImporterOutput {
    let open = DirectiveWrapper {
        directive_type: String::new(),
        date: "2024-01-15".to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Open(OpenData {
            account: "Assets:StubBank".to_string(),
            currencies: vec!["USD".to_string()],
            booking: None,
            metadata: vec![],
        }),
    };
    let mut out = ImporterOutput::new(vec![open]);
    // A warning so the host's bridge-warnings path is exercised too.
    out.warnings.push("stub: synthetic single directive".to_string());
    out
}

wasm_importer_main! {
    name: "sample-stub",
    description: "minimal stub for the host's e2e test",
    identify: identify,
    extract: extract,
}
