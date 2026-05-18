//! Compile-only test that the `wasm_importer_main!` macro expands
//! into valid Rust at the SAME module scope as user fns of the same
//! name (`identify`, `extract`, `extract_enriched`).
//!
//! This file is the contract that PR #1134's first-round release
//! got wrong: the documented example code would not compile because
//! the macro generated `fn identify(...)` etc. at module scope,
//! colliding with the user's free fns. The fix (use
//! `#[unsafe(export_name = "...")]` with `__wasm_importer_*` Rust
//! identifiers) is verified here — if the macro ever regresses to
//! bare `#[no_mangle] pub extern "C" fn identify`, this test crate
//! fails to compile.
//!
//! Each `#[test]` is a thin wrapper around a macro invocation:
//! cargo test verifies they all compile. The macro-generated
//! `extern "C"` exports never get called from this binary — they're
//! just here to prove the expansion is valid (and would panic on
//! native targets anyway, by `pack_output`'s wasm32-only contract).
//!
//! # What this test does NOT verify
//!
//! The `export_name` attribute is gated on `cfg_attr(target_arch =
//! "wasm32", ...)`, so on the native test target the generated fns
//! carry their Rust identifier (`__wasm_importer_alloc` etc.) but
//! NOT the WASM-host-expected linker symbol (`alloc` etc.). The
//! actual host-visible export-name correctness is validated in
//! wave 2.3e: a reference sample importer is compiled to
//! `wasm32-unknown-unknown` and loaded via `WasmImporter::load`,
//! which fails fast if any required export is missing.
//!
//! Only built with `--features guest`. Without the feature, the
//! macro isn't available and there's nothing to test.

#![cfg(feature = "guest")]

use rustledger_plugin_types::{
    EnrichedImporterOutput, EnrichmentWrapper, ImporterInput, ImporterOutput, wasm_importer_main,
};

mod short_form {
    use super::*;

    // The user's free fns — same names the WASM ABI uses. The macro
    // must not collide with these.
    const fn identify(path: &str) -> bool {
        // Placeholder logic — fn is just here to prove the macro
        // accepts the `fn(&str) -> bool` signature.
        !path.is_empty()
    }

    fn extract(_input: ImporterInput) -> ImporterOutput {
        ImporterOutput::empty()
    }

    wasm_importer_main! {
        name: "test-short",
        description: "short-form macro should auto-default extract_enriched",
        identify: identify,
        extract: extract,
    }
}

mod full_form {
    use super::*;

    const fn identify(path: &str) -> bool {
        // Placeholder logic — fn is just here to prove the macro
        // accepts the `fn(&str) -> bool` signature.
        !path.is_empty()
    }

    fn extract(_input: ImporterInput) -> ImporterOutput {
        ImporterOutput::empty()
    }

    fn extract_enriched(_input: ImporterInput) -> EnrichedImporterOutput {
        EnrichedImporterOutput {
            entries: vec![],
            warnings: vec![],
            errors: vec![],
        }
    }

    wasm_importer_main! {
        name: "test-full",
        description: "full-form macro with explicit extract_enriched",
        identify: identify,
        extract: extract,
        extract_enriched: extract_enriched,
    }
}

mod with_closures {
    use super::*;

    fn extract_impl(_input: ImporterInput) -> ImporterOutput {
        ImporterOutput::empty()
    }

    fn enriched_impl(_input: ImporterInput) -> EnrichedImporterOutput {
        EnrichedImporterOutput {
            entries: Vec::<(_, EnrichmentWrapper)>::new(),
            warnings: vec![],
            errors: vec![],
        }
    }

    wasm_importer_main! {
        name: "test-closure",
        description: "non-capturing closures should also work",
        identify: |path: &str| path.is_empty(),
        extract: extract_impl,
        extract_enriched: enriched_impl,
    }
}

mod all_closures {
    use super::*;

    // Verify all three positions accept non-capturing closures
    // simultaneously — `with_closures` only proves it for identify.
    // If the macro's fn-pointer type bounds ever break closure
    // coercion, this test fails to compile.
    wasm_importer_main! {
        name: "all-closures",
        description: "every callback as a non-capturing closure",
        identify: |path: &str| !path.is_empty(),
        extract: |_input: ImporterInput| ImporterOutput::empty(),
        extract_enriched: |_input: ImporterInput| EnrichedImporterOutput {
            entries: Vec::<(_, EnrichmentWrapper)>::new(),
            warnings: vec![],
            errors: vec![],
        },
    }
}

// The mere act of cargo test compiling this crate validates the
// three macro-invocation modules above. Symbol-shape verification
// is done via function-pointer coercion below — which checks the
// signatures without invoking the fns (their pack_output calls
// panic on non-wasm32 targets by design).
//
// If any of these tests fail to COMPILE, the macro has regressed.
// They all "pass" at runtime trivially.

#[test]
fn short_form_emits_expected_signatures() {
    let _: extern "C" fn(u32) -> *mut u8 = short_form::__wasm_importer_alloc;
    let _: extern "C" fn() -> u64 = short_form::__wasm_importer_metadata;
    let _: extern "C" fn(u32, u32) -> u64 = short_form::__wasm_importer_identify;
    let _: extern "C" fn(u32, u32) -> u64 = short_form::__wasm_importer_extract;
    let _: extern "C" fn(u32, u32) -> u64 = short_form::__wasm_importer_extract_enriched;
}

#[test]
fn full_form_emits_expected_signatures() {
    let _: extern "C" fn(u32) -> *mut u8 = full_form::__wasm_importer_alloc;
    let _: extern "C" fn() -> u64 = full_form::__wasm_importer_metadata;
    let _: extern "C" fn(u32, u32) -> u64 = full_form::__wasm_importer_identify;
    let _: extern "C" fn(u32, u32) -> u64 = full_form::__wasm_importer_extract;
    let _: extern "C" fn(u32, u32) -> u64 = full_form::__wasm_importer_extract_enriched;
}

#[test]
fn closures_emit_expected_signatures() {
    // Reference all 5 generated fns so clippy's dead-code analysis
    // can chain through them to `extract_impl`/`enriched_impl`,
    // which the macro consumes by name. If we referenced only
    // __wasm_importer_alloc, the chain would break and clippy
    // would (correctly!) flag the user fns as unused.
    let _: extern "C" fn(u32) -> *mut u8 = with_closures::__wasm_importer_alloc;
    let _: extern "C" fn() -> u64 = with_closures::__wasm_importer_metadata;
    let _: extern "C" fn(u32, u32) -> u64 = with_closures::__wasm_importer_identify;
    let _: extern "C" fn(u32, u32) -> u64 = with_closures::__wasm_importer_extract;
    let _: extern "C" fn(u32, u32) -> u64 = with_closures::__wasm_importer_extract_enriched;
}

#[test]
fn all_closures_emit_expected_signatures() {
    let _: extern "C" fn(u32) -> *mut u8 = all_closures::__wasm_importer_alloc;
    let _: extern "C" fn() -> u64 = all_closures::__wasm_importer_metadata;
    let _: extern "C" fn(u32, u32) -> u64 = all_closures::__wasm_importer_identify;
    let _: extern "C" fn(u32, u32) -> u64 = all_closures::__wasm_importer_extract;
    let _: extern "C" fn(u32, u32) -> u64 = all_closures::__wasm_importer_extract_enriched;
}
