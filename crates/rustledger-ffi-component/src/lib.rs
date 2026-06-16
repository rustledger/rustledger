//! rustledger embedding as a WASI Preview 2 component (#1384, Phase 2).
//!
//! Implements the WIT `rustledger` world (`wit/world.wit`) — the typed
//! replacement for the `rustledger-ffi-wasi` JSON-RPC surface.
//!
//! Phase 2 is in progress (tracer-bullet): the toolchain and binding wiring are
//! proven end-to-end via `version`; the remaining exports are stubbed and are
//! being filled in against the existing loader/query logic, one interface at a
//! time. Stubs `unimplemented!()` (a wasm trap) rather than returning silently
//! wrong data.

// wit-bindgen's `export!` macro emits `#[unsafe(export_name = …)]` shims and
// unsafe blocks for the canonical ABI; the workspace denies `unsafe_code`, so
// allow it here (the hand-written code below contains no unsafe). `missing_docs`
// is allowed because the generated bindings are undocumented by construction.
#![allow(unsafe_code)]
#![allow(missing_docs)]

wit_bindgen::generate!({
    path: "wit/world.wit",
    world: "rustledger",
});

mod convert;

use exports::rustledger::ledger::builder::{
    Directive, Guest as BuilderGuest, InputDirective,
};
use exports::rustledger::ledger::format::Guest as FormatGuest;
use exports::rustledger::ledger::ledger::{
    BatchResult, Guest as LedgerGuest, LoadResult, QueryResult, ValidateResult,
};
use exports::rustledger::ledger::util::{Guest as UtilGuest, TypesInfo};

/// The Component-Model api-version this build implements. Mirrors
/// `rustledger-ffi-wasi`'s `API_VERSION` (additive 2.1 — per-position cost).
const API_VERSION: &str = "2.1";

const TODO: &str = "rustledger-ffi-component: export not yet wired (#1384 Phase 2)";

struct Component;

impl LedgerGuest for Component {
    fn version() -> String {
        API_VERSION.to_string()
    }
    fn load(source: String) -> LoadResult {
        convert::load(&source, "<stdin>")
    }
    fn load_file(path: String) -> LoadResult {
        convert::load_file(&path)
    }
    fn validate(source: String) -> ValidateResult {
        convert::validate(&source)
    }
    fn validate_file(path: String) -> ValidateResult {
        convert::validate_file(&path)
    }
    fn query(source: String, query: String) -> QueryResult {
        convert::query(&source, &query)
    }
    fn query_file(path: String, query: String) -> QueryResult {
        convert::query_file(&path, &query)
    }
    fn batch(source: String, queries: Vec<String>) -> BatchResult {
        convert::batch(&source, &queries)
    }
    fn batch_file(path: String, queries: Vec<String>) -> BatchResult {
        convert::batch_file(&path, &queries)
    }
}

impl BuilderGuest for Component {
    fn create(_entry: InputDirective) -> Result<Directive, String> {
        unimplemented!("{TODO}")
    }
    fn create_batch(_entries: Vec<InputDirective>) -> Result<Vec<Directive>, String> {
        unimplemented!("{TODO}")
    }
    fn filter(_entries: Vec<Directive>, _begin_date: String, _end_date: String) -> Vec<Directive> {
        unimplemented!("{TODO}")
    }
    fn clamp(_entries: Vec<Directive>, _begin_date: String, _end_date: String) -> Vec<Directive> {
        unimplemented!("{TODO}")
    }
}

impl UtilGuest for Component {
    fn types() -> TypesInfo {
        unimplemented!("{TODO}")
    }
    fn is_encrypted(_path: String) -> bool {
        unimplemented!("{TODO}")
    }
    fn get_account_type(_account: String) -> String {
        unimplemented!("{TODO}")
    }
}

impl FormatGuest for Component {
    fn format_source(_source: String) -> String {
        unimplemented!("{TODO}")
    }
    fn format_file(_path: String) -> String {
        unimplemented!("{TODO}")
    }
    fn format_entry(_entry: InputDirective) -> Result<String, String> {
        unimplemented!("{TODO}")
    }
    fn format_entries(_entries: Vec<InputDirective>) -> Result<String, String> {
        unimplemented!("{TODO}")
    }
}

export!(Component);
