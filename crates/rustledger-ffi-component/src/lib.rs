//! rustledger embedding as a WASI Preview 2 component (#1384, Phase 2).
//!
//! Implements the WIT `rustledger` world (`wit/world.wit`) — the typed
//! replacement for the `rustledger-ffi-wasi` JSON-RPC surface.
//!
//! All four interfaces (`ledger`, `builder`, `util`, `format`) are wired: each
//! Guest method delegates to [`convert`], which maps between the WIT types and
//! the loader/query logic reused from `rustledger-ffi-wasi`. Parity with the
//! JSON-RPC surface is exercised by `rustledger-ffi-component-tests`.

// wit-bindgen's `export!` macro emits `#[unsafe(export_name = …)]` shims and
// unsafe blocks for the canonical ABI; the workspace denies `unsafe_code`, so
// allow it here (the hand-written code below contains no unsafe). `missing_docs`
// is allowed because the generated bindings are undocumented by construction.
#![allow(unsafe_code)]
#![allow(missing_docs)]
// wit-bindgen's canonical-ABI lowering emits `Vec::from_raw_parts(p, n, n)`.
#![allow(clippy::same_length_and_capacity)]

wit_bindgen::generate!({
    path: "wit/world.wit",
    world: "rustledger",
});

mod convert;

use exports::rustledger::ledger::builder::{Directive, Guest as BuilderGuest, InputDirective};
use exports::rustledger::ledger::format::Guest as FormatGuest;
use exports::rustledger::ledger::ledger::{
    BatchResult, Guest as LedgerGuest, LoadResult, QueryResult, ValidateResult,
};
use exports::rustledger::ledger::util::{Guest as UtilGuest, TypesInfo};

/// The Component-Model api-version this build implements. Mirrors
/// `rustledger-ffi-wasi`'s `API_VERSION` (additive 2.1 — per-position cost).
const API_VERSION: &str = "2.1";

struct Component;

impl LedgerGuest for Component {
    fn version() -> String {
        API_VERSION.to_string()
    }
    fn load(source: String) -> LoadResult {
        convert::load(&source, "<stdin>")
    }
    fn load_file(
        path: String,
        allow_unrestricted_includes: bool,
        plugins: Vec<String>,
    ) -> LoadResult {
        convert::load_file(&path, allow_unrestricted_includes, &plugins)
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
    fn create(entry: InputDirective) -> Result<Directive, String> {
        convert::create(&entry)
    }
    fn create_batch(entries: Vec<InputDirective>) -> Result<Vec<Directive>, String> {
        convert::create_batch(&entries)
    }
    fn filter(entries: Vec<Directive>, begin_date: String, end_date: String) -> Vec<Directive> {
        convert::filter(entries, &begin_date, &end_date)
    }
    fn clamp(entries: Vec<Directive>, begin_date: String, end_date: String) -> Vec<Directive> {
        convert::clamp(entries, &begin_date, &end_date)
    }
}

impl UtilGuest for Component {
    fn types() -> TypesInfo {
        convert::types_info()
    }
    fn is_encrypted(path: String) -> bool {
        convert::is_encrypted(&path)
    }
    fn get_account_type(account: String) -> String {
        convert::get_account_type(&account)
    }
}

impl FormatGuest for Component {
    fn format_source(source: String) -> String {
        convert::format_source(&source)
    }
    fn format_file(path: String) -> String {
        convert::format_file(&path)
    }
    fn format_entry(entry: InputDirective) -> Result<String, String> {
        convert::format_entry(&entry)
    }
    fn format_entries(entries: Vec<InputDirective>) -> Result<String, String> {
        convert::format_entries(&entries)
    }
}

export!(Component);
