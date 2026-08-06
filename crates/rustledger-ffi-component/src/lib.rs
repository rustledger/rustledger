//! rustledger embedding as a WASI Preview 2 component (#1384, Phase 2).
//!
//! Implements the WIT `rustledger` world (`wit/world.wit`) — the typed
//! replacement for the `rustledger-ffi-wasi` JSON-RPC surface.
//!
//! All four interfaces (`ledger`, `builder`, `util`, `format`) are wired: each
//! Guest method delegates to the private `convert` module, which maps between
//! the WIT types and
//! the loader/query logic reused from `rustledger-ffi-wasi`. `ledger` also
//! exports a stateful `session` resource (a held, booked ledger queried/filtered
//! /clamped without re-parsing) and `builder` a `query-entries` func (BQL over an
//! already-loaded directive set). Parity with the JSON-RPC surface is exercised
//! by `rustledger-ffi-component-tests`.

// This is a wasip2 component: `wit-bindgen`'s `export!` emits canonical-ABI
// shims that don't link as a native `cdylib` (e.g. a `cargo build --workspace`
// on x86_64, as the Arch PKGBUILD runs). Only that `export!` is wasm-specific,
// so it alone is gated to wasm targets (see the bottom of this file); the
// generated type bindings and the [`convert`] conversion logic compile natively,
// which lets the host `cargo build`/`clippy`/`test` actually check them (and the
// `convert` unit tests run on the host). The native `cdylib` is a
// trivially-linkable library with no canonical-ABI exports.
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
use exports::rustledger::ledger::importer::{ExtractResult, Guest as ImporterGuest};
use exports::rustledger::ledger::ledger::{
    BatchResult, BudgetResult, Guest as LedgerGuest, GuestSession, LedgerOptions, LoadResult,
    QueryResult, ReturnsResult, Session, ValidateResult,
};
use exports::rustledger::ledger::util::{Guest as UtilGuest, TypesInfo};

/// The Component-Model api-version this build implements. 3.11 adds
/// `session.account-type` (the account-type root honoring THIS ledger's
/// `name_*` renames — the free `util.get-account-type` hardcodes the
/// English roots and so disagrees with every report surface on a renamed
/// ledger, #1964); 3.10 adds
/// `session.budget` (budgeted vs actual over the held ledger — the
/// `rledger report budget` engine, so a host can render a Fava-style
/// budget view without re-deriving the accrual); 3.9 adds
/// `session.returns` (investment returns — money-weighted XIRR +
/// time-weighted TWR — over the held ledger, #1847); 3.8 adds
/// `session.format` (render the held entries honoring the ledger's
/// `display-precision`, #1766); 3.7 added
/// `session.from-entries-with-options` (the session carries the
/// ledger's options over the boundary, #1766); 3.6 added
/// `importer.dedup` and `format.format-loaded` (the extract → review →
/// save loop); 3.5 added the `importer` interface (identify / infer /
/// extract — the `rledger extract` engine over the boundary); 3.4 added
/// `session.from-entries` (hold a
/// directive set, rustfava#173/#249); 3.2 added the `host.decrypt` import so
/// encrypted (`.gpg`/`.asc`) ledgers can be decrypted by the host (#1667);
/// 3.1 added the `diff` field on `balance-dir` (#1663); 3.0 was the breaking
/// `expand-pads` parameter on `load`/`load-file` (#1628).
const API_VERSION: &str = "3.11";

struct Component;

impl LedgerGuest for Component {
    type Session = LedgerSession;

    fn version() -> String {
        API_VERSION.to_string()
    }
    fn load(source: String, filename: String, expand_pads: bool) -> LoadResult {
        convert::load(&source, &filename, expand_pads)
    }
    fn load_file(
        path: String,
        allow_unrestricted_includes: bool,
        plugins: Vec<String>,
        expand_pads: bool,
    ) -> LoadResult {
        convert::load_file(&path, allow_unrestricted_includes, &plugins, expand_pads)
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

/// A loaded, booked ledger held in the component (`resource session`, #1421).
/// Parses + books once in `new`/`from_file`; `query`/`filter`/`clamp` run on
/// the held ledger via [`convert::SessionState`] with no re-parse or re-render.
struct LedgerSession {
    state: convert::SessionState,
}

impl GuestSession for LedgerSession {
    fn new(source: String) -> Self {
        Self {
            state: convert::SessionState::from_source(&source),
        }
    }

    fn from_entries(entries: Vec<Directive>) -> Session {
        Session::new(Self {
            state: convert::SessionState::from_entries(&entries),
        })
    }

    fn from_entries_with_options(entries: Vec<Directive>, options: LedgerOptions) -> Session {
        Session::new(Self {
            state: convert::SessionState::from_entries_with_options(&entries, options),
        })
    }

    fn from_file(path: String, allow_unrestricted_includes: bool, plugins: Vec<String>) -> Session {
        Session::new(Self {
            state: convert::SessionState::from_file(&path, allow_unrestricted_includes, &plugins),
        })
    }

    fn info(&self) -> LoadResult {
        self.state.info()
    }

    fn account_type(&self, account: String) -> String {
        self.state.account_type(&account)
    }

    fn query(&self, query: String) -> QueryResult {
        self.state.query(&query)
    }

    fn filter(&self, begin_date: String, end_date: String) -> Vec<Directive> {
        self.state.filter(&begin_date, &end_date)
    }

    fn clamp(&self, begin_date: String, end_date: String) -> Vec<Directive> {
        self.state.clamp(&begin_date, &end_date)
    }

    fn dedup(&self, candidates: Vec<Directive>) -> Vec<bool> {
        self.state.dedup(&candidates)
    }

    fn format(&self) -> Result<String, String> {
        self.state.format()
    }

    fn returns(
        &self,
        investments: Vec<String>,
        income: Vec<String>,
        currency: String,
        end_date: String,
    ) -> Result<ReturnsResult, String> {
        self.state
            .returns(&investments, &income, &currency, &end_date)
    }

    fn budget(
        &self,
        from_date: String,
        to_date: String,
        children: bool,
        account_filter: String,
    ) -> Result<BudgetResult, String> {
        self.state
            .budget(&from_date, &to_date, children, &account_filter)
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
    fn query_entries(entries: Vec<Directive>, query: String) -> QueryResult {
        convert::query_entries(&entries, &query)
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

impl ImporterGuest for Component {
    fn identify(filename: String, content: Vec<u8>) -> Vec<String> {
        convert::import_identify(&filename, &content)
    }
    fn infer(filename: String, content: Vec<u8>) -> Result<String, String> {
        convert::import_infer(&filename, &content)
    }
    fn extract(
        filename: String,
        content: Vec<u8>,
        config: String,
    ) -> Result<ExtractResult, String> {
        convert::import_extract(&filename, &content, &config)
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
    fn format_loaded(entries: Vec<Directive>) -> Result<String, String> {
        convert::format_loaded(&entries)
    }
}

// Canonical-ABI export shims are wasm-only (they don't link as a native
// cdylib); everything above compiles and is unit-tested on the host.
#[cfg(target_arch = "wasm32")]
export!(Component);
