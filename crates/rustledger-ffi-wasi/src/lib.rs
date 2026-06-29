// The exposed DTO types (DirectiveJson, Posting, Amount, etc.) carry
// many fields whose meaning is the JSON-RPC API. Per-field rustdoc
// would duplicate the JSON-RPC reference and drift from it. The lib
// is internal-for-testing scope, not a stable public API — until
// item 2 of issue #1200 (ts-rs generation) lands, treat the
// rust-side type docs as authoritative for shape only.
#![allow(missing_docs)]

//! Shared loader/conversion helpers for the rustledger WASI component FFI.
//!
//! # The wasip1 JSON-RPC surface was removed (Phase 5, #1419)
//!
//! This crate used to expose a wasip1 JSON-RPC 2.0 embedding API (a server
//! binary in `main.rs` + a `jsonrpc` router). That surface was retired in
//! Phase 5 ([#1419](https://github.com/rustledger/rustledger/issues/1419)) now
//! that the typed WASI Preview 2 / Component Model binding,
//! [`rustledger-ffi-component`](https://github.com/rustledger/rustledger/issues/1384)
//! (#1384), is the default embedding path (default in rustfava as of Phase 4).
//! The router, the server binary, the round-trip wire-format tests, and the
//! `rustledger-ffi-wasi-*.wasm` release artifact are gone.
//!
//! What remains is a **library only**: the loader orchestration ([`helpers`])
//! and the `Directive → JSON` DTO conversion ([`convert`]) that
//! `rustledger-ffi-component` still reuses. The remaining Phase 5 stages retire
//! the DTO layer (the component will convert core→WIT directly) and relocate
//! this shared code to its final home — at which point this crate is removed.

pub mod convert;
// `helpers` is `pub` so the WIT/Component-Model crate
// (`rustledger-ffi-component`, #1384) can reuse the loader orchestration
// (`load_source`) instead of duplicating it.
pub mod helpers;
pub(crate) mod types;

// Re-export the wire-format DTOs that cross-binding tests inspect, plus the
// load-result DTOs the component crate maps into WIT types.
pub use types::{
    Amount, CostNumber, DirectiveJson, Error, Include, LedgerOptions, Meta, Plugin, Posting,
    PostingCost, TypedValue,
};
// Directive hashing is core→hash (no DTO involved); re-exported at the crate
// root so the component can compute the `meta.hash` field when converting
// core→WIT directly, without depending on the DTO-shaped `convert` module.
pub use convert::compute_directive_hash;
// Input/construction types + converter the component crate maps WIT input into
// (`entry.create`).
pub use types::input::{InputAmount, InputCost, InputCostNumber, InputEntry, InputPosting};
pub use types::input_entry_to_directive;

/// API version this server compiled against. Reported as the
/// `api_version` field on every method's response (`util.version`,
/// `ledger.load`, etc.).
///
/// Increment minor version for backwards-compatible changes.
/// Increment major version for breaking changes.
///
/// # Server vs. client semantics
///
/// This constant is the SERVER's compile-time advertised version.
/// Cross-version clients negotiating wire shape MUST read the
/// `api_version` field FROM THE RESPONSE PAYLOAD they receive — not
/// from a locally-linked `API_VERSION` constant. A client binary
/// statically linked against `rustledger-ffi-wasi` v1.0 carries
/// `API_VERSION = "1.0"` in its image but, if it talks to a
/// dynamically-deployed v2.0 server, must use the v2.0-shaped response
/// — the server's version comes from the wire, not the client's
/// link-time copy.
///
/// # Version history
///
/// * **2.2** — `ledger.load`/`ledger.loadFile` accept an optional
///   `expand_pads` request field; when `true`, `pad` directives are
///   materialized into synthesized `Padding` transactions in the returned
///   entries (balance-computing consumers opt in). Additive and backward
///   compatible — the field defaults to `false` (source-faithful) — hence a
///   minor bump per the policy above (#1628). (The WIT component delivers the
///   same capability via a *breaking* parameter, so it bumps to 3.0.)
/// * **2.1** — `Inventory`/`Position` query values now include an optional
///   `cost` object per position when the holding was booked at cost, using the
///   same wire shape as a directive `PostingCost` (`number` is a tagged
///   `CostNumber`, always `per_unit` for a booked position). Additive and
///   backward compatible — units-only consumers ignore the new field — hence a
///   minor bump per the policy above.
/// * **2.0** — `error.data.errors` on `beancount_parse_error` (-32000)
///   responses is now `ParseErrorEntry[]` (per-error object with
///   `message`, `kind_code`, `hint`, `span`) instead of the previous
///   `string[]` of rendered messages. This is a wire-shape break,
///   hence the major bump per the policy above (round-19 correction:
///   the change shipped briefly as 1.1, which violated the major-on-
///   break rule). Cross-version clients negotiate via `api_version`
///   on the response; v1.x clients that parse errors as `string[]`
///   should refuse to talk to a v2.x server. See `README.md` for the
///   migration recipe.
/// * **1.0** — initial API.
pub const API_VERSION: &str = "2.2";
