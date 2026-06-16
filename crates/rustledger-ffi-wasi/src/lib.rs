// The exposed DTO types (DirectiveJson, Posting, Amount, etc.) carry
// many fields whose meaning is the JSON-RPC API. Per-field rustdoc
// would duplicate the JSON-RPC reference and drift from it. The lib
// is internal-for-testing scope, not a stable public API — until
// item 2 of issue #1200 (ts-rs generation) lands, treat the
// rust-side type docs as authoritative for shape only.
#![allow(missing_docs)]

//! Library surface for the rustledger FFI-WASI binding.
//!
//! Most consumers run this crate as a WASI module (see `main.rs` and
//! the JSON-RPC API doc on the binary). But the `Directive → JSON`
//! conversion functions and DTO types are also useful as a library
//! — primarily for cross-binding equivalence tests (issue #1200) that
//! need to compare this binding's wire format against
//! `rustledger-wasm`'s.
//!
//! The binary in `main.rs` consumes these modules through this lib
//! rather than re-`mod`-ing them, so there's a single source of truth.
//!
//! ## Visibility
//!
//! Two `pub` modules: [`convert`] (for `directive_to_json` and the
//! related conversion functions used by cross-binding equivalence
//! tests) and [`jsonrpc`] (for the binary shim). DTO types are
//! re-exported at the crate root when they're part of the conversion
//! surface; the rest of the internal `types`, `commands`, and
//! `helpers` modules are `pub(crate)`.

pub mod convert;
pub mod jsonrpc;

pub(crate) mod commands;
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
pub const API_VERSION: &str = "2.1";
