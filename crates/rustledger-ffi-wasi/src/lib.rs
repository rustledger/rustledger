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
pub(crate) mod helpers;
pub(crate) mod types;

// Re-export the wire-format DTOs that cross-binding tests inspect.
// Keeping the surface narrow avoids documenting every RPC-response
// type that lives in `types::*` but isn't part of the
// `Directive → JSON` conversion contract.
pub use types::{Amount, CostNumber, DirectiveJson, Meta, Posting, PostingCost, TypedValue};

/// API version for compatibility detection.
/// Increment minor version for backwards-compatible changes.
/// Increment major version for breaking changes.
pub const API_VERSION: &str = "1.0";
