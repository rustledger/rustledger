//! Data transfer objects for WASM serialization.
//!
//! These types provide a JavaScript-friendly representation of Beancount data,
//! using string representations for dates and numbers.
//!
//! # Generated bindings (ADR-0004)
//!
//! The DTOs below have two generator-attribute layers, both inert in
//! normal builds:
//!
//! - **`ts-export`** feature (Phase 1, #1218) — the ts-rs derive emits
//!   per-type `.d.ts` files under `crates/rustledger-wasm/bindings/`.
//!   The post-process script at `scripts/regen-bindings.sh`
//!   concatenates them into the checked-in `bindings/index.d.ts`
//!   (canonical TS API).
//! - **`json-schema`** feature (Phase 3, #1232) — the schemars derive
//!   lets the same script emit `bindings/index.schema.json`
//!   (draft-2020-12). `datamodel-code-generator` then converts that
//!   into `bindings/types.py` (Pydantic v2). Closes the
//!   "hand-maintained Python stubs" gap left open by Phase 1/2.
//!
//! Adding a new field to any DTO below requires running
//! `scripts/regen-bindings.sh` and committing the regenerated TS
//! bundle, JSON Schema, and Python types — CI fails if any of them
//! drift.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

/// Result of parsing a Beancount file.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
// `ledger` is `Option<Ledger>` (nullable on the wire) but has no
// `skip_serializing_if`, so the field key is always present.
// schemars 1.x's per-field `required` attribute would force the key
// into the parent's `required` array but also un-null the type.
// `extend("required" = ...)` overrides the entire required array, so
// we must list every required field (including non-Option ones like
// `errors`) -- if we listed only `ledger`, schemars would drop
// `errors` from required.
#[cfg_attr(
    feature = "json-schema",
    schemars(extend("required" = ["ledger", "errors"]))
)]
pub struct ParseResult {
    /// The parsed ledger (if successful). Emitted as JSON `null` when
    /// parsing failed entirely; no `skip_serializing_if`, so the field
    /// is always present on the wire (TS: `Ledger | null`, not
    /// `ledger?`). See the `#[schemars(extend(...))]` on the struct
    /// itself for the "required-and-nullable" wire-contract enforcement.
    pub ledger: Option<Ledger>,
    /// Parse errors.
    pub errors: Vec<Error>,
}

/// A parsed Beancount ledger.
///
/// **Renamed to `LedgerJson` on the TS side** to avoid colliding with
/// the wasm-bindgen-exported `Ledger` class (the runtime wrapper that
/// owns the parsed data). `LedgerJson` is the wire shape; `Ledger` is
/// the class consumers instantiate via `Ledger.fromFiles(...)`. The
/// Rust struct keeps the shorter name for internal use; the rename
/// is applied via `#[ts(rename = ...)]`.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(
    feature = "ts-export",
    ts(export, export_to = "bindings/", rename = "LedgerJson")
)]
#[cfg_attr(feature = "json-schema", schemars(rename = "LedgerJson"))]
pub struct Ledger {
    /// All directives in the ledger.
    pub directives: Vec<DirectiveJson>,
    /// Ledger options.
    pub options: LedgerOptions,
}

/// Ledger options.
#[derive(
    Debug, Clone, Default, Serialize, Deserialize, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize,
)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
// `title` is `Option<String>` (nullable) but always present on the
// wire. `extend("required" = ...)` overrides the auto-detected list,
// so we must include every required field (operating_currencies
// included). See `ParseResult` for the full rationale.
#[cfg_attr(
    feature = "json-schema",
    schemars(extend("required" = ["operating_currencies", "title"]))
)]
pub struct LedgerOptions {
    /// Operating currencies.
    pub operating_currencies: Vec<String>,
    /// Ledger title. Emitted as JSON `null` when no title is set
    /// (no `skip_serializing_if`; field is always present on the
    /// wire). TS: `string | null`, not `title?`. The required-and-
    /// nullable wire contract is enforced via the `schemars(extend)`
    /// on the struct itself; see `ParseResult` for the rationale.
    pub title: Option<String>,
}

/// Metadata-value wire format for WASM consumers.
///
/// **JSON output is byte-equivalent to FFI-WASI's
/// `meta_value_to_json`** — JS clients writing portable code see
/// identical metadata values from both bindings. The Rust-side
/// types are independent though: FFI-WASI emits
/// `serde_json::Value` (untyped), this crate emits a typed enum.
/// Unifying the source-of-truth is tracked by issue #1200 item 2.
///
/// The host's [`rustledger_core::MetaValue`] is richer than the wire
/// type — `Account`/`Currency`/`Tag`/`Link`/`Date`/`Number` all
/// flatten to JSON strings here, matching FFI-WASI behavior. JS
/// consumers that need the strong type info should query the host
/// via a typed API; this enum is the lossy-but-portable view.
///
/// Untagged on the wire: `"hello"` serializes as a string,
/// `true` as a boolean, `null` as null, and an [`AmountValue`]
/// `{number,currency}` as a plain object. The TypeScript union is
/// `Record<string, string | boolean | {number, currency} | null>` —
/// no raw JSON number arm because `MetaValue::Number` (`Decimal`)
/// stringifies to preserve precision. Issue #1168 proposed
/// `string | number | boolean | null`; we substitute the
/// `{number,currency}` shape for `number` so cost-bearing metadata
/// round-trips cleanly and so JS numeric literals don't silently
/// alias into the wire (see the `meta_value_json_rejects_raw_json_number`
/// test).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub enum MetaValueJson {
    /// String/Account/Currency/Tag/Link/Date/Number — anything the
    /// host can represent as a string, including `rust_decimal::Decimal`
    /// values stringified to preserve precision (JSON numbers can't
    /// represent arbitrary-precision decimals losslessly).
    String(String),
    /// Boolean values.
    Bool(bool),
    /// Amount values (`{number, currency}`) — the only structured
    /// shape that survives the round-trip. Same `{number, currency}`
    /// envelope as [`AmountValue`] so JS consumers can branch on
    /// shape without a discriminator tag.
    ///
    /// **Deserialize note**: serde's untagged-enum matcher accepts
    /// extra fields in a JSON object (`#[serde(deny_unknown_fields)]`
    /// can't be applied per-variant on an untagged enum without
    /// breaking the wider match). A JS client sending
    /// `{number: "100", currency: "USD", extra: "x"}` deserializes as
    /// `Amount { number: "100", currency: "USD" }` with `extra`
    /// silently dropped. Output-side consumers (the production path)
    /// are unaffected; treat `Deserialize` here as best-effort and
    /// validate at the host boundary if you need stricter checks.
    Amount {
        /// The decimal quantity, stringified for precision.
        number: String,
        /// The currency code.
        currency: String,
    },
    /// Absent / null metadata value. Deserializes from JSON `null`;
    /// serializes to JSON `null`. (Serde supports unit variants in
    /// untagged enums for null values specifically — a less common
    /// pattern than struct/tuple variants but well-defined.)
    Null,
}

/// Tagged-union wire-format for a [`rustledger_core::MetaValue`] that
/// preserves the host's variant tag.
///
/// Used **only** in `DirectiveJson::Custom`'s `values` field, where
/// callers genuinely need to distinguish (for example) a `Date` from
/// a `String` or an `Account` — all three of which collapse to a bare
/// JSON string under the untagged [`MetaValueJson`] shape.
///
/// Wire shape: `{"type": "<variant>", "value": ...}` — mirrors
/// `rustledger-ffi-wasi::TypedValue` (see
/// `crates/rustledger-ffi-wasi/src/types/output.rs::TypedValue`) so
/// portable JS consumers see identical envelopes across both bindings.
///
/// **Why `value: MetaValueJson` and not `serde_json::Value`** —
/// `serde_json` is intentionally a host-only dev-dependency for this
/// crate (the runtime build avoids it to keep the wasm32 dep chain
/// small). [`MetaValueJson`] already covers every payload shape
/// FFI-WASI's `TypedValue` emits: `String` for the string-flavored
/// variants, `Bool` for `bool`, `Amount` for `amount`, `Null` for
/// `null`. The serialized JSON is bit-identical to FFI-WASI's.
///
/// `MetaValueJson` (untagged) is retained for the `meta` map of every
/// directive — there the lossy shape is intentional and matches what
/// FFI-WASI's metadata side also emits.
///
/// **Breaking change from #1199** for the WASM binding: pre-#1207
/// `Custom.values` emitted raw `MetaValueJson` values (lossy). Closes
/// #1207.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct TypedValueJson {
    /// Variant tag — one of `"string"`, `"account"`, `"currency"`,
    /// `"tag"`, `"link"`, `"date"`, `"number"`, `"bool"`, `"amount"`,
    /// `"null"`. Matches FFI-WASI's tag strings exactly.
    ///
    /// Renamed via `#[ts(type = ...)]` so the discriminator is a
    /// string-literal union on the TS side. The post-process script
    /// further narrows the full struct shape into a discriminated
    /// union (per-variant `{type, value}` rows) -- see ADR-0004 for
    /// why the narrowing is hand-tuned rather than generator-driven.
    #[serde(rename = "type")]
    #[cfg_attr(
        feature = "ts-export",
        ts(
            type = "\"string\" | \"account\" | \"currency\" | \"tag\" | \"link\" | \"date\" | \"number\" | \"bool\" | \"amount\" | \"null\""
        )
    )]
    pub value_type: String,
    /// Variant payload (see [`MetaValueJson`] for the four shapes).
    pub value: MetaValueJson,
}

/// A directive in JSON-serializable form.
///
/// Each variant corresponds to a Beancount directive type, with fields
/// representing the directive's data in a JavaScript-friendly format.
///
/// All variants carry a `meta` field with user-defined key/value
/// metadata from the source (issue #1168). Empty metadata serializes
/// as an absent field, so existing consumers continue to see the
/// pre-#1168 shape on directives without explicit metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
#[allow(missing_docs)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub enum DirectiveJson {
    /// Transaction directive.
    #[serde(rename = "transaction")]
    Transaction {
        date: String,
        flag: String,
        /// Optional payee. Mirrors FFI-WASI's shape: absent on the
        /// wire when `None` (closes #1221).
        #[serde(skip_serializing_if = "Option::is_none")]
        #[cfg_attr(feature = "ts-export", ts(optional))]
        payee: Option<String>,
        /// Optional narration. Empty narrations are normalized to
        /// `None` in `convert.rs` so the field is absent on the wire
        /// in the empty case -- matches FFI-WASI's pattern (#1221).
        #[serde(skip_serializing_if = "Option::is_none")]
        #[cfg_attr(feature = "ts-export", ts(optional))]
        narration: Option<String>,
        tags: Vec<String>,
        links: Vec<String>,
        postings: Vec<PostingJson>,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    /// Balance assertion.
    #[serde(rename = "balance")]
    Balance {
        date: String,
        account: String,
        amount: AmountValue,
        /// Explicit tolerance from the `~ 0.01` annotation, stringified.
        /// Mirrors `rustledger_core::Balance::tolerance`.
        #[serde(skip_serializing_if = "Option::is_none")]
        #[cfg_attr(feature = "ts-export", ts(optional))]
        tolerance: Option<String>,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    /// Open account.
    #[serde(rename = "open")]
    Open {
        date: String,
        account: String,
        currencies: Vec<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        #[cfg_attr(feature = "ts-export", ts(optional))]
        booking: Option<String>,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    /// Close account.
    #[serde(rename = "close")]
    Close {
        date: String,
        account: String,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    /// Commodity declaration.
    #[serde(rename = "commodity")]
    Commodity {
        date: String,
        currency: String,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    /// Pad directive.
    #[serde(rename = "pad")]
    Pad {
        date: String,
        account: String,
        source_account: String,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    /// Event directive.
    #[serde(rename = "event")]
    Event {
        date: String,
        event_type: String,
        value: String,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    /// Note directive.
    #[serde(rename = "note")]
    Note {
        date: String,
        account: String,
        comment: String,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    /// Document directive.
    #[serde(rename = "document")]
    Document {
        date: String,
        account: String,
        path: String,
        /// Tags attached to the document directive (issue #1144).
        #[serde(skip_serializing_if = "Vec::is_empty", default)]
        tags: Vec<String>,
        /// Links attached to the document directive (issue #1144).
        #[serde(skip_serializing_if = "Vec::is_empty", default)]
        links: Vec<String>,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    /// Price directive.
    #[serde(rename = "price")]
    Price {
        date: String,
        currency: String,
        amount: AmountValue,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    /// Query directive.
    #[serde(rename = "query")]
    Query {
        date: String,
        name: String,
        query_string: String,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    /// Custom directive.
    ///
    /// `values` carries the positional arguments after the type
    /// keyword. Each value is a [`TypedValueJson`] tagged union
    /// (`{type, value}`) that preserves the host `MetaValue`
    /// variant tag, so JS consumers can distinguish (for example)
    /// a `Date` from a `String` from an `Account` — all of which
    /// would otherwise collapse to bare JSON strings under the
    /// untagged `MetaValueJson` shape.
    ///
    /// Pre-#1168: `values` was dropped entirely from the JSON output.
    /// Pre-#1207: present but emitted raw via `MetaValueJson` (lossy).
    /// Post-#1207: emitted via `TypedValueJson` (this variant), mirroring
    /// FFI-WASI's `Vec<TypedValue>`.
    ///
    /// Both `values` and `meta` use `skip_serializing_if` to omit
    /// the field when empty (consistent shape: a Custom directive
    /// with no positional args and no metadata serializes as
    /// `{type, date, custom_type}`, matching what the TS shape
    /// declares via `values?` / `meta?`).
    #[serde(rename = "custom")]
    Custom {
        date: String,
        custom_type: String,
        /// Positional values after the `custom TYPE` keyword. Each
        /// entry is a [`TypedValueJson`] (`{type, value}`) — the
        /// tagged shape preserves the host `MetaValue` variant tag so
        /// JS consumers can distinguish a `Date` from a `String` from
        /// an `Account` (closes #1207). Mirrors FFI-WASI's
        /// `Vec<TypedValue>` exactly.
        #[serde(skip_serializing_if = "Vec::is_empty", default)]
        values: Vec<TypedValueJson>,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
}

impl DirectiveJson {
    /// Return the metadata map for this directive, regardless of
    /// which variant it is.
    ///
    /// Every variant carries a `meta` field but the per-variant
    /// destructure pattern means call sites that want to read meta
    /// generically need a 12-arm match. This accessor centralizes
    /// that match so callers don't reimplement it (and so adding a
    /// future variant fails compilation here, not at every call
    /// site).
    ///
    /// **Rust-only API**: not exposed to JavaScript via
    /// `#[wasm_bindgen]`. JS consumers read `directive.meta`
    /// directly off the serialized object — `meta()` only serves
    /// Rust callers (tests in this crate; downstream Rust crates
    /// that consume the WASM-crate types directly).
    #[must_use]
    pub fn meta(&self) -> &HashMap<String, MetaValueJson> {
        match self {
            Self::Transaction { meta, .. }
            | Self::Balance { meta, .. }
            | Self::Open { meta, .. }
            | Self::Close { meta, .. }
            | Self::Commodity { meta, .. }
            | Self::Pad { meta, .. }
            | Self::Event { meta, .. }
            | Self::Note { meta, .. }
            | Self::Document { meta, .. }
            | Self::Price { meta, .. }
            | Self::Query { meta, .. }
            | Self::Custom { meta, .. } => meta,
        }
    }
}

/// A posting in JSON-serializable form.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct PostingJson {
    /// Account name.
    pub account: String,
    /// Units (amount).
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub units: Option<AmountValue>,
    /// Cost specification.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub cost: Option<PostingCostJson>,
    /// Price annotation.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub price: Option<AmountValue>,
    /// Posting-level flag (e.g., `"!"` for pending). Mirrors
    /// `rustledger_core::Posting::flag`.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub flag: Option<String>,
    /// Posting-level metadata (issue #1168). Empty when the posting
    /// has no explicit metadata.
    #[serde(skip_serializing_if = "HashMap::is_empty", default)]
    pub meta: HashMap<String, MetaValueJson>,
}

/// Wire-format of the numeric component of a [`PostingCostJson`].
///
/// Mirrors `rustledger_core::CostNumber` on the wire so JS consumers
/// see the same mutual exclusion the host enforces. Use the `kind`
/// field as the discriminator.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub enum CostNumberJson {
    /// Per-unit cost (e.g., `{100 USD}`).
    PerUnit {
        /// Per-unit value.
        value: String,
    },
    /// Total cost as written (e.g., `{{1000 USD}}`), pre-booking.
    Total {
        /// Total value.
        value: String,
    },
    /// Post-booking derived per-unit with preserved source total.
    PerUnitFromTotal {
        /// Derived per-unit.
        per_unit: String,
        /// Source total.
        total: String,
    },
}

/// A posting cost in JSON-serializable form.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct PostingCostJson {
    /// Cost number (per-unit, total, or post-booking pair).
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub number: Option<CostNumberJson>,
    /// Cost currency.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub currency: Option<String>,
    /// Acquisition date.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub date: Option<String>,
    /// Lot label.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub label: Option<String>,
}

/// Error severity level.
#[derive(
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    Serialize,
    Deserialize,
    rkyv::Archive,
    rkyv::Serialize,
    rkyv::Deserialize,
)]
#[serde(rename_all = "lowercase")]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub enum Severity {
    /// An error that prevents processing.
    Error,
    /// A warning that doesn't prevent processing.
    Warning,
}

/// An error with source location.
///
/// **Renamed to `BeancountError` on the TS side** to avoid shadowing
/// the JS-builtin `Error` type. The Rust struct keeps the shorter
/// `Error` name for internal use; the rename is applied via
/// `#[ts(rename = ...)]` so consumers see a non-shadowing name.
#[derive(
    Debug, Clone, Serialize, Deserialize, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize,
)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(
    feature = "ts-export",
    ts(export, export_to = "bindings/", rename = "BeancountError")
)]
#[cfg_attr(
    feature = "json-schema",
    schemars(
        rename = "BeancountError",
        extend("required" = ["message", "line", "column", "severity"])
    )
)]
pub struct Error {
    /// Error message.
    pub message: String,
    /// Line number (1-based). `null` when the error has no source
    /// location (e.g. validation errors not tied to a span). Field is
    /// always present on the wire (no `skip_serializing_if`); see the
    /// struct-level `schemars(extend)` for the required-and-nullable
    /// rationale. `range(min = 1)` enforces the 1-based documented
    /// contract on the JSON Schema side (schemars defaults to
    /// `minimum: 0` for u32).
    #[cfg_attr(feature = "json-schema", schemars(range(min = 1)))]
    pub line: Option<u32>,
    /// Column number (1-based). `null` when the error has no source
    /// location. See `line` above for `range` rationale.
    #[cfg_attr(feature = "json-schema", schemars(range(min = 1)))]
    pub column: Option<u32>,
    /// Error severity.
    pub severity: Severity,
}

impl Error {
    /// Create a new error with a message.
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            line: None,
            column: None,
            severity: Severity::Error,
        }
    }

    /// Create an error with a line number.
    pub fn with_line(message: impl Into<String>, line: u32) -> Self {
        Self {
            message: message.into(),
            line: Some(line),
            column: None,
            severity: Severity::Error,
        }
    }

    /// Create a warning.
    pub fn warning(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            line: None,
            column: None,
            severity: Severity::Warning,
        }
    }
}

impl From<rustledger_loader::LedgerError> for Error {
    fn from(e: rustledger_loader::LedgerError) -> Self {
        Self {
            message: e.message,
            line: e.location.as_ref().map(|loc| loc.line as u32),
            column: e.location.as_ref().map(|loc| loc.column as u32),
            severity: match e.severity {
                rustledger_loader::ErrorSeverity::Error => Severity::Error,
                rustledger_loader::ErrorSeverity::Warning => Severity::Warning,
            },
        }
    }
}

/// Result of validation.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct ValidationResult {
    /// Whether the ledger is valid.
    pub valid: bool,
    /// Validation errors.
    pub errors: Vec<Error>,
}

/// Result of a BQL query.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct QueryResult {
    /// Column names.
    pub columns: Vec<String>,
    /// Result rows.
    pub rows: Vec<Vec<CellValue>>,
    /// Query errors.
    pub errors: Vec<Error>,
}

/// A cell value that serializes properly to JavaScript.
///
/// Uses untagged serialization to produce clean JSON output.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
#[allow(missing_docs)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub enum CellValue {
    /// Null value.
    Null,
    /// String value.
    String(String),
    /// Integer value. ts-rs defaults `i64` to `bigint`, but the JSON
    /// wire emits it as a plain Number -- override to `number` so the
    /// TS shape matches what JS consumers actually receive.
    Integer(#[cfg_attr(feature = "ts-export", ts(type = "number"))] i64),
    /// Boolean value.
    Boolean(bool),
    /// Amount with number and currency.
    Amount { number: String, currency: String },
    /// Position with units and optional cost.
    Position {
        units: AmountValue,
        #[serde(skip_serializing_if = "Option::is_none")]
        #[cfg_attr(feature = "ts-export", ts(optional))]
        cost: Option<CostValue>,
    },
    /// Inventory with positions.
    Inventory { positions: Vec<PositionValue> },
    /// Set of strings.
    StringSet(Vec<String>),
    /// Generic set of values (for IN operator).
    Set(Vec<Box<Self>>),
    /// Object with key-value pairs (for `entry` and `meta` columns).
    Object(std::collections::HashMap<String, Box<Self>>),
}

/// Amount value for serialization.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct AmountValue {
    /// The number as a string.
    pub number: String,
    /// The currency.
    pub currency: String,
}

/// Position value for serialization.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct PositionValue {
    /// The units.
    pub units: AmountValue,
}

/// Cost value for serialization.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct CostValue {
    /// Cost per unit.
    pub number: String,
    /// Cost currency.
    pub currency: String,
    /// Acquisition date.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub date: Option<String>,
    /// Lot label.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub label: Option<String>,
}

/// Result of formatting.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
// `formatted` is `Option<String>` (nullable) without
// `skip_serializing_if` -- always present on the wire. See
// `ParseResult` for the `extend("required" = ...)` rationale.
#[cfg_attr(
    feature = "json-schema",
    schemars(extend("required" = ["formatted", "errors"]))
)]
pub struct FormatResult {
    /// Formatted source (if successful). Emitted as JSON `null` on
    /// failure; no `skip_serializing_if`, so the field is always
    /// present on the wire.
    pub formatted: Option<String>,
    /// Format errors.
    pub errors: Vec<Error>,
}

/// Result of pad expansion.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct PadResult {
    /// The original directives, verbatim. `Pad` directives are NOT
    /// removed — consumers wanting a pads-removed view should
    /// filter on directive type. The `padding_transactions` field
    /// carries the synthesized P-flag transactions separately.
    pub directives: Vec<DirectiveJson>,
    /// Generated padding transactions (synthesized P-flag, one per
    /// pad-balance pair, multi-currency pads produce one per
    /// currency).
    pub padding_transactions: Vec<DirectiveJson>,
    /// Pad processing errors (e.g. unused pads with no matching
    /// balance assertion).
    pub errors: Vec<Error>,
}

/// Result of running a plugin.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct PluginResult {
    /// Modified directives.
    pub directives: Vec<DirectiveJson>,
    /// Plugin errors/warnings.
    pub errors: Vec<Error>,
}

/// Plugin information.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct PluginInfo {
    /// Plugin name.
    pub name: String,
    /// Plugin description.
    pub description: String,
}

/// BQL completion suggestion for WASM.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct CompletionJson {
    /// The completion text to insert.
    pub text: String,
    /// Category: keyword, function, column, operator, literal.
    pub category: String,
    /// Optional description/documentation.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub description: Option<String>,
}

/// Result of BQL completion request.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct CompletionResultJson {
    /// List of completions.
    pub completions: Vec<CompletionJson>,
    /// Current context for debugging.
    pub context: String,
}

// =============================================================================
// LSP-like Types for Editor Integration
// =============================================================================

/// A completion item for Beancount source editing.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct EditorCompletion {
    /// The label to display in the completion list.
    pub label: String,
    /// The kind of completion item.
    pub kind: CompletionKind,
    /// A human-readable string with additional information.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub detail: Option<String>,
    /// The text to insert when this completion is selected.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub insert_text: Option<String>,
}

/// The kind of a completion item.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub enum CompletionKind {
    /// A keyword (directive name).
    Keyword,
    /// An account name.
    Account,
    /// An account segment (partial account).
    AccountSegment,
    /// A currency/commodity.
    Currency,
    /// A payee name.
    Payee,
    /// A date value.
    Date,
    /// A text/string value.
    Text,
}

/// Result of a completion request.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct EditorCompletionResult {
    /// The completions.
    pub completions: Vec<EditorCompletion>,
    /// The detected context.
    pub context: String,
}

/// Hover information for a symbol.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct EditorHoverInfo {
    /// The hover content (Markdown formatted).
    pub contents: String,
    /// The range of the hovered symbol (optional).
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub range: Option<EditorRange>,
}

/// A range in the document.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct EditorRange {
    /// Start line (0-based).
    pub start_line: u32,
    /// Start character (0-based).
    pub start_character: u32,
    /// End line (0-based).
    pub end_line: u32,
    /// End character (0-based).
    pub end_character: u32,
}

/// A location in the document.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct EditorLocation {
    /// Line number (0-based).
    pub line: u32,
    /// Character offset (0-based).
    pub character: u32,
}

/// A document symbol for the outline view.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct EditorDocumentSymbol {
    /// The name of this symbol.
    pub name: String,
    /// More detail for this symbol.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub detail: Option<String>,
    /// The kind of this symbol.
    pub kind: SymbolKind,
    /// The range enclosing this symbol.
    pub range: EditorRange,
    /// Children of this symbol (e.g., postings in a transaction).
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub children: Option<Vec<Self>>,
    /// Whether this symbol is deprecated (e.g., closed account).
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub deprecated: Option<bool>,
}

/// The kind of a symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub enum SymbolKind {
    /// A transaction.
    Transaction,
    /// An account (open/close).
    Account,
    /// A balance assertion.
    Balance,
    /// A commodity/currency declaration.
    Commodity,
    /// A posting within a transaction.
    Posting,
    /// A pad directive.
    Pad,
    /// An event.
    Event,
    /// A note.
    Note,
    /// A document link.
    Document,
    /// A price.
    Price,
    /// A query definition.
    Query,
    /// A custom directive.
    Custom,
}

// =============================================================================
// References Types
// =============================================================================

/// The kind of symbol being referenced.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub enum ReferenceKind {
    /// An account reference.
    Account,
    /// A currency/commodity reference.
    Currency,
    /// A payee reference.
    Payee,
}

/// A reference to a symbol in the document.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct EditorReference {
    /// The range of this reference.
    pub range: EditorRange,
    /// The kind of reference.
    pub kind: ReferenceKind,
    /// Whether this is the defining occurrence.
    pub is_definition: bool,
    /// Human-readable context (e.g., directive type).
    #[serde(skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "ts-export", ts(optional))]
    pub context: Option<String>,
}

/// Result of a find-references request.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[cfg_attr(feature = "ts-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "json-schema", derive(schemars::JsonSchema))]
#[cfg_attr(feature = "ts-export", ts(export, export_to = "bindings/"))]
pub struct EditorReferencesResult {
    /// The symbol being searched for.
    pub symbol: String,
    /// The kind of symbol.
    pub kind: ReferenceKind,
    /// All references found.
    pub references: Vec<EditorReference>,
}

// Wire-format pins live in a host-only test module: they test
// `serde_json` round-trips which are target-independent, and pulling
// `serde_json` into the wasm32 test target activates a `getrandom`
// transitive that fails to compile on `wasm32-unknown-unknown`
// without the `wasm_js` backend flag. The shape we're pinning is the
// same on every target, so running these on the host is sufficient.
#[cfg(all(test, not(target_arch = "wasm32")))]
mod cost_number_wire_tests {
    //! Wire-format pins for #1164. Catches silent shape drift that
    //! would break TypeScript clients.

    use super::*;

    #[test]
    fn per_unit_serializes_with_kind_tag() {
        let cn = CostNumberJson::PerUnit {
            value: "100".into(),
        };
        let json = serde_json::to_value(&cn).unwrap();
        assert_eq!(
            json,
            serde_json::json!({"kind": "per_unit", "value": "100"})
        );
    }

    #[test]
    fn total_serializes_with_kind_tag() {
        let cn = CostNumberJson::Total {
            value: "1500".into(),
        };
        let json = serde_json::to_value(&cn).unwrap();
        assert_eq!(json, serde_json::json!({"kind": "total", "value": "1500"}));
    }

    #[test]
    fn per_unit_from_total_carries_both_values() {
        let cn = CostNumberJson::PerUnitFromTotal {
            per_unit: "150".into(),
            total: "300".into(),
        };
        let json = serde_json::to_value(&cn).unwrap();
        assert_eq!(
            json,
            serde_json::json!({
                "kind": "per_unit_from_total",
                "per_unit": "150",
                "total": "300",
            })
        );
    }

    #[test]
    fn round_trip_all_variants() {
        for cn in [
            CostNumberJson::PerUnit { value: "1".into() },
            CostNumberJson::Total { value: "10".into() },
            CostNumberJson::PerUnitFromTotal {
                per_unit: "1".into(),
                total: "10".into(),
            },
        ] {
            let json = serde_json::to_string(&cn).unwrap();
            let back: CostNumberJson = serde_json::from_str(&json).unwrap();
            // Same JSON on round-trip means the wire shape is stable.
            assert_eq!(serde_json::to_string(&back).unwrap(), json);
        }
    }

    #[test]
    fn posting_cost_with_total_pre_booking_distinguishes_from_bare_brace() {
        // Pre-PR, a `Total` cost serialized as `{number: null,
        // currency: ...}` — indistinguishable from a deliberate
        // `{USD}` lot match. The new shape preserves the variant.
        let with_total = PostingCostJson {
            number: Some(CostNumberJson::Total {
                value: "1500".into(),
            }),
            currency: Some("USD".into()),
            date: None,
            label: None,
        };
        let bare = PostingCostJson {
            number: None,
            currency: Some("USD".into()),
            date: None,
            label: None,
        };
        let with_total_json = serde_json::to_value(&with_total).unwrap();
        let bare_json = serde_json::to_value(&bare).unwrap();
        assert_ne!(
            with_total_json, bare_json,
            "pre-booking Total and bare {{}} must serialize distinctly"
        );
        assert!(with_total_json["number"].is_object());
        assert!(bare_json.get("number").is_none());
    }
}

/// Codegen vehicle for the JSON Schema export (ADR-0004 Phase 3, #1232).
///
/// `schema_for!(ParseResult)` only walks types reachable from
/// `ParseResult`, which covers parse output but misses the return shapes
/// of `query`, `format`, `validate`, `runPlugin`, `listPlugins`, the BQL
/// completion API, and the editor LSP-like surfaces. Listing every
/// top-level public DTO here gives the generator a single root that
/// reaches the whole wire surface; the resulting schema has every
/// public type under `$defs`.
///
/// **Not a wire-format type.** No `Serialize`/`Deserialize` derive,
/// no `wasm_bindgen` export -- it exists only so that
/// `schema_for!(RustledgerBindings)` produces the union of
/// definitions. The export test then strips the wrapper's own
/// root-level keys (`type`, `title`, `properties`, `required`) before
/// writing the JSON Schema, so consumers see a definitions-only
/// document with no top-level `RustledgerBindings` object -- and
/// datamodel-code-generator does not emit a corresponding Pydantic
/// class. Field types that are reachable transitively (e.g.
/// `Severity` from `BeancountError`, `CompletionKind` from
/// `EditorCompletion`) don't need to be listed.
#[cfg(feature = "json-schema")]
#[derive(schemars::JsonSchema)]
#[allow(dead_code)]
struct RustledgerBindings {
    parse_result: ParseResult,
    validation_result: ValidationResult,
    query_result: QueryResult,
    format_result: FormatResult,
    pad_result: PadResult,
    plugin_result: PluginResult,
    plugin_info: PluginInfo,
    completion_result: CompletionResultJson,
    editor_completion_result: EditorCompletionResult,
    editor_hover_info: EditorHoverInfo,
    editor_document_symbol: EditorDocumentSymbol,
    editor_references_result: EditorReferencesResult,
    // `EditorLocation` is the return type of `getDefinition()` and is
    // not referenced by any of the other listed DTOs, so it needs an
    // explicit field here -- without it the schema/Python bindings
    // silently omit it while the TS bindings still export it.
    editor_location: EditorLocation,
}

/// JSON Schema export entry point (ADR-0004 Phase 3, issue #1232).
///
/// Counterpart to ts-rs's auto-generated `export_bindings_*` tests.
/// Only compiled when the `json-schema` feature is on, which pulls
/// `schemars` into the dep graph. Driven by `scripts/regen-bindings.sh`:
/// the script sets `RUSTLEDGER_REGEN_SCHEMA=1` and runs `cargo test -p
/// rustledger-wasm --features json-schema --lib -- --include-ignored
/// --nocapture --exact types::export_json_schema::export_index_schema`,
/// which writes `bindings/index.schema.json` from the
/// `RustledgerBindings` wrapper above (covers all public DTOs).
///
/// Two opt-in gates protect the source tree:
///   1. `#[ignore]` -- plain `cargo test` skips this.
///   2. `RUSTLEDGER_REGEN_SCHEMA=1` -- a developer running
///      `cargo test --include-ignored` (a common debug command) does
///      NOT silently overwrite the checked-in schema; the test
///      `panic!`s with a guidance message so the failure is loud and
///      visible without needing `--nocapture`. Only the regen script
///      sets the env var.
///
/// The test also prints a unique sentinel on success
/// (`EXPORT_INDEX_SCHEMA_RAN_OK`) which the regen script greps for --
/// catches the case where `cargo test --exact` matches zero tests
/// (e.g. after a future rename) and silently exits 0 with no
/// regeneration.
#[cfg(all(test, feature = "json-schema", not(target_arch = "wasm32")))]
mod export_json_schema {
    use std::fs;
    use std::path::PathBuf;

    use super::RustledgerBindings;

    /// Sentinel string printed on a successful schema write. The regen
    /// script greps for this exact bytes; do not change without
    /// updating `scripts/regen-bindings.sh`.
    pub const SUCCESS_SENTINEL: &str = "EXPORT_INDEX_SCHEMA_RAN_OK";

    #[test]
    #[ignore = "writes bindings/index.schema.json; driven by scripts/regen-bindings.sh"]
    fn export_index_schema() {
        // Belt-and-suspenders guard. `#[ignore]` already prevents an
        // unintentional run, but `--include-ignored` is common enough
        // in debug workflows that we panic (rather than silently
        // returning Ok) so the failure is visible without
        // `--nocapture`. A green-passing test with the env var unset
        // would otherwise mislead a developer into thinking the
        // schema was regenerated.
        assert!(
            std::env::var_os("RUSTLEDGER_REGEN_SCHEMA").is_some(),
            "export_index_schema mutates bindings/index.schema.json and \
             must be driven by scripts/regen-bindings.sh, not invoked \
             directly. Set RUSTLEDGER_REGEN_SCHEMA=1 to opt in."
        );

        let schema = schemars::schema_for!(RustledgerBindings);

        // Round-trip through `serde_json::Value` so we can strip the
        // wrapper's root-level keys. `RustledgerBindings` exists only
        // to seed `$defs` with every public DTO -- its own
        // `type: object, properties: {...}, required: [...]` shape is
        // an internal artifact, not a wire-format contract. Leaving
        // it in causes datamodel-code-generator to emit a public
        // `RustledgerBindings(BaseModel)` class consumers can import
        // (and worse, prefixed-mangled when we try to rename it with
        // a leading underscore). Stripping after generation gives a
        // definitions-only schema (`$schema` + `$defs` only) which
        // datamodel-code-generator handles cleanly: one Pydantic
        // class per `$def`, no wrapper.
        let mut schema_value = serde_json::to_value(&schema)
            .expect("schemars schema should round-trip through serde_json");
        if let Some(obj) = schema_value.as_object_mut() {
            obj.remove("type");
            obj.remove("title");
            obj.remove("properties");
            obj.remove("required");
            obj.remove("additionalProperties");
            // The wrapper's rustdoc gets emitted as `description`.
            // Drop it -- datamodel-code-generator otherwise treats the
            // root as a documented type and emits a placeholder
            // `Model(RootModel[Any])` class.
            obj.remove("description");
        }

        // Pretty-print to stabilize the on-disk format for git diffs;
        // the regen script later runs prettier over it for a final
        // canonicalization pass alongside the TS bundle.
        let pretty = serde_json::to_string_pretty(&schema_value)
            .expect("stripped schema should serialize cleanly");

        let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        path.push("bindings");
        fs::create_dir_all(&path).expect("create bindings/ directory");
        path.push("index.schema.json");
        fs::write(&path, format!("{pretty}\n")).expect("write index.schema.json");

        // Sentinel for `scripts/regen-bindings.sh` to grep for.
        // `println!` (stdout, not stderr) makes it survive `--quiet`
        // when the script pipes cargo output through `tee`.
        println!("{SUCCESS_SENTINEL}");
        eprintln!("Wrote: {}", path.display());
    }
}

/// Guards the DTOs that hand-override schemars' auto-detected `required`
/// array via `schemars(extend("required" = [...]))`.
///
/// `extend("required" = ...)` *replaces* the auto-detected array rather
/// than merging into it (schemars 1.x has no merge form). So if a field
/// is added to one of these structs and the author forgets to update the
/// hand-written list, that field silently drops out of `required` even
/// though the wire always emits it -- with no compile error and no other
/// test catching it. (PR #1241's round-2 review found exactly this: the
/// round-1 `extend` sweep missed `FormatResult`.)
///
/// Every field on these four DTOs is a required wire field -- the
/// nullable ones (`ParseResult.ledger`, `LedgerOptions.title`,
/// `BeancountError.line/column`, `FormatResult.formatted`) are
/// always-present-but-nullable, never absent. So the invariant is exact:
/// the emitted `required` set must equal the full property set. If you
/// add a genuinely-optional field to one of these structs, this test is
/// the tripwire -- update it deliberately alongside the `extend` list.
#[cfg(all(test, feature = "json-schema", not(target_arch = "wasm32")))]
mod schema_required_invariants {
    use std::collections::BTreeSet;

    use super::RustledgerBindings;

    /// Assert the `$def` for `def_name` lists every one of its
    /// properties in `required`.
    fn assert_required_equals_all_properties(def_name: &str) {
        let schema = schemars::schema_for!(RustledgerBindings);
        let value = serde_json::to_value(&schema).expect("schema round-trips through serde_json");

        let def = value
            .get("$defs")
            .and_then(|d| d.get(def_name))
            .unwrap_or_else(|| panic!("{def_name} missing from $defs"));

        let properties: BTreeSet<&str> = def
            .get("properties")
            .and_then(serde_json::Value::as_object)
            .unwrap_or_else(|| panic!("{def_name} has no properties object"))
            .keys()
            .map(String::as_str)
            .collect();

        let required: BTreeSet<&str> = def
            .get("required")
            .and_then(serde_json::Value::as_array)
            .unwrap_or_else(|| {
                panic!("{def_name}.required is missing -- did schemars(extend) get dropped?")
            })
            .iter()
            .map(|v| v.as_str().expect("required entry should be a string"))
            .collect();

        assert_eq!(
            required, properties,
            "{def_name}: the schemars(extend(\"required\" = [...])) list is out of \
             sync with the struct's fields. Every field on this DTO is a required \
             wire field, so `required` must list all of them. Update the \
             extend(\"required\") attribute on the struct in types.rs (and this \
             test, if you intentionally introduced an optional field)."
        );
    }

    #[test]
    fn parse_result_requires_all_fields() {
        assert_required_equals_all_properties("ParseResult");
    }

    #[test]
    fn ledger_options_requires_all_fields() {
        assert_required_equals_all_properties("LedgerOptions");
    }

    #[test]
    fn beancount_error_requires_all_fields() {
        assert_required_equals_all_properties("BeancountError");
    }

    #[test]
    fn format_result_requires_all_fields() {
        assert_required_equals_all_properties("FormatResult");
    }
}
