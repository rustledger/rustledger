//! WASM Plugin Interface Types for rustledger
//!
//! This crate provides the type definitions for rustledger's WASM plugin interface.
//! Use it as a dependency in your plugin crate to ensure type compatibility with
//! the rustledger host.
//!
//! # Two subsystems
//!
//! Rustledger has two distinct WASM plugin subsystems, and this crate hosts
//! the shared types for both:
//!
//! - **Directive plugins** transform the directive stream *after* parsing
//!   (tagging, dedup, categorization). Required export: `process`. Host
//!   loader: `rustledger-plugin`. The Quick Start below covers this case.
//! - **WASM importers** turn bank-statement files *into* directives.
//!   Required exports: `metadata`, `identify`, `extract`, `extract_enriched`.
//!   Host loader: `rustledger-importer::WasmImporter`. Use the
//!   `wasm_importer_main!` macro (behind the `guest` feature) to generate
//!   the boilerplate. See the [`guest`] module for details.
//!
//! # Directive-Plugin Quick Start
//!
//! Use the [`wasm_plugin_main!`] macro (behind the `guest` feature) to
//! generate the required `alloc` + `process` exports from a single
//! user fn. Add this to your plugin's `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rustledger-plugin-types = { version = "0.15", features = ["guest"] }
//! ```
//!
//! Then in your plugin:
//!
//! ```rust,ignore
//! use rustledger_plugin_types::{
//!     PluginInput, PluginOutput, wasm_plugin_main,
//! };
//!
//! fn process(input: PluginInput) -> PluginOutput {
//!     // Simplest case: keep every input unchanged.
//!     PluginOutput::passthrough(input.directives.len())
//! }
//!
//! wasm_plugin_main! {
//!     process: process,
//! }
//! ```
//!
//! See the [`guest`] module for the full macro reference (including
//! the once-per-crate constraint on the `wasm32` target). If you need
//! to write the `extern "C"` exports manually — for finer control or
//! to avoid the `guest` feature — see the "Without the macro" section
//! in the crate README.
//!
//! # Serialization Format
//!
//! Plugins communicate with the host via `MessagePack` serialization. The host
//! calls `process(ptr, len)` with a pointer to MessagePack-encoded [`PluginInput`].
//! The plugin returns a packed u64 containing a pointer and length to
//! MessagePack-encoded [`PluginOutput`].
//!
//! # Memory Management
//!
//! Plugins must export an `alloc(size: u32) -> *mut u8` function. The host uses
//! this to allocate memory in the WASM linear memory for passing input data.
//! The plugin uses it to allocate memory for output data.
//!
//! Optionally, plugins can export a `dealloc(ptr: *mut u8, size: u32)` function
//! to free memory. This is not required by the host but can be useful for
//! memory management within longer-running plugin operations.
//!
//! # Version Compatibility
//!
//! Plugin types are versioned with rustledger. For best compatibility, use the
//! same minor version of `rustledger-plugin-types` as the rustledger host you're
//! targeting (e.g., `0.15.x` for rustledger `0.15.x`).
//!
//! # Building
//!
//! Build your plugin for the WASM target:
//!
//! ```sh
//! rustup target add wasm32-unknown-unknown
//! cargo build --target wasm32-unknown-unknown --release
//! ```
//!
//! The output will be in `target/wasm32-unknown-unknown/release/your_plugin.wasm`
//!
//! # WASM-Importer Quick Start
//!
//! Importers read source files (CSV, OFX, …) and emit directives. The host
//! loader lives in `rustledger-importer`; the wire format and a
//! boilerplate-eliminating macro live here.
//!
//! Enable the `guest` feature, then use `wasm_importer_main!`:
//!
//! ```toml
//! [dependencies]
//! rustledger-plugin-types = { version = "0.15", features = ["guest"] }
//! ```
//!
//! ```rust,ignore
//! use rustledger_plugin_types::{
//!     DirectiveData, DirectiveWrapper, ImporterInput, ImporterOutput,
//!     OpenData, wasm_importer_main,
//! };
//!
//! fn identify(path: &str) -> bool {
//!     path.ends_with(".mybank")
//! }
//!
//! fn extract(input: ImporterInput) -> ImporterOutput {
//!     // Parse input.content; emit DirectiveWrapper values.
//!     ImporterOutput::new(vec![/* … */])
//! }
//!
//! wasm_importer_main! {
//!     name: "my-bank",
//!     description: "MyBank CSV statements",
//!     identify: identify,
//!     extract: extract,
//!     // `extract_enriched` is auto-generated as a Default-categorization
//!     // passthrough. Add `extract_enriched: my_fn` to override.
//! }
//! ```
//!
//! Importer ABI types defined in this crate: [`ImporterInput`],
//! [`IdentifyInput`], [`IdentifyOutput`], [`ImporterOutput`],
//! [`EnrichedImporterOutput`], [`MetadataOutput`], [`EnrichmentWrapper`],
//! [`AlternativeWrapper`].
//!
//! Wire-format method strings for `EnrichmentWrapper::method`: `"rule"`,
//! `"merchant-dict"` (hyphen, not underscore), `"ml"`, `"llm"`, `"manual"`,
//! `"default"`. Unknown values trigger a host warning and fall back to
//! `Default`.

#![warn(missing_docs)]

#[cfg(feature = "guest")]
pub mod guest;

use serde::{Deserialize, Serialize};

// ============================================================================
// Top-Level Plugin Interface
// ============================================================================

/// Input passed to a plugin.
///
/// The host serializes this struct via `MessagePack` and passes it to the
/// plugin's `process` function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginInput {
    /// All directives to process.
    pub directives: Vec<DirectiveWrapper>,
    /// Ledger options.
    pub options: PluginOptions,
    /// Plugin-specific configuration string (from the plugin directive).
    ///
    /// For example, `plugin "myplugin.wasm" "threshold=100"` would set
    /// `config` to `Some("threshold=100")`.
    pub config: Option<String>,
}

/// Output returned from a plugin.
///
/// The plugin serializes this struct via `MessagePack` and returns a pointer
/// to it from the `process` function.
///
/// Output is an **ordered sequence of operations** ([`PluginOp`]) — not a
/// replacement list of directives. The host materializes the resulting
/// directive list by walking the ops in order, preserving the original
/// source span / `file_id` for `Keep` and `Modify` ops so plugin-transformed
/// directives retain byte-precise source locations for error reporting.
///
/// Every input directive index must appear in EXACTLY ONE op across
/// `Keep` / `Modify` / `Delete`; the host validates this and emits a
/// plugin error if the invariant is violated.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginOutput {
    /// Ordered operations that describe the resulting directive list.
    pub ops: Vec<PluginOp>,
    /// Errors generated by the plugin.
    pub errors: Vec<PluginError>,
}

impl PluginOutput {
    /// Create an output that passes through every input directive unchanged.
    /// `len` is the number of input directives.
    #[must_use]
    pub fn passthrough(len: usize) -> Self {
        Self {
            ops: (0..len).map(PluginOp::Keep).collect(),
            errors: Vec::new(),
        }
    }
}

/// One operation in a [`PluginOutput`]'s ordered op list.
///
/// Ops describe how each output directive relates to the input:
/// - [`PluginOp::Keep`] — reuse `input[i]` unchanged. Span and
///   `file_id` preserved.
/// - [`PluginOp::Modify`] — output a new wrapper, but inherit `input[i]`'s
///   source identity (span / `file_id`). Plugins use this when transforming
///   an existing directive's content (e.g., adding tags) so error
///   reporting still points at the original source location.
/// - [`PluginOp::Insert`] — emit a fresh directive with synthesized
///   source location (`SYNTHESIZED_FILE_ID`, zero span). Use for
///   directives the plugin invents from scratch.
/// - [`PluginOp::Delete`] — drop `input[i]`. Must be explicit; omitting
///   an index without `Delete` is a protocol violation that the host
///   reports as a plugin error.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PluginOp {
    /// Reuse `input[i]` unchanged (preserves original span + `file_id`).
    Keep(usize),
    /// Replace `input[i]`'s content with `wrapper`, but inherit
    /// `input[i]`'s source identity (span + `file_id`).
    Modify(usize, DirectiveWrapper),
    /// Insert a fresh directive with synthesized source location.
    Insert(DirectiveWrapper),
    /// Drop `input[i]`. Must be explicit — see type-level docs.
    Delete(usize),
}

/// Ledger options passed to plugins.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct PluginOptions {
    /// Operating currencies (from `option "operating_currency" "USD"`).
    pub operating_currencies: Vec<String>,
    /// Ledger title (from `option "title" "My Ledger"`).
    pub title: Option<String>,
}

// ============================================================================
// Plugin Errors
// ============================================================================

/// Error generated by a plugin.
///
/// Use [`PluginError::error`] or [`PluginError::warning`] to create errors,
/// and optionally chain [`PluginError::at`] to set the source location.
///
/// # Example
///
/// ```
/// use rustledger_plugin_types::{PluginError, PluginErrorSeverity};
///
/// let error = PluginError::error("Invalid transaction")
///     .at("ledger.beancount", 42);
///
/// let warning = PluginError::warning("Duplicate entry detected");
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginError {
    /// Error message.
    pub message: String,
    /// Source file (if known).
    pub source_file: Option<String>,
    /// Line number (if known).
    pub line_number: Option<u32>,
    /// Error severity.
    pub severity: PluginErrorSeverity,
}

/// Severity of a plugin error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PluginErrorSeverity {
    /// Warning - processing continues.
    #[serde(rename = "warning")]
    Warning,
    /// Error - ledger is marked invalid.
    #[serde(rename = "error")]
    Error,
}

impl PluginError {
    /// Create a new error.
    #[must_use]
    pub fn error(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            source_file: None,
            line_number: None,
            severity: PluginErrorSeverity::Error,
        }
    }

    /// Create a new warning.
    #[must_use]
    pub fn warning(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            source_file: None,
            line_number: None,
            severity: PluginErrorSeverity::Warning,
        }
    }

    /// Set the source location.
    #[must_use]
    pub fn at(mut self, file: impl Into<String>, line: u32) -> Self {
        self.source_file = Some(file.into());
        self.line_number = Some(line);
        self
    }
}

// ============================================================================
// Directive Types
// ============================================================================

/// A wrapper around directives for serialization.
///
/// This wrapper provides a uniform interface for all directive types,
/// with source location tracking for error reporting.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DirectiveWrapper {
    /// The type of directive (derived from data, not serialized to avoid duplicate keys).
    #[serde(skip_serializing, default)]
    pub directive_type: String,
    /// The directive date (YYYY-MM-DD format).
    pub date: String,
    /// Source filename (for tracking through plugin processing).
    /// If None, the directive was created by a plugin.
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub filename: Option<String>,
    /// Source line number (1-based).
    /// If None, the directive was created by a plugin.
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub lineno: Option<u32>,
    /// Directive-specific data as a nested structure.
    #[serde(flatten)]
    pub data: DirectiveData,
}

impl DirectiveWrapper {
    /// Returns the sort order for directive types, matching Python beancount's `SORT_ORDER`.
    ///
    /// Order ensures logical processing:
    /// - Open (-2): Accounts must be opened first
    /// - Balance (-1): Balance assertions checked before transactions
    /// - Default (0): Transactions, Commodity, Pad, Event, Note, Price, Query, Custom
    /// - Document (1): Documents recorded after transactions
    /// - Close (2): Accounts closed last
    #[must_use]
    pub const fn type_sort_order(&self) -> i8 {
        match &self.data {
            DirectiveData::Open(_) => -2,
            DirectiveData::Balance(_) => -1,
            DirectiveData::Document(_) => 1,
            DirectiveData::Close(_) => 2,
            _ => 0,
        }
    }

    /// Returns a sort key tuple matching Python beancount's `entry_sortkey()`.
    ///
    /// Sorts by: (date, `type_order`, lineno)
    #[must_use]
    pub fn sort_key(&self) -> (&str, i8, u32) {
        (
            &self.date,
            self.type_sort_order(),
            self.lineno.unwrap_or(u32::MAX),
        )
    }
}

/// Directive-specific data.
///
/// Each variant corresponds to a Beancount directive type.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum DirectiveData {
    /// Transaction data.
    #[serde(rename = "transaction")]
    Transaction(TransactionData),
    /// Balance assertion data.
    #[serde(rename = "balance")]
    Balance(BalanceData),
    /// Open account data.
    #[serde(rename = "open")]
    Open(OpenData),
    /// Close account data.
    #[serde(rename = "close")]
    Close(CloseData),
    /// Commodity declaration data.
    #[serde(rename = "commodity")]
    Commodity(CommodityData),
    /// Pad directive data.
    #[serde(rename = "pad")]
    Pad(PadData),
    /// Event data.
    #[serde(rename = "event")]
    Event(EventData),
    /// Note data.
    #[serde(rename = "note")]
    Note(NoteData),
    /// Document data.
    #[serde(rename = "document")]
    Document(DocumentData),
    /// Price data.
    #[serde(rename = "price")]
    Price(PriceData),
    /// Query data.
    #[serde(rename = "query")]
    Query(QueryData),
    /// Custom directive data.
    #[serde(rename = "custom")]
    Custom(CustomData),
}

// ============================================================================
// Transaction Types
// ============================================================================

/// Transaction data for serialization.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransactionData {
    /// Transaction flag (`*` for complete, `!` for incomplete/pending).
    pub flag: String,
    /// Optional payee.
    pub payee: Option<String>,
    /// Narration/description.
    pub narration: String,
    /// Tags without the `#` prefix.
    pub tags: Vec<String>,
    /// Links without the `^` prefix.
    pub links: Vec<String>,
    /// Metadata key-value pairs.
    pub metadata: Vec<(String, MetaValueData)>,
    /// Postings.
    pub postings: Vec<PostingData>,
}

/// Source-location metadata for a posting that the host parsed from a
/// beancount file.
///
/// Plugins receive this on every parser-derived posting and **must**
/// preserve it unchanged when modifying an existing posting (the default
/// for a typical "edit one field" plugin). When a plugin synthesizes a
/// brand-new posting, leave [`PostingData::span`] as `None` and the host
/// will mark it `SYNTHESIZED_FILE_ID`.
///
/// Byte offsets are stored as `u64` so the wire format is stable
/// across 32-bit (WASM) and 64-bit (host) targets, and so very large
/// concatenated source trees (includes-of-includes) cannot silently
/// overflow. The contents are otherwise opaque to plugin code: do
/// not synthesize spans by guessing offsets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceSpan {
    /// Start byte offset within the file (inclusive).
    pub start: u64,
    /// End byte offset within the file (exclusive).
    pub end: u64,
    /// Source file index in the host's source map.
    pub file_id: u16,
}

/// Posting data for serialization.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PostingData {
    /// Account name (e.g., `Assets:Bank:Checking`).
    pub account: String,
    /// Units (amount + currency). None for auto-balanced postings.
    pub units: Option<AmountData>,
    /// Cost specification (for lot tracking).
    pub cost: Option<CostData>,
    /// Price annotation (@ or @@).
    pub price: Option<PriceAnnotationData>,
    /// Optional posting flag.
    pub flag: Option<String>,
    /// Posting metadata.
    pub metadata: Vec<(String, MetaValueData)>,
    /// Source location of the posting line in the file the host parsed
    /// from, if any. Plugins **must preserve** this unchanged when
    /// modifying an existing posting; set to `None` only for postings
    /// the plugin itself synthesizes. See [`SourceSpan`] for details.
    #[serde(default)]
    pub span: Option<SourceSpan>,
}

/// Amount data for serialization.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AmountData {
    /// Number as string (preserves precision).
    pub number: String,
    /// Currency code.
    pub currency: String,
}

/// Cost data for serialization.
///
/// Represents cost specifications like `{100 USD}` or `{100 USD, 2024-01-01, "lot1"}`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CostData {
    /// Per-unit cost number.
    pub number_per: Option<String>,
    /// Total cost number.
    pub number_total: Option<String>,
    /// Cost currency.
    pub currency: Option<String>,
    /// Acquisition date.
    pub date: Option<String>,
    /// Lot label.
    pub label: Option<String>,
    /// Merge lots flag.
    pub merge: bool,
}

/// Price annotation data.
///
/// Represents price annotations like `@ 100 USD` or `@@ 1000 USD`
/// (total price).
///
/// # Type-safe consumption (recommended)
///
/// Use [`PriceAnnotationData::view`] to get a [`PriceAnnotationView`]
/// — a typed enum that forces consumers to handle `Unit` and `Total`
/// arms exhaustively at compile time. **All new code that needs to
/// distinguish per-unit from total prices MUST use `view()`** rather
/// than reading `is_total` directly.
///
/// This struct is the wire format (kept for serialization stability
/// across the WASM plugin boundary). The `view()` enum is a shaped
/// accessor on top.
///
/// Pre-refactor (issue #992), the `implicit_prices` plugin read
/// `posting.price.amount` directly and silently ignored `is_total`,
/// emitting `@@` total amounts as per-unit prices. The fix in #997
/// added explicit handling, but the type system didn't catch the bug
/// originally because nothing forced consumers to read the bool. The
/// `view()` enum closes that loop: a missing match arm is a compile
/// error.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PriceAnnotationData {
    /// Whether this is a total price (`@@`) vs per-unit (`@`).
    ///
    /// **Prefer [`PriceAnnotationData::view`] for new code** — reading
    /// this field directly is the bug shape that produced #992
    /// (consumer ignores the field and treats every annotation as
    /// per-unit). The `view()` enum forces exhaustive handling at
    /// compile time.
    pub is_total: bool,
    /// The price amount (optional for incomplete/empty prices).
    pub amount: Option<AmountData>,
    /// The number only (for incomplete prices).
    pub number: Option<String>,
    /// The currency only (for incomplete prices).
    pub currency: Option<String>,
}

/// Typed view of a [`PriceAnnotationData`].
///
/// Each arm distinguishes per-unit (`@`) from total (`@@`) at the
/// **type level**, so a `match` on the view forces consumers to
/// handle both cases. This is the recommended way to consume price
/// annotations — see the docstring on [`PriceAnnotationData`] for the
/// motivating bug.
#[derive(Debug, Clone, Copy)]
pub enum PriceAnnotationView<'a> {
    /// `@ AMOUNT` — per-unit price with a complete amount.
    Unit(&'a AmountData),
    /// `@@ AMOUNT` — total price with a complete amount.
    ///
    /// Consumers that compute prices MUST divide by the posting's
    /// `units.number.abs()` to recover the per-unit price. See
    /// `rustledger_core::extract_per_unit_price` (in the
    /// `rustledger-core` crate; not linked because that crate is not a
    /// dependency of `rustledger-plugin-types`).
    Total(&'a AmountData),
    /// `@ NUMBER` / `@ CURRENCY` — per-unit annotation missing one
    /// or both of (number, currency).
    UnitIncomplete {
        /// The number, if present.
        number: Option<&'a str>,
        /// The currency, if present.
        currency: Option<&'a str>,
    },
    /// `@@ NUMBER` / `@@ CURRENCY` — incomplete total annotation.
    TotalIncomplete {
        /// The number, if present.
        number: Option<&'a str>,
        /// The currency, if present.
        currency: Option<&'a str>,
    },
}

impl PriceAnnotationData {
    /// Get a typed view that distinguishes per-unit from total at
    /// the type level. **Use this for new code that needs to handle
    /// the price differently based on `@` vs `@@`.**
    ///
    /// Returns one of four variants — a missing match arm at the
    /// consumer becomes a compile error, eliminating the class of
    /// bug that produced issue #992.
    #[must_use]
    pub fn view(&self) -> PriceAnnotationView<'_> {
        match (self.is_total, &self.amount) {
            (false, Some(a)) => PriceAnnotationView::Unit(a),
            (true, Some(a)) => PriceAnnotationView::Total(a),
            (false, None) => PriceAnnotationView::UnitIncomplete {
                number: self.number.as_deref(),
                currency: self.currency.as_deref(),
            },
            (true, None) => PriceAnnotationView::TotalIncomplete {
                number: self.number.as_deref(),
                currency: self.currency.as_deref(),
            },
        }
    }
}

// ============================================================================
// Metadata Types
// ============================================================================

/// Metadata value for serialization.
///
/// Metadata can hold various types of values, preserving type information
/// for accurate round-tripping.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", content = "value")]
pub enum MetaValueData {
    /// String value.
    #[serde(rename = "string")]
    String(String),
    /// Number value (as string to preserve precision).
    #[serde(rename = "number")]
    Number(String),
    /// Date value (YYYY-MM-DD).
    #[serde(rename = "date")]
    Date(String),
    /// Account reference.
    #[serde(rename = "account")]
    Account(String),
    /// Currency reference.
    #[serde(rename = "currency")]
    Currency(String),
    /// Tag reference.
    #[serde(rename = "tag")]
    Tag(String),
    /// Link reference.
    #[serde(rename = "link")]
    Link(String),
    /// Amount value.
    #[serde(rename = "amount")]
    Amount(AmountData),
    /// Boolean value.
    #[serde(rename = "bool")]
    Bool(bool),
}

// ============================================================================
// Other Directive Types
// ============================================================================

/// Balance assertion data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BalanceData {
    /// Account name.
    pub account: String,
    /// Expected balance.
    pub amount: AmountData,
    /// Tolerance for balance check.
    pub tolerance: Option<String>,
    /// Metadata key-value pairs.
    #[serde(default)]
    pub metadata: Vec<(String, MetaValueData)>,
}

/// Open account data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OpenData {
    /// Account name.
    pub account: String,
    /// Allowed currencies (empty means any currency).
    pub currencies: Vec<String>,
    /// Booking method (FIFO, LIFO, etc.).
    pub booking: Option<String>,
    /// Metadata key-value pairs.
    #[serde(default)]
    pub metadata: Vec<(String, MetaValueData)>,
}

/// Close account data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CloseData {
    /// Account name.
    pub account: String,
    /// Metadata key-value pairs.
    #[serde(default)]
    pub metadata: Vec<(String, MetaValueData)>,
}

/// Commodity declaration data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CommodityData {
    /// Currency code.
    pub currency: String,
    /// Metadata key-value pairs.
    #[serde(default)]
    pub metadata: Vec<(String, MetaValueData)>,
}

/// Pad directive data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PadData {
    /// Account to pad.
    pub account: String,
    /// Source account for padding.
    pub source_account: String,
    /// Metadata key-value pairs.
    #[serde(default)]
    pub metadata: Vec<(String, MetaValueData)>,
}

/// Event data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EventData {
    /// Event type.
    pub event_type: String,
    /// Event value.
    pub value: String,
    /// Metadata key-value pairs.
    #[serde(default)]
    pub metadata: Vec<(String, MetaValueData)>,
}

/// Note data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NoteData {
    /// Account name.
    pub account: String,
    /// Note comment.
    pub comment: String,
    /// Metadata key-value pairs.
    #[serde(default)]
    pub metadata: Vec<(String, MetaValueData)>,
}

/// Document data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocumentData {
    /// Account name.
    pub account: String,
    /// Document path.
    pub path: String,
    /// Metadata key-value pairs.
    #[serde(default)]
    pub metadata: Vec<(String, MetaValueData)>,
}

/// Price directive data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PriceData {
    /// Currency being priced.
    pub currency: String,
    /// Price amount.
    pub amount: AmountData,
    /// Metadata key-value pairs.
    #[serde(default)]
    pub metadata: Vec<(String, MetaValueData)>,
}

/// Query directive data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueryData {
    /// Query name.
    pub name: String,
    /// Query string (BQL).
    pub query: String,
    /// Metadata key-value pairs.
    #[serde(default)]
    pub metadata: Vec<(String, MetaValueData)>,
}

/// Custom directive data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CustomData {
    /// Custom type (first value after `custom` keyword).
    pub custom_type: String,
    /// Values preserving their types.
    pub values: Vec<MetaValueData>,
    /// Metadata key-value pairs.
    #[serde(default)]
    pub metadata: Vec<(String, MetaValueData)>,
}

// ============================================================================
// Importer ABI (wave 2.3: WASM-loaded importers)
// ============================================================================
//
// These types are the wire format spoken between the rustledger host and
// a WASM-loaded importer plugin (e.g. `rustledger-importer-mt940.wasm`).
//
// # Sandbox model
//
// WASM importers run in the same locked-down sandbox as directive plugins
// (no filesystem, no network, no environment, no syscalls). The host reads
// the source file and passes its bytes via [`ImporterInput::content`] —
// the WASM importer does NOT open the file itself.
//
// # MessagePack contract
//
// All ABI types travel between host and guest as MessagePack-encoded byte
// slices via `rmp_serde`. We use rmp-serde's **default positional struct
// encoding** (compact arrays of values, no field names on the wire). This
// is faster and smaller than map encoding at the cost of being strict
// about field order.
//
// # Versioning
//
// We do not maintain wire-format backward compatibility. Any field
// addition, removal, reorder, or type change is a major-version break
// for the WASM ABI. Users of WASM importer modules are expected to
// rebuild their importer against the host version they're targeting —
// the host's ABI version (exposed via `wave-2.3 release notes`) is the
// authoritative reference.
//
// Rationale: pre-v1.0 we ship structural changes freely; locking serde
// `default`-tolerance into v1.0 would force every future ABI evolution
// to be additive and live with a growing tail of compat shims. We'd
// rather bump majors.

/// Wire-format input passed from the host to a WASM importer's
/// `extract` / `extract_enriched` entry point.
///
/// # `options` design note
///
/// The `options` map is `String -> String`. Values that are
/// semantically numbers, booleans, or other types (e.g.
/// `skip_rows = 5`, `has_header = true`, `delimiter = ","`) are
/// string-encoded on the host side and parsed by the WASM importer.
/// This keeps the WASM ABI minimal (no `serde_json::Value` or `rmpv`
/// dep in the guest crate) at the cost of pushing string parsing into
/// every importer. A future additive field (`options_typed`) could
/// carry typed values if needed; not in v1.0 scope.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImporterInput {
    /// Source file path. Informational only — the WASM sandbox cannot
    /// open this. Used for diagnostics and fingerprint generation.
    pub path: String,
    /// File content bytes. The host reads the file and forwards the
    /// bytes here so the WASM importer doesn't need filesystem access.
    pub content: Vec<u8>,
    /// Target account for imported transactions
    /// (from `ImporterConfig.account`).
    pub account: String,
    /// Currency for amounts (from `ImporterConfig.currency`).
    pub currency: Option<String>,
    /// Free-form importer-specific options. The host serializes
    /// `importers.toml` entries' arbitrary fields into this map; the
    /// WASM importer reads the keys it knows about. Keeps the
    /// wire format independent of any host-side config struct shape.
    /// See the type-level doc for the string-encoding trade-off.
    pub options: std::collections::HashMap<String, String>,
}

/// Wire-format input to a WASM importer's `identify` entry point.
///
/// The WASM importer answers "do I handle this file?" based on the
/// path (typically extension) alone — `extract` is the path that
/// gets file content.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IdentifyInput {
    /// Source file path. Same lossy-utf8 caveat as
    /// [`ImporterInput::path`].
    pub path: String,
}

/// Wire-format output from a WASM importer's `identify`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IdentifyOutput {
    /// True if this importer handles the file at `IdentifyInput.path`.
    pub matches: bool,
}

/// Wire-format output from a WASM importer's `metadata` entry point.
/// Returned once at load time and cached by the host registry — used
/// for `Importer::name()` and `Importer::description()` on the wrapper.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetadataOutput {
    /// Importer name (e.g. `"MT940"`, `"FinTS"`). Used by the registry
    /// for `find_by_name` lookups.
    pub name: String,
    /// Human-readable description for `--list-importers` and similar.
    pub description: String,
}

/// Wire-format output returned from a WASM importer's `extract`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImporterOutput {
    /// Extracted directives.
    pub directives: Vec<DirectiveWrapper>,
    /// Warnings encountered during extraction (non-fatal).
    pub warnings: Vec<String>,
    /// Fatal-but-recoverable errors (e.g. malformed individual rows
    /// the importer chose to skip rather than abort on). Distinct from
    /// `warnings` (informational) and from a WASM trap (which the host
    /// surfaces as an `anyhow::Error`). Reuses the existing
    /// [`PluginError`] shape so importer errors flow into the same
    /// `LedgerError::location` path as plugin errors.
    pub errors: Vec<PluginError>,
}

impl ImporterOutput {
    /// Create an output with no warnings or errors.
    #[must_use]
    pub const fn new(directives: Vec<DirectiveWrapper>) -> Self {
        Self {
            directives,
            warnings: Vec::new(),
            errors: Vec::new(),
        }
    }

    /// Empty result with no directives, no warnings, no errors.
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            directives: Vec::new(),
            warnings: Vec::new(),
            errors: Vec::new(),
        }
    }
}

/// Wire-format output returned from a WASM importer's
/// `extract_enriched`. Each directive is paired with per-directive
/// categorization metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnrichedImporterOutput {
    /// Directive–enrichment pairs, parallel to `ImporterOutput.directives`.
    pub entries: Vec<(DirectiveWrapper, EnrichmentWrapper)>,
    /// Warnings encountered during extraction (non-fatal).
    pub warnings: Vec<String>,
    /// Fatal-but-recoverable errors. Same semantics as
    /// [`ImporterOutput::errors`].
    pub errors: Vec<PluginError>,
}

/// Wire-format counterpart to `rustledger_ops::enrichment::Enrichment`.
///
/// Kept here (rather than in `rustledger-ops`) so the importer ABI is
/// self-contained — WASM importers depend on `rustledger-plugin-types`
/// and shouldn't pull in the larger `rustledger-ops` graph just for an
/// enrichment definition. The host converts between the two shapes at
/// the trait boundary.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnrichmentWrapper {
    /// Index of the directive this enrichment applies to (parallel to
    /// `EnrichedImporterOutput.entries`).
    pub directive_index: usize,
    /// Confidence score for the primary categorization (0.0 to 1.0).
    pub confidence: f64,
    /// How the primary categorization was determined. String-encoded
    /// to avoid pinning the `CategorizationMethod` enum's exact variant
    /// set into the wire format. Must match
    /// `CategorizationMethod::as_meta_value()` in `rustledger-ops`:
    /// `"rule"`, `"merchant-dict"`, `"ml"`, `"llm"`, `"default"`,
    /// `"manual"`. (Note: `merchant-dict` uses a hyphen, not an
    /// underscore — the host string-matches against
    /// `as_meta_value()`'s output, so the wire format must agree.)
    pub method: String,
    /// Other possible categorizations, sorted by confidence descending.
    pub alternatives: Vec<AlternativeWrapper>,
    /// Stable fingerprint for deduplication, serialized as a hex string.
    pub fingerprint: Option<String>,
}

/// Wire-format counterpart to `rustledger_ops::enrichment::Alternative`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlternativeWrapper {
    /// Account this alternative would assign.
    pub account: String,
    /// Confidence score for this alternative (0.0 to 1.0).
    pub confidence: f64,
    /// How this alternative was determined. Same encoding rules as
    /// [`EnrichmentWrapper::method`].
    pub method: String,
}

// ============================================================================
// Utility Functions
// ============================================================================

/// Sort directives using beancount's standard ordering.
///
/// This matches Python beancount's `entry_sortkey()`:
/// 1. Primary: date
/// 2. Secondary: directive type (Open, Balance, default, Document, Close)
/// 3. Tertiary: line number (preserves file order for same-date, same-type entries)
pub fn sort_directives(directives: &mut [DirectiveWrapper]) {
    directives.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_plugin_error_builder() {
        let error = PluginError::error("test error").at("file.beancount", 10);
        assert_eq!(error.message, "test error");
        assert_eq!(error.source_file, Some("file.beancount".to_string()));
        assert_eq!(error.line_number, Some(10));
        assert_eq!(error.severity, PluginErrorSeverity::Error);
    }

    #[test]
    fn test_plugin_warning() {
        let warning = PluginError::warning("test warning");
        assert_eq!(warning.severity, PluginErrorSeverity::Warning);
    }

    #[test]
    fn test_directive_sort_order() {
        let open = DirectiveWrapper {
            directive_type: String::new(),
            date: "2024-01-01".to_string(),
            filename: None,
            lineno: Some(1),
            data: DirectiveData::Open(OpenData {
                account: "Assets:Bank".to_string(),
                currencies: vec![],
                booking: None,
                metadata: vec![],
            }),
        };
        assert_eq!(open.type_sort_order(), -2);

        let close = DirectiveWrapper {
            directive_type: String::new(),
            date: "2024-01-01".to_string(),
            filename: None,
            lineno: Some(2),
            data: DirectiveData::Close(CloseData {
                account: "Assets:Bank".to_string(),
                metadata: vec![],
            }),
        };
        assert_eq!(close.type_sort_order(), 2);
    }

    #[test]
    fn test_serde_roundtrip() {
        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: String::new(),
                date: "2024-01-15".to_string(),
                filename: Some("test.beancount".to_string()),
                lineno: Some(42),
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: Some("Coffee Shop".to_string()),
                    narration: "Morning coffee".to_string(),
                    tags: vec!["food".to_string()],
                    links: vec![],
                    metadata: vec![],
                    postings: vec![PostingData {
                        account: "Expenses:Food".to_string(),
                        units: Some(AmountData {
                            number: "5.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    }],
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: Some("Test Ledger".to_string()),
            },
            config: Some("threshold=100".to_string()),
        };

        // Test JSON roundtrip
        let json = serde_json::to_string(&input).unwrap();
        let decoded: PluginInput = serde_json::from_str(&json).unwrap();
        assert_eq!(decoded.directives.len(), 1);
        assert_eq!(decoded.config, Some("threshold=100".to_string()));

        // Test MessagePack roundtrip
        let msgpack = rmp_serde::to_vec(&input).unwrap();
        let decoded: PluginInput = rmp_serde::from_slice(&msgpack).unwrap();
        assert_eq!(decoded.directives.len(), 1);
    }

    // ===== PriceAnnotationData::view() — all four arms =====
    //
    // The view() enum is the type-safe interface that prevents the
    // #992 bug shape (consumer ignoring the is_total discriminator).
    // These tests pin the mapping from (is_total, amount) to each
    // PriceAnnotationView variant so a refactor of the underlying
    // struct can't silently change the dispatch.

    fn amount(number: &str, currency: &str) -> AmountData {
        AmountData {
            number: number.to_string(),
            currency: currency.to_string(),
        }
    }

    #[test]
    fn view_unit_complete() {
        // `@ 1.40 EUR`
        let pad = PriceAnnotationData {
            is_total: false,
            amount: Some(amount("1.40", "EUR")),
            number: None,
            currency: None,
        };
        match pad.view() {
            PriceAnnotationView::Unit(a) => {
                assert_eq!(a.number, "1.40");
                assert_eq!(a.currency, "EUR");
            }
            other => panic!("expected Unit, got {other:?}"),
        }
    }

    #[test]
    fn view_total_complete() {
        // `@@ 1500 USD`
        let pad = PriceAnnotationData {
            is_total: true,
            amount: Some(amount("1500", "USD")),
            number: None,
            currency: None,
        };
        match pad.view() {
            PriceAnnotationView::Total(a) => {
                assert_eq!(a.number, "1500");
                assert_eq!(a.currency, "USD");
            }
            other => panic!("expected Total, got {other:?}"),
        }
    }

    #[test]
    fn view_unit_incomplete_number_only() {
        // `@ 1.40` — number but no currency
        let pad = PriceAnnotationData {
            is_total: false,
            amount: None,
            number: Some("1.40".to_string()),
            currency: None,
        };
        match pad.view() {
            PriceAnnotationView::UnitIncomplete { number, currency } => {
                assert_eq!(number, Some("1.40"));
                assert_eq!(currency, None);
            }
            other => panic!("expected UnitIncomplete, got {other:?}"),
        }
    }

    #[test]
    fn view_unit_incomplete_currency_only() {
        // `@ EUR` — currency but no number
        let pad = PriceAnnotationData {
            is_total: false,
            amount: None,
            number: None,
            currency: Some("EUR".to_string()),
        };
        match pad.view() {
            PriceAnnotationView::UnitIncomplete { number, currency } => {
                assert_eq!(number, None);
                assert_eq!(currency, Some("EUR"));
            }
            other => panic!("expected UnitIncomplete, got {other:?}"),
        }
    }

    #[test]
    fn view_unit_incomplete_neither() {
        // `@` — bare annotation, neither number nor currency
        let pad = PriceAnnotationData {
            is_total: false,
            amount: None,
            number: None,
            currency: None,
        };
        match pad.view() {
            PriceAnnotationView::UnitIncomplete { number, currency } => {
                assert_eq!(number, None);
                assert_eq!(currency, None);
            }
            other => panic!("expected UnitIncomplete, got {other:?}"),
        }
    }

    #[test]
    fn view_total_incomplete_number_only() {
        // `@@ 1500`
        let pad = PriceAnnotationData {
            is_total: true,
            amount: None,
            number: Some("1500".to_string()),
            currency: None,
        };
        match pad.view() {
            PriceAnnotationView::TotalIncomplete { number, currency } => {
                assert_eq!(number, Some("1500"));
                assert_eq!(currency, None);
            }
            other => panic!("expected TotalIncomplete, got {other:?}"),
        }
    }

    #[test]
    fn view_total_incomplete_currency_only() {
        // `@@ USD`
        let pad = PriceAnnotationData {
            is_total: true,
            amount: None,
            number: None,
            currency: Some("USD".to_string()),
        };
        match pad.view() {
            PriceAnnotationView::TotalIncomplete { number, currency } => {
                assert_eq!(number, None);
                assert_eq!(currency, Some("USD"));
            }
            other => panic!("expected TotalIncomplete, got {other:?}"),
        }
    }

    #[test]
    fn view_total_incomplete_neither() {
        // `@@` — bare total annotation
        let pad = PriceAnnotationData {
            is_total: true,
            amount: None,
            number: None,
            currency: None,
        };
        match pad.view() {
            PriceAnnotationView::TotalIncomplete { number, currency } => {
                assert_eq!(number, None);
                assert_eq!(currency, None);
            }
            other => panic!("expected TotalIncomplete, got {other:?}"),
        }
    }

    #[test]
    fn view_amount_present_takes_priority_over_number_currency_fields() {
        // If both `amount` AND the loose `number`/`currency` fields
        // are set, `amount` wins — view() returns Unit/Total, never
        // an Incomplete variant. This pins the precedence so a
        // future field-juggling refactor can't accidentally invert
        // it.
        let pad = PriceAnnotationData {
            is_total: false,
            amount: Some(amount("1.40", "EUR")),
            number: Some("99".to_string()),    // ignored
            currency: Some("XYZ".to_string()), // ignored
        };
        match pad.view() {
            PriceAnnotationView::Unit(a) => {
                assert_eq!(a.number, "1.40");
                assert_eq!(a.currency, "EUR");
            }
            other => panic!("expected Unit, got {other:?}"),
        }
    }

    // ===== Importer ABI round-trip tests =====
    //
    // Pin the MessagePack-roundtrip shape of the WASM importer wire
    // format. If any field is renamed, removed, or its type changes,
    // these tests catch it — that's a v1.0 ABI breakage we want to
    // notice at code-change time.

    #[test]
    fn importer_input_msgpack_roundtrip() {
        let mut options = std::collections::HashMap::new();
        options.insert("date_column".to_string(), "Date".to_string());
        options.insert("delimiter".to_string(), ",".to_string());

        let original = ImporterInput {
            path: "/path/to/foo.csv".to_string(),
            content: vec![0xDE, 0xAD, 0xBE, 0xEF],
            account: "Assets:Bank".to_string(),
            currency: Some("USD".to_string()),
            options,
        };
        let bytes = rmp_serde::to_vec(&original).unwrap();
        let decoded: ImporterInput = rmp_serde::from_slice(&bytes).unwrap();
        assert_eq!(decoded.path, original.path);
        assert_eq!(decoded.content, original.content);
        assert_eq!(decoded.account, original.account);
        assert_eq!(decoded.currency, original.currency);
        assert_eq!(decoded.options, original.options);
    }

    #[test]
    fn importer_output_msgpack_roundtrip_empty() {
        let original = ImporterOutput::empty();
        let bytes = rmp_serde::to_vec(&original).unwrap();
        let decoded: ImporterOutput = rmp_serde::from_slice(&bytes).unwrap();
        assert!(decoded.directives.is_empty());
        assert!(decoded.warnings.is_empty());
    }

    #[test]
    fn importer_output_msgpack_roundtrip_with_warning() {
        let mut out = ImporterOutput::new(vec![]);
        out.warnings.push("Skipped row 3: bad date".to_string());
        let bytes = rmp_serde::to_vec(&out).unwrap();
        let decoded: ImporterOutput = rmp_serde::from_slice(&bytes).unwrap();
        assert_eq!(decoded.warnings.len(), 1);
        assert!(decoded.warnings[0].contains("bad date"));
    }

    #[test]
    fn enrichment_wrapper_msgpack_roundtrip() {
        let original = EnrichmentWrapper {
            directive_index: 7,
            confidence: 0.85,
            method: "rule".to_string(),
            alternatives: vec![AlternativeWrapper {
                account: "Expenses:Groceries".to_string(),
                confidence: 0.75,
                method: "merchant-dict".to_string(),
            }],
            fingerprint: Some("abc123def456".to_string()),
        };
        let bytes = rmp_serde::to_vec(&original).unwrap();
        let decoded: EnrichmentWrapper = rmp_serde::from_slice(&bytes).unwrap();
        assert_eq!(decoded.directive_index, original.directive_index);
        assert!((decoded.confidence - original.confidence).abs() < f64::EPSILON);
        assert_eq!(decoded.method, original.method);
        assert_eq!(decoded.alternatives.len(), 1);
        assert_eq!(decoded.alternatives[0].account, "Expenses:Groceries");
        // Every field on AlternativeWrapper must round-trip — if any drift
        // silently (renamed / dropped / type-changed) we want to catch it
        // here, not at the WASM boundary where it'd corrupt enriched results.
        assert!(
            (decoded.alternatives[0].confidence - 0.75).abs() < f64::EPSILON,
            "alternative confidence must round-trip exactly"
        );
        assert_eq!(decoded.alternatives[0].method, "merchant-dict");
        assert_eq!(decoded.fingerprint, original.fingerprint);
    }

    #[test]
    fn enriched_importer_output_msgpack_roundtrip() {
        // Cover the more complex enriched variant — pair of
        // (DirectiveWrapper, EnrichmentWrapper) with metadata,
        // plus warnings + errors. Asserts every field individually.
        let dir = DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-01-15".to_string(),
            filename: Some("/tmp/foo.csv".to_string()),
            lineno: Some(7),
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: Some("Whole Foods".to_string()),
                narration: "Groceries".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![],
            }),
        };
        let enr = EnrichmentWrapper {
            directive_index: 0,
            confidence: 0.92,
            method: "rule".to_string(),
            alternatives: vec![AlternativeWrapper {
                account: "Expenses:Other".to_string(),
                confidence: 0.10,
                method: "default".to_string(),
            }],
            fingerprint: Some("dead-beef".to_string()),
        };
        let original = EnrichedImporterOutput {
            entries: vec![(dir, enr)],
            warnings: vec!["row 3 skipped".to_string()],
            errors: vec![PluginError::error("row 4 unparsable").at("/tmp/foo.csv", 4)],
        };
        let bytes = rmp_serde::to_vec(&original).unwrap();
        let decoded: EnrichedImporterOutput = rmp_serde::from_slice(&bytes).unwrap();
        assert_eq!(decoded.entries.len(), 1);
        let (dir, enr) = &decoded.entries[0];
        // `directive_type` is intentionally `#[serde(skip_serializing, default)]`
        // on `DirectiveWrapper` — derived from the `data` variant, not on the
        // wire. Don't assert it here.
        assert_eq!(dir.date, "2024-01-15");
        match &dir.data {
            DirectiveData::Transaction(t) => {
                assert_eq!(t.payee.as_deref(), Some("Whole Foods"));
                assert_eq!(t.narration, "Groceries");
            }
            other => panic!("expected Transaction, got {other:?}"),
        }
        assert_eq!(enr.directive_index, 0);
        assert!((enr.confidence - 0.92).abs() < f64::EPSILON);
        assert_eq!(enr.method, "rule");
        assert_eq!(enr.alternatives.len(), 1);
        assert_eq!(enr.alternatives[0].method, "default");
        assert_eq!(enr.fingerprint, Some("dead-beef".to_string()));
        assert_eq!(decoded.warnings, vec!["row 3 skipped".to_string()]);
        assert_eq!(decoded.errors.len(), 1);
        assert_eq!(decoded.errors[0].message, "row 4 unparsable");
        assert_eq!(
            decoded.errors[0].source_file,
            Some("/tmp/foo.csv".to_string())
        );
        assert_eq!(decoded.errors[0].line_number, Some(4));
    }

    #[test]
    fn identify_input_output_msgpack_roundtrip() {
        let input = IdentifyInput {
            path: "/tmp/statement.mt940".to_string(),
        };
        let input_bytes = rmp_serde::to_vec(&input).unwrap();
        let decoded_input: IdentifyInput = rmp_serde::from_slice(&input_bytes).unwrap();
        assert_eq!(decoded_input.path, input.path);

        let output = IdentifyOutput { matches: true };
        let output_bytes = rmp_serde::to_vec(&output).unwrap();
        let decoded_output: IdentifyOutput = rmp_serde::from_slice(&output_bytes).unwrap();
        assert!(decoded_output.matches);
    }

    #[test]
    fn metadata_output_msgpack_roundtrip() {
        let original = MetadataOutput {
            name: "MT940".to_string(),
            description: "SWIFT MT940 bank statement importer".to_string(),
        };
        let bytes = rmp_serde::to_vec(&original).unwrap();
        let decoded: MetadataOutput = rmp_serde::from_slice(&bytes).unwrap();
        assert_eq!(decoded.name, original.name);
        assert_eq!(decoded.description, original.description);
    }
}
