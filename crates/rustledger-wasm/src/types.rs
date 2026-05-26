//! Data transfer objects for WASM serialization.
//!
//! These types provide a JavaScript-friendly representation of Beancount data,
//! using string representations for dates and numbers.

use serde::{Deserialize, Serialize};

/// Result of parsing a Beancount file.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParseResult {
    /// The parsed ledger (if successful).
    pub ledger: Option<Ledger>,
    /// Parse errors.
    pub errors: Vec<Error>,
}

/// A parsed Beancount ledger.
#[derive(Debug, Clone, Serialize, Deserialize)]
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
pub struct LedgerOptions {
    /// Operating currencies.
    pub operating_currencies: Vec<String>,
    /// Ledger title.
    pub title: Option<String>,
}

/// A directive in JSON-serializable form.
///
/// Each variant corresponds to a Beancount directive type, with fields
/// representing the directive's data in a JavaScript-friendly format.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
#[allow(missing_docs)]
pub enum DirectiveJson {
    /// Transaction directive.
    #[serde(rename = "transaction")]
    Transaction {
        date: String,
        flag: String,
        payee: Option<String>,
        narration: Option<String>,
        tags: Vec<String>,
        links: Vec<String>,
        postings: Vec<PostingJson>,
    },
    /// Balance assertion.
    #[serde(rename = "balance")]
    Balance {
        date: String,
        account: String,
        amount: AmountValue,
    },
    /// Open account.
    #[serde(rename = "open")]
    Open {
        date: String,
        account: String,
        currencies: Vec<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        booking: Option<String>,
    },
    /// Close account.
    #[serde(rename = "close")]
    Close { date: String, account: String },
    /// Commodity declaration.
    #[serde(rename = "commodity")]
    Commodity { date: String, currency: String },
    /// Pad directive.
    #[serde(rename = "pad")]
    Pad {
        date: String,
        account: String,
        source_account: String,
    },
    /// Event directive.
    #[serde(rename = "event")]
    Event {
        date: String,
        event_type: String,
        value: String,
    },
    /// Note directive.
    #[serde(rename = "note")]
    Note {
        date: String,
        account: String,
        comment: String,
    },
    /// Document directive.
    #[serde(rename = "document")]
    Document {
        date: String,
        account: String,
        path: String,
    },
    /// Price directive.
    #[serde(rename = "price")]
    Price {
        date: String,
        currency: String,
        amount: AmountValue,
    },
    /// Query directive.
    #[serde(rename = "query")]
    Query {
        date: String,
        name: String,
        query_string: String,
    },
    /// Custom directive.
    #[serde(rename = "custom")]
    Custom { date: String, custom_type: String },
}

/// A posting in JSON-serializable form.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PostingJson {
    /// Account name.
    pub account: String,
    /// Units (amount).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub units: Option<AmountValue>,
    /// Cost specification.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cost: Option<PostingCostJson>,
    /// Price annotation.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub price: Option<AmountValue>,
}

/// Wire-format of the numeric component of a [`PostingCostJson`].
///
/// Mirrors `rustledger_core::CostNumber` on the wire so JS consumers
/// see the same mutual exclusion the host enforces. Use the `kind`
/// field as the discriminator.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
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
pub struct PostingCostJson {
    /// Cost number (per-unit, total, or post-booking pair).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub number: Option<CostNumberJson>,
    /// Cost currency.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub currency: Option<String>,
    /// Acquisition date.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub date: Option<String>,
    /// Lot label.
    #[serde(skip_serializing_if = "Option::is_none")]
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
pub enum Severity {
    /// An error that prevents processing.
    Error,
    /// A warning that doesn't prevent processing.
    Warning,
}

/// An error with source location.
#[derive(
    Debug, Clone, Serialize, Deserialize, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize,
)]
pub struct Error {
    /// Error message.
    pub message: String,
    /// Line number (1-based).
    pub line: Option<u32>,
    /// Column number (1-based).
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
pub struct ValidationResult {
    /// Whether the ledger is valid.
    pub valid: bool,
    /// Validation errors.
    pub errors: Vec<Error>,
}

/// Result of a BQL query.
#[derive(Debug, Clone, Serialize, Deserialize)]
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
pub enum CellValue {
    /// Null value.
    Null,
    /// String value.
    String(String),
    /// Integer value.
    Integer(i64),
    /// Boolean value.
    Boolean(bool),
    /// Amount with number and currency.
    Amount { number: String, currency: String },
    /// Position with units and optional cost.
    Position {
        units: AmountValue,
        #[serde(skip_serializing_if = "Option::is_none")]
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
pub struct AmountValue {
    /// The number as a string.
    pub number: String,
    /// The currency.
    pub currency: String,
}

/// Position value for serialization.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PositionValue {
    /// The units.
    pub units: AmountValue,
}

/// Cost value for serialization.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CostValue {
    /// Cost per unit.
    pub number: String,
    /// Cost currency.
    pub currency: String,
    /// Acquisition date.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub date: Option<String>,
    /// Lot label.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
}

/// Result of formatting.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FormatResult {
    /// Formatted source (if successful).
    pub formatted: Option<String>,
    /// Format errors.
    pub errors: Vec<Error>,
}

/// Result of pad expansion.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PadResult {
    /// Directives with pads removed.
    pub directives: Vec<DirectiveJson>,
    /// Generated padding transactions.
    pub padding_transactions: Vec<DirectiveJson>,
    /// Pad processing errors.
    pub errors: Vec<Error>,
}

/// Result of running a plugin.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginResult {
    /// Modified directives.
    pub directives: Vec<DirectiveJson>,
    /// Plugin errors/warnings.
    pub errors: Vec<Error>,
}

/// Plugin information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginInfo {
    /// Plugin name.
    pub name: String,
    /// Plugin description.
    pub description: String,
}

/// BQL completion suggestion for WASM.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionJson {
    /// The completion text to insert.
    pub text: String,
    /// Category: keyword, function, column, operator, literal.
    pub category: String,
    /// Optional description/documentation.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,
}

/// Result of BQL completion request.
#[derive(Debug, Clone, Serialize, Deserialize)]
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
pub struct EditorCompletion {
    /// The label to display in the completion list.
    pub label: String,
    /// The kind of completion item.
    pub kind: CompletionKind,
    /// A human-readable string with additional information.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    /// The text to insert when this completion is selected.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub insert_text: Option<String>,
}

/// The kind of a completion item.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
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
pub struct EditorCompletionResult {
    /// The completions.
    pub completions: Vec<EditorCompletion>,
    /// The detected context.
    pub context: String,
}

/// Hover information for a symbol.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EditorHoverInfo {
    /// The hover content (Markdown formatted).
    pub contents: String,
    /// The range of the hovered symbol (optional).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub range: Option<EditorRange>,
}

/// A range in the document.
#[derive(Debug, Clone, Serialize, Deserialize)]
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
pub struct EditorLocation {
    /// Line number (0-based).
    pub line: u32,
    /// Character offset (0-based).
    pub character: u32,
}

/// A document symbol for the outline view.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EditorDocumentSymbol {
    /// The name of this symbol.
    pub name: String,
    /// More detail for this symbol.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    /// The kind of this symbol.
    pub kind: SymbolKind,
    /// The range enclosing this symbol.
    pub range: EditorRange,
    /// Children of this symbol (e.g., postings in a transaction).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub children: Option<Vec<Self>>,
    /// Whether this symbol is deprecated (e.g., closed account).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub deprecated: Option<bool>,
}

/// The kind of a symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
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
pub struct EditorReference {
    /// The range of this reference.
    pub range: EditorRange,
    /// The kind of reference.
    pub kind: ReferenceKind,
    /// Whether this is the defining occurrence.
    pub is_definition: bool,
    /// Human-readable context (e.g., directive type).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub context: Option<String>,
}

/// Result of a find-references request.
#[derive(Debug, Clone, Serialize, Deserialize)]
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
