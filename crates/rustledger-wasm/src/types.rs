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
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
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

/// A posting cost in JSON-serializable form.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PostingCostJson {
    /// Cost per unit.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub number_per: Option<String>,
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    /// An error that prevents processing.
    Error,
    /// A warning that doesn't prevent processing.
    Warning,
}

/// An error with source location.
#[derive(Debug, Clone, Serialize, Deserialize)]
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
