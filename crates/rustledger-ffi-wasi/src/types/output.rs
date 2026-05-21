//! Output types for JSON serialization.

use std::collections::HashMap;

use rustledger_core::{MetaValue, Metadata};
use serde::Serialize;

/// Metadata includes filename, lineno, hash, plus any user-defined key-value pairs.
#[derive(Serialize, Default)]
pub struct Meta {
    pub filename: String,
    pub lineno: u32,
    /// Entry hash (SHA256 of canonical representation).
    pub hash: String,
    #[serde(flatten)]
    pub user: HashMap<String, serde_json::Value>,
}

impl Meta {
    pub fn new(filename: &str, lineno: u32, hash: String, directive_meta: &Metadata) -> Self {
        let mut user = HashMap::new();
        for (key, value) in directive_meta {
            user.insert(key.clone(), meta_value_to_json(value));
        }
        Self {
            filename: filename.to_string(),
            lineno,
            hash,
            user,
        }
    }
}

/// Convert `MetaValue` to JSON, extracting raw values without extra formatting.
pub fn meta_value_to_json(value: &MetaValue) -> serde_json::Value {
    match value {
        MetaValue::String(s) => serde_json::Value::String(s.clone()),
        MetaValue::Account(a) => serde_json::Value::String(a.to_string()),
        MetaValue::Currency(c) => serde_json::Value::String(c.to_string()),
        MetaValue::Tag(t) => serde_json::Value::String(t.to_string()),
        MetaValue::Link(l) => serde_json::Value::String(l.to_string()),
        MetaValue::Date(d) => serde_json::Value::String(d.to_string()),
        MetaValue::Number(n) => serde_json::json!(n.to_string()),
        MetaValue::Bool(b) => serde_json::Value::Bool(*b),
        MetaValue::Amount(a) => serde_json::json!({
            "number": a.number.to_string(),
            "currency": a.currency.to_string()
        }),
        MetaValue::None => serde_json::Value::Null,
    }
}

#[derive(Serialize, Clone)]
pub struct Error {
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub column: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub field: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub entry_index: Option<usize>,
    pub severity: String,
    /// Processing phase that produced this error.
    ///
    /// Known values:
    /// - `"parse"` — syntax/load errors (default when constructed via `Error::new()`)
    /// - `"validate"` — semantic validation errors (set via `.validate_phase()`)
    ///
    /// Non-ledger contexts (e.g., query parsing) reuse the default `"parse"` value,
    /// which is acceptable since those errors are also syntactic in nature.
    pub phase: String,
}

impl Error {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            line: None,
            column: None,
            field: None,
            entry_index: None,
            severity: "error".to_string(),
            phase: "parse".to_string(),
        }
    }

    pub const fn with_line(mut self, line: u32) -> Self {
        self.line = Some(line);
        self
    }

    pub fn validate_phase(mut self) -> Self {
        self.phase = "validate".to_string();
        self
    }
}

#[derive(Serialize, Clone)]
pub struct Amount {
    pub number: String,
    pub currency: String,
}

/// Wire-format of the numeric component of a [`PostingCost`].
///
/// Mirrors the host's `rustledger_core::CostNumber` enum so JSON
/// consumers see the same mutual exclusion the host enforces. The
/// `kind` tag is the discriminator; consumers should switch on it
/// rather than probing for present-but-null fields.
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum CostNumber {
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
    /// Post-booking: derived per-unit plus preserved source total.
    PerUnitFromTotal {
        /// Derived per-unit.
        per_unit: String,
        /// Original total.
        total: String,
    },
}

#[derive(Serialize)]
pub struct PostingCost {
    /// Cost number (per-unit, total, or post-booking pair).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub number: Option<CostNumber>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub currency: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub date: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
}

/// A typed value preserving the original type from the beancount source.
#[derive(Serialize)]
#[serde(rename_all = "lowercase")]
pub struct TypedValue {
    #[serde(rename = "type")]
    pub value_type: &'static str,
    pub value: serde_json::Value,
}

impl TypedValue {
    pub fn from_meta_value(mv: &MetaValue) -> Self {
        match mv {
            MetaValue::String(s) => Self {
                value_type: "string",
                value: serde_json::Value::String(s.clone()),
            },
            MetaValue::Account(a) => Self {
                value_type: "account",
                value: serde_json::Value::String(a.to_string()),
            },
            MetaValue::Currency(c) => Self {
                value_type: "currency",
                value: serde_json::Value::String(c.to_string()),
            },
            MetaValue::Tag(t) => Self {
                value_type: "tag",
                value: serde_json::Value::String(t.to_string()),
            },
            MetaValue::Link(l) => Self {
                value_type: "link",
                value: serde_json::Value::String(l.to_string()),
            },
            MetaValue::Date(d) => Self {
                value_type: "date",
                value: serde_json::Value::String(d.to_string()),
            },
            MetaValue::Number(n) => Self {
                value_type: "number",
                value: serde_json::Value::String(n.to_string()),
            },
            MetaValue::Bool(b) => Self {
                value_type: "bool",
                value: serde_json::Value::Bool(*b),
            },
            MetaValue::Amount(a) => Self {
                value_type: "amount",
                value: serde_json::json!({
                    "number": a.number.to_string(),
                    "currency": a.currency.to_string()
                }),
            },
            MetaValue::None => Self {
                value_type: "null",
                value: serde_json::Value::Null,
            },
        }
    }
}

#[derive(Serialize)]
pub struct Posting {
    pub account: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub units: Option<Amount>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cost: Option<PostingCost>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub price: Option<Amount>,
    /// Posting-level flag (e.g., "!" for pending).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub flag: Option<String>,
    #[serde(skip_serializing_if = "HashMap::is_empty")]
    pub meta: HashMap<String, serde_json::Value>,
}

#[derive(Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum DirectiveJson {
    Transaction {
        date: String,
        flag: String,
        #[serde(skip_serializing_if = "Option::is_none")]
        payee: Option<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        narration: Option<String>,
        tags: Vec<String>,
        links: Vec<String>,
        postings: Vec<Posting>,
        meta: Meta,
    },
    Open {
        date: String,
        account: String,
        currencies: Vec<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        booking: Option<String>,
        meta: Meta,
    },
    Close {
        date: String,
        account: String,
        meta: Meta,
    },
    Balance {
        date: String,
        account: String,
        amount: Amount,
        /// Explicit tolerance (e.g., "~ 0.01").
        #[serde(skip_serializing_if = "Option::is_none")]
        tolerance: Option<String>,
        meta: Meta,
    },
    Pad {
        date: String,
        account: String,
        source_account: String,
        meta: Meta,
    },
    Commodity {
        date: String,
        currency: String,
        meta: Meta,
    },
    Price {
        date: String,
        currency: String,
        amount: Amount,
        meta: Meta,
    },
    Event {
        date: String,
        event_type: String,
        value: String,
        meta: Meta,
    },
    Note {
        date: String,
        account: String,
        comment: String,
        meta: Meta,
    },
    Document {
        date: String,
        account: String,
        path: String,
        meta: Meta,
    },
    Query {
        date: String,
        name: String,
        query_string: String,
        meta: Meta,
    },
    Custom {
        date: String,
        custom_type: String,
        values: Vec<TypedValue>,
        meta: Meta,
    },
}

#[derive(Serialize)]
pub struct LedgerOptions {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub title: Option<String>,
    pub operating_currency: Vec<String>,
    pub name_assets: String,
    pub name_liabilities: String,
    pub name_equity: String,
    pub name_income: String,
    pub name_expenses: String,
    pub documents: Vec<String>,
    pub commodities: Vec<String>,
    pub booking_method: String,
    pub display_precision: HashMap<String, u32>,
    /// Whether to render commas in numbers.
    pub render_commas: bool,
    /// Default tolerances per currency (e.g., {"USD": "0.005", "*": "0.01"}).
    #[serde(skip_serializing_if = "HashMap::is_empty")]
    pub inferred_tolerance_default: HashMap<String, String>,
    /// Tolerance multiplier (default 0.5).
    pub inferred_tolerance_multiplier: String,
    /// Whether to infer tolerance from cost.
    pub infer_tolerance_from_cost: bool,
    /// Account for rounding errors.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub account_rounding: Option<String>,
    /// Account for previous balances (opening balances).
    pub account_previous_balances: String,
    /// Account for previous earnings.
    pub account_previous_earnings: String,
    /// Account for previous conversions.
    pub account_previous_conversions: String,
    /// Account for current earnings.
    pub account_current_earnings: String,
    /// Account for current conversion differences.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub account_current_conversions: Option<String>,
    /// Account for unrealized gains.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub account_unrealized_gains: Option<String>,
    /// Currency for conversion (if specified).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub conversion_currency: Option<String>,
}

impl Default for LedgerOptions {
    fn default() -> Self {
        Self {
            title: None,
            operating_currency: Vec::new(),
            name_assets: "Assets".to_string(),
            name_liabilities: "Liabilities".to_string(),
            name_equity: "Equity".to_string(),
            name_income: "Income".to_string(),
            name_expenses: "Expenses".to_string(),
            documents: Vec::new(),
            commodities: Vec::new(),
            booking_method: "STRICT".to_string(),
            display_precision: HashMap::new(),
            render_commas: false,
            inferred_tolerance_default: HashMap::new(),
            inferred_tolerance_multiplier: "0.5".to_string(),
            infer_tolerance_from_cost: false,
            account_rounding: None,
            account_previous_balances: "Equity:Opening-Balances".to_string(),
            account_previous_earnings: "Equity:Earnings:Previous".to_string(),
            account_previous_conversions: "Equity:Conversions:Previous".to_string(),
            account_current_earnings: "Equity:Earnings:Current".to_string(),
            account_current_conversions: None,
            account_unrealized_gains: None,
            conversion_currency: None,
        }
    }
}

/// A plugin directive from the source file.
#[derive(Serialize)]
pub struct Plugin {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub config: Option<String>,
}

/// An include directive from the source file.
#[derive(Serialize)]
pub struct Include {
    pub path: String,
    pub lineno: u32,
}

#[derive(Serialize)]
pub struct LoadOutput {
    pub api_version: &'static str,
    pub entries: Vec<DirectiveJson>,
    pub errors: Vec<Error>,
    pub options: LedgerOptions,
    pub plugins: Vec<Plugin>,
    pub includes: Vec<Include>,
}

#[derive(Serialize)]
pub struct ValidateOutput {
    pub api_version: &'static str,
    pub valid: bool,
    pub errors: Vec<Error>,
    /// Number of parse-phase errors (syntactic)
    pub parse_error_count: usize,
    /// Number of validate-phase errors (semantic)
    pub validate_error_count: usize,
}

#[derive(Serialize)]
pub struct ColumnInfo {
    pub name: String,
    pub datatype: String,
}

#[derive(Serialize)]
pub struct QueryOutput {
    pub api_version: &'static str,
    pub columns: Vec<ColumnInfo>,
    pub rows: Vec<Vec<serde_json::Value>>,
    pub errors: Vec<Error>,
}

/// Output for batch command: load + multiple queries in one parse.
#[derive(Serialize)]
pub struct BatchOutput {
    pub api_version: &'static str,
    pub load: LoadOutput,
    pub queries: Vec<QueryOutput>,
}

#[cfg(test)]
mod tests {
    use super::*;

    // ===== Cost-number wire-format tests (#1164) =====
    //
    // These pin the JSON shape FFI consumers depend on. Mirrors host
    // `CostNumber` exactly — any silent shape change is a wire break.

    #[test]
    fn cost_number_per_unit_serializes_with_kind_tag() {
        let cn = CostNumber::PerUnit {
            value: "100".into(),
        };
        let json = serde_json::to_value(&cn).unwrap();
        assert_eq!(
            json,
            serde_json::json!({"kind": "per_unit", "value": "100"})
        );
    }

    #[test]
    fn cost_number_total_serializes_with_kind_tag() {
        let cn = CostNumber::Total {
            value: "1500".into(),
        };
        let json = serde_json::to_value(&cn).unwrap();
        assert_eq!(json, serde_json::json!({"kind": "total", "value": "1500"}));
    }

    #[test]
    fn cost_number_per_unit_from_total_carries_both_values() {
        let cn = CostNumber::PerUnitFromTotal {
            per_unit: "150".into(),
            total: "300".into(),
        };
        let json = serde_json::to_value(&cn).unwrap();
        // Load-bearing: the preserved total survives serialization so
        // downstream consumers don't have to redivide. This is what
        // the pre-PR shape silently lost.
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
    fn posting_cost_omits_number_when_none() {
        let pc = PostingCost {
            number: None,
            currency: Some("USD".into()),
            date: None,
            label: None,
        };
        let json = serde_json::to_string(&pc).unwrap();
        // `skip_serializing_if = "Option::is_none"` keeps the JSON
        // shape lean — a bare `{USD}` lot match has no `number` key.
        assert!(!json.contains("number"));
        assert!(json.contains("currency"));
    }

    #[test]
    fn test_error_default_phase_is_parse() {
        let err = Error::new("test");
        assert_eq!(err.phase, "parse");
    }

    #[test]
    fn test_error_validate_phase() {
        let err = Error::new("test").validate_phase();
        assert_eq!(err.phase, "validate");
    }

    #[test]
    fn test_error_phase_serializes() {
        let err = Error::new("test");
        let json = serde_json::to_value(&err).unwrap();
        assert_eq!(json["phase"], "parse");

        let err = Error::new("test").validate_phase();
        let json = serde_json::to_value(&err).unwrap();
        assert_eq!(json["phase"], "validate");
    }

    #[test]
    fn test_validate_output_includes_phase_counts() {
        let output = ValidateOutput {
            api_version: "1",
            valid: false,
            errors: vec![
                Error::new("parse err"),
                Error::new("validate err").validate_phase(),
            ],
            parse_error_count: 1,
            validate_error_count: 1,
        };
        let json = serde_json::to_value(&output).unwrap();
        assert_eq!(json["parse_error_count"], 1);
        assert_eq!(json["validate_error_count"], 1);
    }
}
