//! Beancount WASM Bindings.
//!
//! This crate provides WebAssembly bindings for using Beancount from JavaScript/TypeScript.
//!
//! # Features
//!
//! - Parse Beancount files
//! - Validate ledgers
//! - Run BQL queries
//! - Format directives
//!
//! # Example (JavaScript)
//!
//! ```javascript
//! import init, { parse, validate, query } from 'beancount-wasm';
//!
//! await init();
//!
//! const source = `
//! 2024-01-01 open Assets:Bank USD
//! 2024-01-15 * "Coffee"
//!   Expenses:Food  5.00 USD
//!   Assets:Bank   -5.00 USD
//! `;
//!
//! const result = parse(source);
//! if (result.errors.length === 0) {
//!     const validation = validate(result.ledger);
//!     console.log('Validation errors:', validation.errors);
//! }
//! ```

#![forbid(unsafe_code)]
#![warn(missing_docs)]

use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

use rustledger_core::{Amount, Directive};
use rustledger_parser::parse as parse_beancount;
use rustledger_validate::validate as validate_ledger;

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
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DirectiveJson {
    /// Directive type.
    #[serde(rename = "type")]
    pub directive_type: String,
    /// Directive date (YYYY-MM-DD).
    pub date: String,
    /// Directive-specific data.
    #[serde(flatten)]
    pub data: serde_json::Value,
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
    pub severity: String,
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
    pub rows: Vec<Vec<serde_json::Value>>,
    /// Query errors.
    pub errors: Vec<Error>,
}

/// Parse a Beancount source string.
///
/// Returns a JSON object with the parsed ledger and any errors.
#[wasm_bindgen]
pub fn parse(source: &str) -> JsValue {
    let result = parse_beancount(source);

    let errors: Vec<Error> = result
        .errors
        .iter()
        .map(|e| Error {
            message: e.to_string(),
            line: Some(e.span().0 as u32 + 1),
            column: None,
            severity: "error".to_string(),
        })
        .collect();

    let ledger = if errors.is_empty() {
        Some(Ledger {
            directives: result
                .directives
                .iter()
                .map(|spanned| directive_to_json(&spanned.value))
                .collect(),
            options: LedgerOptions::default(),
        })
    } else {
        // Still return directives even with errors
        Some(Ledger {
            directives: result
                .directives
                .iter()
                .map(|spanned| directive_to_json(&spanned.value))
                .collect(),
            options: LedgerOptions::default(),
        })
    };

    let parse_result = ParseResult { ledger, errors };

    serde_wasm_bindgen::to_value(&parse_result).unwrap_or(JsValue::NULL)
}

/// Validate a parsed ledger.
///
/// Takes a ledger JSON object and returns validation errors.
#[wasm_bindgen]
pub fn validate(ledger_json: &str) -> JsValue {
    // Parse the ledger JSON back to directives
    let ledger: Result<Ledger, _> = serde_json::from_str(ledger_json);

    match ledger {
        Ok(ledger) => {
            // Reconstruct directives from JSON
            let mut directives = Vec::new();
            let mut conversion_errors = Vec::new();

            for dir_json in &ledger.directives {
                match json_to_directive(dir_json) {
                    Ok(directive) => directives.push(directive),
                    Err(e) => conversion_errors.push(Error {
                        message: format!("Failed to reconstruct directive: {e}"),
                        line: None,
                        column: None,
                        severity: "error".to_string(),
                    }),
                }
            }

            if !conversion_errors.is_empty() {
                let result = ValidationResult {
                    valid: false,
                    errors: conversion_errors,
                };
                return serde_wasm_bindgen::to_value(&result).unwrap_or(JsValue::NULL);
            }

            // Run validation
            let validation_errors = validate_ledger(&directives);
            let errors: Vec<Error> = validation_errors
                .iter()
                .map(|e| Error {
                    message: e.message.clone(),
                    line: None,
                    column: None,
                    severity: "error".to_string(),
                })
                .collect();

            let result = ValidationResult {
                valid: errors.is_empty(),
                errors,
            };
            serde_wasm_bindgen::to_value(&result).unwrap_or(JsValue::NULL)
        }
        Err(e) => {
            let result = ValidationResult {
                valid: false,
                errors: vec![Error {
                    message: format!("Invalid ledger JSON: {e}"),
                    line: None,
                    column: None,
                    severity: "error".to_string(),
                }],
            };
            serde_wasm_bindgen::to_value(&result).unwrap_or(JsValue::NULL)
        }
    }
}

/// Validate a Beancount source string directly.
///
/// Parses and validates in one step.
#[wasm_bindgen]
pub fn validate_source(source: &str) -> JsValue {
    let parse_result = parse_beancount(source);

    // Collect parse errors
    let mut errors: Vec<Error> = parse_result
        .errors
        .iter()
        .map(|e| Error {
            message: e.to_string(),
            line: Some(e.span().0 as u32 + 1),
            column: None,
            severity: "error".to_string(),
        })
        .collect();

    // If parsing succeeded, run validation
    if parse_result.errors.is_empty() {
        let directives: Vec<_> = parse_result
            .directives
            .iter()
            .map(|s| s.value.clone())
            .collect();

        let validation_errors = validate_ledger(&directives);
        for err in validation_errors {
            errors.push(Error {
                message: err.message,
                line: None,
                column: None,
                severity: "error".to_string(),
            });
        }
    }

    let result = ValidationResult {
        valid: errors.is_empty(),
        errors,
    };

    serde_wasm_bindgen::to_value(&result).unwrap_or(JsValue::NULL)
}

/// Run a BQL query on a Beancount source string.
///
/// Parses the source, then executes the query.
#[wasm_bindgen]
pub fn query(source: &str, query_str: &str) -> JsValue {
    use rustledger_query::{parse as parse_query, Executor};

    // Parse the source
    let parse_result = parse_beancount(source);

    if !parse_result.errors.is_empty() {
        let result = QueryResult {
            columns: Vec::new(),
            rows: Vec::new(),
            errors: parse_result
                .errors
                .iter()
                .map(|e| Error {
                    message: e.to_string(),
                    line: Some(e.span().0 as u32 + 1),
                    column: None,
                    severity: "error".to_string(),
                })
                .collect(),
        };
        return serde_wasm_bindgen::to_value(&result).unwrap_or(JsValue::NULL);
    }

    // Parse the query
    let query = match parse_query(query_str) {
        Ok(q) => q,
        Err(e) => {
            let result = QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors: vec![Error {
                    message: format!("Query parse error: {e}"),
                    line: None,
                    column: None,
                    severity: "error".to_string(),
                }],
            };
            return serde_wasm_bindgen::to_value(&result).unwrap_or(JsValue::NULL);
        }
    };

    // Execute the query
    let directives: Vec<_> = parse_result
        .directives
        .iter()
        .map(|s| s.value.clone())
        .collect();

    let mut executor = Executor::new(&directives);
    match executor.execute(&query) {
        Ok(result) => {
            let rows: Vec<Vec<serde_json::Value>> = result
                .rows
                .iter()
                .map(|row| row.iter().map(value_to_json).collect())
                .collect();

            let query_result = QueryResult {
                columns: result.columns,
                rows,
                errors: Vec::new(),
            };
            serde_wasm_bindgen::to_value(&query_result).unwrap_or(JsValue::NULL)
        }
        Err(e) => {
            let result = QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors: vec![Error {
                    message: format!("Query execution error: {e}"),
                    line: None,
                    column: None,
                    severity: "error".to_string(),
                }],
            };
            serde_wasm_bindgen::to_value(&result).unwrap_or(JsValue::NULL)
        }
    }
}

/// Get version information.
#[wasm_bindgen]
pub fn version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
}

// Helper functions

fn directive_to_json(directive: &Directive) -> DirectiveJson {
    match directive {
        Directive::Transaction(txn) => DirectiveJson {
            directive_type: "transaction".to_string(),
            date: txn.date.to_string(),
            data: serde_json::json!({
                "flag": txn.flag.to_string(),
                "payee": txn.payee,
                "narration": txn.narration,
                "tags": txn.tags,
                "links": txn.links,
                "postings": txn.postings.iter().map(|p| {
                    serde_json::json!({
                        "account": p.account,
                        "units": p.units.as_ref().map(incomplete_amount_to_json),
                        "cost": p.cost.as_ref().map(|c| serde_json::json!({
                            "number_per": c.number_per.map(|n| n.to_string()),
                            "currency": c.currency,
                            "date": c.date.map(|d| d.to_string()),
                            "label": c.label,
                        })),
                    })
                }).collect::<Vec<_>>(),
            }),
        },
        Directive::Balance(bal) => DirectiveJson {
            directive_type: "balance".to_string(),
            date: bal.date.to_string(),
            data: serde_json::json!({
                "account": bal.account,
                "amount": amount_to_json(&bal.amount),
            }),
        },
        Directive::Open(open) => DirectiveJson {
            directive_type: "open".to_string(),
            date: open.date.to_string(),
            data: serde_json::json!({
                "account": open.account,
                "currencies": open.currencies,
                "booking": open.booking,
            }),
        },
        Directive::Close(close) => DirectiveJson {
            directive_type: "close".to_string(),
            date: close.date.to_string(),
            data: serde_json::json!({
                "account": close.account,
            }),
        },
        Directive::Commodity(comm) => DirectiveJson {
            directive_type: "commodity".to_string(),
            date: comm.date.to_string(),
            data: serde_json::json!({
                "currency": comm.currency,
            }),
        },
        Directive::Pad(pad) => DirectiveJson {
            directive_type: "pad".to_string(),
            date: pad.date.to_string(),
            data: serde_json::json!({
                "account": pad.account,
                "source_account": pad.source_account,
            }),
        },
        Directive::Event(event) => DirectiveJson {
            directive_type: "event".to_string(),
            date: event.date.to_string(),
            data: serde_json::json!({
                "type": event.event_type,
                "value": event.value,
            }),
        },
        Directive::Note(note) => DirectiveJson {
            directive_type: "note".to_string(),
            date: note.date.to_string(),
            data: serde_json::json!({
                "account": note.account,
                "comment": note.comment,
            }),
        },
        Directive::Document(doc) => DirectiveJson {
            directive_type: "document".to_string(),
            date: doc.date.to_string(),
            data: serde_json::json!({
                "account": doc.account,
                "path": doc.path,
            }),
        },
        Directive::Price(price) => DirectiveJson {
            directive_type: "price".to_string(),
            date: price.date.to_string(),
            data: serde_json::json!({
                "currency": price.currency,
                "amount": amount_to_json(&price.amount),
            }),
        },
        Directive::Query(query) => DirectiveJson {
            directive_type: "query".to_string(),
            date: query.date.to_string(),
            data: serde_json::json!({
                "name": query.name,
                "query": query.query,
            }),
        },
        Directive::Custom(custom) => DirectiveJson {
            directive_type: "custom".to_string(),
            date: custom.date.to_string(),
            data: serde_json::json!({
                "type": custom.custom_type,
            }),
        },
    }
}

fn amount_to_json(amount: &Amount) -> serde_json::Value {
    serde_json::json!({
        "number": amount.number.to_string(),
        "currency": amount.currency,
    })
}

fn incomplete_amount_to_json(amount: &rustledger_core::IncompleteAmount) -> serde_json::Value {
    use rustledger_core::IncompleteAmount;
    match amount {
        IncompleteAmount::Complete(a) => amount_to_json(a),
        IncompleteAmount::NumberOnly(n) => serde_json::json!({
            "number": n.to_string(),
            "currency": null,
        }),
        IncompleteAmount::CurrencyOnly(c) => serde_json::json!({
            "number": null,
            "currency": c,
        }),
    }
}

fn json_to_directive(json: &DirectiveJson) -> Result<Directive, String> {
    use rustledger_core::NaiveDate;
    use rustledger_core::{
        Balance, Close, Commodity, CostSpec, Custom, Decimal, Document, Event, IncompleteAmount,
        Note, Open, Pad, Posting, Price, Transaction,
    };

    let date = NaiveDate::parse_from_str(&json.date, "%Y-%m-%d")
        .map_err(|e| format!("invalid date '{}': {}", json.date, e))?;

    match json.directive_type.as_str() {
        "transaction" => {
            let flag = json
                .data
                .get("flag")
                .and_then(|v| v.as_str())
                .and_then(|s| s.chars().next())
                .unwrap_or('*');
            let payee = json
                .data
                .get("payee")
                .and_then(|v| v.as_str())
                .map(String::from);
            let narration = json
                .data
                .get("narration")
                .and_then(|v| v.as_str())
                .unwrap_or("")
                .to_string();
            let tags: Vec<String> = json
                .data
                .get("tags")
                .and_then(|v| v.as_array())
                .map(|arr| {
                    arr.iter()
                        .filter_map(|v| v.as_str().map(String::from))
                        .collect()
                })
                .unwrap_or_default();
            let links: Vec<String> = json
                .data
                .get("links")
                .and_then(|v| v.as_array())
                .map(|arr| {
                    arr.iter()
                        .filter_map(|v| v.as_str().map(String::from))
                        .collect()
                })
                .unwrap_or_default();

            let postings_json = json
                .data
                .get("postings")
                .and_then(|v| v.as_array())
                .cloned()
                .unwrap_or_default();

            let mut postings = Vec::new();
            for p in postings_json {
                let account = p
                    .get("account")
                    .and_then(|v| v.as_str())
                    .ok_or("posting missing account")?
                    .to_string();

                let units = if let Some(units_json) = p.get("units") {
                    if units_json.is_null() {
                        None
                    } else {
                        let number = units_json
                            .get("number")
                            .and_then(|v| v.as_str())
                            .and_then(|s| s.parse::<Decimal>().ok());
                        let currency = units_json
                            .get("currency")
                            .and_then(|v| v.as_str())
                            .map(String::from);

                        match (number, currency) {
                            (Some(n), Some(c)) => {
                                Some(IncompleteAmount::Complete(Amount::new(n, c)))
                            }
                            (Some(n), None) => Some(IncompleteAmount::NumberOnly(n)),
                            (None, Some(c)) => Some(IncompleteAmount::CurrencyOnly(c)),
                            (None, None) => None,
                        }
                    }
                } else {
                    None
                };

                let cost = if let Some(cost_json) = p.get("cost") {
                    if cost_json.is_null() {
                        None
                    } else {
                        let number_per = cost_json
                            .get("number_per")
                            .and_then(|v| v.as_str())
                            .and_then(|s| s.parse::<Decimal>().ok());
                        let currency = cost_json
                            .get("currency")
                            .and_then(|v| v.as_str())
                            .map(String::from);
                        let cost_date = cost_json
                            .get("date")
                            .and_then(|v| v.as_str())
                            .and_then(|s| NaiveDate::parse_from_str(s, "%Y-%m-%d").ok());
                        let label = cost_json
                            .get("label")
                            .and_then(|v| v.as_str())
                            .map(String::from);

                        Some(CostSpec {
                            number_per,
                            number_total: None,
                            currency,
                            date: cost_date,
                            label,
                            merge: false,
                        })
                    }
                } else {
                    None
                };

                postings.push(Posting {
                    account,
                    units,
                    cost,
                    price: None,
                    flag: None,
                    meta: std::collections::HashMap::new(),
                });
            }

            let mut txn = Transaction::new(date, &narration);
            txn.flag = flag;
            txn.payee = payee;
            txn.tags = tags;
            txn.links = links;
            txn.postings = postings;
            Ok(Directive::Transaction(txn))
        }
        "balance" => {
            let account = json
                .data
                .get("account")
                .and_then(|v| v.as_str())
                .ok_or("balance missing account")?
                .to_string();
            let amount_json = json.data.get("amount").ok_or("balance missing amount")?;
            let amount = json_to_amount(amount_json)?;
            Ok(Directive::Balance(Balance {
                date,
                account,
                amount,
                tolerance: None,
                meta: std::collections::HashMap::new(),
            }))
        }
        "open" => {
            let account = json
                .data
                .get("account")
                .and_then(|v| v.as_str())
                .ok_or("open missing account")?
                .to_string();
            let currencies: Vec<String> = json
                .data
                .get("currencies")
                .and_then(|v| v.as_array())
                .map(|arr| {
                    arr.iter()
                        .filter_map(|v| v.as_str().map(String::from))
                        .collect()
                })
                .unwrap_or_default();
            let booking = json
                .data
                .get("booking")
                .and_then(|v| v.as_str())
                .map(String::from);
            Ok(Directive::Open(Open {
                date,
                account,
                currencies,
                booking,
                meta: std::collections::HashMap::new(),
            }))
        }
        "close" => {
            let account = json
                .data
                .get("account")
                .and_then(|v| v.as_str())
                .ok_or("close missing account")?
                .to_string();
            Ok(Directive::Close(Close {
                date,
                account,
                meta: std::collections::HashMap::new(),
            }))
        }
        "commodity" => {
            let currency = json
                .data
                .get("currency")
                .and_then(|v| v.as_str())
                .ok_or("commodity missing currency")?
                .to_string();
            Ok(Directive::Commodity(Commodity {
                date,
                currency,
                meta: std::collections::HashMap::new(),
            }))
        }
        "pad" => {
            let account = json
                .data
                .get("account")
                .and_then(|v| v.as_str())
                .ok_or("pad missing account")?
                .to_string();
            let source_account = json
                .data
                .get("source_account")
                .and_then(|v| v.as_str())
                .ok_or("pad missing source_account")?
                .to_string();
            Ok(Directive::Pad(Pad {
                date,
                account,
                source_account,
                meta: std::collections::HashMap::new(),
            }))
        }
        "event" => {
            let event_type = json
                .data
                .get("type")
                .and_then(|v| v.as_str())
                .ok_or("event missing type")?
                .to_string();
            let value = json
                .data
                .get("value")
                .and_then(|v| v.as_str())
                .ok_or("event missing value")?
                .to_string();
            Ok(Directive::Event(Event {
                date,
                event_type,
                value,
                meta: std::collections::HashMap::new(),
            }))
        }
        "note" => {
            let account = json
                .data
                .get("account")
                .and_then(|v| v.as_str())
                .ok_or("note missing account")?
                .to_string();
            let comment = json
                .data
                .get("comment")
                .and_then(|v| v.as_str())
                .ok_or("note missing comment")?
                .to_string();
            Ok(Directive::Note(Note {
                date,
                account,
                comment,
                meta: std::collections::HashMap::new(),
            }))
        }
        "document" => {
            let account = json
                .data
                .get("account")
                .and_then(|v| v.as_str())
                .ok_or("document missing account")?
                .to_string();
            let path = json
                .data
                .get("path")
                .and_then(|v| v.as_str())
                .ok_or("document missing path")?
                .to_string();
            Ok(Directive::Document(Document {
                date,
                account,
                path,
                tags: Vec::new(),
                links: Vec::new(),
                meta: std::collections::HashMap::new(),
            }))
        }
        "price" => {
            let currency = json
                .data
                .get("currency")
                .and_then(|v| v.as_str())
                .ok_or("price missing currency")?
                .to_string();
            let amount_json = json.data.get("amount").ok_or("price missing amount")?;
            let amount = json_to_amount(amount_json)?;
            Ok(Directive::Price(Price {
                date,
                currency,
                amount,
                meta: std::collections::HashMap::new(),
            }))
        }
        "query" => {
            let name = json
                .data
                .get("name")
                .and_then(|v| v.as_str())
                .ok_or("query missing name")?
                .to_string();
            let query = json
                .data
                .get("query")
                .and_then(|v| v.as_str())
                .ok_or("query missing query")?
                .to_string();
            Ok(Directive::Query(rustledger_core::Query {
                date,
                name,
                query,
                meta: std::collections::HashMap::new(),
            }))
        }
        "custom" => {
            let custom_type = json
                .data
                .get("type")
                .and_then(|v| v.as_str())
                .ok_or("custom missing type")?
                .to_string();
            Ok(Directive::Custom(Custom {
                date,
                custom_type,
                values: Vec::new(),
                meta: std::collections::HashMap::new(),
            }))
        }
        other => Err(format!("unknown directive type: {other}")),
    }
}

fn json_to_amount(json: &serde_json::Value) -> Result<Amount, String> {
    use rustledger_core::Decimal;

    let number = json
        .get("number")
        .and_then(|v| v.as_str())
        .ok_or("amount missing number")?;
    let currency = json
        .get("currency")
        .and_then(|v| v.as_str())
        .ok_or("amount missing currency")?;

    let decimal: Decimal = number
        .parse()
        .map_err(|e| format!("invalid number '{number}': {e}"))?;

    Ok(Amount::new(decimal, currency))
}

fn value_to_json(value: &rustledger_query::Value) -> serde_json::Value {
    use rustledger_query::Value;

    match value {
        Value::String(s) => serde_json::Value::String(s.clone()),
        Value::Number(n) => serde_json::json!(n.to_string()),
        Value::Integer(i) => serde_json::json!(i),
        Value::Date(d) => serde_json::Value::String(d.to_string()),
        Value::Boolean(b) => serde_json::Value::Bool(*b),
        Value::Amount(a) => amount_to_json(a),
        Value::Position(p) => serde_json::json!({
            "units": amount_to_json(&p.units),
            "cost": p.cost.as_ref().map(|c| serde_json::json!({
                "number": c.number.to_string(),
                "currency": c.currency,
                "date": c.date.map(|d| d.to_string()),
                "label": c.label,
            })),
        }),
        Value::Inventory(inv) => serde_json::json!({
            "positions": inv.positions().iter().map(|p| serde_json::json!({
                "units": amount_to_json(&p.units),
            })).collect::<Vec<_>>(),
        }),
        Value::StringSet(set) => serde_json::json!(set),
        Value::Null => serde_json::Value::Null,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple() {
        let source = r#"
2024-01-01 open Assets:Bank USD

2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food:Coffee  5.00 USD
  Assets:Bank          -5.00 USD
"#;

        let result = parse_beancount(source);
        assert!(result.errors.is_empty());
        assert_eq!(result.directives.len(), 2);
    }

    #[test]
    fn test_version() {
        let v = version();
        assert!(!v.is_empty());
    }

    #[test]
    fn test_json_to_directive_roundtrip() {
        let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food:Coffee  5.00 USD
  Assets:Bank          -5.00 USD
2024-01-20 balance Assets:Bank 100.00 USD
"#;

        let result = parse_beancount(source);
        assert!(result.errors.is_empty());

        // Convert to JSON
        for spanned in &result.directives {
            let json = directive_to_json(&spanned.value);

            // Convert back from JSON
            let reconstructed = json_to_directive(&json).expect("should reconstruct directive");

            // Verify directive types match
            match (&spanned.value, &reconstructed) {
                (Directive::Open(a), Directive::Open(b)) => {
                    assert_eq!(a.date, b.date);
                    assert_eq!(a.account, b.account);
                    assert_eq!(a.currencies, b.currencies);
                }
                (Directive::Transaction(a), Directive::Transaction(b)) => {
                    assert_eq!(a.date, b.date);
                    assert_eq!(a.narration, b.narration);
                    assert_eq!(a.postings.len(), b.postings.len());
                }
                (Directive::Balance(a), Directive::Balance(b)) => {
                    assert_eq!(a.date, b.date);
                    assert_eq!(a.account, b.account);
                    assert_eq!(a.amount.number, b.amount.number);
                    assert_eq!(a.amount.currency, b.amount.currency);
                }
                _ => panic!("directive type mismatch"),
            }
        }
    }

    #[test]
    fn test_validate_ledger_reconstruction() {
        // Test that we can reconstruct directives for validation
        let ledger = Ledger {
            directives: vec![
                DirectiveJson {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    data: serde_json::json!({
                        "account": "Assets:Bank",
                        "currencies": ["USD"],
                    }),
                },
                DirectiveJson {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-15".to_string(),
                    data: serde_json::json!({
                        "flag": "*",
                        "narration": "Test",
                        "postings": [
                            {
                                "account": "Assets:Bank",
                                "units": {"number": "100.00", "currency": "USD"},
                            },
                            {
                                "account": "Equity:Opening",
                                "units": {"number": "-100.00", "currency": "USD"},
                            },
                        ],
                    }),
                },
            ],
            options: LedgerOptions::default(),
        };

        // Reconstruct directives from JSON
        let mut directives = Vec::new();
        for dir_json in &ledger.directives {
            let directive = json_to_directive(dir_json).expect("should reconstruct directive");
            directives.push(directive);
        }

        // Verify we got the right directives
        assert_eq!(directives.len(), 2);
        assert!(matches!(directives[0], Directive::Open(_)));
        assert!(matches!(directives[1], Directive::Transaction(_)));

        // Run validation (should find Equity:Opening not opened)
        let validation_errors = validate_ledger(&directives);
        assert!(
            !validation_errors.is_empty(),
            "should detect Equity:Opening not opened"
        );
    }

    #[test]
    fn test_all_directive_types_reconstruction() {
        // Test reconstruction of all directive types
        let test_cases = vec![
            DirectiveJson {
                directive_type: "open".to_string(),
                date: "2024-01-01".to_string(),
                data: serde_json::json!({"account": "Assets:Bank", "currencies": ["USD"]}),
            },
            DirectiveJson {
                directive_type: "close".to_string(),
                date: "2024-12-31".to_string(),
                data: serde_json::json!({"account": "Assets:Bank"}),
            },
            DirectiveJson {
                directive_type: "commodity".to_string(),
                date: "2024-01-01".to_string(),
                data: serde_json::json!({"currency": "USD"}),
            },
            DirectiveJson {
                directive_type: "balance".to_string(),
                date: "2024-01-15".to_string(),
                data: serde_json::json!({"account": "Assets:Bank", "amount": {"number": "100.00", "currency": "USD"}}),
            },
            DirectiveJson {
                directive_type: "pad".to_string(),
                date: "2024-01-01".to_string(),
                data: serde_json::json!({"account": "Assets:Bank", "source_account": "Equity:Opening"}),
            },
            DirectiveJson {
                directive_type: "event".to_string(),
                date: "2024-01-01".to_string(),
                data: serde_json::json!({"type": "location", "value": "NYC"}),
            },
            DirectiveJson {
                directive_type: "note".to_string(),
                date: "2024-01-01".to_string(),
                data: serde_json::json!({"account": "Assets:Bank", "comment": "Test note"}),
            },
            DirectiveJson {
                directive_type: "document".to_string(),
                date: "2024-01-01".to_string(),
                data: serde_json::json!({"account": "Assets:Bank", "path": "/path/to/doc.pdf"}),
            },
            DirectiveJson {
                directive_type: "price".to_string(),
                date: "2024-01-01".to_string(),
                data: serde_json::json!({"currency": "AAPL", "amount": {"number": "150.00", "currency": "USD"}}),
            },
            DirectiveJson {
                directive_type: "query".to_string(),
                date: "2024-01-01".to_string(),
                data: serde_json::json!({"name": "test_query", "query": "SELECT account"}),
            },
            DirectiveJson {
                directive_type: "custom".to_string(),
                date: "2024-01-01".to_string(),
                data: serde_json::json!({"type": "budget"}),
            },
        ];

        for json in test_cases {
            let result = json_to_directive(&json);
            assert!(
                result.is_ok(),
                "failed to reconstruct {}: {:?}",
                json.directive_type,
                result.err()
            );
        }
    }
}
