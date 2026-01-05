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

mod convert;
pub mod types;
mod utils;

use std::collections::HashMap;
use wasm_bindgen::prelude::*;

use rustledger_core::Directive;
use rustledger_parser::parse as parse_beancount;
use rustledger_validate::validate as validate_ledger;

use convert::{directive_to_json, json_to_directive, value_to_cell};
use types::{
    CompletionJson, CompletionResultJson, Error, FormatResult, Ledger, LedgerOptions, PadResult,
    ParseResult, PluginInfo, PluginResult, QueryResult, ValidationResult,
};
use utils::LineLookup;

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

    let ledger = Some(Ledger {
        directives: result
            .directives
            .iter()
            .map(|spanned| directive_to_json(&spanned.value))
            .collect(),
        options: LedgerOptions::default(),
    });

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
/// Parses, interpolates, and validates in one step.
#[wasm_bindgen]
pub fn validate_source(source: &str) -> JsValue {
    use rustledger_booking::interpolate;

    let parse_result = parse_beancount(source);
    let lookup = LineLookup::new(source);

    // Collect parse errors
    let mut errors: Vec<Error> = parse_result
        .errors
        .iter()
        .map(|e| Error {
            message: e.to_string(),
            line: Some(lookup.byte_to_line(e.span().0)),
            column: None,
            severity: "error".to_string(),
        })
        .collect();

    // If parsing succeeded, run interpolation then validation
    if parse_result.errors.is_empty() {
        // Build a map from date to line number for error reporting
        let mut date_to_line: HashMap<String, u32> = HashMap::new();
        for spanned in &parse_result.directives {
            let line = lookup.byte_to_line(spanned.span.start);
            let date = match &spanned.value {
                Directive::Transaction(t) => t.date.to_string(),
                Directive::Balance(b) => b.date.to_string(),
                Directive::Open(o) => o.date.to_string(),
                Directive::Close(c) => c.date.to_string(),
                Directive::Pad(p) => p.date.to_string(),
                Directive::Commodity(c) => c.date.to_string(),
                Directive::Event(e) => e.date.to_string(),
                Directive::Query(q) => q.date.to_string(),
                Directive::Note(n) => n.date.to_string(),
                Directive::Document(d) => d.date.to_string(),
                Directive::Price(p) => p.date.to_string(),
                Directive::Custom(c) => c.date.to_string(),
            };
            date_to_line.entry(date).or_insert(line);
        }

        let mut directives: Vec<_> = parse_result
            .directives
            .iter()
            .map(|s| s.value.clone())
            .collect();

        // Interpolate transactions (fill in missing amounts)
        for (i, directive) in directives.iter_mut().enumerate() {
            if let Directive::Transaction(txn) = directive {
                match interpolate(txn) {
                    Ok(result) => {
                        *txn = result.transaction;
                    }
                    Err(e) => {
                        let line = lookup.byte_to_line(parse_result.directives[i].span.start);
                        errors.push(Error {
                            message: e.to_string(),
                            line: Some(line),
                            column: None,
                            severity: "error".to_string(),
                        });
                    }
                }
            }
        }

        // Run validation
        let validation_errors = validate_ledger(&directives);
        for err in validation_errors {
            let line = date_to_line.get(&err.date.to_string()).copied();
            errors.push(Error {
                message: err.message,
                line,
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
/// Parses the source, interpolates, then executes the query.
#[wasm_bindgen]
pub fn query(source: &str, query_str: &str) -> JsValue {
    use rustledger_booking::interpolate;
    use rustledger_query::{Executor, parse as parse_query};

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

    let lookup = LineLookup::new(source);

    // Extract and interpolate directives
    let mut directives: Vec<_> = parse_result
        .directives
        .iter()
        .map(|s| s.value.clone())
        .collect();

    let mut interpolation_errors = Vec::new();
    for (i, directive) in directives.iter_mut().enumerate() {
        if let Directive::Transaction(txn) = directive {
            match interpolate(txn) {
                Ok(result) => {
                    *txn = result.transaction;
                }
                Err(e) => {
                    let line = lookup.byte_to_line(parse_result.directives[i].span.start);
                    interpolation_errors.push(Error {
                        message: e.to_string(),
                        line: Some(line),
                        column: None,
                        severity: "error".to_string(),
                    });
                }
            }
        }
    }

    // Return errors if interpolation failed
    if !interpolation_errors.is_empty() {
        let result = QueryResult {
            columns: Vec::new(),
            rows: Vec::new(),
            errors: interpolation_errors,
        };
        return serde_wasm_bindgen::to_value(&result).unwrap_or(JsValue::NULL);
    }

    let mut executor = Executor::new(&directives);
    match executor.execute(&query) {
        Ok(result) => {
            let rows: Vec<Vec<_>> = result
                .rows
                .iter()
                .map(|row| row.iter().map(value_to_cell).collect())
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

/// Format a Beancount source string.
///
/// Parses and reformats with consistent alignment.
#[wasm_bindgen]
pub fn format(source: &str) -> JsValue {
    use rustledger_core::{FormatConfig, format_directive};

    let parse_result = parse_beancount(source);

    if !parse_result.errors.is_empty() {
        let result = FormatResult {
            formatted: None,
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

    let config = FormatConfig::default();
    let mut formatted = String::new();

    for spanned in &parse_result.directives {
        formatted.push_str(&format_directive(&spanned.value, &config));
        formatted.push('\n');
    }

    let result = FormatResult {
        formatted: Some(formatted),
        errors: Vec::new(),
    };

    serde_wasm_bindgen::to_value(&result).unwrap_or(JsValue::NULL)
}

/// Process pad directives and expand them.
///
/// Returns directives with pad-generated transactions included.
#[wasm_bindgen]
pub fn expand_pads(source: &str) -> JsValue {
    use rustledger_booking::{interpolate, process_pads};

    let parse_result = parse_beancount(source);

    if !parse_result.errors.is_empty() {
        let result = PadResult {
            directives: Vec::new(),
            padding_transactions: Vec::new(),
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

    // Extract and interpolate directives
    let mut directives: Vec<_> = parse_result
        .directives
        .iter()
        .map(|s| s.value.clone())
        .collect();

    for directive in &mut directives {
        if let Directive::Transaction(txn) = directive {
            if let Ok(result) = interpolate(txn) {
                *txn = result.transaction;
            }
        }
    }

    // Process pads
    let pad_result = process_pads(&directives);

    let result = PadResult {
        directives: pad_result
            .directives
            .iter()
            .map(directive_to_json)
            .collect(),
        padding_transactions: pad_result
            .padding_transactions
            .iter()
            .map(|txn| directive_to_json(&Directive::Transaction(txn.clone())))
            .collect(),
        errors: pad_result
            .errors
            .iter()
            .map(|e| Error {
                message: e.message.clone(),
                line: None,
                column: None,
                severity: "error".to_string(),
            })
            .collect(),
    };

    serde_wasm_bindgen::to_value(&result).unwrap_or(JsValue::NULL)
}

/// Run a native plugin on the source.
///
/// Available plugins: `implicit_prices`, `check_commodity`, `auto_accounts`,
/// `auto_tag`, `leafonly`, `noduplicates`, `onecommodity`, `unique_prices`,
/// `check_closing`, `close_tree`, `coherent_cost`, `sellgains`, `pedantic`, `unrealized`
#[wasm_bindgen]
pub fn run_plugin(source: &str, plugin_name: &str) -> JsValue {
    use rustledger_booking::interpolate;
    use rustledger_plugin::{
        NativePluginRegistry, PluginInput, PluginOptions, directives_to_wrappers,
        wrappers_to_directives,
    };

    let parse_result = parse_beancount(source);

    if !parse_result.errors.is_empty() {
        let result = PluginResult {
            directives: Vec::new(),
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

    // Extract and interpolate directives
    let mut directives: Vec<_> = parse_result
        .directives
        .iter()
        .map(|s| s.value.clone())
        .collect();

    for directive in &mut directives {
        if let Directive::Transaction(txn) = directive {
            if let Ok(result) = interpolate(txn) {
                *txn = result.transaction;
            }
        }
    }

    // Find and run the plugin
    let registry = NativePluginRegistry::new();
    let Some(plugin) = registry.find(plugin_name) else {
        let result = PluginResult {
            directives: Vec::new(),
            errors: vec![Error {
                message: format!("Unknown plugin: {plugin_name}"),
                line: None,
                column: None,
                severity: "error".to_string(),
            }],
        };
        return serde_wasm_bindgen::to_value(&result).unwrap_or(JsValue::NULL);
    };

    // Convert directives to plugin format and run
    let wrappers = directives_to_wrappers(&directives);
    let input = PluginInput {
        directives: wrappers,
        options: PluginOptions::default(),
        config: None,
    };

    let output = plugin.process(input);

    // Convert back
    let output_directives = match wrappers_to_directives(&output.directives) {
        Ok(dirs) => dirs,
        Err(e) => {
            let result = PluginResult {
                directives: Vec::new(),
                errors: vec![Error {
                    message: format!("Conversion error: {e}"),
                    line: None,
                    column: None,
                    severity: "error".to_string(),
                }],
            };
            return serde_wasm_bindgen::to_value(&result).unwrap_or(JsValue::NULL);
        }
    };

    let result = PluginResult {
        directives: output_directives.iter().map(directive_to_json).collect(),
        errors: output
            .errors
            .iter()
            .map(|e| Error {
                message: e.message.clone(),
                line: None,
                column: None,
                severity: match e.severity {
                    rustledger_plugin::PluginErrorSeverity::Warning => "warning".to_string(),
                    rustledger_plugin::PluginErrorSeverity::Error => "error".to_string(),
                },
            })
            .collect(),
    };

    serde_wasm_bindgen::to_value(&result).unwrap_or(JsValue::NULL)
}

/// List available native plugins.
#[wasm_bindgen]
pub fn list_plugins() -> JsValue {
    let plugins = vec![
        PluginInfo {
            name: "implicit_prices".to_string(),
            description: "Generate price entries from transaction costs/prices".to_string(),
        },
        PluginInfo {
            name: "check_commodity".to_string(),
            description: "Verify all commodities are declared".to_string(),
        },
        PluginInfo {
            name: "auto_accounts".to_string(),
            description: "Auto-generate Open directives for used accounts".to_string(),
        },
        PluginInfo {
            name: "auto_tag".to_string(),
            description: "Auto-tag transactions by account patterns".to_string(),
        },
        PluginInfo {
            name: "leafonly".to_string(),
            description: "Error on postings to non-leaf accounts".to_string(),
        },
        PluginInfo {
            name: "noduplicates".to_string(),
            description: "Hash-based duplicate transaction detection".to_string(),
        },
        PluginInfo {
            name: "onecommodity".to_string(),
            description: "Enforce single commodity per account".to_string(),
        },
        PluginInfo {
            name: "unique_prices".to_string(),
            description: "One price per day per currency pair".to_string(),
        },
        PluginInfo {
            name: "check_closing".to_string(),
            description: "Zero balance assertion on account closing".to_string(),
        },
        PluginInfo {
            name: "close_tree".to_string(),
            description: "Close descendant accounts automatically".to_string(),
        },
        PluginInfo {
            name: "coherent_cost".to_string(),
            description: "Enforce cost OR price (not both) consistency".to_string(),
        },
        PluginInfo {
            name: "sellgains".to_string(),
            description: "Cross-check capital gains against sales".to_string(),
        },
        PluginInfo {
            name: "pedantic".to_string(),
            description: "Enable all strict validation rules".to_string(),
        },
        PluginInfo {
            name: "unrealized".to_string(),
            description: "Calculate unrealized gains/losses".to_string(),
        },
    ];

    serde_wasm_bindgen::to_value(&plugins).unwrap_or(JsValue::NULL)
}

/// Calculate account balances.
///
/// Returns balances grouped by account.
#[wasm_bindgen]
pub fn balances(source: &str) -> JsValue {
    // Just use the query function with BALANCES
    query(source, "BALANCES")
}

/// Get BQL query completions at cursor position.
///
/// Returns context-aware completions for the BQL query language.
#[wasm_bindgen]
pub fn bql_completions(partial_query: &str, cursor_pos: usize) -> JsValue {
    use rustledger_query::completions;

    let result = completions::complete(partial_query, cursor_pos);

    let json_result = CompletionResultJson {
        completions: result
            .completions
            .into_iter()
            .map(|c| CompletionJson {
                text: c.text,
                category: c.category.as_str().to_string(),
                description: c.description,
            })
            .collect(),
        context: format!("{:?}", result.context),
    };

    serde_wasm_bindgen::to_value(&json_result).unwrap_or(JsValue::NULL)
}

#[cfg(test)]
mod tests {
    use super::*;
    use types::DirectiveJson;

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
    fn test_validate_ledger_reconstruction() {
        use types::{AmountValue, PostingJson};

        // Test that we can reconstruct directives for validation
        let ledger = Ledger {
            directives: vec![
                DirectiveJson::Open {
                    date: "2024-01-01".to_string(),
                    account: "Assets:Bank".to_string(),
                    currencies: vec!["USD".to_string()],
                    booking: None,
                },
                DirectiveJson::Transaction {
                    date: "2024-01-15".to_string(),
                    flag: "*".to_string(),
                    payee: None,
                    narration: Some("Test".to_string()),
                    tags: vec![],
                    links: vec![],
                    postings: vec![
                        PostingJson {
                            account: "Assets:Bank".to_string(),
                            units: Some(AmountValue {
                                number: "100.00".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                        },
                        PostingJson {
                            account: "Equity:Opening".to_string(),
                            units: Some(AmountValue {
                                number: "-100.00".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                        },
                    ],
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
}
