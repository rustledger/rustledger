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
//! import init, { parse, validateSource, query } from '@rustledger/wasm';
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
//!     const validation = validateSource(source);
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

use rustledger_booking::interpolate;
use rustledger_core::Directive;
use rustledger_parser::{ParseResult as ParserResult, parse as parse_beancount};
use rustledger_validate::validate as validate_ledger;

use convert::{directive_to_json, value_to_cell};
#[cfg(feature = "completions")]
use types::{CompletionJson, CompletionResultJson};
use types::{
    Error, FormatResult, Ledger, LedgerOptions, PadResult, ParseResult, QueryResult, Severity,
    ValidationResult,
};
#[cfg(feature = "plugins")]
use types::{PluginInfo, PluginResult};
use utils::LineLookup;

// =============================================================================
// TypeScript Type Definitions
// =============================================================================

#[wasm_bindgen(typescript_custom_section)]
const TS_TYPES: &'static str = r#"
/** Error severity level. */
export type Severity = 'error' | 'warning';

/** Error with source location information. */
export interface BeancountError {
    message: string;
    line?: number;
    column?: number;
    severity: Severity;
}

/** Amount with number and currency. */
export interface Amount {
    number: string;
    currency: string;
}

/** Posting cost specification. */
export interface PostingCost {
    number_per?: string;
    currency?: string;
    date?: string;
    label?: string;
}

/** A posting within a transaction. */
export interface Posting {
    account: string;
    units?: Amount;
    cost?: PostingCost;
    price?: Amount;
}

/** Base directive with date. */
interface BaseDirective {
    date: string;
}

/** Transaction directive. */
export interface TransactionDirective extends BaseDirective {
    type: 'transaction';
    flag: string;
    payee?: string;
    narration?: string;
    tags: string[];
    links: string[];
    postings: Posting[];
}

/** Balance assertion directive. */
export interface BalanceDirective extends BaseDirective {
    type: 'balance';
    account: string;
    amount: Amount;
}

/** Open account directive. */
export interface OpenDirective extends BaseDirective {
    type: 'open';
    account: string;
    currencies: string[];
    booking?: string;
}

/** Close account directive. */
export interface CloseDirective extends BaseDirective {
    type: 'close';
    account: string;
}

/** All directive types. */
export type Directive =
    | TransactionDirective
    | BalanceDirective
    | OpenDirective
    | CloseDirective
    | { type: 'commodity'; date: string; currency: string }
    | { type: 'pad'; date: string; account: string; source_account: string }
    | { type: 'event'; date: string; event_type: string; value: string }
    | { type: 'note'; date: string; account: string; comment: string }
    | { type: 'document'; date: string; account: string; path: string }
    | { type: 'price'; date: string; currency: string; amount: Amount }
    | { type: 'query'; date: string; name: string; query_string: string }
    | { type: 'custom'; date: string; custom_type: string };

/** Ledger options. */
export interface LedgerOptions {
    operating_currencies: string[];
    title?: string;
}

/** Parsed ledger. */
export interface Ledger {
    directives: Directive[];
    options: LedgerOptions;
}

/** Result of parsing a Beancount file. */
export interface ParseResult {
    ledger?: Ledger;
    errors: BeancountError[];
}

/** Result of validation. */
export interface ValidationResult {
    valid: boolean;
    errors: BeancountError[];
}

/** Cell value in query results. */
export type CellValue =
    | null
    | string
    | number
    | boolean
    | Amount
    | { units: Amount; cost?: { number: string; currency: string; date?: string; label?: string } }
    | { positions: Array<{ units: Amount }> }
    | string[];

/** Result of a BQL query. */
export interface QueryResult {
    columns: string[];
    rows: CellValue[][];
    errors: BeancountError[];
}

/** Result of formatting. */
export interface FormatResult {
    formatted?: string;
    errors: BeancountError[];
}

/** Result of pad expansion. */
export interface PadResult {
    directives: Directive[];
    padding_transactions: Directive[];
    errors: BeancountError[];
}

/** Result of running a plugin. */
export interface PluginResult {
    directives: Directive[];
    errors: BeancountError[];
}

/** Plugin information. */
export interface PluginInfo {
    name: string;
    description: string;
}

/** BQL completion suggestion. */
export interface Completion {
    text: string;
    category: string;
    description?: string;
}

/** Result of BQL completion request. */
export interface CompletionResult {
    completions: Completion[];
    context: string;
}

/**
 * A parsed and validated ledger that caches the parse result.
 * Use this class when you need to perform multiple operations on the same
 * source without re-parsing each time.
 */
export class ParsedLedger {
    constructor(source: string);
    free(): void;

    /** Check if the ledger is valid (no parse or validation errors). */
    isValid(): boolean;

    /** Get all errors (parse + validation). */
    getErrors(): BeancountError[];

    /** Get parse errors only. */
    getParseErrors(): BeancountError[];

    /** Get validation errors only. */
    getValidationErrors(): BeancountError[];

    /** Get the parsed directives. */
    getDirectives(): Directive[];

    /** Get the ledger options. */
    getOptions(): LedgerOptions;

    /** Get the number of directives. */
    directiveCount(): number;

    /** Run a BQL query on this ledger. */
    query(queryStr: string): QueryResult;

    /** Get account balances (shorthand for query("BALANCES")). */
    balances(): QueryResult;

    /** Format the ledger source. */
    format(): FormatResult;

    /** Expand pad directives. */
    expandPads(): PadResult;

    /** Run a native plugin on this ledger. */
    runPlugin(pluginName: string): PluginResult;
}
"#;

// =============================================================================
// Initialization
// =============================================================================

/// Initialize the WASM module.
///
/// This sets up panic hooks for better error messages in the browser console.
/// Call this once before using any other functions.
#[wasm_bindgen(start)]
pub fn init() {
    // Set up panic hook for better error messages
    console_error_panic_hook::set_once();
}

// =============================================================================
// Internal Helpers
// =============================================================================

/// Result of loading and interpolating a source file.
struct LoadResult {
    directives: Vec<Directive>,
    options: LedgerOptions,
    errors: Vec<Error>,
    lookup: LineLookup,
    parse_result: ParserResult,
}

/// Parse and interpolate a Beancount source string.
///
/// This is the common entry point for all processing functions.
fn load_and_interpolate(source: &str) -> LoadResult {
    let parse_result = parse_beancount(source);
    let lookup = LineLookup::new(source);

    // Collect parse errors
    let mut errors: Vec<Error> = parse_result
        .errors
        .iter()
        .map(|e| Error::with_line(e.to_string(), lookup.byte_to_line(e.span().0)))
        .collect();

    // Extract options
    let options = extract_options(&parse_result.options);

    // Extract directives
    let mut directives: Vec<_> = parse_result
        .directives
        .iter()
        .map(|s| s.value.clone())
        .collect();

    // Interpolate transactions (fill in missing amounts)
    if errors.is_empty() {
        for (i, directive) in directives.iter_mut().enumerate() {
            if let Directive::Transaction(txn) = directive {
                match interpolate(txn) {
                    Ok(result) => {
                        *txn = result.transaction;
                    }
                    Err(e) => {
                        let line = lookup.byte_to_line(parse_result.directives[i].span.start);
                        errors.push(Error::with_line(e.to_string(), line));
                    }
                }
            }
        }
    }

    LoadResult {
        directives,
        options,
        errors,
        lookup,
        parse_result,
    }
}

/// Run validation on a loaded ledger and return validation errors.
fn run_validation(load: &LoadResult) -> Vec<Error> {
    if !load.errors.is_empty() {
        return Vec::new();
    }

    let mut date_to_line: HashMap<String, u32> = HashMap::new();
    for spanned in &load.parse_result.directives {
        let line = load.lookup.byte_to_line(spanned.span.start);
        let date = spanned.value.date().to_string();
        date_to_line.entry(date).or_insert(line);
    }

    validate_ledger(&load.directives)
        .into_iter()
        .map(|err| {
            let line = date_to_line.get(&err.date.to_string()).copied();
            Error {
                message: err.message,
                line,
                column: None,
                severity: Severity::Error,
            }
        })
        .collect()
}

/// Serialize a value to `JsValue` using JSON-compatible settings.
///
/// This ensures:
/// - `None` serializes as `null` (not `undefined`)
/// - Maps serialize as plain objects (not ES2015 `Map`)
fn to_js<T: serde::Serialize>(value: &T) -> Result<JsValue, JsError> {
    let serializer = serde_wasm_bindgen::Serializer::json_compatible();
    value
        .serialize(&serializer)
        .map_err(|e| JsError::new(&e.to_string()))
}

// =============================================================================
// Public API
// =============================================================================

/// Parse a Beancount source string.
///
/// Returns a `ParseResult` with the parsed ledger and any errors.
#[wasm_bindgen]
pub fn parse(source: &str) -> Result<JsValue, JsError> {
    let result = parse_beancount(source);
    let lookup = LineLookup::new(source);

    let errors: Vec<Error> = result
        .errors
        .iter()
        .map(|e| Error::with_line(e.to_string(), lookup.byte_to_line(e.span().0)))
        .collect();

    // Extract options from parsed result
    let options = extract_options(&result.options);

    let ledger = Some(Ledger {
        directives: result
            .directives
            .iter()
            .map(|spanned| directive_to_json(&spanned.value))
            .collect(),
        options,
    });

    let parse_result = ParseResult { ledger, errors };
    to_js(&parse_result)
}

/// Extract [`LedgerOptions`] from parsed option directives.
fn extract_options(options: &[(String, String, rustledger_parser::Span)]) -> LedgerOptions {
    let mut ledger_options = LedgerOptions::default();

    for (key, value, _span) in options {
        match key.as_str() {
            "title" => ledger_options.title = Some(value.clone()),
            "operating_currency" => {
                ledger_options.operating_currencies.push(value.clone());
            }
            _ => {} // Ignore other options for now
        }
    }

    ledger_options
}

/// Validate a Beancount source string.
///
/// Parses, interpolates, and validates in one step.
/// Returns a `ValidationResult` indicating whether the ledger is valid.
#[wasm_bindgen(js_name = "validateSource")]
pub fn validate_source(source: &str) -> Result<JsValue, JsError> {
    let load = load_and_interpolate(source);
    let validation_errors = run_validation(&load);
    let mut errors = load.errors;
    errors.extend(validation_errors);

    let result = ValidationResult {
        valid: errors.is_empty(),
        errors,
    };
    to_js(&result)
}

/// Run a BQL query on a Beancount source string.
///
/// Parses the source, interpolates, then executes the query.
/// Returns a `QueryResult` with columns, rows, and any errors.
#[wasm_bindgen]
pub fn query(source: &str, query_str: &str) -> Result<JsValue, JsError> {
    use rustledger_query::{Executor, parse as parse_query};

    let load = load_and_interpolate(source);

    // Return early if there were parse/interpolation errors
    if !load.errors.is_empty() {
        let result = QueryResult {
            columns: Vec::new(),
            rows: Vec::new(),
            errors: load.errors,
        };
        return to_js(&result);
    }

    // Parse the query
    let query = match parse_query(query_str) {
        Ok(q) => q,
        Err(e) => {
            let result = QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors: vec![Error::new(format!("Query parse error: {e}"))],
            };
            return to_js(&result);
        }
    };

    let mut executor = Executor::new(&load.directives);
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
            to_js(&query_result)
        }
        Err(e) => {
            let result = QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors: vec![Error::new(format!("Query execution error: {e}"))],
            };
            to_js(&result)
        }
    }
}

/// Get version information.
///
/// Returns the version string of the rustledger-wasm package.
#[wasm_bindgen]
pub fn version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
}

/// Format a Beancount source string.
///
/// Parses and reformats with consistent alignment.
/// Returns a `FormatResult` with the formatted source or errors.
#[wasm_bindgen]
pub fn format(source: &str) -> Result<JsValue, JsError> {
    use rustledger_core::{FormatConfig, format_directive};

    let parse_result = parse_beancount(source);
    let lookup = LineLookup::new(source);

    if !parse_result.errors.is_empty() {
        let result = FormatResult {
            formatted: None,
            errors: parse_result
                .errors
                .iter()
                .map(|e| Error::with_line(e.to_string(), lookup.byte_to_line(e.span().0)))
                .collect(),
        };
        return to_js(&result);
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
    to_js(&result)
}

/// Process pad directives and expand them.
///
/// Returns directives with pad-generated transactions included.
#[wasm_bindgen(js_name = "expandPads")]
pub fn expand_pads(source: &str) -> Result<JsValue, JsError> {
    use rustledger_booking::process_pads;

    let load = load_and_interpolate(source);

    // Return early if there were parse/interpolation errors
    if !load.errors.is_empty() {
        let result = PadResult {
            directives: Vec::new(),
            padding_transactions: Vec::new(),
            errors: load.errors,
        };
        return to_js(&result);
    }

    // Process pads
    let pad_result = process_pads(&load.directives);

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
            .map(|e| Error::new(e.message.clone()))
            .collect(),
    };
    to_js(&result)
}

/// Run a native plugin on the source.
///
/// Available plugins can be listed with `listPlugins()`.
#[cfg(feature = "plugins")]
#[wasm_bindgen(js_name = "runPlugin")]
pub fn run_plugin(source: &str, plugin_name: &str) -> Result<JsValue, JsError> {
    use rustledger_plugin::{
        NativePluginRegistry, PluginInput, PluginOptions, directives_to_wrappers,
        wrappers_to_directives,
    };

    let load = load_and_interpolate(source);

    // Return early if there were parse/interpolation errors
    if !load.errors.is_empty() {
        let result = PluginResult {
            directives: Vec::new(),
            errors: load.errors,
        };
        return to_js(&result);
    }

    // Find and run the plugin
    let registry = NativePluginRegistry::new();
    let Some(plugin) = registry.find(plugin_name) else {
        let result = PluginResult {
            directives: Vec::new(),
            errors: vec![Error::new(format!("Unknown plugin: {plugin_name}"))],
        };
        return to_js(&result);
    };

    // Convert directives to plugin format and run
    let wrappers = directives_to_wrappers(&load.directives);
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
                errors: vec![Error::new(format!("Conversion error: {e}"))],
            };
            return to_js(&result);
        }
    };

    let result = PluginResult {
        directives: output_directives.iter().map(directive_to_json).collect(),
        errors: output
            .errors
            .iter()
            .map(|e| match e.severity {
                rustledger_plugin::PluginErrorSeverity::Warning => {
                    Error::warning(e.message.clone())
                }
                rustledger_plugin::PluginErrorSeverity::Error => Error::new(e.message.clone()),
            })
            .collect(),
    };
    to_js(&result)
}

/// List available native plugins.
///
/// Returns an array of `PluginInfo` objects with name and description.
#[cfg(feature = "plugins")]
#[wasm_bindgen(js_name = "listPlugins")]
pub fn list_plugins() -> Result<JsValue, JsError> {
    use rustledger_plugin::NativePluginRegistry;

    let registry = NativePluginRegistry::new();
    let plugins: Vec<PluginInfo> = registry
        .list()
        .iter()
        .map(|p| PluginInfo {
            name: p.name().to_string(),
            description: p.description().to_string(),
        })
        .collect();

    to_js(&plugins)
}

/// Calculate account balances.
///
/// Shorthand for `query(source, "BALANCES")`.
#[wasm_bindgen]
pub fn balances(source: &str) -> Result<JsValue, JsError> {
    query(source, "BALANCES")
}

/// Get BQL query completions at cursor position.
///
/// Returns context-aware completions for the BQL query language.
#[cfg(feature = "completions")]
#[wasm_bindgen(js_name = "bqlCompletions")]
pub fn bql_completions(partial_query: &str, cursor_pos: usize) -> Result<JsValue, JsError> {
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

    to_js(&json_result)
}

// =============================================================================
// Stateful Ledger Class
// =============================================================================

/// A parsed and validated ledger that caches the parse result.
///
/// Use this class when you need to perform multiple operations on the same
/// source without re-parsing each time.
///
/// # Example (JavaScript)
///
/// ```javascript
/// const ledger = new ParsedLedger(source);
/// if (ledger.isValid()) {
///     const balances = ledger.query("BALANCES");
///     const formatted = ledger.format();
/// }
/// ```
#[wasm_bindgen]
pub struct ParsedLedger {
    directives: Vec<Directive>,
    options: LedgerOptions,
    parse_errors: Vec<Error>,
    validation_errors: Vec<Error>,
}

#[wasm_bindgen]
impl ParsedLedger {
    /// Create a new `ParsedLedger` from source text.
    ///
    /// Parses, interpolates, and validates the source. Call `isValid()` to check for errors.
    #[wasm_bindgen(constructor)]
    pub fn new(source: &str) -> Self {
        let load = load_and_interpolate(source);
        let validation_errors = run_validation(&load);

        Self {
            directives: load.directives,
            options: load.options,
            parse_errors: load.errors,
            validation_errors,
        }
    }

    /// Check if the ledger is valid (no parse or validation errors).
    #[wasm_bindgen(js_name = "isValid")]
    pub fn is_valid(&self) -> bool {
        self.parse_errors.is_empty() && self.validation_errors.is_empty()
    }

    /// Get all errors (parse + validation).
    #[wasm_bindgen(js_name = "getErrors")]
    pub fn get_errors(&self) -> Result<JsValue, JsError> {
        let mut all_errors = self.parse_errors.clone();
        all_errors.extend(self.validation_errors.clone());
        to_js(&all_errors)
    }

    /// Get parse errors only.
    #[wasm_bindgen(js_name = "getParseErrors")]
    pub fn get_parse_errors(&self) -> Result<JsValue, JsError> {
        to_js(&self.parse_errors)
    }

    /// Get validation errors only.
    #[wasm_bindgen(js_name = "getValidationErrors")]
    pub fn get_validation_errors(&self) -> Result<JsValue, JsError> {
        to_js(&self.validation_errors)
    }

    /// Get the parsed directives.
    #[wasm_bindgen(js_name = "getDirectives")]
    pub fn get_directives(&self) -> Result<JsValue, JsError> {
        let directives: Vec<_> = self.directives.iter().map(directive_to_json).collect();
        to_js(&directives)
    }

    /// Get the ledger options.
    #[wasm_bindgen(js_name = "getOptions")]
    pub fn get_options(&self) -> Result<JsValue, JsError> {
        to_js(&self.options)
    }

    /// Get the number of directives.
    #[wasm_bindgen(js_name = "directiveCount")]
    pub fn directive_count(&self) -> usize {
        self.directives.len()
    }

    /// Run a BQL query on this ledger.
    #[wasm_bindgen]
    pub fn query(&self, query_str: &str) -> Result<JsValue, JsError> {
        use rustledger_query::{Executor, parse as parse_query};

        if !self.parse_errors.is_empty() {
            let result = QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors: self.parse_errors.clone(),
            };
            return to_js(&result);
        }

        let query = match parse_query(query_str) {
            Ok(q) => q,
            Err(e) => {
                let result = QueryResult {
                    columns: Vec::new(),
                    rows: Vec::new(),
                    errors: vec![Error::new(format!("Query parse error: {e}"))],
                };
                return to_js(&result);
            }
        };

        let mut executor = Executor::new(&self.directives);
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
                to_js(&query_result)
            }
            Err(e) => {
                let result = QueryResult {
                    columns: Vec::new(),
                    rows: Vec::new(),
                    errors: vec![Error::new(format!("Query execution error: {e}"))],
                };
                to_js(&result)
            }
        }
    }

    /// Get account balances (shorthand for query("BALANCES")).
    #[wasm_bindgen]
    pub fn balances(&self) -> Result<JsValue, JsError> {
        self.query("BALANCES")
    }

    /// Format the ledger source.
    #[wasm_bindgen]
    pub fn format(&self) -> Result<JsValue, JsError> {
        use rustledger_core::{FormatConfig, format_directive};

        if !self.parse_errors.is_empty() {
            let result = FormatResult {
                formatted: None,
                errors: self.parse_errors.clone(),
            };
            return to_js(&result);
        }

        let config = FormatConfig::default();
        let mut formatted = String::new();

        for directive in &self.directives {
            formatted.push_str(&format_directive(directive, &config));
            formatted.push('\n');
        }

        let result = FormatResult {
            formatted: Some(formatted),
            errors: Vec::new(),
        };
        to_js(&result)
    }

    /// Expand pad directives.
    #[wasm_bindgen(js_name = "expandPads")]
    pub fn expand_pads(&self) -> Result<JsValue, JsError> {
        use rustledger_booking::process_pads;

        if !self.parse_errors.is_empty() {
            let result = PadResult {
                directives: Vec::new(),
                padding_transactions: Vec::new(),
                errors: self.parse_errors.clone(),
            };
            return to_js(&result);
        }

        let pad_result = process_pads(&self.directives);

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
                .map(|e| Error::new(e.message.clone()))
                .collect(),
        };
        to_js(&result)
    }

    /// Run a native plugin on this ledger.
    #[cfg(feature = "plugins")]
    #[wasm_bindgen(js_name = "runPlugin")]
    pub fn run_plugin(&self, plugin_name: &str) -> Result<JsValue, JsError> {
        use rustledger_plugin::{
            NativePluginRegistry, PluginInput, PluginOptions, directives_to_wrappers,
            wrappers_to_directives,
        };

        if !self.parse_errors.is_empty() {
            let result = PluginResult {
                directives: Vec::new(),
                errors: self.parse_errors.clone(),
            };
            return to_js(&result);
        }

        let registry = NativePluginRegistry::new();
        let Some(plugin) = registry.find(plugin_name) else {
            let result = PluginResult {
                directives: Vec::new(),
                errors: vec![Error::new(format!("Unknown plugin: {plugin_name}"))],
            };
            return to_js(&result);
        };

        let wrappers = directives_to_wrappers(&self.directives);
        let input = PluginInput {
            directives: wrappers,
            options: PluginOptions::default(),
            config: None,
        };

        let output = plugin.process(input);

        let output_directives = match wrappers_to_directives(&output.directives) {
            Ok(dirs) => dirs,
            Err(e) => {
                let result = PluginResult {
                    directives: Vec::new(),
                    errors: vec![Error::new(format!("Conversion error: {e}"))],
                };
                return to_js(&result);
            }
        };

        let result = PluginResult {
            directives: output_directives.iter().map(directive_to_json).collect(),
            errors: output
                .errors
                .iter()
                .map(|e| match e.severity {
                    rustledger_plugin::PluginErrorSeverity::Warning => {
                        Error::warning(e.message.clone())
                    }
                    rustledger_plugin::PluginErrorSeverity::Error => Error::new(e.message.clone()),
                })
                .collect(),
        };
        to_js(&result)
    }
}

// =============================================================================
// Tests
// =============================================================================

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
    fn test_load_and_interpolate() {
        // Valid ledger
        let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;
        let load = load_and_interpolate(source);
        assert!(load.errors.is_empty());
        assert_eq!(load.directives.len(), 3);

        // Invalid ledger (unopened account)
        let source = r#"
2024-01-01 open Assets:Bank USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;
        let load = load_and_interpolate(source);
        assert!(load.errors.is_empty()); // Parse succeeds
        let validation_errors = validate_ledger(&load.directives);
        assert!(
            !validation_errors.is_empty(),
            "should detect Expenses:Food not opened"
        );
    }
}
