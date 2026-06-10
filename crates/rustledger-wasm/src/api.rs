//! Public WASM API functions.
//!
//! These functions are exposed to JavaScript via wasm-bindgen.

use std::collections::HashMap;
use std::path::Path;
use wasm_bindgen::prelude::*;

use rustledger_core::Directive;
use rustledger_loader::{FileSystem, LoadError, LoadResult};
use rustledger_parser::parse as parse_beancount;

use crate::convert::{directive_to_json, value_to_cell};
use crate::helpers::{extract_options, load_and_book, run_validation, to_js};
#[cfg(feature = "completions")]
use crate::types::{CompletionJson, CompletionResultJson};
use crate::types::{
    Error, FormatResult, Ledger, PadResult, ParseResult, QueryResult, Severity, ValidationResult,
};
#[cfg(feature = "plugins")]
use crate::types::{PluginInfo, PluginResult};
use crate::utils::LineLookup;

/// Convert [`LoadResult`] errors to detailed Error objects with line/column info.
///
/// This preserves parse error details that would be lost by simple `to_string()`.
fn load_errors_to_errors(load_result: &LoadResult) -> Vec<Error> {
    let mut errors = Vec::new();

    for load_error in &load_result.errors {
        match load_error {
            LoadError::ParseErrors {
                path,
                errors: parse_errors,
            } => {
                // Expand parse errors with file path and line info
                for parse_error in parse_errors {
                    let span = parse_error.span();
                    // Try to get line number from source map
                    let line = load_result
                        .source_map
                        .get_by_path(path)
                        .map(|file| file.line_col(span.0).0 as u32);

                    let msg = format!("{}: {}", path.display(), parse_error);
                    if let Some(line_num) = line {
                        errors.push(Error::with_line(msg, line_num));
                    } else {
                        errors.push(Error::new(msg));
                    }
                }
            }
            other => {
                // Other errors use default string conversion
                errors.push(Error::new(other.to_string()));
            }
        }
    }

    errors
}

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

/// Validate a Beancount source string.
///
/// Parses, interpolates, and validates in one step.
/// Returns a `ValidationResult` indicating whether the ledger is valid.
#[wasm_bindgen(js_name = "validateSource")]
pub fn validate_source(source: &str) -> Result<JsValue, JsError> {
    let load = load_and_book(source);
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

    let load = load_and_book(source);

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
                errors: vec![Error::new(e.to_string())],
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
    use rustledger_parser::format::format_source_with_parsed;

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

    // Reuse the `parse_result` we produced for the error gate above
    // instead of letting `format_source` re-parse. Byte-identical
    // output per parser-side `format_source_with_parsed_matches_format_source`.
    let formatted = format_source_with_parsed(&parse_result, source);

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

    let load = load_and_book(source);

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
/// Materialize a plugin's `ops` against its input wrapper list,
/// producing the resulting flat wrapper list. Used by WASM entry
/// points that need to round-trip a plugin's output back to
/// `Vec<Directive>` for JSON serialization.
#[cfg(feature = "plugins")]
pub fn materialize_plugin_ops(
    input: &[rustledger_plugin::types::DirectiveWrapper],
    output: &rustledger_plugin::types::PluginOutput,
) -> Vec<rustledger_plugin::types::DirectiveWrapper> {
    let mut out = Vec::with_capacity(output.ops.len());
    for op in &output.ops {
        match op {
            rustledger_plugin::PluginOp::Keep(i) => {
                if let Some(w) = input.get(*i) {
                    out.push(w.clone());
                }
            }
            rustledger_plugin::PluginOp::Modify(_, w) | rustledger_plugin::PluginOp::Insert(w) => {
                out.push(w.clone());
            }
            rustledger_plugin::PluginOp::Delete(_) => {}
        }
    }
    out
}

/// Run a single named plugin against a Beancount source and return
/// the resulting directives as JSON.
#[cfg(feature = "plugins")]
#[wasm_bindgen(js_name = "runPlugin")]
pub fn run_plugin(source: &str, plugin_name: &str) -> Result<JsValue, JsError> {
    use rustledger_plugin::{
        NativePluginRegistry, PluginInput, PluginOptions, directives_to_wrappers,
        wrappers_to_directives,
    };

    let load = load_and_book(source);

    // Return early if there were parse/interpolation errors
    if !load.errors.is_empty() {
        let result = PluginResult {
            directives: Vec::new(),
            errors: load.errors,
        };
        return to_js(&result);
    }

    // Find and run the plugin
    let registry = NativePluginRegistry::global();
    // External API runs plugins on already-booked input — synth
    // plugins are a loader-internal concern and would re-emit Opens
    // for accounts the booking pass already opened.
    let Some(plugin) = registry.find_regular(plugin_name) else {
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

    let input_dirs = input.directives.clone();
    let output = plugin.process(input);

    // Materialize ops back to wrappers, then convert.
    let materialized_wrappers = materialize_plugin_ops(&input_dirs, &output);
    let output_directives = match wrappers_to_directives(&materialized_wrappers) {
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

    let registry = NativePluginRegistry::global();
    let plugins: Vec<PluginInfo> = registry
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

/// Parse multiple Beancount files with include resolution.
///
/// This function accepts a map of file paths to file contents and an entry point,
/// resolving `include` directives across the files. This enables multi-file ledgers
/// in WASM environments where filesystem access is not available.
///
/// # Arguments
///
/// * `files` - A JavaScript object mapping file paths to their contents.
///   Example: `{ "main.beancount": "include \"accounts.beancount\"", "accounts.beancount": "..." }`
/// * `entry_point` - The main file to start loading from (must exist in `files`).
///
/// # Returns
///
/// A `ParseResult` with the parsed ledger from all files and any errors.
///
/// # Example (JavaScript)
///
/// ```javascript
/// const result = parseMultiFile({
///   "main.beancount": `
///     include "accounts.beancount"
///     2024-01-15 * "Coffee"
///       Expenses:Food  5.00 USD
///       Assets:Bank
///   `,
///   "accounts.beancount": `
///     2024-01-01 open Assets:Bank USD
///     2024-01-01 open Expenses:Food USD
///   `
/// }, "main.beancount");
/// ```
#[wasm_bindgen(js_name = "parseMultiFile")]
pub fn parse_multi_file(files: JsValue, entry_point: &str) -> Result<JsValue, JsError> {
    use rustledger_booking::interpolate;
    use rustledger_loader::{Loader, VirtualFileSystem};

    // Parse the JavaScript object to a HashMap
    let file_map: HashMap<String, String> = serde_wasm_bindgen::from_value(files)
        .map_err(|e| JsError::new(&format!("Invalid files object: {e}")))?;

    if file_map.is_empty() {
        return Err(JsError::new("Files map cannot be empty"));
    }

    // Create virtual filesystem with all files
    let vfs = VirtualFileSystem::from_files(file_map);

    // Check entry point exists using VFS path normalization
    if !vfs.exists(Path::new(entry_point)) {
        return Err(JsError::new(&format!(
            "Entry point '{entry_point}' not found in files map"
        )));
    }

    // Create loader with virtual filesystem
    let mut loader = Loader::new().with_filesystem(Box::new(vfs));

    // Load from entry point
    let load_result = match loader.load(Path::new(entry_point)) {
        Ok(result) => result,
        Err(e) => {
            let result = ParseResult {
                ledger: None,
                errors: vec![Error::new(format!("Load error: {e}"))],
            };
            return to_js(&result);
        }
    };

    // Collect load errors with detailed parse error info
    let mut errors = load_errors_to_errors(&load_result);

    // Extract options from loader options
    let options = crate::types::LedgerOptions {
        title: load_result.options.title.clone(),
        operating_currencies: load_result.options.operating_currency.clone(),
    };

    // Extract and interpolate directives
    let mut directives: Vec<Directive> = load_result
        .directives
        .into_iter()
        .map(|s| s.value)
        .collect();

    // Interpolate transactions (fill in missing amounts)
    if errors.is_empty() {
        for directive in &mut directives {
            if let Directive::Transaction(txn) = directive {
                match interpolate(txn) {
                    Ok(result) => {
                        *txn = result.transaction;
                    }
                    Err(e) => {
                        errors.push(Error::new(e.to_string()));
                    }
                }
            }
        }
    }

    let ledger = Some(Ledger {
        directives: directives.iter().map(directive_to_json).collect(),
        options,
    });

    let result = ParseResult { ledger, errors };
    to_js(&result)
}

/// Validate multiple Beancount files with include resolution.
///
/// Similar to `parseMultiFile`, but also runs validation.
/// Returns a `ValidationResult` indicating whether the ledger is valid.
#[wasm_bindgen(js_name = "validateMultiFile")]
pub fn validate_multi_file(files: JsValue, entry_point: &str) -> Result<JsValue, JsError> {
    use rustledger_loader::{LoadOptions, Loader, VirtualFileSystem, process};

    // Parse the JavaScript object to a HashMap
    let file_map: HashMap<String, String> = serde_wasm_bindgen::from_value(files)
        .map_err(|e| JsError::new(&format!("Invalid files object: {e}")))?;

    if file_map.is_empty() {
        return Err(JsError::new("Files map cannot be empty"));
    }

    // Create virtual filesystem with all files
    let vfs = VirtualFileSystem::from_files(file_map);

    // Check entry point exists using VFS path normalization
    if !vfs.exists(Path::new(entry_point)) {
        return Err(JsError::new(&format!(
            "Entry point '{entry_point}' not found in files map"
        )));
    }

    // Create loader with virtual filesystem
    let mut loader = Loader::new().with_filesystem(Box::new(vfs));

    // Load from entry point
    let load_result = match loader.load(Path::new(entry_point)) {
        Ok(result) => result,
        Err(e) => {
            let result = ValidationResult {
                valid: false,
                errors: vec![Error::new(format!("Load error: {e}"))],
            };
            return to_js(&result);
        }
    };

    // Check for parse errors first (preserves detailed per-error line info)
    let parse_errors = load_errors_to_errors(&load_result);
    if !parse_errors.is_empty() {
        let result = ValidationResult {
            valid: false,
            errors: parse_errors,
        };
        return to_js(&result);
    }

    // Run the shared processing pipeline:
    // sort → synth-plugins → Early validation → book → regular-plugins → Late validation → finalize
    let options = LoadOptions {
        validate: true,
        ..Default::default()
    };

    let ledger = match process(load_result, &options) {
        Ok(ledger) => ledger,
        Err(e) => {
            let result = ValidationResult {
                valid: false,
                errors: vec![Error::new(format!("Processing error: {e}"))],
            };
            return to_js(&result);
        }
    };

    let errors: Vec<Error> = ledger.errors.into_iter().map(Error::from).collect();

    let result = ValidationResult {
        valid: errors.is_empty(),
        errors,
    };
    to_js(&result)
}

/// Run a BQL query on multiple Beancount files.
///
/// Similar to `query`, but accepts multiple files with include resolution.
///
/// Note: Glob patterns in `include` directives are not supported in multi-file mode
/// since there is no real filesystem to enumerate. Use explicit file paths instead.
#[wasm_bindgen(js_name = "queryMultiFile")]
pub fn query_multi_file(
    files: JsValue,
    entry_point: &str,
    query_str: &str,
) -> Result<JsValue, JsError> {
    use rustledger_booking::expand_pads;
    use rustledger_loader::{LoadOptions, Loader, VirtualFileSystem, process};
    use rustledger_query::{Executor, parse as parse_query};

    // Parse the JavaScript object to a HashMap
    let file_map: HashMap<String, String> = serde_wasm_bindgen::from_value(files)
        .map_err(|e| JsError::new(&format!("Invalid files object: {e}")))?;

    if file_map.is_empty() {
        return Err(JsError::new("Files map cannot be empty"));
    }

    // Create virtual filesystem with all files
    let vfs = VirtualFileSystem::from_files(file_map);

    // Check entry point exists using VFS path normalization
    if !vfs.exists(Path::new(entry_point)) {
        return Err(JsError::new(&format!(
            "Entry point '{entry_point}' not found in files map"
        )));
    }

    // Create loader with virtual filesystem
    let mut loader = Loader::new().with_filesystem(Box::new(vfs));

    // Load from entry point
    let load_result = match loader.load(Path::new(entry_point)) {
        Ok(result) => result,
        Err(e) => {
            let result = QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors: vec![Error::new(format!("Load error: {e}"))],
            };
            return to_js(&result);
        }
    };

    // Check for parse errors first (preserves detailed per-error line info)
    let parse_errors = load_errors_to_errors(&load_result);
    if !parse_errors.is_empty() {
        let result = QueryResult {
            columns: Vec::new(),
            rows: Vec::new(),
            errors: parse_errors,
        };
        return to_js(&result);
    }

    // Run the shared processing pipeline (queries skip validation):
    // sort → synth-plugins → book → regular-plugins → finalize
    let options = LoadOptions {
        validate: false,
        ..Default::default()
    };

    let ledger = match process(load_result, &options) {
        Ok(ledger) => ledger,
        Err(e) => {
            let result = QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors: vec![Error::new(format!("Processing error: {e}"))],
            };
            return to_js(&result);
        }
    };

    // Only abort on actual errors, not warnings (matching CLI query behavior)
    let errors: Vec<Error> = ledger.errors.into_iter().map(Error::from).collect();
    let has_errors = errors.iter().any(|e| e.severity == Severity::Error);
    if has_errors {
        let result = QueryResult {
            columns: Vec::new(),
            rows: Vec::new(),
            errors,
        };
        return to_js(&result);
    }

    // Expand pads into synthetic transactions (matching CLI query pipeline)
    let booked_directives: Vec<_> = ledger.directives.into_iter().map(|s| s.value).collect();
    let directives = expand_pads(&booked_directives);

    // Parse the query
    let query = match parse_query(query_str) {
        Ok(q) => q,
        Err(e) => {
            let result = QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors: vec![Error::new(e.to_string())],
            };
            return to_js(&result);
        }
    };

    // Execute query
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

/// Compute a SHA-256 fingerprint of one or more source strings.
///
/// Returns the fingerprint as a lowercase hex string. Store this value
/// alongside serialized ledger bytes and compare on subsequent loads to
/// detect whether the source has changed.
///
/// Each string is separated by a NUL byte before hashing so that
/// `["ab", "c"]` produces a different fingerprint from `["a", "bc"]`.
///
/// The fingerprint is order-sensitive: `["a", "b"]` hashes differently
/// from `["b", "a"]`. Callers using an unordered collection should sort
/// by filename first for deterministic results.
#[wasm_bindgen(js_name = "hashSources")]
#[allow(clippy::needless_pass_by_value)] // wasm-bindgen requires owned Vec<String>
pub fn hash_sources(sources: Vec<String>) -> String {
    let refs: Vec<&str> = sources.iter().map(String::as_str).collect();
    crate::cache::hash_sources(&refs)
}
