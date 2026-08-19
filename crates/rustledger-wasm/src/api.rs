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
use crate::helpers::{
    extract_options, has_fatal, load_and_book, parse_error_to_wasm, run_validation, to_js,
};
#[cfg(feature = "completions")]
use crate::types::{CompletionJson, CompletionResultJson};
use crate::types::{
    Error, FormatResult, Ledger, PadResult, ParseResult, QueryResult, Severity, ValidationResult,
};
#[cfg(feature = "plugins")]
use crate::types::{PluginInfo, PluginResult};
use crate::utils::LineLookup;

/// Whether a load error makes the directive stream unusable.
///
/// Not every load error does. `DuplicateInclude` says a file was reached twice
/// in the include graph — the loader still loaded it exactly once, so the
/// ledger is complete and every figure derived from it is right. It has to be
/// REPORTED (beancount says `Duplicate filename parsed` and `bean-check` exits
/// 1, as does `rledger check`), but aborting on it throws away a correct
/// answer: `rledger query` prints the notice and still returns the rows.
///
/// Treating every load error as fatal did exactly that — a query over a ledger
/// with a shared prices file included from two journals returned NO rows,
/// where the CLI returns them. The same shape as a warning being treated as an
/// error, one layer down.
fn load_error_is_fatal(error: &LoadError) -> bool {
    !matches!(error, LoadError::DuplicateInclude { .. })
}

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
                // Expand parse errors with the same rich fields as the
                // single-file path (code / phase / hint / file / full span).
                for parse_error in parse_errors {
                    let span = parse_error.span();
                    let file = load_result.source_map.get_by_path(path);
                    let mut err = Error::new(format!("{}: {}", path.display(), parse_error))
                        .with_code(format!("P{:04}", parse_error.kind_code()))
                        .with_phase("parse")
                        .with_hint(parse_error.hint.clone())
                        .with_file(Some(path.display().to_string()));
                    if let Some(file) = file {
                        let (sl, sc) = file.line_col(span.0);
                        let (el, ec) = file.line_col(span.1);
                        err = err.with_span((sl as u32, sc as u32), (el as u32, ec as u32));
                    }
                    errors.push(err);
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
        .map(|e| parse_error_to_wasm(e, &lookup, None))
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
        // Warnings do not invalidate a ledger (matching `rledger check`, which
        // exits 0 on warning-only input); only actual errors do.
        valid: !has_fatal(&errors),
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
    use rustledger_booking::merge_with_padding;
    use rustledger_query::{Executor, parse as parse_query};

    let load = load_and_book(source);

    // Return early only on actual errors (parse/booking); warnings must not
    // abort processing.
    if has_fatal(&load.errors) {
        let result = QueryResult {
            columns: Vec::new(),
            rows: Vec::new(),
            errors: load.errors,
        };
        return to_js(&result);
    }

    // Carry any non-fatal load warnings through every result path so callers
    // still see them alongside (or instead of) query output.
    let warnings = load.errors;

    // Parse the query
    let query = match parse_query(query_str) {
        Ok(q) => q,
        Err(e) => {
            let mut errors = warnings;
            errors.push(Error::new(e.to_string()));
            let result = QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors,
            };
            return to_js(&result);
        }
    };

    // Merge pad-synthesized transactions: query is a balance-
    // computing consumer (#1288). `merge_with_padding` preserves
    // Pad directives so `FROM #entries WHERE type = 'pad'` audits
    // continue to enumerate them, AND handles multi-pad shadowing
    // (#1300) correctly by construction via `process_pads`.
    let directives = merge_with_padding(&load.directives);
    let mut executor = Executor::new(&directives);
    // Config-aware classification (POSSIGN/ACCOUNT_SORTKEY honor name_*
    // renames) — same wiring as the CLI query path.
    executor.set_account_types(crate::helpers::account_types_from_raw(
        &load.parse_result.options,
    ));
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
                errors: warnings,
            };
            to_js(&query_result)
        }
        Err(e) => {
            let mut errors = warnings;
            errors.push(Error::new(format!("Query execution error: {e}")));
            let result = QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors,
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
                .map(|e| parse_error_to_wasm(e, &lookup, None))
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

    // Return early only on actual errors (parse/booking); warnings must not
    // abort processing.
    if has_fatal(&load.errors) {
        let result = PadResult {
            directives: Vec::new(),
            padding_transactions: Vec::new(),
            errors: load.errors,
        };
        return to_js(&result);
    }

    // Carry non-fatal load warnings through to the result.
    let mut errors = load.errors;

    // Process pads
    let pad_result = process_pads(&load.directives);
    errors.extend(
        pad_result
            .errors
            .iter()
            .map(|e| Error::new(e.message.clone())),
    );

    let result = PadResult {
        // The source stream, verbatim — `process_pads` no longer
        // echoes its input back, so read it from the directives we
        // already loaded instead of from the result.
        directives: load.directives.iter().map(directive_to_json).collect(),
        padding_transactions: pad_result
            .padding_transactions
            .iter()
            .map(|txn| directive_to_json(&Directive::Transaction(txn.clone())))
            .collect(),
        errors,
    };
    to_js(&result)
}

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

    // Return early only on actual errors (parse/booking); warnings must not
    // abort processing.
    if has_fatal(&load.errors) {
        let result = PluginResult {
            directives: Vec::new(),
            errors: load.errors,
        };
        return to_js(&result);
    }

    // Carry non-fatal load warnings through every result path.
    let warnings = load.errors;

    // Find and run the plugin
    let registry = NativePluginRegistry::global();
    // External API runs plugins on already-booked input — synth
    // plugins are a loader-internal concern and would re-emit Opens
    // for accounts the booking pass already opened.
    let Some(plugin) = registry.find_regular(plugin_name) else {
        let mut errors = warnings;
        errors.push(Error::new(format!("Unknown plugin: {plugin_name}")));
        let result = PluginResult {
            directives: Vec::new(),
            errors,
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
            let mut errors = warnings;
            errors.push(Error::new(format!("Conversion error: {e}")));
            let result = PluginResult {
                directives: Vec::new(),
                errors,
            };
            return to_js(&result);
        }
    };

    let mut errors = warnings;
    errors.extend(output.errors.iter().map(|e| match e.severity {
        rustledger_plugin::PluginErrorSeverity::Warning => Error::warning(e.message.clone()),
        rustledger_plugin::PluginErrorSeverity::Error => Error::new(e.message.clone()),
    }));
    let result = PluginResult {
        directives: output_directives.iter().map(directive_to_json).collect(),
        errors,
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
/// On a clean parse, the returned directives are run through the same processing
/// pipeline as `validateMultiFile` / `queryMultiFile` (sort → synth-plugins →
/// book → regular-plugins, validation excluded), so they are sorted, include
/// plugin-synthesized `Open`/`Document` directives, and have booked amounts —
/// consistent with the other multi-file surfaces. If parsing produced errors, the
/// raw parsed directives are returned instead (the pipeline is not run on a
/// malformed ledger) alongside those errors.
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

    // Run the canonical processing pipeline (sort → synth-plugins → book →
    // regular-plugins) on a clean parse, so the directive stream matches what
    // `validateMultiFile` / `queryMultiFile` see — sorted, with synthesized
    // Opens/Documents, and booked amounts. (Previously this used a manual
    // per-transaction interpolate loop that skipped sort/synth/booking, so a JS
    // consumer got an unsorted, synth-free, merely-interpolated stream.)
    // Validation is OFF: this is the parse surface, so it surfaces parse + booking
    // errors but not balance/assertion failures.
    //
    // On parse errors we keep the raw directives we managed to parse rather than
    // book a malformed ledger (mirroring the old "interpolate only when clean").
    let directives: Vec<Directive> = if errors.is_empty() {
        let process_options = LoadOptions {
            validate: false,
            ..Default::default()
        };
        match process(load_result, &process_options) {
            Ok(ledger) => {
                errors.extend(ledger.errors.into_iter().map(Error::from));
                ledger.directives.into_iter().map(|s| s.value).collect()
            }
            Err(e) => {
                let result = ParseResult {
                    ledger: None,
                    errors: vec![Error::new(format!("Processing error: {e}"))],
                };
                return to_js(&result);
            }
        }
    } else {
        load_result
            .directives
            .into_iter()
            .map(|s| s.value)
            .collect()
    };

    let ledger = Some(Ledger {
        directives: directives.iter().map(directive_to_json).collect(),
        options,
    });

    let result = ParseResult { ledger, errors };
    to_js(&result)
}

/// The validation pipeline, over whichever [`FileSystem`] it is handed.
///
/// One body for every backend: a file map through `validateMultiFile`, host
/// callbacks through `validateWithHost`. Include resolution, ordering, glob
/// expansion, duplicate detection and per-file error attribution belong to the
/// loader in both cases — which is the point of #2101, and would be undone by
/// giving either entry point its own copy of this.
fn validate_with_filesystem(
    fs: Box<dyn rustledger_loader::FileSystem>,
    entry_point: &str,
) -> ValidationResult {
    use rustledger_loader::{LoadOptions, Loader, process};

    let mut loader = Loader::new().with_filesystem(fs);

    // Load from entry point
    let load_result = match loader.load(Path::new(entry_point)) {
        Ok(result) => result,
        Err(e) => {
            let result = ValidationResult {
                valid: false,
                errors: vec![Error::new(format!("Load error: {e}"))],
            };
            return result;
        }
    };

    // Report every load error, but abort only on one that makes the directive
    // stream unusable — see `load_error_is_fatal`.
    let load_errors = load_errors_to_errors(&load_result);
    if load_result.errors.iter().any(load_error_is_fatal) {
        return ValidationResult {
            valid: false,
            errors: load_errors,
        };
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
            return result;
        }
    };

    let errors: Vec<Error> = ledger.errors.into_iter().map(Error::from).collect();

    ValidationResult {
        // Warnings do not invalidate a ledger; only actual errors do.
        valid: !has_fatal(&errors),
        errors,
    }
}

/// Validate multiple Beancount files with include resolution.
///
/// Similar to `parseMultiFile`, but also runs validation.
/// Returns a `ValidationResult` indicating whether the ledger is valid.
#[wasm_bindgen(js_name = "validateMultiFile")]
pub fn validate_multi_file(files: JsValue, entry_point: &str) -> Result<JsValue, JsError> {
    use rustledger_loader::VirtualFileSystem;

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

    to_js(&validate_with_filesystem(Box::new(vfs), entry_point))
}

/// Validate a ledger whose files the HOST supplies, one at a time.
///
/// `host` is an object with:
///
/// - `readFile(path) => string | null` — required. `null` means "cannot read
///   this", which the loader reports as a missing include against the file
///   that asked for it.
/// - `glob(pattern) => string[]` — optional. Without it, a glob `include`
///   reports "does not match any files", as a backend without glob support
///   does.
/// - `realpath(path) => string` — optional, and the interesting one. The
///   loader de-duplicates by the path this returns, so a host that resolves
///   symlinks (and, on a case-insensitive filesystem, case) gets a file
///   reached two ways loaded ONCE, without the caller having to know that
///   include graphs can contain diamonds.
///
/// # Why this exists alongside `validateMultiFile`
///
/// `validateMultiFile` takes every file up front, which means the CALLER has
/// to know which files a ledger contains — so it walks `include` directives
/// itself. That is a second implementation of the loader's include handling,
/// and the MCP server's copy was wrong four separate ways before it was
/// replaced (#2100). Here the host supplies primitives that encode nothing
/// about beancount, and the walking has one implementation: this one, the
/// same `Loader` behind `rledger check` (#2101).
///
/// # Errors
///
/// When `host` is not an object carrying a callable `readFile`.
#[wasm_bindgen(js_name = "validateWithHost")]
pub fn validate_with_host(host: &JsValue, entry_point: &str) -> Result<JsValue, JsError> {
    use crate::host_fs::{HostFs, HostScope};

    // Held for the whole call; cleared on drop, including on an early return.
    let _scope = HostScope::install(host).map_err(|e| JsError::new(&e))?;
    let result = validate_with_filesystem(Box::new(HostFs), entry_point);
    to_js(&result)
}

/// Run a BQL query over a ledger whose files the HOST supplies.
///
/// Same contract as [`validate_with_host`]; see it for the shape of `host`.
///
/// # Errors
///
/// When `host` is not an object carrying a callable `readFile`.
#[wasm_bindgen(js_name = "queryWithHost")]
pub fn query_with_host(
    host: &JsValue,
    entry_point: &str,
    query_str: &str,
) -> Result<JsValue, JsError> {
    use crate::host_fs::{HostFs, HostScope};

    let _scope = HostScope::install(host).map_err(|e| JsError::new(&e))?;
    query_with_filesystem(Box::new(HostFs), entry_point, query_str)
}

/// The query pipeline, over whichever [`FileSystem`] it is handed.
///
/// Companion to [`validate_with_filesystem`]; see it for why both entry points
/// share one body rather than each carrying a copy.
fn query_with_filesystem(
    fs: Box<dyn rustledger_loader::FileSystem>,
    entry_point: &str,
    query_str: &str,
) -> Result<JsValue, JsError> {
    use rustledger_booking::merge_with_padding;
    use rustledger_loader::{LoadOptions, Loader, process};
    use rustledger_query::{Executor, parse as parse_query};
    let mut loader = Loader::new().with_filesystem(fs);

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

    // Report every load error, but abort only on one that makes the directive
    // stream unusable. A duplicate include is not one: the ledger loaded
    // correctly and `rledger query` returns its rows alongside the notice.
    let load_errors = load_errors_to_errors(&load_result);
    if load_result.errors.iter().any(load_error_is_fatal) {
        let result = QueryResult {
            columns: Vec::new(),
            rows: Vec::new(),
            errors: load_errors,
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
    // — and not on a LOAD-phase notice either. `process` turns every load
    // error into a blocking `LOAD` ledger error, which is right for `check`
    // but not here: anything genuinely unusable already aborted above via
    // `load_error_is_fatal`, so what survives to this point is reportable and
    // no reason to throw away a correct answer. `rledger query` prints
    // `LOAD: Duplicate filename parsed` and still returns the rows.
    let errors: Vec<Error> = ledger.errors.into_iter().map(Error::from).collect();
    let has_errors = errors
        .iter()
        .any(|e| e.severity == Severity::Error && e.code.as_deref() != Some("LOAD"));
    if has_errors {
        let result = QueryResult {
            columns: Vec::new(),
            rows: Vec::new(),
            errors,
        };
        return to_js(&result);
    }

    // Merge pad-synthesized transactions into the directive stream
    // (matching CLI query pipeline). See `wasm::query` above for the
    // architectural rule.
    // Grab the configured account types before `ledger` fields are moved.
    let account_types = ledger.options.to_account_types();
    let booked_directives: Vec<_> = ledger.directives.into_iter().map(|s| s.value).collect();
    let directives = merge_with_padding(&booked_directives);

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
    executor.set_account_types(account_types);
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
                errors: load_errors,
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
    use rustledger_loader::VirtualFileSystem;

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

    query_with_filesystem(Box::new(vfs), entry_point, query_str)
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

#[cfg(test)]
mod load_error_tests {
    use super::*;
    use rustledger_loader::VirtualFileSystem;
    use std::collections::HashMap;

    /// A diamond — `shared` reached directly and again through `mid` — that
    /// ALSO fails a balance assertion.
    ///
    /// The second error is what makes the test discriminating. Both errors
    /// being present proves the pipeline RAN; the duplicate alone would prove
    /// only that something reported it, which an abort does too. An earlier
    /// version of this test asserted just the duplicate and passed happily
    /// with the abort restored.
    fn diamond_with_a_failing_assertion() -> VirtualFileSystem {
        let mut files = HashMap::new();
        files.insert(
            "main.beancount".to_string(),
            "2020-01-01 open Assets:Cash USD\n2020-01-01 open Expenses:Food USD\n\
             include \"sub/shared.beancount\"\ninclude \"sub/mid.beancount\"\n\
             2020-06-01 balance Assets:Cash  -999999.00 USD\n"
                .to_string(),
        );
        files.insert(
            "sub/shared.beancount".to_string(),
            "2020-03-01 * \"s\"\n  Expenses:Food   100.00 USD\n  Assets:Cash    -100.00 USD\n"
                .to_string(),
        );
        files.insert(
            "sub/mid.beancount".to_string(),
            "include \"shared.beancount\"\n".to_string(),
        );
        VirtualFileSystem::from_files(files)
    }

    #[test]
    fn a_duplicate_include_is_reported_but_does_not_abort() {
        // The ledger is COMPLETE — the loader loaded the shared file once — so
        // processing must still run. Aborting instead is what made a wasm
        // query over such a ledger return no rows at all, where `rledger
        // query` prints the notice and answers.
        let result = validate_with_filesystem(
            Box::new(diamond_with_a_failing_assertion()),
            "main.beancount",
        );

        assert!(
            result
                .errors
                .iter()
                .any(|e| e.message.contains("Duplicate filename")),
            "the duplicate must be reported, as `rledger check` reports it: {:?}",
            result.errors
        );
        assert!(
            result
                .errors
                .iter()
                .any(|e| e.message.contains("Balance failed")),
            "the balance assertion must have been CHECKED, which only happens \
             if the duplicate did not abort the pipeline: {:?}",
            result.errors
        );
        assert!(!result.valid, "matching bean-check's exit 1");
    }

    #[test]
    fn only_unusable_load_errors_are_fatal() {
        // A duplicate include leaves a usable directive stream; a parse error
        // does not. This predicate is what lets the query path answer over the
        // first and refuse the second.
        assert!(!load_error_is_fatal(&LoadError::DuplicateInclude {
            path: "shared.beancount".to_string(),
        }));
        assert!(load_error_is_fatal(&LoadError::IncludeCycle {
            cycle: vec!["a".to_string(), "a".to_string()],
        }));
        assert!(load_error_is_fatal(&LoadError::PathTraversal {
            include_path: "../../etc/passwd".to_string(),
            base_dir: std::path::PathBuf::from("/ledger"),
        }));
    }
}
