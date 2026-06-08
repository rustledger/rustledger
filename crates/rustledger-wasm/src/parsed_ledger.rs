//! Stateful ledger classes for WASM.
//!
//! Provides two classes:
//! - [`ParsedLedger`]: Single-file ledger with full editor features (completions, hover, etc.)
//! - [`Ledger`]: Multi-file ledger for queries and validation (no position-based editor features)

use std::collections::HashMap;
use std::path::Path;
use wasm_bindgen::prelude::*;

use rustledger_core::Directive;
use rustledger_parser::ParseResult as ParserResult;

use crate::cache;
use crate::convert::directive_to_json;
use crate::editor;
use crate::helpers::{load_and_book, run_validation, to_js};
#[cfg(feature = "plugins")]
use crate::types::PluginResult;
use crate::types::{Error, FormatResult, LedgerOptions, PadResult, QueryResult};

// =============================================================================
// Shared query/directive logic (used by both ParsedLedger and Ledger)
// =============================================================================

fn execute_query(directives: &[Directive], query_str: &str) -> Result<JsValue, JsError> {
    use crate::convert::value_to_cell;
    use rustledger_query::{Executor, parse as parse_query};

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

    let mut executor = Executor::new(directives);
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

fn execute_expand_pads(directives: &[Directive]) -> Result<JsValue, JsError> {
    use rustledger_booking::process_pads;

    let pad_result = process_pads(directives);

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

#[cfg(feature = "plugins")]
fn execute_plugin(directives: &[Directive], plugin_name: &str) -> Result<JsValue, JsError> {
    use rustledger_plugin::{
        NativePluginRegistry, PluginInput, PluginOptions, directives_to_wrappers,
        wrappers_to_directives,
    };

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

    let wrappers = directives_to_wrappers(directives);
    let input = PluginInput {
        directives: wrappers,
        options: PluginOptions::default(),
        config: None,
    };

    let input_dirs = input.directives.clone();
    let output = plugin.process(input);
    let materialized = crate::api::materialize_plugin_ops(&input_dirs, &output);

    let output_directives = match wrappers_to_directives(&materialized) {
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

// =============================================================================
// ParsedLedger: Single-file with full editor features
// =============================================================================

/// A parsed and validated single-file ledger with editor features.
///
/// Use this class for single-file ledgers where you need completions, hover,
/// go-to-definition, and other editor integration features.
///
/// For multi-file ledgers, use [`Ledger`] instead.
///
/// # Example (JavaScript)
///
/// ```javascript
/// const ledger = new ParsedLedger(source);
/// if (ledger.isValid()) {
///     const balances = ledger.query("BALANCES");
///     const completions = ledger.getCompletions(line, char);
/// }
/// ```
#[wasm_bindgen(skip_typescript)]
pub struct ParsedLedger {
    /// The original source text.
    source: String,
    /// The raw parse result (for editor features).
    parse_result: ParserResult,
    /// The booked directives.
    directives: Vec<Directive>,
    /// Ledger options.
    options: LedgerOptions,
    /// Parse errors.
    parse_errors: Vec<Error>,
    /// Validation errors.
    validation_errors: Vec<Error>,
    /// Cached editor data (accounts, currencies, payees, line index).
    editor_cache: editor::EditorCache,
}

#[wasm_bindgen]
impl ParsedLedger {
    /// Create a new `ParsedLedger` from a single source string.
    ///
    /// Parses, books, and validates the source. Call `isValid()` to check for errors.
    #[wasm_bindgen(constructor)]
    pub fn new(source: &str) -> Self {
        let load = load_and_book(source);
        let validation_errors = run_validation(&load);
        let editor_cache = editor::EditorCache::new(source, &load.parse_result);

        Self {
            source: source.to_string(),
            parse_result: load.parse_result,
            directives: load.directives,
            options: load.options,
            parse_errors: load.errors,
            validation_errors,
            editor_cache,
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
        if !self.parse_errors.is_empty() {
            let result = QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors: self.parse_errors.clone(),
            };
            return to_js(&result);
        }
        execute_query(&self.directives, query_str)
    }

    /// Get account balances (shorthand for query("BALANCES")).
    #[wasm_bindgen]
    pub fn balances(&self) -> Result<JsValue, JsError> {
        self.query("BALANCES")
    }

    /// Format the ledger source.
    ///
    /// Reformats the original source preserving comments, blank lines, and
    /// non-directive content with file-wide aligned columns.
    #[wasm_bindgen]
    pub fn format(&self) -> Result<JsValue, JsError> {
        use rustledger_parser::format::format_source;

        if !self.parse_errors.is_empty() {
            let result = FormatResult {
                formatted: None,
                errors: self.parse_errors.clone(),
            };
            return to_js(&result);
        }

        let formatted = format_source(&self.source);

        let result = FormatResult {
            formatted: Some(formatted),
            errors: Vec::new(),
        };
        to_js(&result)
    }

    /// Expand pad directives.
    #[wasm_bindgen(js_name = "expandPads")]
    pub fn expand_pads(&self) -> Result<JsValue, JsError> {
        if !self.parse_errors.is_empty() {
            let result = PadResult {
                directives: Vec::new(),
                padding_transactions: Vec::new(),
                errors: self.parse_errors.clone(),
            };
            return to_js(&result);
        }
        execute_expand_pads(&self.directives)
    }

    /// Run a native plugin on this ledger.
    #[cfg(feature = "plugins")]
    #[wasm_bindgen(js_name = "runPlugin")]
    pub fn run_plugin(&self, plugin_name: &str) -> Result<JsValue, JsError> {
        if !self.parse_errors.is_empty() {
            let result = PluginResult {
                directives: Vec::new(),
                errors: self.parse_errors.clone(),
            };
            return to_js(&result);
        }
        execute_plugin(&self.directives, plugin_name)
    }

    // =========================================================================
    // Editor Integration (LSP-like features)
    // =========================================================================

    /// Get completions at the given position.
    #[wasm_bindgen(js_name = "getCompletions")]
    pub fn get_completions(&self, line: u32, character: u32) -> Result<JsValue, JsError> {
        let result =
            editor::get_completions_cached(&self.source, line, character, &self.editor_cache);
        to_js(&result)
    }

    /// Get hover information at the given position.
    #[wasm_bindgen(js_name = "getHoverInfo")]
    pub fn get_hover_info(&self, line: u32, character: u32) -> Result<JsValue, JsError> {
        let result = editor::get_hover_info_cached(
            &self.source,
            line,
            character,
            &self.parse_result,
            &self.editor_cache,
        );
        to_js(&result)
    }

    /// Get the definition location for the symbol at the given position.
    #[wasm_bindgen(js_name = "getDefinition")]
    pub fn get_definition(&self, line: u32, character: u32) -> Result<JsValue, JsError> {
        let result = editor::get_definition_cached(
            &self.source,
            line,
            character,
            &self.parse_result,
            &self.editor_cache,
        );
        to_js(&result)
    }

    /// Get all document symbols for the outline view.
    #[wasm_bindgen(js_name = "getDocumentSymbols")]
    pub fn get_document_symbols(&self) -> Result<JsValue, JsError> {
        let result = editor::get_document_symbols_cached(&self.parse_result, &self.editor_cache);
        to_js(&result)
    }

    /// Find all references to the symbol at the given position.
    #[wasm_bindgen(js_name = "getReferences")]
    pub fn get_references(&self, line: u32, character: u32) -> Result<JsValue, JsError> {
        let result = editor::get_references_cached(
            &self.source,
            line,
            character,
            &self.parse_result,
            &self.editor_cache,
        );
        to_js(&result)
    }

    // =========================================================================
    // Serialization / Caching
    // =========================================================================

    /// Serialize this ledger to a compact binary blob (rkyv).
    ///
    /// Store the bytes in OPFS or `IndexedDB` alongside a source fingerprint
    /// (see [`crate::hash_sources`]) and restore later with [`ParsedLedger::from_cache`].
    #[wasm_bindgen]
    pub fn serialize(&self) -> Result<Vec<u8>, JsError> {
        // Clone fields into the payload. rkyv's Serialize derive requires owned
        // types; a zero-copy borrowed serializer would add significant complexity
        // for minimal gain since serialize() is called once per cache write.
        let payload = cache::ParsedLedgerPayload {
            directives: self.directives.clone(),
            options: self.options.clone(),
            parse_errors: self.parse_errors.clone(),
            validation_errors: self.validation_errors.clone(),
        };
        cache::serialize_parsed(&payload).map_err(|e| JsError::new(&e))
    }

    /// Restore a `ParsedLedger` from bytes produced by [`ParsedLedger::serialize`].
    ///
    /// The `source` parameter must be the same source text used when the cache
    /// was created; it is re-parsed (but not re-booked or re-validated) so that
    /// editor features continue to work.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes are invalid or were produced by a different
    /// library version.
    #[wasm_bindgen(js_name = "fromCache")]
    pub fn from_cache(bytes: &[u8], source: &str) -> Result<Self, JsError> {
        let mut payload = cache::deserialize_parsed(bytes).map_err(|e| JsError::new(&e))?;

        // Re-intern strings to deduplicate identical Arc<str> allocations.
        rustledger_loader::reintern_plain_directives(&mut payload.directives);

        // Re-parse source for editor spans (cheap; booking is the expensive part).
        let parse_result = rustledger_parser::parse(source);
        let editor_cache = editor::EditorCache::new(source, &parse_result);

        Ok(Self {
            source: source.to_string(),
            parse_result,
            directives: payload.directives,
            options: payload.options,
            parse_errors: payload.parse_errors,
            validation_errors: payload.validation_errors,
            editor_cache,
        })
    }
}

// =============================================================================
// Ledger: Multi-file with queries and cross-file completions
// =============================================================================

/// A fully processed multi-file ledger for queries and validation.
///
/// Use this class for ledgers that span multiple files with `include` directives.
/// Caches the processed result for efficient repeated queries.
///
/// For single-file ledgers with editor features, use [`ParsedLedger`] instead.
///
/// # Example (JavaScript)
///
/// ```javascript
/// const ledger = Ledger.fromFiles({
///     "main.beancount": 'include "accounts.beancount"\n...',
///     "accounts.beancount": "2024-01-01 open Assets:Bank USD\n..."
/// }, "main.beancount");
///
/// if (ledger.isValid()) {
///     const balances = ledger.query("BALANCES");
///     const completions = ledger.getCompletions(currentSource, line, char);
/// }
/// ```
#[wasm_bindgen(skip_typescript)]
pub struct Ledger {
    /// The booked directives from all files.
    directives: Vec<Directive>,
    /// Ledger options.
    options: LedgerOptions,
    /// Processing errors (load, booking, validation).
    errors: Vec<Error>,
    /// Editor cache for cross-file completions.
    editor_cache: editor::EditorCache,
}

#[wasm_bindgen]
impl Ledger {
    /// Create a `Ledger` from multiple files with include resolution.
    ///
    /// Loads and runs the same processing pipeline as the CLI:
    /// sort → synth-plugins → Early validation → book → regular-plugins → Late validation → finalize.
    ///
    /// # Arguments
    ///
    /// * `files` - A JavaScript object mapping file paths to their contents.
    /// * `entry_point` - The main file to start loading from (must exist in `files`).
    #[wasm_bindgen(js_name = "fromFiles")]
    pub fn from_files(files: JsValue, entry_point: &str) -> Result<Self, JsError> {
        use rustledger_loader::{FileSystem, LoadOptions, Loader, VirtualFileSystem, process};

        let file_map: HashMap<String, String> = serde_wasm_bindgen::from_value(files)
            .map_err(|e| JsError::new(&format!("Invalid files object: {e}")))?;

        if file_map.is_empty() {
            return Err(JsError::new("Files map cannot be empty"));
        }

        let vfs = VirtualFileSystem::from_files(file_map);

        if !vfs.exists(Path::new(entry_point)) {
            return Err(JsError::new(&format!(
                "Entry point '{entry_point}' not found in files map"
            )));
        }

        let mut loader = Loader::new().with_filesystem(Box::new(vfs));

        let load_result = match loader.load(Path::new(entry_point)) {
            Ok(result) => result,
            Err(e) => {
                return Ok(Self {
                    directives: Vec::new(),
                    options: LedgerOptions::default(),
                    errors: vec![Error::new(format!("Load error: {e}"))],
                    editor_cache: editor::EditorCache::from_directives(&[]),
                });
            }
        };

        let options = LedgerOptions {
            title: load_result.options.title.clone(),
            operating_currencies: load_result.options.operating_currency.clone(),
        };

        let load_options = LoadOptions {
            validate: true,
            ..Default::default()
        };

        match process(load_result, &load_options) {
            Ok(ledger) => {
                let directives: Vec<Directive> =
                    ledger.directives.into_iter().map(|s| s.value).collect();
                let mut errors: Vec<Error> = ledger.errors.into_iter().map(Error::from).collect();
                // Include option warnings (E7001–E7006) so WASM consumers
                // see the same diagnostics as `rledger check` and the LSP.
                for w in &ledger.options.warnings {
                    errors.push(Error::new(format!("[{}] {}", w.code, w.message)));
                }
                let editor_cache = editor::EditorCache::from_directives(&directives);

                Ok(Self {
                    directives,
                    options,
                    errors,
                    editor_cache,
                })
            }
            Err(e) => Ok(Self {
                directives: Vec::new(),
                options,
                errors: vec![Error::new(format!("Processing error: {e}"))],
                editor_cache: editor::EditorCache::from_directives(&[]),
            }),
        }
    }

    /// Check if the ledger is valid (no errors).
    #[wasm_bindgen(js_name = "isValid")]
    pub fn is_valid(&self) -> bool {
        self.errors.is_empty()
    }

    /// Get all errors.
    #[wasm_bindgen(js_name = "getErrors")]
    pub fn get_errors(&self) -> Result<JsValue, JsError> {
        to_js(&self.errors)
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
        execute_query(&self.directives, query_str)
    }

    /// Get account balances (shorthand for query("BALANCES")).
    #[wasm_bindgen]
    pub fn balances(&self) -> Result<JsValue, JsError> {
        self.query("BALANCES")
    }

    /// Expand pad directives.
    #[wasm_bindgen(js_name = "expandPads")]
    pub fn expand_pads(&self) -> Result<JsValue, JsError> {
        execute_expand_pads(&self.directives)
    }

    /// Run a native plugin on this ledger.
    #[cfg(feature = "plugins")]
    #[wasm_bindgen(js_name = "runPlugin")]
    pub fn run_plugin(&self, plugin_name: &str) -> Result<JsValue, JsError> {
        execute_plugin(&self.directives, plugin_name)
    }

    /// Get completions for a source string using cross-file data.
    ///
    /// Pass the source text of the file currently being edited.
    /// Completions use accounts, currencies, and payees from all loaded files.
    #[wasm_bindgen(js_name = "getCompletions")]
    pub fn get_completions(
        &self,
        source: &str,
        line: u32,
        character: u32,
    ) -> Result<JsValue, JsError> {
        let result = editor::get_completions_cached(source, line, character, &self.editor_cache);
        to_js(&result)
    }

    // =========================================================================
    // Serialization / Caching
    // =========================================================================

    /// Serialize this ledger to a compact binary blob (rkyv).
    ///
    /// Store the bytes in OPFS or `IndexedDB` alongside a source fingerprint
    /// (see [`crate::hash_sources`]) and restore later with [`Ledger::from_cache`].
    #[wasm_bindgen]
    pub fn serialize(&self) -> Result<Vec<u8>, JsError> {
        let payload = cache::LedgerPayload {
            directives: self.directives.clone(),
            options: self.options.clone(),
            errors: self.errors.clone(),
        };
        cache::serialize_ledger(&payload).map_err(|e| JsError::new(&e))
    }

    /// Restore a `Ledger` from bytes produced by [`Ledger::serialize`].
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes are invalid or were produced by a different
    /// library version.
    #[wasm_bindgen(js_name = "fromCache")]
    pub fn from_cache(bytes: &[u8]) -> Result<Self, JsError> {
        let mut payload = cache::deserialize_ledger(bytes).map_err(|e| JsError::new(&e))?;

        // Re-intern strings to deduplicate identical Arc<str> allocations.
        rustledger_loader::reintern_plain_directives(&mut payload.directives);

        let editor_cache = editor::EditorCache::from_directives(&payload.directives);

        Ok(Self {
            directives: payload.directives,
            options: payload.options,
            errors: payload.errors,
            editor_cache,
        })
    }
}
