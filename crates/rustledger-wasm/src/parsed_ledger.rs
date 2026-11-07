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
use crate::helpers::{has_fatal, load_and_book, option_warnings_to_errors, run_validation, to_js};
#[cfg(feature = "plugins")]
use crate::types::PluginResult;
use crate::types::{Error, FormatResult, LedgerOptions, PadResult, QueryResult};

// =============================================================================
// Shared query/directive logic (used by both ParsedLedger and Ledger)
// =============================================================================

/// The pad-expanded, spanned directives a ledger's queries run on, built
/// once per ledger from its plain directives and kept spans (#2825).
fn query_directives<'c>(
    cache: &'c std::cell::OnceCell<Vec<rustledger_core::Spanned<Directive>>>,
    directives: &[Directive],
    spans: &[crate::helpers::DirectiveSpan],
) -> &'c [rustledger_core::Spanned<Directive>] {
    cache.get_or_init(|| {
        rustledger_booking::merge_with_padding_spanned(&crate::helpers::spanned_directives(
            directives, spans,
        ))
    })
}

/// Run one query over `expanded` (pad-expanded and spanned, so the source
/// columns resolve from `source_map`, #2825) with the ledger's `context`, through
/// [`rustledger_query::Executor::for_ledger`], the constructor the CLI and the
/// FFI component use too.
///
/// `load_errors` are the errors the ledger's load reported, none of which
/// stops a query (the caller has refused if one does). They lead the result's
/// `errors` on every path, answered or not, as the free `query` reports its
/// load's, so a caller reading only the result still learns that the rows
/// may be partial (#2882).
fn execute_query(
    expanded: &[rustledger_core::Spanned<Directive>],
    source_map: &rustledger_loader::SourceMap,
    context: rustledger_query::executor::LedgerContext<'_>,
    query_str: &str,
    created_tables: &std::cell::RefCell<rustledger_query::executor::CreatedTables>,
    load_errors: Vec<Error>,
) -> Result<JsValue, JsError> {
    use crate::convert::value_to_cell;
    use rustledger_query::{Executor, parse as parse_query};

    let query = match parse_query(query_str) {
        Ok(q) => q,
        Err(e) => {
            let mut errors = load_errors;
            errors.push(Error::new(e.to_string()));
            let result = QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors,
            };
            return to_js(&result);
        }
    };

    // `expanded` is pad-expanded (BQL is a balance-computing consumer, #1288):
    // `ParsedLedger.directives` / `Ledger.directives` are source-faithful, and
    // each ledger builds the expanded, spanned view once, in
    // [`query_directives`].
    // Config-aware classification (POSSIGN/ACCOUNT_SORTKEY honor name_*
    // renames) comes in `context`: the wasm wire LedgerOptions deliberately
    // lacks name_*, so callers supply it from their construction source.
    let mut executor = Executor::for_ledger(expanded, source_map, context);
    // The tables earlier queries made, handed back whatever this one does:
    // a failed query leaves them as they were (#2579).
    executor.set_created_tables(created_tables.take());
    let executed = executor.execute(&query);
    created_tables.replace(executor.take_created_tables());
    match executed {
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
            let mut errors = load_errors;
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

fn execute_expand_pads(directives: &[Directive]) -> Result<JsValue, JsError> {
    use rustledger_booking::process_pads;

    let pad_result = process_pads(directives);

    let result = PadResult {
        // The source stream, verbatim — `process_pads` no longer
        // echoes its input back, so read it from the directives we
        // were handed instead of from the result.
        directives: directives.iter().map(directive_to_json).collect(),
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
    /// Each booked directive's span and file id, for the source columns
    /// of a query (#2825).
    directive_spans: Vec<crate::helpers::DirectiveSpan>,
    /// `#balances.discrepancy`, recomputed from the source the first time a
    /// query reads it and kept for the next (#2823).
    discrepancies: std::sync::OnceLock<Vec<rustledger_loader::BalanceDiscrepancy>>,
    /// The loader's source map (the text named `<string>`, and plugin
    /// placeholder locations), for the source columns (#2825). Rebuilt from the
    /// text alone for a ledger restored from a cache.
    source_map: rustledger_loader::SourceMap,
    /// The pad-expanded, spanned directives queries run on, built once.
    query_directives: std::cell::OnceCell<Vec<rustledger_core::Spanned<Directive>>>,
    /// Ledger options.
    options: LedgerOptions,
    /// Parse errors.
    /// Parse and booking errors — the *soundness* list.
    ///
    /// Every operation gate below reads this and only this. An entry here means
    /// the directive stream could not be built, so running a query over it
    /// would be answering with data that does not exist.
    parse_errors: Vec<Error>,
    /// Option diagnostics (E7001, E7003, ...), kept out of `parse_errors` for
    /// the same reason they are kept out of `ProcessedLedger::errors`: an
    /// invalid option does not make the directive stream unsound, so it must
    /// not stop a query from running. Reported by `isValid`, `getErrors`, and
    /// `getParseErrors`; invisible to the gates.
    option_errors: Vec<Error>,
    /// Validation errors.
    validation_errors: Vec<Error>,
    /// Whether a query refuses: the load reported a parse error or a booking
    /// failure (`LedgerError::blocks_queries`, the rule the file-based query
    /// surfaces share, #2861, #2882). Any other load error in `parse_errors`,
    /// a plugin's among them, is reported by `getErrors` while the query
    /// answers, as `Ledger.query` does; before #2882 any load error refused.
    query_refused: bool,
    /// Cached editor data (accounts, currencies, payees, line index).
    editor_cache: editor::EditorCache,
    /// The tables this ledger's `CREATE TABLE` queries made, there for its
    /// later queries (#2579). Each `query` builds a fresh executor over the
    /// directives and lends it these.
    created_tables: std::cell::RefCell<rustledger_query::executor::CreatedTables>,
}

#[wasm_bindgen]
impl ParsedLedger {
    /// Create a new `ParsedLedger` from a single source string.
    ///
    /// Parses, books, and validates the source. Call `isValid()` to check for errors.
    #[wasm_bindgen(constructor)]
    pub fn new(source: &str) -> Self {
        let load = load_and_book(source);
        // Before merging option diagnostics in: `run_validation` gates on
        // `load.errors`, and an invalid option must not stop a ledger's real
        // validation errors from being reported (#2299).
        let validation_errors = run_validation(&load);
        let editor_cache = editor::EditorCache::new(source, &load.parse_result);

        Self {
            source: source.to_string(),
            parse_result: load.parse_result,
            directives: load.directives,
            directive_spans: load.directive_spans,
            discrepancies: std::sync::OnceLock::new(),
            source_map: load.source_map,
            query_directives: std::cell::OnceCell::new(),
            options: load.options,
            parse_errors: load.errors,
            option_errors: load.option_errors,
            validation_errors,
            query_refused: load.query_blocked,
            editor_cache,
            created_tables: std::cell::RefCell::default(),
        }
    }

    /// Check if the ledger is valid (no parse or validation ERRORS).
    ///
    /// Warnings do not make a ledger invalid, matching `rledger check`, which
    /// exits 0 on a warning-only ledger. Both of these vectors can hold
    /// warnings: `run_validation` assigns severity per code, so a
    /// warning-severity validation entry used to read as invalid here (#2291).
    #[wasm_bindgen(js_name = "isValid")]
    pub fn is_valid(&self) -> bool {
        !has_fatal(&self.parse_errors)
            && !has_fatal(&self.option_errors)
            && !has_fatal(&self.validation_errors)
    }

    /// Get all errors (parse + validation).
    #[wasm_bindgen(js_name = "getErrors")]
    pub fn get_errors(&self) -> Result<JsValue, JsError> {
        let mut all_errors = self.parse_errors.clone();
        all_errors.extend(self.option_errors.clone());
        all_errors.extend(self.validation_errors.clone());
        to_js(&all_errors)
    }

    /// Get parse errors only.
    #[wasm_bindgen(js_name = "getParseErrors")]
    pub fn get_parse_errors(&self) -> Result<JsValue, JsError> {
        // Option diagnostics carry `phase: "parse"`, so they belong in the
        // parse-phase view even though the gates must not see them.
        let mut errors = self.parse_errors.clone();
        errors.extend(self.option_errors.clone());
        to_js(&errors)
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
    ///
    /// Refuses, with no columns and the load's errors, when the source failed
    /// to parse or a transaction failed to book (`LedgerError::blocks_queries`,
    /// the rule every query surface shares, #2861, #2882). Otherwise it
    /// answers, and the result's `errors` lead with the load's other errors
    /// (a plugin's, an unresolved include's) and option diagnostics, as the
    /// free `query` reports them; validation errors stay in `getErrors`, as
    /// the free `query` does not validate. Before #2882 it refused on any load
    /// error and answered with no errors.
    ///
    /// A table a `CREATE TABLE` makes stays for this ledger's later queries
    /// (#2579).
    #[wasm_bindgen]
    pub fn query(&self, query_str: &str) -> Result<JsValue, JsError> {
        if self.query_refused {
            // The load's errors and option diagnostics, as the free `query`
            // refuses with them (`reported_errors`).
            let result = QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors: self
                    .parse_errors
                    .iter()
                    .chain(&self.option_errors)
                    .cloned()
                    .collect(),
            };
            return to_js(&result);
        }
        // The text is named `<string>`, as beancount's `load_string` names it
        // (#2825); `#balances.discrepancy` is computed from it only if the
        // query reads the column (#2823).
        let expanded = query_directives(
            &self.query_directives,
            &self.directives,
            &self.directive_spans,
        );
        let options = &self.parse_result.options;
        execute_query(
            expanded,
            &self.source_map,
            crate::helpers::lazy_query_context(
                &self.source_map,
                &self.discrepancies,
                crate::helpers::account_types_from_raw(options),
                crate::helpers::booking_method_from_raw(options),
                crate::helpers::summary_accounts_from_raw(options),
            ),
            query_str,
            &self.created_tables,
            self.parse_errors
                .iter()
                .chain(&self.option_errors)
                .cloned()
                .collect(),
        )
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
        use rustledger_parser::format::format_source_with_parsed;

        if !self.parse_errors.is_empty() {
            let result = FormatResult {
                formatted: None,
                errors: self.parse_errors.clone(),
            };
            return to_js(&result);
        }

        // Reuse the cached `ParseResult` we already own instead of
        // re-parsing `self.source`. Byte-identical output to
        // `format_source(&self.source)` per the parser-side
        // `format_source_with_parsed_matches_format_source` test.
        // On large ledgers loaded into a long-lived WASM session,
        // this cuts the per-format cost roughly in half.
        let formatted = format_source_with_parsed(&self.parse_result, &self.source);

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
            directive_spans: self.directive_spans.clone(),
            placeholders: crate::helpers::placeholder_locations(&self.source_map),
            options: self.options.clone(),
            parse_errors: self.parse_errors.clone(),
            option_errors: self.option_errors.clone(),
            validation_errors: self.validation_errors.clone(),
            query_refused: self.query_refused,
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
            directive_spans: payload.directive_spans,
            discrepancies: std::sync::OnceLock::new(),
            source_map: {
                let map = crate::helpers::string_source_map(source);
                crate::helpers::restore_placeholders(&map, &payload.placeholders);
                map
            },
            query_directives: std::cell::OnceCell::new(),
            options: payload.options,
            parse_errors: payload.parse_errors,
            option_errors: payload.option_errors,
            validation_errors: payload.validation_errors,
            query_refused: payload.query_refused,
            editor_cache,
            created_tables: std::cell::RefCell::default(),
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
    /// Each directive's span and file id, for the source columns of a query
    /// (#2825). Empty for a ledger restored from a cache.
    directive_spans: Vec<crate::helpers::DirectiveSpan>,
    /// The files the ledger was loaded from, so a query resolves `filename` /
    /// `lineno` / `location` (#2825). Empty for a ledger restored from a
    /// cache, whose source columns read NULL.
    source_map: rustledger_loader::SourceMap,
    /// The validating load's failing assertions, for `#balances.discrepancy`
    /// (#2823). Empty for a ledger restored from a cache.
    balance_discrepancies: Vec<rustledger_loader::BalanceDiscrepancy>,
    /// The pad-expanded, spanned directives queries run on, built once.
    query_directives: std::cell::OnceCell<Vec<rustledger_core::Spanned<Directive>>>,
    /// Ledger options.
    options: LedgerOptions,
    /// Configured account-type roots (`name_*` renames) for query
    /// classification. Not part of the wire `LedgerOptions` (deliberate);
    /// persisted in the cache payload so `fromCache` ledgers classify
    /// identically.
    account_types: rustledger_core::AccountTypes,
    /// The effective booking method the ledger was booked with, the default
    /// BQL realizes with (#2386). Persisted in the cache payload, like
    /// `account_types`.
    booking_method: rustledger_core::BookingMethod,
    /// The `account_previous_*` accounts `FROM ... OPEN ON` summarizes into
    /// (#2401). Persisted in the cache payload, like `account_types`.
    summary_accounts: rustledger_query::executor::SummaryAccounts,
    /// Processing errors (load, booking, validation).
    errors: Vec<Error>,
    /// Whether `errors` holds one that stops a query from answering
    /// (`LedgerError::blocks_queries`, #2861: a parse error, a file that
    /// could not be read or decrypted, a booking failure), or the load or
    /// processing failed outright. Archived in the cache payload, since the
    /// restored `errors` no longer carry the flag.
    query_refused: bool,
    /// Editor cache for cross-file completions.
    editor_cache: editor::EditorCache,
    /// The tables this ledger's `CREATE TABLE` queries made, there for its
    /// later queries (#2579). Each `query` builds a fresh executor over the
    /// directives and lends it these.
    created_tables: std::cell::RefCell<rustledger_query::executor::CreatedTables>,
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
                    directive_spans: Vec::new(),
                    source_map: rustledger_loader::SourceMap::new(),
                    balance_discrepancies: Vec::new(),

                    query_directives: std::cell::OnceCell::new(),
                    options: LedgerOptions::default(),
                    account_types: rustledger_core::AccountTypes::default(),
                    booking_method: LoadOptions::default().booking_method,
                    summary_accounts: rustledger_query::executor::SummaryAccounts::default(),
                    errors: vec![Error::new(format!("Load error: {e}"))],
                    editor_cache: editor::EditorCache::from_directives(&[]),
                    query_refused: true,
                    created_tables: std::cell::RefCell::default(),
                });
            }
        };

        let options = LedgerOptions {
            title: load_result.options.title.clone(),
            operating_currencies: load_result.options.operating_currency.clone(),
        };
        let account_types = load_result.options.to_account_types();
        let summary_accounts =
            rustledger_query::executor::SummaryAccounts::from_options(&load_result.options);

        let load_options = LoadOptions {
            validate: true,
            ..Default::default()
        };
        // Read before `process` consumes the options, so the error arm below
        // carries it too; `Ledger::booking_method` is this same value.
        let booking_method = load_result
            .options
            .effective_booking_method(load_options.booking_method);

        match process(load_result, &load_options) {
            Ok(ledger) => {
                let balance_discrepancies = ledger.balance_discrepancies;
                let source_map = ledger.source_map;
                let (directives, directive_spans): (Vec<Directive>, Vec<_>) = ledger
                    .directives
                    .into_iter()
                    .map(|s| (s.value, (s.span, s.file_id)))
                    .unzip();
                // The file-based query rule (#2861): not over a parse error,
                // a file that could not be read or decrypted, or a booking
                // failure; every other error is reported beside the rows.
                let query_refused = ledger
                    .errors
                    .iter()
                    .any(rustledger_loader::LedgerError::blocks_queries);
                let mut errors: Vec<Error> = ledger.errors.into_iter().map(Error::from).collect();
                errors.extend(option_warnings_to_errors(&ledger.options.warnings));
                let editor_cache = editor::EditorCache::from_directives(&directives);

                Ok(Self {
                    directives,
                    directive_spans,
                    source_map,
                    balance_discrepancies,

                    query_directives: std::cell::OnceCell::new(),
                    options,
                    account_types,
                    booking_method,
                    summary_accounts,
                    errors,
                    editor_cache,
                    query_refused,
                    created_tables: std::cell::RefCell::default(),
                })
            }
            Err(e) => Ok(Self {
                directives: Vec::new(),
                directive_spans: Vec::new(),
                source_map: rustledger_loader::SourceMap::new(),
                balance_discrepancies: Vec::new(),

                query_directives: std::cell::OnceCell::new(),
                options,
                account_types,
                booking_method,
                summary_accounts,
                errors: vec![Error::new(format!("Processing error: {e}"))],
                editor_cache: editor::EditorCache::from_directives(&[]),
                query_refused: true,
                created_tables: std::cell::RefCell::default(),
            }),
        }
    }

    /// Check if the ledger is valid (no errors).
    #[wasm_bindgen(js_name = "isValid")]
    /// Warnings do not make a ledger invalid, matching `rledger check`, which
    /// exits 0 on a warning-only ledger. `has_fatal` is what `api.rs` already
    /// uses for its `valid` field; this method was still asking whether the
    /// list was empty, so giving E7009 the right severity would not have been
    /// enough on its own (#2291).
    pub fn is_valid(&self) -> bool {
        !has_fatal(&self.errors)
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
    ///
    /// A table a `CREATE TABLE` makes stays for this ledger's later queries
    /// (#2579).
    #[wasm_bindgen]
    pub fn query(&self, query_str: &str) -> Result<JsValue, JsError> {
        // Refuses when a file failed to parse or a transaction failed to
        // book (`LedgerError::blocks_queries`), and answers otherwise,
        // reporting every other error (an include of a missing file, a failed
        // assertion, ...) in the result's `errors` ahead of its own, and in
        // `getErrors`, as `rledger query` and `queryMultiFile` do (#2861). It
        // answered over a parse or booking failure; until #2882 an answer
        // carried none of the load's errors.
        if self.query_refused {
            return to_js(&QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors: self.errors.clone(),
            });
        }
        let expanded = query_directives(
            &self.query_directives,
            &self.directives,
            &self.directive_spans,
        );
        execute_query(
            expanded,
            &self.source_map,
            rustledger_query::executor::LedgerContext {
                account_types: self.account_types.clone(),
                booking_method: self.booking_method,
                summary_accounts: self.summary_accounts.clone(),
                balance_discrepancies: rustledger_query::executor::BalanceDiscrepancies::Known(
                    self.balance_discrepancies.clone(),
                ),
            },
            query_str,
            &self.created_tables,
            self.errors.clone(),
        )
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
            account_type_names: vec![
                self.account_types.assets.clone(),
                self.account_types.liabilities.clone(),
                self.account_types.equity.clone(),
                self.account_types.income.clone(),
                self.account_types.expenses.clone(),
            ],
            booking_method: self.booking_method.to_string(),
            summary_account_names: vec![
                self.summary_accounts.previous_balances.clone(),
                self.summary_accounts.previous_earnings.clone(),
                self.summary_accounts.previous_conversions.clone(),
                self.summary_accounts.current_earnings.clone(),
                self.summary_accounts.current_conversions.clone(),
                self.summary_accounts.conversion_currency.clone(),
            ],
            errors: self.errors.clone(),
            query_refused: self.query_refused,
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

        let account_types = match <[String; 5]>::try_from(payload.account_type_names) {
            Ok([assets, liabilities, equity, income, expenses]) => rustledger_core::AccountTypes {
                assets,
                liabilities,
                equity,
                income,
                expenses,
            },
            // Wrong arity can only come from a hand-built blob (the version
            // header already gates format changes); fall back to defaults
            // rather than erroring on an otherwise-valid payload.
            Err(_) => rustledger_core::AccountTypes::default(),
        };

        // Written by `serialize` from a parsed method, so it parses back; the
        // fallback only covers a hand-built blob, as `account_types` does.
        let booking_method = payload
            .booking_method
            .parse()
            .unwrap_or(rustledger_core::BookingMethod::Strict);
        let summary_accounts = match <[String; 6]>::try_from(payload.summary_account_names) {
            Ok(
                [
                    previous_balances,
                    previous_earnings,
                    previous_conversions,
                    current_earnings,
                    current_conversions,
                    conversion_currency,
                ],
            ) => rustledger_query::executor::SummaryAccounts {
                previous_balances,
                previous_earnings,
                previous_conversions,
                current_earnings,
                current_conversions,
                conversion_currency,
            },
            // Wrong arity can only come from a hand-built blob, as for
            // `account_types`; fall back to beancount's names.
            Err(_) => rustledger_query::executor::SummaryAccounts::default(),
        };

        Ok(Self {
            directives: payload.directives,
            directive_spans: Vec::new(),
            source_map: rustledger_loader::SourceMap::new(),
            balance_discrepancies: Vec::new(),

            query_directives: std::cell::OnceCell::new(),
            options: payload.options,
            account_types,
            booking_method,
            summary_accounts,
            errors: payload.errors,
            editor_cache,
            query_refused: payload.query_refused,
            created_tables: std::cell::RefCell::default(),
        })
    }
}

#[cfg(test)]
mod option_warning_severity_tests {
    use super::*;
    use crate::types::Severity;
    use rustledger_loader::OptionWarning;

    fn warn(code: &'static str) -> OptionWarning {
        OptionWarning {
            code,
            message: "msg".to_string(),
            option: "title".to_string(),
            value: "v".to_string(),
        }
    }

    /// #2291, third surface. `rledger check` exits 0 on E7003 and E7009, so a
    /// ledger it calls clean must not arrive here carrying errors.
    ///
    /// The loop this replaced sent every option warning out as an `Error`,
    /// under a comment claiming parity with `check` and the LSP: the claim
    /// outlived the agreement.
    #[test]
    fn warnings_stay_warnings_and_errors_stay_errors() {
        let mapped = option_warnings_to_errors(&[
            warn("E7009"),
            warn("E7003"),
            warn("E7001"),
            warn("E7002"),
        ]);
        let sev: Vec<_> = mapped.iter().map(|e| e.severity).collect();
        assert_eq!(
            sev,
            vec![
                Severity::Warning,
                Severity::Warning,
                Severity::Error,
                Severity::Error
            ],
            "severity must follow OptionWarning::is_error, the rule `rledger check` reads"
        );
    }

    /// The code reaches consumers as a FIELD, not as message text (#2297).
    ///
    /// This case used to pin the `[E7009] ` prefix, because that prefix was
    /// the only place the code survived and #2292 could have dropped it by
    /// accident. The code now has a field of its own, so the guard moves to
    /// the field rather than being deleted: something still has to fail if a
    /// future change stops carrying it.
    ///
    /// The message is asserted NOT to repeat it, which is what makes the
    /// WASM text identical to the CLI's for the same warning.
    #[test]
    fn the_code_travels_in_its_own_field() {
        let mapped = option_warnings_to_errors(&[warn("E7009")]);
        assert_eq!(mapped[0].code.as_deref(), Some("E7009"));
        assert_eq!(
            mapped[0].phase.as_deref(),
            Some("parse"),
            "`rledger check` reports these under the parse phase"
        );
        assert_eq!(
            mapped[0].message, "msg",
            "the message must carry the text alone; the code has a field now"
        );
    }

    /// A ledger whose only complaint is a warning is VALID, the same way
    /// `rledger check` exits 0 on one.
    ///
    /// `Ledger::is_valid` was `errors.is_empty()`, which cannot tell a warning
    /// from an error. `has_fatal` exists for exactly this and is what `api.rs`
    /// uses for its `valid` field; this one method never got it. Giving E7009
    /// the right severity was not enough on its own, because the predicate
    /// consumers actually call never looked at severity.
    #[test]
    fn a_warning_only_ledger_is_valid() {
        let ledger = Ledger {
            directives: Vec::new(),
            directive_spans: Vec::new(),
            source_map: rustledger_loader::SourceMap::new(),
            balance_discrepancies: Vec::new(),

            query_directives: std::cell::OnceCell::new(),
            options: LedgerOptions::default(),
            account_types: rustledger_core::AccountTypes::default(),
            booking_method: rustledger_core::BookingMethod::Strict,
            summary_accounts: rustledger_query::executor::SummaryAccounts::default(),
            errors: option_warnings_to_errors(&[warn("E7009")]),
            editor_cache: editor::EditorCache::from_directives(&[]),
            query_refused: false,
            created_tables: std::cell::RefCell::default(),
        };
        assert_eq!(
            ledger.errors.len(),
            1,
            "the warning must still be REPORTED, just not fatal"
        );
        assert!(
            ledger.is_valid(),
            "a ledger carrying only E7009 is valid; `rledger check` exits 0 on it"
        );

        let broken = Ledger {
            directives: Vec::new(),
            directive_spans: Vec::new(),
            source_map: rustledger_loader::SourceMap::new(),
            balance_discrepancies: Vec::new(),

            query_directives: std::cell::OnceCell::new(),
            options: LedgerOptions::default(),
            account_types: rustledger_core::AccountTypes::default(),
            booking_method: rustledger_core::BookingMethod::Strict,
            summary_accounts: rustledger_query::executor::SummaryAccounts::default(),
            errors: option_warnings_to_errors(&[warn("E7001")]),
            editor_cache: editor::EditorCache::from_directives(&[]),
            query_refused: false,
            created_tables: std::cell::RefCell::default(),
        };
        assert!(
            !broken.is_valid(),
            "E7001 is an error; the ledger must not read as valid"
        );
    }

    /// The multi-file class caches the same diagnostics and decides validity
    /// off the restored list, so it needs the round-trip pinned too.
    ///
    /// `Ledger::is_valid` is `!has_fatal(&self.errors)`, reading exactly what
    /// `from_cache` handed back. Severity is the field that decides it, and
    /// severity is what #2291 changed without bumping `CACHE_VERSION` — so a
    /// round-trip that silently altered it would reproduce that bug from cache.
    #[test]
    fn ledger_option_diagnostics_survive_the_cache_round_trip() {
        let warning = Error::warning("Option \"title\" specified twice".to_string())
            .with_code("E7003")
            .with_phase("parse");
        let fatal = Error::new("Invalid option \"nonsense_option\"".to_string())
            .with_code("E7001")
            .with_phase("parse");

        for (label, errors, expect_valid) in [
            ("warning only", vec![warning.clone()], true),
            ("with an error", vec![warning, fatal], false),
        ] {
            let ledger = Ledger {
                directives: Vec::new(),
                directive_spans: Vec::new(),
                source_map: rustledger_loader::SourceMap::new(),
                balance_discrepancies: Vec::new(),

                query_directives: std::cell::OnceCell::new(),
                options: LedgerOptions::default(),
                account_types: rustledger_core::AccountTypes::default(),
                booking_method: rustledger_core::BookingMethod::Strict,
                summary_accounts: rustledger_query::executor::SummaryAccounts::default(),
                errors,
                editor_cache: editor::EditorCache::from_directives(&[]),
                query_refused: false,
                created_tables: std::cell::RefCell::default(),
            };
            let restored =
                Ledger::from_cache(&ledger.serialize().expect("serialize")).expect("restore");

            let shape = |l: &Ledger| -> Vec<(Option<String>, Severity)> {
                l.errors
                    .iter()
                    .map(|e| (e.code.clone(), e.severity))
                    .collect()
            };
            assert_eq!(
                shape(&restored),
                shape(&ledger),
                "{label}: code and severity must both survive the round trip"
            );
            assert_eq!(
                restored.is_valid(),
                expect_valid,
                "{label}: validity is decided off the restored list"
            );
        }
    }

    /// The cache must carry option diagnostics, or a cached ledger reports
    /// clean where a fresh one reports E7001.
    ///
    /// `from_cache` restores the archived diagnostics verbatim and re-parses
    /// the source only for editor spans, so nothing downstream re-derives
    /// them. The cross-version case is handled by the `CACHE_VERSION` 21 bump;
    /// this pins the round-trip itself, which is what makes the bump
    /// sufficient. Both lists are checked: option diagnostics must come back,
    /// and they must come back in `option_errors` rather than leaking into the
    /// soundness list the operation gates read.
    #[test]
    fn option_diagnostics_survive_the_cache_round_trip() {
        let src = "option \"nonsense_option\" \"x\"\n2024-01-01 open Assets:Cash USD\n";
        let fresh = ParsedLedger::new(src);
        let restored =
            ParsedLedger::from_cache(&fresh.serialize().expect("serialize"), src).expect("restore");

        let codes = |errors: &[Error]| -> Vec<String> {
            errors.iter().filter_map(|e| e.code.clone()).collect()
        };
        assert!(
            codes(&fresh.option_errors).contains(&"E7001".to_string()),
            "precondition: a fresh parse reports it"
        );
        assert_eq!(
            codes(&restored.option_errors),
            codes(&fresh.option_errors),
            "a restored ledger must report what a fresh one does"
        );
        assert!(
            restored.parse_errors.is_empty(),
            "and must not restore them into the list the operation gates read"
        );
        assert_eq!(
            restored.is_valid(),
            fresh.is_valid(),
            "and must agree on validity"
        );
    }

    /// A warning-only ledger must still be operable.
    ///
    /// `rledger check` exits 0 on a duplicated option (E7003 is a warning), and
    /// `isValid()` agrees. But `query`, `format`, `expandPads`, and `runPlugin`
    /// gate on `!parse_errors.is_empty()` — an emptiness test, which is exactly
    /// what #2291 replaced in `is_valid` and did not replace here. Routing
    /// option diagnostics through that list made every one of those operations
    /// refuse to run on a ledger reporting itself valid.
    #[test]
    fn a_warning_only_option_does_not_disable_operations() {
        let src = "option \"title\" \"a\"\noption \"title\" \"b\"\n\
2024-01-01 open Assets:Cash USD\n";
        let parsed = ParsedLedger::new(src);

        assert!(
            parsed
                .option_errors
                .iter()
                .any(|e| e.code.as_deref() == Some("E7003")),
            "precondition: the fixture raises the warning"
        );
        assert!(parsed.is_valid(), "a warning-only ledger is valid");
        assert!(
            parsed.parse_errors.is_empty(),
            "the gates read `parse_errors`; an option warning must not land \
             there or every operation refuses to run while isValid() says true"
        );
    }

    /// And an option ERROR must not disable them either: it does not make the
    /// directive stream unsound, which is the only thing those gates mean.
    /// `api::query` already behaves this way, so `ParsedLedger::query` doing
    /// otherwise would be the same operation answering two ways.
    #[test]
    fn an_invalid_option_does_not_disable_operations() {
        let src = "option \"nonsense_option\" \"x\"\n2024-01-01 open Assets:Cash USD\n";
        let parsed = ParsedLedger::new(src);

        assert!(!parsed.is_valid(), "precondition: E7001 makes it invalid");
        assert!(
            parsed.parse_errors.is_empty(),
            "an invalid option is reported, but the directives are sound and \
             a query over them must still run"
        );
    }

    /// End-to-end on the surface JS actually calls. `rledger check` errors and
    /// exits 1 on this source; `new ParsedLedger(src)` used to report a clean
    /// ledger, because the loader's E7001 was dropped before anyone could read
    /// it (#2299).
    #[test]
    fn an_invalid_option_is_visible_through_the_constructor() {
        let src = "option \"nonsense_option\" \"x\"\n2024-01-01 open Assets:Cash USD\n";
        let parsed = ParsedLedger::new(src);

        assert!(
            parsed
                .option_errors
                .iter()
                .any(|e| e.code.as_deref() == Some("E7001")),
            "E7001 must be reported; got {:?}",
            parsed
                .option_errors
                .iter()
                .map(|e| (&e.code, e.severity))
                .collect::<Vec<_>>()
        );
        assert!(
            !parsed.is_valid(),
            "E7001 is an error, so the ledger must not read as valid — \
             `rledger check` exits 1 on this source"
        );
    }

    /// And the option error must not cost the ledger its real diagnostics:
    /// `run_validation` is gated on `load.errors`, so an option folded in
    /// there would silently swallow the undefined-account error below.
    #[test]
    fn an_invalid_option_does_not_hide_a_real_validation_error() {
        let src = "option \"nonsense_option\" \"x\"\n\
2024-01-01 open Assets:Cash USD\n\
2024-01-02 * \"p\"\n  Assets:Cash 1 USD\n  Assets:NeverOpened -1 USD\n";
        let parsed = ParsedLedger::new(src);

        assert!(
            parsed
                .option_errors
                .iter()
                .any(|e| e.code.as_deref() == Some("E7001")),
            "precondition: the option error is reported"
        );
        assert!(
            !parsed.validation_errors.is_empty(),
            "the undefined-account error must survive alongside E7001"
        );
    }

    /// The same rule on the single-source surface, through the real
    /// constructor rather than a hand-built struct.
    ///
    /// A one-posting transaction is `SinglePosting` (E3004), which
    /// `ErrorCode::is_warning` classifies as a warning, so `run_validation`
    /// hands it back at `Severity::Warning`. The posting is zero so the
    /// transaction still balances and E3004 is the ONLY finding: `rledger
    /// check` prints "1 warning" and exits 0 on this exact source. `ParsedLedger::is_valid` was
    /// `parse_errors.is_empty() && validation_errors.is_empty()`, which called
    /// that ledger invalid while `rledger check` exits 0 on it.
    #[test]
    fn a_warning_only_source_is_valid_but_still_reports() {
        let src =
            "2024-01-01 open Assets:Cash EUR\n\n2024-02-01 * \"zero\"\n  Assets:Cash   0 EUR\n";
        let parsed = ParsedLedger::new(src);
        assert!(
            parsed
                .validation_errors
                .iter()
                .any(|e| e.severity == Severity::Warning),
            "fixture must produce a warning-severity validation entry; got {:?}",
            parsed
                .validation_errors
                .iter()
                .map(|e| (&e.code, e.severity))
                .collect::<Vec<_>>()
        );
        assert!(
            !parsed
                .validation_errors
                .iter()
                .any(|e| e.severity == Severity::Error),
            "fixture must not produce any hard error"
        );
        assert!(
            parsed.is_valid(),
            "a warning-only ledger is valid; `rledger check` exits 0 on it"
        );
    }
}
