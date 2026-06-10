//! JSON-RPC 2.0 method router.
//!
//! This module dispatches JSON-RPC method calls to the appropriate handlers.

use std::fs;
use std::path::Path;

use rustledger_booking::BookingEngine;
use rustledger_core::{Directive, NaiveDate};
use rustledger_loader::Loader;
use rustledger_plugin::{
    NativePluginRegistry, PluginInput, PluginOptions, directive_to_wrapper, wrapper_to_directive,
};
use rustledger_validate::{ValidationOptions, ValidationSession};

use super::error::RpcError;
use super::request::{
    BatchFileParams, BatchParams, ClampEntriesParams, CreateEntriesParams, CreateEntryParams,
    FilterEntriesParams, FormatEntriesParams, FormatEntryParams, FormatFileParams,
    FormatSourceParams, GetAccountTypeParams, IsEncryptedParams, LoadFileParams, LoadParams,
    QueryFileParams, QueryParams, Request, ValidateFileParams, ValidateParams,
};
use super::response::Response;
use super::response::results::{
    CreateEntriesResult, CreateEntryResult, FormatResult, GetAccountTypeResult, IsEncryptedResult,
    VersionResult,
};
use crate::API_VERSION;
use crate::commands::load::LoadFullOutput;
use crate::commands::query::execute_query;
use crate::convert::directive_to_json;
use crate::helpers::load_source;
use crate::types::{
    BatchOutput, DirectiveJson, Error, LedgerOptions, LoadOutput, Plugin, QueryOutput,
    ValidateOutput, input_entry_to_directive,
};

/// Route a JSON-RPC request to the appropriate handler.
pub fn route(request: &Request) -> Response {
    let id = request.id.clone();

    // Validate the request first
    if let Err(e) = request.validate() {
        return Response::invalid_request(id, e);
    }

    // Dispatch based on method
    let result = dispatch(&request.method, &request.params);

    match result {
        Ok(value) => Response::success(id, value),
        Err(err) => Response::error(id, err),
    }
}

/// Dispatch a method call to the appropriate handler.
fn dispatch(method: &str, params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    match method {
        // Ledger operations
        "ledger.load" => handle_load(params),
        "ledger.loadFile" => handle_load_file(params),
        "ledger.validate" => handle_validate(params),
        "ledger.validateFile" => handle_validate_file(params),

        // Query operations
        "query.execute" => handle_query(params),
        "query.executeFile" => handle_query_file(params),
        "query.batch" => handle_batch(params),
        "query.batchFile" => handle_batch_file(params),

        // Format operations
        "format.source" => handle_format_source(params),
        "format.file" => handle_format_file(params),
        "format.entry" => handle_format_entry(params),
        "format.entries" => handle_format_entries(params),

        // Entry operations
        "entry.create" => handle_create_entry(params),
        "entry.createBatch" => handle_create_entries(params),
        "entry.filter" => handle_filter_entries(params),
        "entry.clamp" => handle_clamp_entries(params),

        // Utility operations
        "util.version" => handle_version(),
        "util.types" => handle_types(),
        "util.isEncrypted" => handle_is_encrypted(params),
        "util.getAccountType" => handle_get_account_type(params),

        _ => Err(RpcError::method_not_found(method)),
    }
}

// =============================================================================
// Ledger operations
// =============================================================================

fn handle_load(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: LoadParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let filename = params.filename.as_deref().unwrap_or("<stdin>");
    let load = load_source(&params.source);

    let entries: Vec<DirectiveJson> = load
        .directives
        .iter()
        .zip(load.directive_lines.iter())
        .map(|(d, &line)| directive_to_json(d, line, filename))
        .collect();

    let output = LoadOutput {
        api_version: API_VERSION,
        entries,
        errors: load.errors,
        options: load.options,
        plugins: load.plugins,
        includes: load.includes,
    };

    serde_json::to_value(output).map_err(|e| RpcError::internal_error(e.to_string()))
}

fn handle_load_file(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: LoadFileParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let path = Path::new(&params.path);

    // Load using the full loader. `with_path_security` defaults to
    // `true` (confines the include graph to the entry file's directory
    // tree) — FFI is the most security-sensitive surface, so safe-by-
    // default matters. Callers that legitimately need cross-tree
    // includes (e.g., `include "../shared/accounts.bean"`) can opt out
    // via the request's `path_security: false` field.
    let mut loader = Loader::new().with_path_security(params.path_security);
    let load_result = loader
        .load(path)
        .map_err(|e| RpcError::file_error(format!("Failed to load file: {e}")))?;

    // Collect errors from loader
    let mut errors: Vec<Error> = load_result
        .errors
        .iter()
        .map(|e| Error::new(e.to_string()))
        .collect();

    // Convert directives and get line numbers/filenames
    let mut directives: Vec<Directive> = Vec::new();
    let mut directive_lines: Vec<u32> = Vec::new();
    let mut directive_files: Vec<String> = Vec::new();

    for spanned in &load_result.directives {
        directives.push(spanned.value.clone());

        let file_id = spanned.file_id as usize;
        if let Some(source_file) = load_result.source_map.get(file_id) {
            let (line, _col) = source_file.line_col(spanned.span.start);
            directive_lines.push(line as u32);
            directive_files.push(source_file.path.display().to_string());
        } else {
            directive_lines.push(0);
            directive_files.push("<unknown>".to_string());
        }
    }

    // Run booking and interpolation
    let booking_method = load_result
        .options
        .booking_method
        .parse()
        .unwrap_or(rustledger_core::BookingMethod::Strict);
    let mut booking_engine = BookingEngine::with_method(booking_method);
    booking_engine.register_account_methods(directives.iter());

    for (i, directive) in directives.iter_mut().enumerate() {
        if let Directive::Transaction(txn) = directive {
            match booking_engine.book_and_interpolate(txn) {
                Ok(result) => {
                    booking_engine.apply(&result.transaction);
                    *txn = result.transaction;
                    rustledger_booking::normalize_prices(txn);
                }
                Err(e) => {
                    errors.push(Error::new(e.to_string()).with_line(directive_lines[i]));
                }
            }
        }
    }

    // Run plugins if requested
    let run_plugins: Vec<&str> = params.plugins.iter().map(String::as_str).collect();
    if !run_plugins.is_empty() && errors.is_empty() {
        let registry = NativePluginRegistry::global();

        for plugin_name in run_plugins {
            // External API runs plugins on already-booked input — synth
            // plugins are a loader-internal concern and would re-emit
            // Opens for accounts the booking pass already opened.
            if let Some(plugin) = registry.find_regular(plugin_name) {
                let wrappers: Vec<_> = directives
                    .iter()
                    .enumerate()
                    .map(|(i, d)| {
                        let mut wrapper = directive_to_wrapper(d);
                        wrapper.filename = Some(
                            directive_files
                                .get(i)
                                .cloned()
                                .unwrap_or_else(|| "<unknown>".to_string()),
                        );
                        wrapper.lineno = Some(directive_lines.get(i).copied().unwrap_or(0));
                        wrapper
                    })
                    .collect();

                let input = PluginInput {
                    directives: wrappers,
                    options: PluginOptions {
                        operating_currencies: load_result.options.operating_currency.clone(),
                        title: load_result.options.title.clone(),
                    },
                    config: None,
                };

                // Materialize the plugin's ops back into a flat wrapper list.
                let input_dirs = input.directives.clone();
                let output = plugin.process(input);

                for err in output.errors {
                    errors.push(Error::new(err.message));
                }

                let materialized = {
                    let mut out: Vec<rustledger_plugin::types::DirectiveWrapper> =
                        Vec::with_capacity(output.ops.len());
                    for op in &output.ops {
                        match op {
                            rustledger_plugin::PluginOp::Keep(i) => {
                                if let Some(w) = input_dirs.get(*i) {
                                    out.push(w.clone());
                                }
                            }
                            rustledger_plugin::PluginOp::Modify(_, w)
                            | rustledger_plugin::PluginOp::Insert(w) => out.push(w.clone()),
                            rustledger_plugin::PluginOp::Delete(_) => {}
                        }
                    }
                    out
                };

                let mut new_directives = Vec::new();
                let mut new_lines = Vec::new();
                let mut new_files = Vec::new();

                for wrapper in &materialized {
                    if let Ok(directive) = wrapper_to_directive(wrapper) {
                        new_directives.push(directive);
                        new_lines.push(wrapper.lineno.unwrap_or(0));
                        new_files.push(
                            wrapper
                                .filename
                                .clone()
                                .unwrap_or_else(|| "<plugin>".to_string()),
                        );
                    }
                }

                directives = new_directives;
                directive_lines = new_lines;
                directive_files = new_files;
            } else {
                errors.push(Error::new(format!("Unknown plugin: {plugin_name}")));
            }
        }
    }

    // Convert options
    let options = build_ledger_options(&load_result.options);

    // Convert plugins from loader result
    let plugins: Vec<Plugin> = load_result
        .plugins
        .iter()
        .map(|p| Plugin {
            name: p.name.clone(),
            config: p.config.clone(),
        })
        .collect();

    // Get list of loaded files
    let loaded_files: Vec<String> = load_result
        .source_map
        .files()
        .iter()
        .map(|sf| sf.path.display().to_string())
        .collect();

    // Build entries
    let entries: Vec<DirectiveJson> = directives
        .iter()
        .enumerate()
        .map(|(i, d)| {
            directive_to_json(
                d,
                directive_lines.get(i).copied().unwrap_or(0),
                directive_files.get(i).map_or("<unknown>", String::as_str),
            )
        })
        .collect();

    let output = LoadFullOutput {
        api_version: API_VERSION,
        entries,
        errors,
        options,
        plugins,
        loaded_files,
    };

    serde_json::to_value(output).map_err(|e| RpcError::internal_error(e.to_string()))
}

fn handle_validate(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: ValidateParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let load = load_source(&params.source);
    // Separate parse errors from booking/interpolation errors (both come from load_source).
    // Parse errors are tagged phase="parse"; booking errors are tagged phase="validate".
    let parse_error_count = load.errors.iter().filter(|e| e.phase == "parse").count();
    let mut errors = load.errors;

    // Only run semantic validation when there are no syntactic (parse) errors.
    // Booking errors are semantic and don't prevent validation from running.
    //
    // The FFI receives already-booked directives, so it runs Early +
    // Late + finalize back-to-back through a single `ValidationSession`
    // — same shape as the LSP. See `rustledger_validate::Phase` for the
    // architecture rationale.
    if parse_error_count == 0 {
        let today = jiff::Zoned::now().date();
        let session = ValidationSession::new(ValidationOptions::default());
        let (session, mut validation_errors) =
            session.run_early_spanned(&load.spanned_directives, today);
        let (session, late_errs) = session.run_late_spanned(&load.spanned_directives, today);
        validation_errors.extend(late_errs);
        validation_errors.extend(session.finalize());
        for err in validation_errors {
            let mut e = Error::new(&err.message).validate_phase();
            if let Some(span) = err.span {
                e = e.with_line(load.line_lookup.byte_to_line(span.start));
            }
            errors.push(e);
        }
    }

    // Count validate-phase errors after all errors have been collected.
    let validate_error_count = errors.iter().filter(|e| e.phase == "validate").count();

    let output = ValidateOutput {
        api_version: API_VERSION,
        valid: errors.is_empty(),
        errors,
        parse_error_count,
        validate_error_count,
    };

    serde_json::to_value(output).map_err(|e| RpcError::internal_error(e.to_string()))
}

fn handle_validate_file(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: ValidateFileParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let source = fs::read_to_string(&params.path)
        .map_err(|e| RpcError::file_error(format!("Failed to read file '{}': {e}", params.path)))?;

    let validate_params = ValidateParams { source };
    handle_validate(&serde_json::to_value(validate_params).unwrap())
}

// =============================================================================
// Query operations
// =============================================================================

fn handle_query(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: QueryParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let load = load_source(&params.source);

    if !load.errors.is_empty() {
        let output = QueryOutput {
            api_version: API_VERSION,
            columns: vec![],
            rows: vec![],
            errors: load.errors,
        };
        return serde_json::to_value(output).map_err(|e| RpcError::internal_error(e.to_string()));
    }

    let output = execute_query(&load.directives, &params.query);
    serde_json::to_value(output).map_err(|e| RpcError::internal_error(e.to_string()))
}

fn handle_query_file(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: QueryFileParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let source = fs::read_to_string(&params.path)
        .map_err(|e| RpcError::file_error(format!("Failed to read file '{}': {e}", params.path)))?;

    let query_params = QueryParams {
        source,
        query: params.query,
    };
    handle_query(&serde_json::to_value(query_params).unwrap())
}

fn handle_batch(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: BatchParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let filename = params.filename.as_deref().unwrap_or("<stdin>");
    let load = load_source(&params.source);

    // Build load output
    let entries: Vec<DirectiveJson> = load
        .directives
        .iter()
        .zip(load.directive_lines.iter())
        .map(|(d, &line)| directive_to_json(d, line, filename))
        .collect();

    let load_output = LoadOutput {
        api_version: API_VERSION,
        entries,
        errors: load.errors.clone(),
        options: load.options,
        plugins: load.plugins,
        includes: load.includes,
    };

    // Execute queries (only if no parse errors)
    let query_outputs: Vec<QueryOutput> = if load.errors.is_empty() {
        params
            .queries
            .iter()
            .map(|q| execute_query(&load.directives, q))
            .collect()
    } else {
        // Return error for each query
        params
            .queries
            .iter()
            .map(|_| QueryOutput {
                api_version: API_VERSION,
                columns: vec![],
                rows: vec![],
                errors: vec![Error::new("Cannot execute query: parse errors exist")],
            })
            .collect()
    };

    let output = BatchOutput {
        api_version: API_VERSION,
        load: load_output,
        queries: query_outputs,
    };

    serde_json::to_value(output).map_err(|e| RpcError::internal_error(e.to_string()))
}

fn handle_batch_file(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: BatchFileParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let source = fs::read_to_string(&params.path)
        .map_err(|e| RpcError::file_error(format!("Failed to read file '{}': {e}", params.path)))?;

    let batch_params = BatchParams {
        source,
        queries: params.queries,
        filename: Some(params.path),
    };
    handle_batch(&serde_json::to_value(batch_params).unwrap())
}

// =============================================================================
// Format operations
// =============================================================================

fn handle_format_source(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: FormatSourceParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;
    format_source_to_response(&params.source)
}

fn handle_format_file(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: FormatFileParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;
    let source = fs::read_to_string(&params.path)
        .map_err(|e| RpcError::file_error(format!("Failed to read file '{}': {e}", params.path)))?;
    format_source_to_response(&source)
}

/// Shared canonical-format implementation for `format.source` and
/// `format.file`. Gates on a clean parse, runs `format_source`, returns
/// either a `FormatResult` JSON value on success or a
/// `beancount_parse_error` `RpcError` (JSON-RPC code -32000, the
/// application-level error variant) on parse failure. Avoids the
/// re-serialization round-trip the two endpoints used to go through.
///
/// **Error code policy.** Application-level beancount parse failures
/// use -32000 (`ErrorCode::BeancountParseError`), NOT -32700 (which
/// JSON-RPC 2.0 reserves for malformed JSON in the request envelope).
/// Clients that dispatch on JSON-RPC error codes should treat -32000
/// as "the source the user submitted is invalid" and -32700 as "I
/// received bytes that weren't valid JSON."
///
/// On parse errors the message field stays single-line for log-friendly
/// consumption; the full list of error strings is attached as a
/// structured `data` array per JSON-RPC 2.0, so callers that want to
/// surface individual errors can inspect `error.data` rather than
/// scraping the message. The array is capped at 100 entries with
/// `truncated: bool` exposing the elision.
fn format_source_to_response(source: &str) -> Result<serde_json::Value, RpcError> {
    let parse_result = rustledger_parser::parse(source);
    if !parse_result.errors.is_empty() {
        // Cap the per-error array to keep the JSON-RPC response bounded.
        // A pathological 10MB binary fed into `format.file` can produce
        // tens of thousands of error strings; the structured response
        // would otherwise grow multi-megabyte and DOS the embedder's
        // transport. `total` and `truncated` let the consumer detect
        // and surface the elision.
        const MAX_ERRORS: usize = 100;
        let total = parse_result.errors.len();
        // Structured per-error object: `message` (rendered Display),
        // `kind_code` (stable numeric discriminant — see
        // `rustledger_parser::ParseError::kind_code`), and `span`
        // (byte range into the source). Consumers can detect specific
        // error kinds — e.g., `BomInDirectiveBody` is code 26 — and
        // wire structural UX (a 'Remove BOM' suggestion, a code action)
        // without regex-matching the message body.
        let errors: Vec<serde_json::Value> = parse_result
            .errors
            .iter()
            .take(MAX_ERRORS)
            .map(|e| {
                // `hint` is optional — serde_json::json! includes it
                // unconditionally, so we serialize Some -> string and
                // None -> null. RPC consumers that want to surface a
                // fix-it suggestion (e.g., 'Remove BOM' for
                // BomInDirectiveBody) read this field; consumers that
                // don't can ignore it. ParseError::Display only emits
                // the primary message, not the hint, so without this
                // field the hint would be silently dropped at the
                // FFI boundary.
                serde_json::json!({
                    "message": e.to_string(),
                    "kind_code": e.kind_code(),
                    "hint": e.hint,
                    "span": { "start": e.span.start, "end": e.span.end },
                })
            })
            .collect();
        let message = format!("cannot format source with {total} parse error(s)");
        let data = serde_json::json!({
            "errors": errors,
            "total": total,
            "truncated": total > MAX_ERRORS,
        });
        return Err(RpcError::beancount_parse_error(message).with_data(data));
    }

    // Reuse the parse_result we already produced for the error gate
    // above instead of letting `format_source` parse the same bytes
    // a second time. Same output (byte-identical, pinned by
    // `format_source_with_parsed_matches_format_source` in the
    // parser tests); roughly half the per-RPC CPU cost on large
    // inputs.
    let formatted = rustledger_parser::format::format_source_with_parsed(&parse_result, source);

    let result = FormatResult { formatted };
    serde_json::to_value(result).map_err(|e| RpcError::internal_error(e.to_string()))
}

fn handle_format_entry(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: FormatEntryParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let directive = input_entry_to_directive(&params.entry)
        .map_err(|e| RpcError::invalid_params(format!("Invalid entry: {e}")))?;

    let config = rustledger_core::format::FormatConfig::default();
    let formatted =
        rustledger_parser::format::canonicalize_directives(std::iter::once(&directive), &config)
            .map_err(|e| RpcError::internal_error(e.to_string()))?;
    let result = FormatResult { formatted };
    serde_json::to_value(result).map_err(|e| RpcError::internal_error(e.to_string()))
}

fn handle_format_entries(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: FormatEntriesParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let mut directives: Vec<rustledger_core::Directive> = Vec::with_capacity(params.entries.len());
    for (i, entry) in params.entries.iter().enumerate() {
        directives.push(
            input_entry_to_directive(entry).map_err(|e| {
                RpcError::invalid_params(format!("Invalid entry at index {i}: {e}"))
            })?,
        );
    }
    let config = rustledger_core::format::FormatConfig::default();
    let formatted = rustledger_parser::format::canonicalize_directives(directives.iter(), &config)
        .map_err(|e| RpcError::internal_error(e.to_string()))?;

    let result = FormatResult { formatted };
    serde_json::to_value(result).map_err(|e| RpcError::internal_error(e.to_string()))
}

// =============================================================================
// Entry operations
// =============================================================================

fn handle_create_entry(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: CreateEntryParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let directive = input_entry_to_directive(&params.entry)
        .map_err(|e| RpcError::invalid_params(format!("Invalid entry: {e}")))?;

    let entry = directive_to_json(&directive, 0, "<created>");

    let result = CreateEntryResult { entry };
    serde_json::to_value(result).map_err(|e| RpcError::internal_error(e.to_string()))
}

fn handle_create_entries(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: CreateEntriesParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let mut entries = Vec::new();
    for (i, input_entry) in params.entries.iter().enumerate() {
        let directive = input_entry_to_directive(input_entry)
            .map_err(|e| RpcError::invalid_params(format!("Invalid entry at index {i}: {e}")))?;
        entries.push(directive_to_json(&directive, 0, "<created>"));
    }

    let result = CreateEntriesResult { entries };
    serde_json::to_value(result).map_err(|e| RpcError::internal_error(e.to_string()))
}

fn handle_filter_entries(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    use crate::commands::clamp::filter_entries;

    let params: FilterEntriesParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let begin_date: NaiveDate = params
        .begin_date
        .parse()
        .map_err(|e| RpcError::invalid_params(format!("Invalid begin_date: {e}")))?;
    let end_date: NaiveDate = params
        .end_date
        .parse()
        .map_err(|e| RpcError::invalid_params(format!("Invalid end_date: {e}")))?;

    let result = filter_entries(params.entries, begin_date, end_date);
    serde_json::to_value(result).map_err(|e| RpcError::internal_error(e.to_string()))
}

fn handle_clamp_entries(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    use crate::commands::clamp::clamp_entries;

    let params: ClampEntriesParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let begin_date = params
        .begin_date
        .as_ref()
        .map(|d| d.parse::<NaiveDate>())
        .transpose()
        .map_err(|e| RpcError::invalid_params(format!("Invalid begin_date: {e}")))?
        .ok_or_else(|| RpcError::invalid_params("begin_date is required"))?;

    let end_date = params
        .end_date
        .as_ref()
        .map(|d| d.parse::<NaiveDate>())
        .transpose()
        .map_err(|e| RpcError::invalid_params(format!("Invalid end_date: {e}")))?
        .ok_or_else(|| RpcError::invalid_params("end_date is required"))?;

    let result = clamp_entries(params.entries, begin_date, end_date);
    serde_json::to_value(result).map_err(|e| RpcError::internal_error(e.to_string()))
}

// =============================================================================
// Utility operations
// =============================================================================

fn handle_version() -> Result<serde_json::Value, RpcError> {
    let result = VersionResult {
        api_version: API_VERSION,
        version: env!("CARGO_PKG_VERSION").to_string(),
    };
    serde_json::to_value(result).map_err(|e| RpcError::internal_error(e.to_string()))
}

fn handle_types() -> Result<serde_json::Value, RpcError> {
    use crate::commands::util::{MissingSentinel, TypesOutput};

    let output = TypesOutput {
        api_version: API_VERSION,
        all_directives: vec![
            "transaction",
            "balance",
            "open",
            "close",
            "commodity",
            "pad",
            "event",
            "note",
            "document",
            "price",
            "query",
            "custom",
        ],
        booking_methods: vec![
            "STRICT",
            "STRICT_WITH_SIZE",
            "NONE",
            "AVERAGE",
            "FIFO",
            "LIFO",
            "HIFO",
        ],
        missing: MissingSentinel {
            description: "Represents a missing/interpolated amount in a posting",
            json_representation: "null or {currency_only: string}",
        },
        account_types: vec!["Assets", "Liabilities", "Equity", "Income", "Expenses"],
    };

    serde_json::to_value(output).map_err(|e| RpcError::internal_error(e.to_string()))
}

fn handle_is_encrypted(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: IsEncryptedParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let path = Path::new(&params.path);
    let encrypted = path
        .extension()
        .is_some_and(|ext| ext.eq_ignore_ascii_case("gpg") || ext.eq_ignore_ascii_case("asc"));

    let result = IsEncryptedResult { encrypted };
    serde_json::to_value(result).map_err(|e| RpcError::internal_error(e.to_string()))
}

fn handle_get_account_type(params: &serde_json::Value) -> Result<serde_json::Value, RpcError> {
    let params: GetAccountTypeParams = serde_json::from_value(params.clone())
        .map_err(|e| RpcError::invalid_params(format!("Invalid params: {e}")))?;

    let account_type = if let Some(first_component) = params.account.split(':').next() {
        match first_component {
            "Assets" => "assets",
            "Liabilities" => "liabilities",
            "Equity" => "equity",
            "Income" => "income",
            "Expenses" => "expenses",
            _ => "unknown",
        }
    } else {
        "unknown"
    };

    let result = GetAccountTypeResult {
        account_type: account_type.to_string(),
    };
    serde_json::to_value(result).map_err(|e| RpcError::internal_error(e.to_string()))
}

// =============================================================================
// Helper functions
// =============================================================================

fn build_ledger_options(options: &rustledger_loader::Options) -> LedgerOptions {
    LedgerOptions {
        title: options.title.clone(),
        operating_currency: options.operating_currency.clone(),
        name_assets: options.name_assets.clone(),
        name_liabilities: options.name_liabilities.clone(),
        name_equity: options.name_equity.clone(),
        name_income: options.name_income.clone(),
        name_expenses: options.name_expenses.clone(),
        documents: options.documents.clone(),
        commodities: Vec::new(),
        booking_method: options.booking_method.clone(),
        display_precision: options
            .display_precision
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect(),
        render_commas: options.render_commas,
        inferred_tolerance_default: options
            .inferred_tolerance_default
            .iter()
            .map(|(k, v)| (k.clone(), v.to_string()))
            .collect(),
        inferred_tolerance_multiplier: options.inferred_tolerance_multiplier.to_string(),
        infer_tolerance_from_cost: options.infer_tolerance_from_cost,
        account_rounding: options.account_rounding.clone(),
        account_previous_balances: options.account_previous_balances.clone(),
        account_previous_earnings: options.account_previous_earnings.clone(),
        account_previous_conversions: options.account_previous_conversions.clone(),
        account_current_earnings: options.account_current_earnings.clone(),
        account_current_conversions: options.account_current_conversions.clone(),
        account_unrealized_gains: options.account_unrealized_gains.clone(),
        conversion_currency: options.conversion_currency.clone(),
    }
}
