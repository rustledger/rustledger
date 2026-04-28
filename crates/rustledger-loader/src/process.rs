//! Processing pipeline: sort → book → plugins → validate.
//!
//! This module orchestrates the full processing pipeline for a beancount ledger,
//! equivalent to Python's `loader.load_file()` function.

use crate::{LoadError, LoadResult, Options, Plugin, SourceMap};
use rustledger_core::{BookingMethod, Directive, DisplayContext};
use rustledger_parser::Spanned;
use std::path::Path;
use thiserror::Error;

/// Options for loading and processing a ledger.
#[derive(Debug, Clone)]
pub struct LoadOptions {
    /// Booking method for lot matching (default: Strict).
    pub booking_method: BookingMethod,
    /// Run plugins declared in the file (default: true).
    pub run_plugins: bool,
    /// Run `auto_accounts` plugin (default: false).
    pub auto_accounts: bool,
    /// Additional native plugins to run (by name).
    pub extra_plugins: Vec<String>,
    /// Plugin configurations for extra plugins.
    pub extra_plugin_configs: Vec<Option<String>>,
    /// Run validation after processing (default: true).
    pub validate: bool,
    /// Enable path security (prevent include traversal).
    pub path_security: bool,
}

impl Default for LoadOptions {
    fn default() -> Self {
        Self {
            booking_method: BookingMethod::Strict,
            run_plugins: true,
            auto_accounts: false,
            extra_plugins: Vec::new(),
            extra_plugin_configs: Vec::new(),
            validate: true,
            path_security: false,
        }
    }
}

impl LoadOptions {
    /// Create options for raw loading (no booking, no plugins, no validation).
    #[must_use]
    pub const fn raw() -> Self {
        Self {
            booking_method: BookingMethod::Strict,
            run_plugins: false,
            auto_accounts: false,
            extra_plugins: Vec::new(),
            extra_plugin_configs: Vec::new(),
            validate: false,
            path_security: false,
        }
    }
}

/// Errors that can occur during ledger processing.
#[derive(Debug, Error)]
pub enum ProcessError {
    /// Loading failed.
    #[error("loading failed: {0}")]
    Load(#[from] LoadError),

    /// Booking/interpolation error.
    #[cfg(feature = "booking")]
    #[error("booking error: {message}")]
    Booking {
        /// Error message.
        message: String,
        /// Date of the transaction.
        date: rustledger_core::NaiveDate,
        /// Narration of the transaction.
        narration: String,
    },

    /// Plugin execution error.
    #[cfg(feature = "plugins")]
    #[error("plugin error: {0}")]
    Plugin(String),

    /// Validation error.
    #[cfg(feature = "validation")]
    #[error("validation error: {0}")]
    Validation(String),

    /// Plugin output conversion error.
    #[cfg(feature = "plugins")]
    #[error("failed to convert plugin output: {0}")]
    PluginConversion(String),
}

/// A fully processed ledger.
///
/// This is the result of loading and processing a beancount file,
/// equivalent to the tuple returned by Python's `loader.load_file()`.
#[derive(Debug)]
pub struct Ledger {
    /// Processed directives (sorted, booked, plugins applied).
    pub directives: Vec<Spanned<Directive>>,
    /// Options parsed from the file.
    pub options: Options,
    /// Plugins declared in the file.
    pub plugins: Vec<Plugin>,
    /// Source map for error reporting.
    pub source_map: SourceMap,
    /// Errors encountered during processing.
    pub errors: Vec<LedgerError>,
    /// Display context for formatting numbers.
    pub display_context: DisplayContext,
}

/// Unified error type for ledger processing.
///
/// This encompasses all error types that can occur during loading,
/// booking, plugin execution, and validation.
#[derive(Debug)]
#[non_exhaustive]
pub struct LedgerError {
    /// Error severity.
    pub severity: ErrorSeverity,
    /// Error code (e.g., "E0001", "W8002").
    pub code: String,
    /// Human-readable error message.
    pub message: String,
    /// Source location, if available.
    pub location: Option<ErrorLocation>,
    /// Byte span (inclusive start, exclusive end) in the source file,
    /// used by rich renderers (e.g. miette) to draw a snippet around
    /// the offending directive. Consumers that only need `file:line:col`
    /// should use `location`; those that want to show the surrounding
    /// source text want this.
    pub source_span: Option<(usize, usize)>,
    /// Source file ID — index into the ledger's [`SourceMap`]. Used
    /// alongside `source_span` for snippet rendering.
    pub file_id: Option<u16>,
    /// Processing phase that produced this error: "parse", "validate", or "plugin".
    pub phase: String,
}

/// Error severity level.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorSeverity {
    /// Error - indicates a problem that should be fixed.
    Error,
    /// Warning - indicates a potential issue.
    Warning,
}

/// Source location for an error.
#[derive(Debug, Clone)]
pub struct ErrorLocation {
    /// File path.
    pub file: std::path::PathBuf,
    /// Line number (1-indexed).
    pub line: usize,
    /// Column number (1-indexed).
    pub column: usize,
}

impl LedgerError {
    /// Create a new error with the given phase.
    pub fn error(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            severity: ErrorSeverity::Error,
            code: code.into(),
            message: message.into(),
            location: None,
            source_span: None,
            file_id: None,
            phase: "validate".to_string(),
        }
    }

    /// Create a new warning.
    pub fn warning(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            severity: ErrorSeverity::Warning,
            code: code.into(),
            message: message.into(),
            location: None,
            source_span: None,
            file_id: None,
            phase: "validate".to_string(),
        }
    }

    /// Attach a source span and file ID so rich renderers can draw a snippet.
    #[must_use]
    pub const fn with_source_span(mut self, span: (usize, usize), file_id: u16) -> Self {
        self.source_span = Some(span);
        self.file_id = Some(file_id);
        self
    }

    /// Set the processing phase for this error.
    #[must_use]
    pub fn with_phase(mut self, phase: impl Into<String>) -> Self {
        self.phase = phase.into();
        self
    }

    /// Add a location to this error.
    #[must_use]
    pub fn with_location(mut self, location: ErrorLocation) -> Self {
        self.location = Some(location);
        self
    }
}

/// Process a raw load result into a fully processed ledger.
///
/// This applies the processing pipeline:
/// 1. Sort directives by date
/// 2. Run booking/interpolation
/// 3. Run plugins
/// 4. Run validation (optional)
pub fn process(raw: LoadResult, options: &LoadOptions) -> Result<Ledger, ProcessError> {
    let mut directives = raw.directives;
    let mut errors: Vec<LedgerError> = Vec::new();

    // Convert load errors to ledger errors (parse phase)
    for load_err in raw.errors {
        errors.push(LedgerError::error("LOAD", load_err.to_string()).with_phase("parse"));
    }

    // 1. Sort by date, type priority, then cost-basis reductions last.
    // Transactions without cost reductions (no negative-units + cost-spec
    // postings) process before those that reduce lots, ensuring lots exist
    // when matched regardless of file ordering.
    directives.sort_by_cached_key(|d| {
        (
            d.value.date(),
            d.value.priority(),
            d.value.has_cost_reduction(),
        )
    });

    // 2. Booking/interpolation
    //
    // The booking method comes from two sources: the API-level
    // `LoadOptions.booking_method` and the file-level `option
    // "booking_method"`. The file-level option takes precedence only
    // when the file explicitly set it AND the caller hasn't overridden
    // the API-level default. This matches Python beancount, where
    // `option "booking_method" "FIFO"` sets the default for all accounts
    // without an explicit method on their `open` directive.
    //
    // We check `set_options` (not `booking_method.is_empty()`) because
    // `Options::new()` defaults `booking_method` to "STRICT", so the
    // string is never empty.
    #[cfg(feature = "booking")]
    {
        let file_set_booking = raw.options.set_options.contains("booking_method");
        let effective_method = if file_set_booking {
            raw.options
                .booking_method
                .parse()
                .unwrap_or(options.booking_method)
        } else {
            options.booking_method
        };
        run_booking(&mut directives, effective_method, &mut errors);
    }

    // 3. Run plugins (including document discovery when run_plugins is enabled)
    // Note: Document discovery only runs when run_plugins is true to respect raw mode semantics.
    // LoadOptions::raw() sets run_plugins=false to prevent any directive mutations.
    #[cfg(feature = "plugins")]
    if options.run_plugins || !options.extra_plugins.is_empty() || options.auto_accounts {
        run_plugins(
            &mut directives,
            &raw.plugins,
            &raw.options,
            options,
            &raw.source_map,
            &mut errors,
        )?;
    }

    // 4. Validation
    #[cfg(feature = "validation")]
    if options.validate {
        run_validation(&directives, &raw.options, &raw.source_map, &mut errors);
    }

    Ok(Ledger {
        directives,
        options: raw.options,
        plugins: raw.plugins,
        source_map: raw.source_map,
        errors,
        display_context: raw.display_context,
    })
}

/// Run booking and interpolation on transactions.
#[cfg(feature = "booking")]
fn run_booking(
    directives: &mut Vec<Spanned<Directive>>,
    booking_method: BookingMethod,
    errors: &mut Vec<LedgerError>,
) {
    use rustledger_booking::BookingEngine;

    let mut engine = BookingEngine::with_method(booking_method);
    engine.register_account_methods(directives.iter().map(|s| &s.value));

    for spanned in directives.iter_mut() {
        if let Directive::Transaction(txn) = &mut spanned.value {
            match engine.book_and_interpolate(txn) {
                Ok(result) => {
                    engine.apply(&result.transaction);
                    *txn = result.transaction;
                }
                Err(e) => {
                    errors.push(LedgerError::error(
                        "BOOK",
                        format!("{} ({}, \"{}\")", e, txn.date, txn.narration),
                    ));
                }
            }
        }
    }
}

/// Run plugins on directives.
///
/// Executes native plugins (and document discovery) on the given directives,
/// modifying them in-place. Plugin errors are appended to `errors`.
///
/// This is called by [`process()`] as part of the full pipeline, but can also
/// be called standalone (e.g., by the LSP) when plugin execution is needed
/// outside the normal load flow.
#[cfg(feature = "plugins")]
pub fn run_plugins(
    directives: &mut Vec<Spanned<Directive>>,
    file_plugins: &[Plugin],
    file_options: &Options,
    options: &LoadOptions,
    source_map: &SourceMap,
    errors: &mut Vec<LedgerError>,
) -> Result<(), ProcessError> {
    use rustledger_plugin::{
        DocumentDiscoveryPlugin, NativePlugin, NativePluginRegistry, PluginInput, PluginOptions,
        directive_to_wrapper_with_location, wrapper_to_directive,
    };

    // Resolve document directories relative to the main file's directory
    // Document discovery only runs when run_plugins is true (respects raw mode)
    let base_dir = source_map
        .files()
        .first()
        .and_then(|f| f.path.parent())
        .unwrap_or_else(|| std::path::Path::new("."));

    let has_document_dirs = options.run_plugins && !file_options.documents.is_empty();
    let resolved_documents: Vec<String> = if has_document_dirs {
        file_options
            .documents
            .iter()
            .map(|d| {
                let path = std::path::Path::new(d);
                if path.is_absolute() {
                    d.clone()
                } else {
                    base_dir.join(path).to_string_lossy().to_string()
                }
            })
            .collect()
    } else {
        Vec::new()
    };

    // Collect raw plugin names first (we'll resolve them with the registry later)
    // Tuple: (name, config, force_python)
    let mut raw_plugins: Vec<(String, Option<String>, bool)> = Vec::new();

    // Add auto_accounts first if requested
    if options.auto_accounts {
        raw_plugins.push(("auto_accounts".to_string(), None, false));
    }

    // Add plugins from the file
    if options.run_plugins {
        for plugin in file_plugins {
            raw_plugins.push((
                plugin.name.clone(),
                plugin.config.clone(),
                plugin.force_python,
            ));
        }
    }

    // Add extra plugins from options
    for (i, plugin_name) in options.extra_plugins.iter().enumerate() {
        let config = options.extra_plugin_configs.get(i).cloned().flatten();
        raw_plugins.push((plugin_name.clone(), config, false));
    }

    // Check if we have any work to do - early return before creating registry
    if raw_plugins.is_empty() && !has_document_dirs {
        return Ok(());
    }

    // Convert directives to plugin format with source locations
    let mut wrappers: Vec<_> = directives
        .iter()
        .map(|spanned| {
            let (filename, lineno) = if let Some(file) = source_map.get(spanned.file_id as usize) {
                let (line, _col) = file.line_col(spanned.span.start);
                (Some(file.path.display().to_string()), Some(line as u32))
            } else {
                (None, None)
            };
            directive_to_wrapper_with_location(&spanned.value, filename, lineno)
        })
        .collect();

    let plugin_options = PluginOptions {
        operating_currencies: file_options.operating_currency.clone(),
        title: file_options.title.clone(),
    };

    // Run document discovery plugin if documents directories are configured
    if has_document_dirs {
        let doc_plugin = DocumentDiscoveryPlugin::new(resolved_documents, base_dir.to_path_buf());
        let input = PluginInput {
            directives: std::mem::take(&mut wrappers),
            options: plugin_options.clone(),
            config: None,
        };
        let output = doc_plugin.process(input);

        // Collect plugin errors
        for err in output.errors {
            let ledger_err = match err.severity {
                rustledger_plugin::PluginErrorSeverity::Error => {
                    LedgerError::error("PLUGIN", err.message)
                }
                rustledger_plugin::PluginErrorSeverity::Warning => {
                    LedgerError::warning("PLUGIN", err.message)
                }
            };
            errors.push(ledger_err);
        }

        wrappers = output.directives;
    }

    // Run each plugin (only create registry if we have plugins to run)
    if !raw_plugins.is_empty() {
        let registry = NativePluginRegistry::new();

        for (raw_name, plugin_config, force_python) in &raw_plugins {
            // Resolve the plugin name - try direct match first, then prefixed variants.
            // Skip native resolution when force_python is set (plugin "python:..." prefix).
            let resolved_name = if *force_python {
                None
            } else if registry.find(raw_name).is_some() {
                Some(raw_name.as_str())
            } else if let Some(short_name) = raw_name.strip_prefix("beancount.plugins.") {
                registry.find(short_name).is_some().then_some(short_name)
            } else if let Some(short_name) = raw_name.strip_prefix("beancount_reds_plugins.") {
                registry.find(short_name).is_some().then_some(short_name)
            } else if let Some(short_name) = raw_name.strip_prefix("beancount_lazy_plugins.") {
                registry.find(short_name).is_some().then_some(short_name)
            } else {
                None
            };

            if let Some(name) = resolved_name
                && let Some(plugin) = registry.find(name)
            {
                // Move wrappers into the plugin input instead of cloning.
                // The plugin returns modified directives in its output,
                // which we reassign to `wrappers` below.
                let input = PluginInput {
                    directives: std::mem::take(&mut wrappers),
                    options: plugin_options.clone(),
                    config: plugin_config.clone(),
                };

                let output = plugin.process(input);

                // Collect plugin errors
                for err in output.errors {
                    let ledger_err = match err.severity {
                        rustledger_plugin::PluginErrorSeverity::Error => {
                            LedgerError::error("PLUGIN", err.message).with_phase("plugin")
                        }
                        rustledger_plugin::PluginErrorSeverity::Warning => {
                            LedgerError::warning("PLUGIN", err.message).with_phase("plugin")
                        }
                    };
                    errors.push(ledger_err);
                }

                wrappers = output.directives;
            } else {
                // Not a native plugin — categorize and handle
                let plugin_path = std::path::Path::new(raw_name);
                let ext = plugin_path
                    .extension()
                    .and_then(|e| e.to_str())
                    .unwrap_or("")
                    .to_lowercase();

                // The closure is only invoked from inside the wasm-plugins /
                // python-plugins cfg blocks below. The whole function is
                // already `#[cfg(feature = "plugins")]`, so this only matters
                // when `plugins` is enabled but neither child feature is
                // (e.g. `--features native-plugins`). Allow `unused_variables`
                // for exactly that configuration. Underscore-prefixing the
                // binding would have been the wrong fix because we DO call
                // the closure in builds with one of the features enabled,
                // which would trip `no_effect_underscore_binding` instead.
                #[cfg_attr(
                    not(any(feature = "wasm-plugins", feature = "python-plugins")),
                    allow(unused_variables)
                )]
                let resolve_path = |name: &str| -> Result<std::path::PathBuf, String> {
                    let p = std::path::Path::new(name);
                    let resolved = if p.is_absolute() {
                        p.to_path_buf()
                    } else {
                        base_dir.join(name)
                    };

                    // Path security: prevent plugins from outside the ledger directory
                    if options.path_security
                        && let (Ok(canon_base), Ok(canon_plugin)) =
                            (base_dir.canonicalize(), resolved.canonicalize())
                        && !canon_plugin.starts_with(&canon_base)
                    {
                        return Err(format!(
                            "plugin path '{name}' is outside the ledger directory"
                        ));
                    }

                    Ok(resolved)
                };

                if ext == "wasm" {
                    // WASM plugin
                    #[cfg(feature = "wasm-plugins")]
                    {
                        let wasm_path = match resolve_path(raw_name) {
                            Ok(p) => p,
                            Err(e) => {
                                errors.push(LedgerError::error("PLUGIN", e).with_phase("plugin"));
                                continue;
                            }
                        };
                        match run_wasm_plugin(&wasm_path, &wrappers, &plugin_options, plugin_config)
                        {
                            Ok((output_directives, plugin_errors)) => {
                                for err in plugin_errors {
                                    errors.push(err);
                                }
                                wrappers = output_directives;
                            }
                            Err(e) => {
                                errors.push(
                                    LedgerError::error(
                                        "PLUGIN",
                                        format!("WASM plugin {} failed: {e}", wasm_path.display()),
                                    )
                                    .with_phase("plugin"),
                                );
                            }
                        }
                    }
                    #[cfg(not(feature = "wasm-plugins"))]
                    {
                        errors.push(
                            LedgerError::error(
                                "PLUGIN",
                                format!(
                                    "WASM plugin '{raw_name}' requires the wasm-plugins feature",
                                ),
                            )
                            .with_phase("plugin"),
                        );
                    }
                } else if *force_python
                    || ext == "py"
                    || raw_name.contains(std::path::MAIN_SEPARATOR)
                    || raw_name.contains('.')
                {
                    // Python module or file-based plugin (or force_python via "python:" prefix)
                    #[cfg(feature = "python-plugins")]
                    {
                        let resolved = match resolve_path(raw_name) {
                            Ok(p) => p,
                            Err(e) => {
                                errors.push(LedgerError::error("PLUGIN", e).with_phase("plugin"));
                                continue;
                            }
                        };
                        match run_python_plugin(
                            raw_name,
                            &resolved,
                            base_dir,
                            &wrappers,
                            &plugin_options,
                            plugin_config,
                        ) {
                            Ok((output_directives, plugin_errors)) => {
                                for err in plugin_errors {
                                    errors.push(err);
                                }
                                wrappers = output_directives;
                            }
                            Err(e) => {
                                errors.push(LedgerError::error("E8002", e).with_phase("plugin"));
                            }
                        }
                    }
                    #[cfg(not(feature = "python-plugins"))]
                    {
                        errors.push(
                            LedgerError::error(
                                "E8005",
                                format!(
                                    "Python plugin \"{raw_name}\" requires the python-plugins feature",
                                ),
                            )
                            .with_phase("plugin"),
                        );
                    }
                } else {
                    // Completely unknown plugin name — try to suggest a module path
                    #[cfg(feature = "python-plugins")]
                    {
                        use rustledger_plugin::python::{is_python_available, suggest_module_path};
                        let suggestion = if is_python_available() {
                            suggest_module_path(raw_name)
                        } else {
                            None
                        };
                        if let Some(module_path) = suggestion {
                            errors.push(
                                LedgerError::error(
                                    "E8004",
                                    format!(
                                        "Cannot resolve Python module '{raw_name}'. Replace with: plugin \"{module_path}\""
                                    ),
                                )
                                .with_phase("plugin"),
                            );
                        } else {
                            errors.push(
                                LedgerError::error(
                                    "E8001",
                                    format!("Plugin not found: \"{raw_name}\""),
                                )
                                .with_phase("plugin"),
                            );
                        }
                    }
                    #[cfg(not(feature = "python-plugins"))]
                    {
                        errors.push(
                            LedgerError::error(
                                "E8001",
                                format!("Plugin not found: \"{raw_name}\""),
                            )
                            .with_phase("plugin"),
                        );
                    }
                }
            }
        }
    }

    // Build a filename -> file_id lookup for restoring locations
    let filename_to_file_id: std::collections::HashMap<String, u16> = source_map
        .files()
        .iter()
        .map(|f| (f.path.display().to_string(), f.id as u16))
        .collect();

    // Convert back to directives, preserving source locations from wrappers
    let mut new_directives = Vec::with_capacity(wrappers.len());
    for wrapper in &wrappers {
        let directive = wrapper_to_directive(wrapper)
            .map_err(|e| ProcessError::PluginConversion(e.to_string()))?;

        // Reconstruct span from filename/lineno if available, falling back to
        // the plugin-synthesized sentinel when no source location is recoverable.
        // See `rustledger_parser::SYNTHESIZED_FILE_ID` and issue #896.
        let (span, file_id) =
            if let (Some(filename), Some(lineno)) = (&wrapper.filename, wrapper.lineno) {
                if let Some(&fid) = filename_to_file_id.get(filename) {
                    // Found the file - reconstruct approximate span from line number
                    if let Some(file) = source_map.get(fid as usize) {
                        let span_start = file.line_start(lineno as usize).unwrap_or(0);
                        (rustledger_parser::Span::new(span_start, span_start), fid)
                    } else {
                        (
                            rustledger_parser::Span::new(0, 0),
                            rustledger_parser::SYNTHESIZED_FILE_ID,
                        )
                    }
                } else {
                    // Plugin-generated directive with an unknown/synthetic filename.
                    (
                        rustledger_parser::Span::new(0, 0),
                        rustledger_parser::SYNTHESIZED_FILE_ID,
                    )
                }
            } else {
                // Plugin-generated directive with no source location at all.
                (
                    rustledger_parser::Span::new(0, 0),
                    rustledger_parser::SYNTHESIZED_FILE_ID,
                )
            };

        new_directives.push(Spanned::new(directive, span).with_file_id(file_id as usize));
    }

    *directives = new_directives;
    Ok(())
}

/// Run validation on directives.
#[cfg(feature = "validation")]
fn run_validation(
    directives: &[Spanned<Directive>],
    file_options: &Options,
    source_map: &SourceMap,
    errors: &mut Vec<LedgerError>,
) {
    use rustledger_validate::{ValidationOptions, validate_spanned_with_options};

    // Resolve document directories relative to the main file's directory
    let base_dir = source_map
        .files()
        .first()
        .and_then(|f| f.path.parent())
        .unwrap_or_else(|| std::path::Path::new("."));

    let resolved_document_dirs: Vec<std::path::PathBuf> = file_options
        .documents
        .iter()
        .map(|d| {
            let path = std::path::Path::new(d);
            if path.is_absolute() {
                path.to_path_buf()
            } else {
                base_dir.join(path)
            }
        })
        .collect();

    let account_types: Vec<String> = file_options
        .account_types()
        .iter()
        .map(|s| (*s).to_string())
        .collect();

    let validation_options = ValidationOptions::default()
        .with_account_types(account_types)
        .with_document_dirs(resolved_document_dirs)
        .with_infer_tolerance_from_cost(file_options.infer_tolerance_from_cost)
        .with_tolerance_multiplier(file_options.inferred_tolerance_multiplier)
        .with_inferred_tolerance_default(file_options.inferred_tolerance_default.clone());

    let validation_errors = validate_spanned_with_options(directives, validation_options);

    for err in validation_errors {
        let phase = if err.code.is_parse_phase() {
            "parse"
        } else {
            "validate"
        };
        let severity_level = if err.code.is_warning() {
            ErrorSeverity::Warning
        } else {
            ErrorSeverity::Error
        };
        // Fold the advisory note (if any) into the message so it propagates
        // through every downstream format (LedgerError, JSON diagnostic, CLI
        // report, LSP diagnostic) without each one needing a dedicated field.
        let message = match &err.note {
            Some(note) => format!("{err}\n  note: {note}"),
            None => err.to_string(),
        };
        // Resolve span + file_id into a file/line/column triple so CLI and
        // LSP consumers can render `file:line:col` headers without having
        // to do the lookup themselves (issue #901).
        let location = err.span.and_then(|span| {
            let fid = err.file_id? as usize;
            let file = source_map.get(fid)?;
            let (line, column) = file.line_col(span.start);
            Some(ErrorLocation {
                file: file.path.clone(),
                line,
                column,
            })
        });
        errors.push(LedgerError {
            severity: severity_level,
            code: err.code.code().to_string(),
            message,
            location,
            source_span: err.span.map(|s| (s.start, s.end)),
            file_id: err.file_id,
            phase: phase.to_string(),
        });
    }
}

/// Load and fully process a beancount file.
///
/// This is the main entry point, equivalent to Python's `loader.load_file()`.
/// It performs: parse → sort → book → plugins → validate.
///
/// # Example
///
/// ```ignore
/// use rustledger_loader::{load, LoadOptions};
/// use std::path::Path;
///
/// let ledger = load(Path::new("ledger.beancount"), LoadOptions::default())?;
/// for error in &ledger.errors {
///     eprintln!("{}: {}", error.code, error.message);
/// }
/// ```
pub fn load(path: &Path, options: &LoadOptions) -> Result<Ledger, ProcessError> {
    let mut loader = crate::Loader::new();

    if options.path_security {
        loader = loader.with_path_security(true);
    }

    let raw = loader.load(path)?;
    process(raw, options)
}

/// Load a beancount file without processing.
///
/// This returns raw directives without sorting, booking, or plugins.
/// Use this when you need the original parse output.
pub fn load_raw(path: &Path) -> Result<LoadResult, LoadError> {
    crate::Loader::new().load(path)
}

/// Run a WASM plugin and return its output directives and errors.
#[cfg(feature = "wasm-plugins")]
fn run_wasm_plugin(
    wasm_path: &std::path::Path,
    directives: &[rustledger_plugin_types::DirectiveWrapper],
    options: &rustledger_plugin::PluginOptions,
    config: &Option<String>,
) -> Result<
    (
        Vec<rustledger_plugin_types::DirectiveWrapper>,
        Vec<LedgerError>,
    ),
    String,
> {
    use rustledger_plugin::{PluginInput, PluginManager};

    let mut mgr = PluginManager::new();
    let plugin_idx = mgr
        .load(wasm_path)
        .map_err(|e| format!("failed to load: {e}"))?;

    let input = PluginInput {
        directives: directives.to_vec(),
        options: options.clone(),
        config: config.clone(),
    };

    let output = mgr
        .execute(plugin_idx, &input)
        .map_err(|e| format!("execution failed: {e}"))?;

    let mut errors = Vec::new();
    for err in output.errors {
        let ledger_err = match err.severity {
            rustledger_plugin::PluginErrorSeverity::Error => {
                LedgerError::error("PLUGIN", err.message).with_phase("plugin")
            }
            rustledger_plugin::PluginErrorSeverity::Warning => {
                LedgerError::warning("PLUGIN", err.message).with_phase("plugin")
            }
        };
        errors.push(ledger_err);
    }

    Ok((output.directives, errors))
}

/// Run a Python module plugin via the WASI-based Python runtime.
#[cfg(feature = "python-plugins")]
fn run_python_plugin(
    module_name: &str,
    resolved_path: &std::path::Path,
    base_dir: &std::path::Path,
    directives: &[rustledger_plugin_types::DirectiveWrapper],
    options: &rustledger_plugin::PluginOptions,
    config: &Option<String>,
) -> Result<
    (
        Vec<rustledger_plugin_types::DirectiveWrapper>,
        Vec<LedgerError>,
    ),
    String,
> {
    use rustledger_plugin::{PluginInput, python::PythonRuntime};

    let runtime = PythonRuntime::new().map_err(|e| format!("Python runtime unavailable: {e}"))?;

    let input = PluginInput {
        directives: directives.to_vec(),
        options: options.clone(),
        config: config.clone(),
    };

    // Try file-based execution first, then module-based
    let is_file = resolved_path.exists()
        || std::path::Path::new(module_name)
            .extension()
            .is_some_and(|ext| ext.eq_ignore_ascii_case("py"))
        || module_name.contains(std::path::MAIN_SEPARATOR);

    let output = if is_file {
        runtime
            .execute_module(module_name, &input, Some(base_dir))
            .map_err(|e| format!("Python plugin execution failed: {e}"))?
    } else {
        runtime
            .execute_module(module_name, &input, Some(base_dir))
            .map_err(|e| format!("Python plugin '{module_name}' execution failed: {e}"))?
    };

    let mut errors = Vec::new();
    for err in output.errors {
        let ledger_err = match err.severity {
            rustledger_plugin::PluginErrorSeverity::Error => {
                LedgerError::error("PLUGIN", err.message).with_phase("plugin")
            }
            rustledger_plugin::PluginErrorSeverity::Warning => {
                LedgerError::warning("PLUGIN", err.message).with_phase("plugin")
            }
        };
        errors.push(ledger_err);
    }

    Ok((output.directives, errors))
}
