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
        date: chrono::NaiveDate,
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
pub struct LedgerError {
    /// Error severity.
    pub severity: ErrorSeverity,
    /// Error code (e.g., "E0001", "W8002").
    pub code: String,
    /// Human-readable error message.
    pub message: String,
    /// Source location, if available.
    pub location: Option<ErrorLocation>,
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
    /// Create a new error.
    pub fn error(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            severity: ErrorSeverity::Error,
            code: code.into(),
            message: message.into(),
            location: None,
        }
    }

    /// Create a new warning.
    pub fn warning(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            severity: ErrorSeverity::Warning,
            code: code.into(),
            message: message.into(),
            location: None,
        }
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

    // Convert load errors to ledger errors
    for load_err in raw.errors {
        errors.push(LedgerError::error("LOAD", load_err.to_string()));
    }

    // 1. Sort by date (and priority for same-date directives)
    directives.sort_by(|a, b| {
        a.value
            .date()
            .cmp(&b.value.date())
            .then_with(|| a.value.priority().cmp(&b.value.priority()))
    });

    // 2. Booking/interpolation
    #[cfg(feature = "booking")]
    {
        run_booking(&mut directives, options, &mut errors);
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
            &raw.source_map,
            options,
            &mut errors,
        )?;
    }

    // 4. Validation
    #[cfg(feature = "validation")]
    if options.validate {
        run_validation(&directives, &raw.options, &mut errors);
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
    options: &LoadOptions,
    errors: &mut Vec<LedgerError>,
) {
    use rustledger_booking::BookingEngine;

    let mut engine = BookingEngine::with_method(options.booking_method);

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
#[cfg(feature = "plugins")]
fn run_plugins(
    directives: &mut Vec<Spanned<Directive>>,
    file_plugins: &[Plugin],
    file_options: &Options,
    source_map: &SourceMap,
    options: &LoadOptions,
    errors: &mut Vec<LedgerError>,
) -> Result<(), ProcessError> {
    use rustledger_plugin::{
        DocumentDiscoveryPlugin, NativePlugin, NativePluginRegistry, PluginInput, PluginOptions,
        directives_to_wrappers, wrappers_to_directives,
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
    let mut raw_plugins: Vec<(String, Option<String>)> = Vec::new();

    // Add auto_accounts first if requested
    if options.auto_accounts {
        raw_plugins.push(("auto_accounts".to_string(), None));
    }

    // Add plugins from the file
    if options.run_plugins {
        for plugin in file_plugins {
            raw_plugins.push((plugin.name.clone(), plugin.config.clone()));
        }
    }

    // Add extra plugins from options
    for (i, plugin_name) in options.extra_plugins.iter().enumerate() {
        let config = options.extra_plugin_configs.get(i).cloned().flatten();
        raw_plugins.push((plugin_name.clone(), config));
    }

    // Check if we have any work to do - early return before creating registry
    if raw_plugins.is_empty() && !has_document_dirs {
        return Ok(());
    }

    // Convert directives to plugin format (without spans for now)
    let plain_directives: Vec<Directive> = directives.iter().map(|s| s.value.clone()).collect();
    let mut wrappers = directives_to_wrappers(&plain_directives);

    let plugin_options = PluginOptions {
        operating_currencies: file_options.operating_currency.clone(),
        title: file_options.title.clone(),
    };

    // Run document discovery plugin if documents directories are configured
    if has_document_dirs {
        let doc_plugin = DocumentDiscoveryPlugin::new(resolved_documents, base_dir.to_path_buf());
        let input = PluginInput {
            directives: wrappers.clone(),
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

        for (raw_name, plugin_config) in &raw_plugins {
            // Resolve the plugin name - try direct match first, then prefixed variants
            let resolved_name = if registry.find(raw_name).is_some() {
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
                let input = PluginInput {
                    directives: wrappers.clone(),
                    options: plugin_options.clone(),
                    config: plugin_config.clone(),
                };

                let output = plugin.process(input);

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
        }
    }

    // Convert back to directives
    let processed = wrappers_to_directives(&wrappers)
        .map_err(|e| ProcessError::PluginConversion(e.to_string()))?;

    // Replace directives, preserving spans where possible
    if processed.len() == directives.len() {
        // Same count - update in place
        for (i, new_directive) in processed.into_iter().enumerate() {
            directives[i].value = new_directive;
        }
    } else {
        // Count changed - plugins added/removed directives.
        // Use synthetic zero spans for plugin-generated directives since we cannot
        // reliably map them back to source locations. Error reporting for these
        // directives will show the plugin name instead of a file location.
        *directives = processed
            .into_iter()
            .map(|d| Spanned::new(d, rustledger_parser::Span::new(0, 0)))
            .collect();
    }

    Ok(())
}

/// Run validation on directives.
#[cfg(feature = "validation")]
fn run_validation(
    directives: &[Spanned<Directive>],
    file_options: &Options,
    errors: &mut Vec<LedgerError>,
) {
    use rustledger_validate::{ValidationOptions, validate_spanned_with_options};

    let account_types: Vec<String> = file_options
        .account_types()
        .iter()
        .map(|s| (*s).to_string())
        .collect();

    let validation_options = ValidationOptions {
        account_types,
        infer_tolerance_from_cost: file_options.infer_tolerance_from_cost,
        tolerance_multiplier: file_options.inferred_tolerance_multiplier,
        inferred_tolerance_default: file_options.inferred_tolerance_default.clone(),
        ..Default::default()
    };

    let validation_errors = validate_spanned_with_options(directives, validation_options);

    for err in validation_errors {
        errors.push(LedgerError::error(err.code.code(), err.to_string()));
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
