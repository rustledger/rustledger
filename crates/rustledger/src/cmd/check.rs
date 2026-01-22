//! Shared implementation for bean-check and rledger-check commands.

use crate::cmd::completions::ShellType;
use crate::report::{self, SourceCache};
use anyhow::{Context, Result};
use chrono::NaiveDate;
use clap::{Parser, ValueEnum};
use rayon::prelude::*;
use rustledger_booking::{InterpolationError, interpolate};
use rustledger_core::Directive;
use rustledger_loader::{
    CacheEntry, CachedOptions, CachedPlugin, LoadError, LoadResult, Loader, load_cache_entry,
    reintern_directives, save_cache_entry,
};
#[cfg(feature = "python-plugin-wasm")]
use rustledger_plugin::PluginManager;
use rustledger_plugin::{NativePluginRegistry, PluginInput, PluginOptions, wrappers_to_directives};
use rustledger_validate::{ValidationOptions, validate_spanned_with_options};
use serde::Serialize;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;
use tracing::Level;
use tracing_subscriber::fmt::format::FmtSpan;

/// Check if a Python plugin can be imported.
///
/// This function attempts to verify if a plugin module exists in the Python environment
/// by running `python3 -c "import <module>"`. For file-based plugins (paths ending in .py
/// or containing path separators), it checks if the file exists.
///
/// Returns `true` if the plugin appears to be available, `false` otherwise.
fn check_python_plugin_exists(plugin_name: &str) -> bool {
    // For file-based plugins (relative/absolute paths), check filesystem
    let is_py_file = std::path::Path::new(plugin_name)
        .extension()
        .is_some_and(|ext| ext.eq_ignore_ascii_case("py"));
    if is_py_file || plugin_name.contains(std::path::MAIN_SEPARATOR) {
        // For relative paths, we can't easily resolve them without knowing the
        // beancount file's directory, so we'll be conservative and assume they exist
        // if they look like file paths. Python beancount will validate them properly.
        return true;
    }

    // For module-style plugins, try to import with Python
    // Use sys.argv to safely pass the plugin name without shell interpolation
    let output = std::process::Command::new("python3")
        .args([
            "-c",
            "import importlib, sys; importlib.import_module(sys.argv[1])",
            plugin_name,
        ])
        .output();

    match output {
        Ok(result) => result.status.success(),
        Err(_) => {
            // Python not available - be conservative and assume plugin exists
            // This avoids false positives when Python isn't installed
            true
        }
    }
}

/// Output format for diagnostics.
#[derive(Debug, Clone, Copy, Default, ValueEnum)]
pub enum OutputFormat {
    /// Human-readable text output (default)
    #[default]
    Text,
    /// JSON output for IDE/tooling integration
    Json,
}

/// A diagnostic message in JSON format.
#[derive(Debug, Serialize)]
pub struct JsonDiagnostic {
    /// Source file path
    pub file: String,
    /// Line number (1-based)
    pub line: usize,
    /// Column number (1-based)
    pub column: usize,
    /// End line number (1-based)
    pub end_line: usize,
    /// End column number (1-based)
    pub end_column: usize,
    /// Severity: "error" or "warning"
    pub severity: String,
    /// Error code (e.g., "P0012", "E1001")
    pub code: String,
    /// Error message
    pub message: String,
    /// Optional hint for fixing the error
    #[serde(skip_serializing_if = "Option::is_none")]
    pub hint: Option<String>,
    /// Optional context information
    #[serde(skip_serializing_if = "Option::is_none")]
    pub context: Option<String>,
}

/// JSON output structure for all diagnostics.
#[derive(Debug, Serialize)]
pub struct JsonOutput {
    /// List of diagnostics
    pub diagnostics: Vec<JsonDiagnostic>,
    /// Total error count
    pub error_count: usize,
    /// Total warning count
    pub warning_count: usize,
}

/// Convert a byte offset to (line, column) in 1-based indexing.
fn byte_offset_to_line_col(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut col = 1;
    for (i, ch) in source.char_indices() {
        if i >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

/// Validate beancount files and report errors.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// The beancount file to check
    #[arg(value_name = "FILE", required_unless_present = "generate_completions")]
    pub file: Option<PathBuf>,

    /// Generate shell completions and exit
    #[arg(long, value_name = "SHELL", hide = true)]
    pub generate_completions: Option<ShellType>,

    /// Show verbose output including timing information
    #[arg(short, long)]
    pub verbose: bool,

    /// Suppress all output (just use exit code)
    #[arg(short, long)]
    pub quiet: bool,

    /// Disable the binary cache for parsed directives
    #[arg(short = 'C', long = "no-cache")]
    pub no_cache: bool,

    /// Override the cache filename (not yet implemented)
    #[arg(long, value_name = "CACHE_FILE", hide = true)]
    pub cache_filename: Option<PathBuf>,

    /// Implicitly enable auto-plugins (`auto_accounts`, etc.)
    #[arg(short = 'a', long)]
    pub auto: bool,

    /// Load a WASM plugin (can be specified multiple times)
    #[cfg(feature = "python-plugin-wasm")]
    #[arg(long = "plugin", value_name = "WASM_FILE")]
    pub plugins: Vec<PathBuf>,

    /// Run built-in native plugins (e.g., `implicit_prices`, `check_commodity`)
    #[arg(long = "native-plugin", value_name = "NAME")]
    pub native_plugins: Vec<String>,

    /// Output format (text or json)
    #[arg(long, short = 'f', value_enum, default_value = "text")]
    pub format: OutputFormat,
}

fn run(args: &Args) -> Result<ExitCode> {
    let mut stdout = io::stdout().lock();
    let start = std::time::Instant::now();

    // File is guaranteed to be Some here (checked in main)
    let file = args.file.as_ref().expect("file required");

    // Check if file exists
    if !file.exists() {
        anyhow::bail!("file not found: {}", file.display());
    }

    // Collect diagnostics for JSON output
    let json_mode = matches!(args.format, OutputFormat::Json);
    let mut diagnostics: Vec<JsonDiagnostic> = Vec::new();

    // Determine if colors should be used (TTY detection + NO_COLOR)
    let use_color = !json_mode && report::should_use_color();

    // Try loading from cache first (unless --no-cache)
    let cache_entry = if args.no_cache {
        None
    } else {
        load_cache_entry(file)
    };

    let (load_result, from_cache) = if let Some(mut entry) = cache_entry {
        if args.verbose && !args.quiet {
            eprintln!("Loaded {} directives from cache", entry.directives.len());
        }

        // Re-intern strings to deduplicate memory
        let dedup_count = reintern_directives(&mut entry.directives);
        if args.verbose && !args.quiet {
            eprintln!("Re-interned strings ({dedup_count} deduplicated)");
        }

        // Rebuild source map from cached file list
        let mut source_map = rustledger_loader::SourceMap::new();
        for path in entry.file_paths() {
            if let Ok(content) = std::fs::read_to_string(&path) {
                source_map.add_file(path, content.into());
            }
        }

        // Convert CachedPlugin -> Plugin (span/file_id are not meaningful from cache)
        let plugins: Vec<rustledger_loader::Plugin> = entry
            .plugins
            .iter()
            .map(|p| rustledger_loader::Plugin {
                name: p.name.clone(),
                config: p.config.clone(),
                span: rustledger_parser::Span::new(0, 0),
                file_id: 0,
            })
            .collect();

        let result = rustledger_loader::LoadResult {
            directives: entry.directives,
            options: entry.options.into(),
            plugins,
            source_map,
            errors: Vec::new(),
            // Build display context from cached directives
            display_context: rustledger_core::DisplayContext::new(),
        };
        (result, true)
    } else {
        // Load the file normally
        if args.verbose && !args.quiet {
            eprintln!("Loading {}...", file.display());
        }

        let mut loader = Loader::new();
        let result = loader
            .load(file)
            .with_context(|| format!("failed to load {}", file.display()))?;

        // Save to cache (unless --no-cache or there are parse errors)
        if !args.no_cache && result.errors.is_empty() {
            // Collect all loaded file paths for cache (as strings for serialization)
            let files: Vec<String> = result
                .source_map
                .files()
                .iter()
                .map(|f| f.path.to_string_lossy().into_owned())
                .collect();
            let files = if files.is_empty() {
                vec![file.to_string_lossy().into_owned()]
            } else {
                files
            };

            // Create full cache entry
            let entry = CacheEntry {
                directives: result.directives.clone(),
                options: CachedOptions::from(&result.options),
                plugins: result
                    .plugins
                    .iter()
                    .map(|p| CachedPlugin {
                        name: p.name.clone(),
                        config: p.config.clone(),
                    })
                    .collect(),
                files,
            };

            if let Err(e) = save_cache_entry(file, &entry) {
                if args.verbose && !args.quiet {
                    eprintln!("Warning: failed to save cache: {e}");
                }
            } else if args.verbose && !args.quiet {
                eprintln!("Saved {} directives to cache", result.directives.len());
            }
        }

        (result, false)
    };

    // Build source cache for error reporting
    let mut cache = SourceCache::new();
    for source_file in load_result.source_map.files() {
        // Use lossy UTF-8 decoding to handle non-UTF-8 files gracefully
        let content = std::fs::read(&source_file.path)
            .map(|b| String::from_utf8_lossy(&b).into_owned())
            .unwrap_or_default();
        let path_str = source_file.path.display().to_string();
        cache.add(&path_str, content);
    }

    // Also add the main file (use lossy decoding for non-UTF-8 files)
    let main_content = std::fs::read(file)
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .with_context(|| format!("failed to read {}", file.display()))?;
    cache.add(&file.display().to_string(), main_content);

    // Count errors
    let mut error_count = 0;

    // Report load/parse errors
    for load_error in &load_result.errors {
        match load_error {
            LoadError::ParseErrors { path, errors } => {
                let source = std::fs::read_to_string(path).unwrap_or_default();
                let path_str = path.display().to_string();

                if json_mode {
                    for error in errors {
                        let (start_line, start_col) =
                            byte_offset_to_line_col(&source, error.span.start);
                        let (end_line, end_col) = byte_offset_to_line_col(&source, error.span.end);
                        diagnostics.push(JsonDiagnostic {
                            file: path_str.clone(),
                            line: start_line,
                            column: start_col,
                            end_line,
                            end_column: end_col,
                            severity: "error".to_string(),
                            code: format!("P{:04}", error.kind_code()),
                            message: error.message(),
                            hint: error.hint.clone(),
                            context: error.context.clone(),
                        });
                    }
                    error_count += errors.len();
                } else if args.quiet {
                    error_count += errors.len();
                } else {
                    error_count +=
                        report::report_parse_errors(errors, path, &source, &mut stdout, use_color)?;
                }
            }
            LoadError::Io { path, source } => {
                let path_str = path.display().to_string();
                if json_mode {
                    diagnostics.push(JsonDiagnostic {
                        file: path_str,
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        code: "E0001".to_string(),
                        message: format!("failed to read file: {source}"),
                        hint: None,
                        context: None,
                    });
                } else if !args.quiet {
                    writeln!(stdout, "error: failed to read {path_str}: {source}")?;
                }
                error_count += 1;
            }
            LoadError::IncludeCycle { cycle } => {
                if json_mode {
                    diagnostics.push(JsonDiagnostic {
                        file: cycle.first().cloned().unwrap_or_default(),
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        code: "E0002".to_string(),
                        message: format!("include cycle detected: {}", cycle.join(" -> ")),
                        hint: Some("break the cycle by removing one of the includes".to_string()),
                        context: None,
                    });
                } else if !args.quiet {
                    writeln!(
                        stdout,
                        "error: include cycle detected: {}",
                        cycle.join(" -> ")
                    )?;
                }
                error_count += 1;
            }
            LoadError::PathTraversal {
                include_path,
                base_dir,
            } => {
                if json_mode {
                    diagnostics.push(JsonDiagnostic {
                        file: base_dir.display().to_string(),
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        code: "E0003".to_string(),
                        message: format!(
                            "path traversal not allowed: {} escapes {}",
                            include_path,
                            base_dir.display()
                        ),
                        hint: Some("use paths within the base directory".to_string()),
                        context: None,
                    });
                } else if !args.quiet {
                    writeln!(
                        stdout,
                        "error: path traversal not allowed: {} escapes {}",
                        include_path,
                        base_dir.display()
                    )?;
                }
                error_count += 1;
            }
            LoadError::Decryption { path, message } => {
                let path_str = path.display().to_string();
                if json_mode {
                    diagnostics.push(JsonDiagnostic {
                        file: path_str,
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        code: "E0004".to_string(),
                        message: format!("failed to decrypt: {message}"),
                        hint: None,
                        context: None,
                    });
                } else if !args.quiet {
                    writeln!(
                        stdout,
                        "error: failed to decrypt {}: {}",
                        path.display(),
                        message
                    )?;
                }
                error_count += 1;
            }
        }
    }

    // Report option errors (E7001, E7002, E7003)
    // In Python beancount, invalid options are errors, not warnings
    let main_file_str = file.display().to_string();
    let option_error_count = load_result.options.warnings.len();
    for warning in &load_result.options.warnings {
        if json_mode {
            diagnostics.push(JsonDiagnostic {
                file: main_file_str.clone(),
                line: 1,
                column: 1,
                end_line: 1,
                end_column: 1,
                severity: "error".to_string(),
                code: warning.code.to_string(),
                message: warning.message.clone(),
                hint: None,
                context: None,
            });
        } else if !args.quiet {
            writeln!(stdout, "error[{}]: {}", warning.code, warning.message)?;
        }
    }
    error_count += option_error_count;

    // Validate plugins declared in the beancount file
    // Like Python beancount, report an error if a plugin is not found
    let native_registry = NativePluginRegistry::new();
    let mut plugin_warning_count = 0usize;
    for plugin in &load_result.plugins {
        // Check if it's a known native plugin
        let is_native = native_registry.find(&plugin.name).is_some();
        // Check for common beancount.plugins.* that we support as native
        let is_supported_beancount_plugin = plugin.name.starts_with("beancount.plugins.")
            && native_registry
                .find(
                    plugin
                        .name
                        .strip_prefix("beancount.plugins.")
                        .unwrap_or(&plugin.name),
                )
                .is_some();

        if !is_native && !is_supported_beancount_plugin {
            // Get source location for error reporting
            let (line, column, file_path) =
                if let Some(source_file) = load_result.source_map.get(plugin.file_id) {
                    let (l, c) = source_file.line_col(plugin.span.start);
                    (l, c, source_file.path.clone())
                } else {
                    (1, 1, file.clone())
                };

            // Check if Python can import this plugin
            let python_can_import = check_python_plugin_exists(&plugin.name);

            if python_can_import {
                // Plugin exists in Python but we can't run it - warn but don't fail
                if json_mode {
                    diagnostics.push(JsonDiagnostic {
                        file: file_path.display().to_string(),
                        line,
                        column,
                        end_line: line,
                        end_column: column + plugin.name.len(),
                        severity: "warning".to_string(),
                        code: "W8002".to_string(),
                        message: format!(
                            "Python plugin \"{}\" found but cannot be executed by rustledger",
                            plugin.name
                        ),
                        hint: Some(
                            "Plugin validation skipped. Use Python beancount for full plugin support."
                                .to_string(),
                        ),
                        context: None,
                    });
                } else if !args.quiet {
                    writeln!(
                        stdout,
                        "{}:{}: warning[W8002]: Python plugin \"{}\" found but cannot be executed",
                        file_path.display(),
                        line,
                        plugin.name
                    )?;
                }
                plugin_warning_count += 1;
            } else {
                // Plugin doesn't exist - error (matches Python beancount behavior)
                if json_mode {
                    diagnostics.push(JsonDiagnostic {
                        file: file_path.display().to_string(),
                        line,
                        column,
                        end_line: line,
                        end_column: column + plugin.name.len(),
                        severity: "error".to_string(),
                        code: "E8001".to_string(),
                        message: format!("Plugin not found: \"{}\"", plugin.name),
                        hint: Some(
                            "Plugin could not be found by Python. Check the plugin name and installation."
                                .to_string(),
                        ),
                        context: None,
                    });
                } else if !args.quiet {
                    writeln!(
                        stdout,
                        "{}:{}: error[E8001]: Plugin not found: \"{}\"",
                        file_path.display(),
                        line,
                        plugin.name
                    )?;
                }
                error_count += 1;
            }
        }
    }

    // Destructure to enable move instead of clone
    let LoadResult {
        directives: spanned_directives,
        options,
        plugins: file_plugins,
        source_map,
        ..
    } = load_result;

    // Extract directives and spans in a single pass for efficiency
    // We need the spans for validation error reporting
    let (mut directives, directive_spans): (Vec<_>, Vec<(rustledger_parser::Span, u16)>) =
        spanned_directives
            .into_iter()
            .map(|s| (s.value, (s.span, s.file_id)))
            .unzip();

    // Save account types before options are partially moved
    let account_types: Vec<String> = options
        .account_types()
        .iter()
        .map(|s| (*s).to_string())
        .collect();

    // Build list of native plugins to run from CLI args
    let mut native_plugins_to_run = args.native_plugins.clone();

    // Also run plugins declared in the beancount file (if they're native)
    for plugin in &file_plugins {
        // Try with full name first, then without beancount.plugins. prefix
        let plugin_name = if native_registry.find(&plugin.name).is_some() {
            plugin.name.clone()
        } else if let Some(short_name) = plugin.name.strip_prefix("beancount.plugins.") {
            if native_registry.find(short_name).is_some() {
                short_name.to_string()
            } else {
                continue; // Unknown plugin, already reported error above
            }
        } else {
            continue; // Unknown plugin, already reported error above
        };

        if !native_plugins_to_run.contains(&plugin_name) {
            native_plugins_to_run.push(plugin_name);
        }
    }

    // If --auto is set, add auto-plugins
    if args.auto && !native_plugins_to_run.contains(&"auto_accounts".to_string()) {
        native_plugins_to_run.insert(0, "auto_accounts".to_string());
    }

    // Run plugins if specified
    #[cfg(feature = "python-plugin-wasm")]
    let has_wasm_plugins = !args.plugins.is_empty();
    #[cfg(not(feature = "python-plugin-wasm"))]
    let has_wasm_plugins = false;

    if !native_plugins_to_run.is_empty() || has_wasm_plugins {
        if args.verbose && !args.quiet {
            eprintln!("Running plugins...");
        }

        let wrappers = rustledger_plugin::directives_to_wrappers(&directives);
        let plugin_input = PluginInput {
            directives: wrappers,
            options: PluginOptions {
                operating_currencies: options.operating_currency,
                title: options.title,
            },
            config: None,
        };

        // native_registry already created above for plugin validation
        let mut current_input = plugin_input;

        for plugin_name in &native_plugins_to_run {
            if let Some(plugin) = native_registry.find(plugin_name) {
                if args.verbose && !args.quiet {
                    eprintln!("  Running native plugin: {}", plugin.name());
                }
                let output = plugin.process(current_input.clone());

                for err in &output.errors {
                    if !args.quiet {
                        writeln!(stdout, "{:?}: {}", err.severity, err.message)?;
                    }
                    error_count += 1;
                }

                current_input = PluginInput {
                    directives: output.directives,
                    options: current_input.options.clone(),
                    config: None,
                };
            } else if !args.quiet {
                writeln!(stdout, "warning: unknown native plugin: {plugin_name}")?;
            }
        }

        #[cfg(feature = "python-plugin-wasm")]
        if !args.plugins.is_empty() {
            let mut wasm_manager = PluginManager::new();

            for plugin_path in &args.plugins {
                if args.verbose && !args.quiet {
                    eprintln!("  Loading WASM plugin: {}", plugin_path.display());
                }
                if let Err(e) = wasm_manager.load(plugin_path) {
                    if !args.quiet {
                        writeln!(
                            stdout,
                            "error: failed to load WASM plugin {}: {}",
                            plugin_path.display(),
                            e
                        )?;
                    }
                    error_count += 1;
                }
            }

            if !wasm_manager.is_empty() {
                if args.verbose && !args.quiet {
                    eprintln!("  Executing {} WASM plugin(s)...", wasm_manager.len());
                }

                match wasm_manager.execute_all(current_input.clone()) {
                    Ok(output) => {
                        for err in &output.errors {
                            if !args.quiet {
                                writeln!(stdout, "{:?}: {}", err.severity, err.message)?;
                            }
                            error_count += 1;
                        }

                        current_input = PluginInput {
                            directives: output.directives,
                            options: current_input.options.clone(),
                            config: None,
                        };
                    }
                    Err(e) => {
                        if !args.quiet {
                            writeln!(stdout, "error: WASM plugin execution failed: {e}")?;
                        }
                        error_count += 1;
                    }
                }
            }
        }

        match wrappers_to_directives(&current_input.directives) {
            Ok(converted) => {
                directives = converted;
            }
            Err(e) => {
                if !args.quiet {
                    writeln!(stdout, "error: failed to convert plugin output: {e}")?;
                }
                error_count += 1;
            }
        }
    }

    // Run interpolation on transactions (parallel)
    if args.verbose && !args.quiet {
        eprintln!("Interpolating {} directives...", directives.len());
    }

    let interpolation_errors: Vec<(NaiveDate, String, InterpolationError)> = directives
        .par_iter_mut()
        .filter_map(|directive| {
            if let Directive::Transaction(txn) = directive {
                match interpolate(txn) {
                    Ok(result) => {
                        *txn = result.transaction;
                        None
                    }
                    Err(e) => {
                        // Skip CannotInferCurrency errors when transaction has empty cost specs
                        // because the cost will be filled by lot matching during validation.
                        // This matches Python beancount behavior where booking runs before interpolation.
                        let has_empty_cost_spec = txn.postings.iter().any(|p| {
                            if let Some(cost) = &p.cost {
                                cost.number_per.is_none() && cost.number_total.is_none()
                            } else {
                                false
                            }
                        });
                        if has_empty_cost_spec
                            && matches!(e, InterpolationError::CannotInferCurrency { .. })
                        {
                            None // Skip error - lot matching will handle this
                        } else {
                            Some((txn.date, txn.narration.to_string(), e))
                        }
                    }
                }
            } else {
                None
            }
        })
        .collect();

    if !interpolation_errors.is_empty() {
        if json_mode {
            for (date, narration, err) in &interpolation_errors {
                diagnostics.push(JsonDiagnostic {
                    file: main_file_str.clone(),
                    line: 1, // Transaction dates don't have line numbers yet
                    column: 1,
                    end_line: 1,
                    end_column: 1,
                    severity: "error".to_string(),
                    code: "INTERP".to_string(),
                    message: format!("{err}"),
                    hint: None,
                    context: Some(format!("{date}, \"{narration}\"")),
                });
            }
        } else if !args.quiet {
            for (date, narration, err) in &interpolation_errors {
                writeln!(stdout, "error[INTERP]: {err} ({date}, \"{narration}\")")?;
                writeln!(stdout)?;
            }
        }
    }
    error_count += interpolation_errors.len();

    // Validate the directives
    if args.verbose && !args.quiet {
        eprintln!("Validating {} directives...", directives.len());
    }

    // Build validation options with account types from loader options
    // Set document_base to the file's directory for relative path resolution
    let document_base = file.parent().map(std::path::Path::to_path_buf);
    let validation_options = ValidationOptions {
        account_types,
        document_base,
        ..Default::default()
    };

    // Convert directives back to Spanned form for validation
    // If directive count matches original, re-associate original spans
    // Otherwise use default spans (plugins may have added/removed directives)
    let spanned_for_validation: Vec<rustledger_parser::Spanned<Directive>> =
        if directives.len() == directive_spans.len() {
            directives
                .into_iter()
                .zip(directive_spans)
                .map(|(d, (span, file_id))| {
                    rustledger_parser::Spanned::new(d, span).with_file_id(file_id as usize)
                })
                .collect()
        } else {
            // Directive count changed (plugins modified list), use default spans
            directives
                .into_iter()
                .map(|d| rustledger_parser::Spanned::new(d, rustledger_parser::Span::new(0, 0)))
                .collect()
        };
    let validation_errors =
        validate_spanned_with_options(&spanned_for_validation, validation_options);
    let validation_error_count = validation_errors
        .iter()
        .filter(|e| !e.code.is_warning())
        .count();
    let validation_warning_count = validation_errors
        .iter()
        .filter(|e| e.code.is_warning())
        .count();
    error_count += validation_error_count;

    if !validation_errors.is_empty() {
        if json_mode {
            for err in &validation_errors {
                let severity = if err.code.is_warning() {
                    "warning"
                } else {
                    "error"
                };
                diagnostics.push(JsonDiagnostic {
                    file: main_file_str.clone(),
                    line: 1, // Validation errors don't have precise locations yet
                    column: 1,
                    end_line: 1,
                    end_column: 1,
                    severity: severity.to_string(),
                    code: err.code.code().to_string(),
                    message: err.message.clone(),
                    hint: None,
                    context: Some(format!("{}", err.date)),
                });
            }
        } else if !args.quiet {
            report::report_validation_errors(
                &validation_errors,
                &source_map,
                &cache,
                &mut stdout,
                use_color,
            )?;
        }
    }

    // Print summary / output
    let elapsed = start.elapsed();
    let warning_count = validation_warning_count + plugin_warning_count;

    if json_mode {
        let output = JsonOutput {
            diagnostics,
            error_count,
            warning_count,
        };
        writeln!(stdout, "{}", serde_json::to_string_pretty(&output)?)?;
    } else if !args.quiet {
        if args.verbose {
            let cache_note = if from_cache { " (from cache)" } else { "" };
            writeln!(
                stdout,
                "\nChecked in {:.2}ms{}",
                elapsed.as_secs_f64() * 1000.0,
                cache_note
            )?;
        }
        report::print_summary(error_count, warning_count, &mut stdout, use_color)?;
    }

    if error_count > 0 {
        Ok(ExitCode::from(1))
    } else {
        Ok(ExitCode::SUCCESS)
    }
}

/// Main entry point for the check command.
pub fn main() -> ExitCode {
    main_with_name("rledger-check")
}

/// Main entry point with custom binary name (for bean-check compatibility).
pub fn main_with_name(bin_name: &str) -> ExitCode {
    let args = Args::parse();

    // Handle shell completion generation
    if let Some(shell) = args.generate_completions {
        crate::cmd::completions::generate_completions::<Args>(shell, bin_name);
        return ExitCode::SUCCESS;
    }

    if args.verbose {
        tracing_subscriber::fmt()
            .with_max_level(Level::DEBUG)
            .with_span_events(FmtSpan::CLOSE)
            .init();
    }

    match run(&args) {
        Ok(exit_code) => exit_code,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(2)
        }
    }
}
