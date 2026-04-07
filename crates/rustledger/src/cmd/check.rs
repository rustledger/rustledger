//! Shared implementation for bean-check and rledger check commands.

use crate::cmd::completions::ShellType;
use crate::report::{self, SourceCache};
use anyhow::{Context, Result};
use chrono::NaiveDate;
use clap::{Parser, ValueEnum};
use rustledger_booking::{BookingEngine, InterpolationError};
use rustledger_core::{BookingMethod, Directive};
use rustledger_loader::{
    CacheEntry, CachedOptions, CachedPlugin, LoadError, LoadResult, Loader, load_cache_entry,
    reintern_directives, save_cache_entry,
};
#[cfg(feature = "python-plugin-wasm")]
use rustledger_plugin::PluginManager;
#[cfg(feature = "python-plugin-wasm")]
use rustledger_plugin::python::{PythonRuntime, is_python_available, suggest_module_path};
use rustledger_plugin::{NativePluginRegistry, PluginInput, PluginOptions};
use rustledger_validate::{ValidationOptions, validate_spanned_with_options};
use serde::Serialize;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;
use tracing::Level;
use tracing_subscriber::fmt::format::FmtSpan;

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
    /// Processing phase: "parse" or "validate"
    pub phase: String,
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
    /// Number of parse-phase errors
    pub parse_error_count: usize,
    /// Number of validate-phase errors
    pub validate_error_count: usize,
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
    /// The beancount file to check (uses config default if not specified)
    #[arg(value_name = "FILE")]
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

/// Run the check command with the given arguments.
pub fn run(args: &Args) -> Result<ExitCode> {
    let mut stdout = io::stdout().lock();
    let start = std::time::Instant::now();

    // File is required (the --generate-completions flag is only for standalone bean-check)
    let Some(file) = args.file.as_ref() else {
        anyhow::bail!("FILE is required");
    };

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
                force_python: p.force_python,
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

        // Save to cache (unless --no-cache, parse errors, or option warnings)
        // Option warnings (E7001-E7006) are not stored in the cache, so we must
        // avoid caching files that have them — otherwise the warnings are silently
        // lost on subsequent loads.
        if !args.no_cache && result.errors.is_empty() && result.options.warnings.is_empty() {
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
                        force_python: p.force_python,
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

    // Count errors split by phase
    let mut error_count = 0;
    let mut parse_error_count = 0;
    let mut validate_error_count = 0;

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
                            phase: "parse".to_string(),
                            code: format!("P{:04}", error.kind_code()),
                            message: error.message(),
                            hint: error.hint.clone(),
                            context: error.context.clone(),
                        });
                    }
                    error_count += errors.len();
                    parse_error_count += errors.len();
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
                        phase: "parse".to_string(),
                        code: "E0001".to_string(),
                        message: format!("failed to read file: {source}"),
                        hint: None,
                        context: None,
                    });
                    parse_error_count += 1;
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
                        phase: "parse".to_string(),
                        code: "E0002".to_string(),
                        message: format!("include cycle detected: {}", cycle.join(" -> ")),
                        hint: Some("break the cycle by removing one of the includes".to_string()),
                        context: None,
                    });
                    parse_error_count += 1;
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
                        phase: "parse".to_string(),
                        code: "E0003".to_string(),
                        message: format!(
                            "path traversal not allowed: {} escapes {}",
                            include_path,
                            base_dir.display()
                        ),
                        hint: Some("use paths within the base directory".to_string()),
                        context: None,
                    });
                    parse_error_count += 1;
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
                        phase: "parse".to_string(),
                        code: "E0004".to_string(),
                        message: format!("failed to decrypt: {message}"),
                        hint: None,
                        context: None,
                    });
                    parse_error_count += 1;
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
            LoadError::GlobNoMatch { pattern } => {
                if json_mode {
                    diagnostics.push(JsonDiagnostic {
                        file: file.display().to_string(),
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        phase: "parse".to_string(),
                        code: "E0005".to_string(),
                        message: format!("include pattern \"{pattern}\" does not match any files"),
                        hint: Some(
                            "check that the glob pattern is correct and files exist".to_string(),
                        ),
                        context: None,
                    });
                    parse_error_count += 1;
                } else if !args.quiet {
                    writeln!(
                        stdout,
                        "error: include pattern \"{pattern}\" does not match any files"
                    )?;
                }
                error_count += 1;
            }
            LoadError::GlobError { pattern, message } => {
                if json_mode {
                    diagnostics.push(JsonDiagnostic {
                        file: file.display().to_string(),
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        phase: "parse".to_string(),
                        code: "E0006".to_string(),
                        message: format!(
                            "failed to expand include pattern \"{pattern}\": {message}"
                        ),
                        hint: None,
                        context: None,
                    });
                    parse_error_count += 1;
                } else if !args.quiet {
                    writeln!(
                        stdout,
                        "error: failed to expand include pattern \"{pattern}\": {message}"
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
                phase: "parse".to_string(),
                code: warning.code.to_string(),
                message: warning.message.clone(),
                hint: None,
                context: None,
            });
            parse_error_count += 1;
        } else if !args.quiet {
            writeln!(stdout, "error[{}]: {}", warning.code, warning.message)?;
        }
    }
    error_count += option_error_count;

    // Validate plugins declared in the beancount file and categorize them
    let native_registry = NativePluginRegistry::new();
    #[cfg(feature = "python-plugin-wasm")]
    let mut python_plugins_to_run: Vec<rustledger_loader::Plugin> = Vec::new();
    #[cfg(feature = "python-plugin-wasm")]
    let mut wasm_plugins_from_file: Vec<(PathBuf, Option<String>)> = Vec::new();
    #[cfg(feature = "python-plugin-wasm")]
    let beancount_dir = file.parent().unwrap_or(std::path::Path::new("."));

    for plugin in &load_result.plugins {
        // Check if it's a WASM plugin (by file extension) - route to WASM runtime
        #[cfg(feature = "python-plugin-wasm")]
        {
            let is_wasm_file = std::path::Path::new(&plugin.name)
                .extension()
                .is_some_and(|ext| ext.eq_ignore_ascii_case("wasm"));

            if is_wasm_file {
                // Resolve path relative to beancount file's directory
                let wasm_path = if std::path::Path::new(&plugin.name).is_absolute() {
                    PathBuf::from(&plugin.name)
                } else {
                    beancount_dir.join(&plugin.name)
                };
                wasm_plugins_from_file.push((wasm_path, plugin.config.clone()));
                continue;
            }
        }

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

        // Determine if we should use Python for this plugin
        let use_python = plugin.force_python || (!is_native && !is_supported_beancount_plugin);

        if use_python {
            #[cfg(feature = "python-plugin-wasm")]
            {
                // Check if it's a file-based plugin (can be executed directly)
                let is_py_file = std::path::Path::new(&plugin.name)
                    .extension()
                    .is_some_and(|ext| ext.eq_ignore_ascii_case("py"));
                let is_file_based = is_py_file || plugin.name.contains(std::path::MAIN_SEPARATOR);

                if is_file_based {
                    // File-based Python plugins can be executed in WASM sandbox
                    python_plugins_to_run.push(plugin.clone());
                } else {
                    // Module-based plugin - we can't resolve it without system Python
                    // Provide helpful error message with suggestion
                    let (line, file_path) =
                        if let Some(source_file) = load_result.source_map.get(plugin.file_id) {
                            let (l, _) = source_file.line_col(plugin.span.start);
                            (l, source_file.path.clone())
                        } else {
                            (1, file.clone())
                        };

                    // Try to find the module path using system Python (for helpful error only)
                    let suggestion = if is_python_available() {
                        suggest_module_path(&plugin.name)
                    } else {
                        None
                    };

                    if let Some(module_path) = suggestion {
                        if !args.quiet {
                            let plugin_name = &plugin.name;
                            writeln!(
                                stdout,
                                "{}:{line}: error[E8004]: Cannot resolve Python module '{plugin_name}'",
                                file_path.display(),
                            )?;
                            writeln!(stdout)?;
                            writeln!(stdout, "Replace line {line}:")?;
                            writeln!(stdout, "  plugin \"{plugin_name}\"")?;
                            writeln!(stdout, "with:")?;
                            writeln!(stdout, "  plugin \"{module_path}\"")?;
                        }
                    } else if !args.quiet {
                        let plugin_name = &plugin.name;
                        writeln!(
                            stdout,
                            "{}:{line}: error[E8001]: Plugin not found: \"{plugin_name}\"",
                            file_path.display(),
                        )?;
                    }
                    error_count += 1;
                }
            }
            #[cfg(not(feature = "python-plugin-wasm"))]
            {
                // Python plugins not supported in this build
                let (line, _column, file_path) =
                    if let Some(source_file) = load_result.source_map.get(plugin.file_id) {
                        let (l, c) = source_file.line_col(plugin.span.start);
                        (l, c, source_file.path.clone())
                    } else {
                        (1, 1, file.clone())
                    };

                if !args.quiet {
                    writeln!(
                        stdout,
                        "{}:{}: error[E8005]: Python plugin \"{}\" requires python-plugin-wasm feature",
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
        directives: mut spanned_directives,
        options,
        plugins: file_plugins,
        source_map,
        ..
    } = load_result;

    // Run booking and interpolation FIRST (before plugins)
    // This matches Python beancount behavior where booking fills in missing amounts
    // before plugins run. Plugins like gain_loss need the interpolated amounts.
    if args.verbose && !args.quiet {
        eprintln!(
            "Booking and interpolating {} directives...",
            spanned_directives.len()
        );
    }

    // Sort directives by date before booking, so lot matching works correctly
    spanned_directives.sort_by(|a, b| {
        a.value
            .date()
            .cmp(&b.value.date())
            .then_with(|| a.value.priority().cmp(&b.value.priority()))
    });

    let booking_method: BookingMethod = options
        .booking_method
        .parse()
        .unwrap_or(BookingMethod::Strict);
    let mut booking_engine = BookingEngine::with_method(booking_method);
    let mut interpolation_errors: Vec<(NaiveDate, String, InterpolationError)> = Vec::new();

    for spanned in &mut spanned_directives {
        if let Directive::Transaction(txn) = &mut spanned.value {
            match booking_engine.book_and_interpolate(txn) {
                Ok(result) => {
                    booking_engine.apply(&result.transaction);
                    *txn = result.transaction;
                }
                Err(e) => {
                    if let rustledger_booking::BookingError::Interpolation(interp_err) = e {
                        interpolation_errors.push((
                            txn.date,
                            txn.narration.to_string(),
                            interp_err,
                        ));
                    }
                }
            }
        }
    }

    // Extract directives and spans in a single pass for efficiency
    // We need the spans for validation error reporting
    let (directives, directive_spans): (Vec<_>, Vec<(rustledger_parser::Span, u16)>) =
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

    // Build list of native plugins to run from CLI args (with no config)
    let mut native_plugins_to_run: Vec<(String, Option<String>)> = args
        .native_plugins
        .iter()
        .map(|name| (name.clone(), None))
        .collect();

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

        if !native_plugins_to_run.iter().any(|(n, _)| n == &plugin_name) {
            native_plugins_to_run.push((plugin_name, plugin.config.clone()));
        }
    }

    // If --auto is set, add auto-plugins
    if args.auto
        && !native_plugins_to_run
            .iter()
            .any(|(n, _)| n == "auto_accounts")
    {
        native_plugins_to_run.insert(0, ("auto_accounts".to_string(), None));
    }

    // Run plugins if specified
    #[cfg(feature = "python-plugin-wasm")]
    let has_wasm_plugins = !args.plugins.is_empty() || !wasm_plugins_from_file.is_empty();
    #[cfg(not(feature = "python-plugin-wasm"))]
    let has_wasm_plugins = false;
    #[cfg(feature = "python-plugin-wasm")]
    let has_python_plugins = !python_plugins_to_run.is_empty();
    #[cfg(not(feature = "python-plugin-wasm"))]
    let has_python_plugins = false;

    // Declare spanned_directives before the plugin block so it's available afterwards.
    // Allow useless_let_if_seq because refactoring this to an expression would make
    // the code much harder to read given the complexity of both branches.
    #[allow(clippy::useless_let_if_seq)]
    let mut spanned_directives: Vec<rustledger_parser::Spanned<Directive>>;

    if !native_plugins_to_run.is_empty() || has_wasm_plugins || has_python_plugins {
        if args.verbose && !args.quiet {
            eprintln!("Running plugins...");
        }

        // Convert directives to wrappers WITH source locations for proper error reporting
        let wrappers: Vec<_> = directives
            .iter()
            .zip(directive_spans.iter())
            .map(|(directive, (span, file_id))| {
                let (filename, lineno) = if let Some(file) = source_map.get(*file_id as usize) {
                    let (line, _col) = file.line_col(span.start);
                    (Some(file.path.display().to_string()), Some(line as u32))
                } else {
                    (None, None)
                };
                rustledger_plugin::directive_to_wrapper_with_location(directive, filename, lineno)
            })
            .collect();

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

        for (plugin_name, plugin_config) in &native_plugins_to_run {
            if let Some(plugin) = native_registry.find(plugin_name) {
                if args.verbose && !args.quiet {
                    eprintln!("  Running native plugin: {}", plugin.name());
                }
                // Set config for this specific plugin
                let plugin_input = PluginInput {
                    directives: current_input.directives.clone(),
                    options: current_input.options.clone(),
                    config: plugin_config.clone(),
                };
                let output = plugin.process(plugin_input);

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

        // Run Python plugins (file-based only - module-based are rejected earlier)
        #[cfg(feature = "python-plugin-wasm")]
        if !python_plugins_to_run.is_empty() {
            // Lazily initialize Python runtime
            match PythonRuntime::new() {
                Ok(runtime) => {
                    for plugin in &python_plugins_to_run {
                        if args.verbose && !args.quiet {
                            eprintln!("  Running Python plugin: {}", plugin.name);
                        }

                        // Set config for this specific plugin
                        let plugin_input = PluginInput {
                            directives: current_input.directives.clone(),
                            options: current_input.options.clone(),
                            config: plugin.config.clone(),
                        };

                        match runtime.execute_module(&plugin.name, &plugin_input, file.parent()) {
                            Ok(output) => {
                                for err in &output.errors {
                                    if !args.quiet {
                                        let severity = match err.severity {
                                            rustledger_plugin::PluginErrorSeverity::Error => {
                                                "error"
                                            }
                                            rustledger_plugin::PluginErrorSeverity::Warning => {
                                                "warning"
                                            }
                                        };
                                        writeln!(stdout, "{severity}: {}", err.message)?;
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
                                    writeln!(
                                        stdout,
                                        "error[E8002]: Python plugin execution failed: {e}"
                                    )?;
                                }
                                error_count += 1;
                            }
                        }
                    }
                }
                Err(e) => {
                    // E8003: Python runtime unavailable
                    if !args.quiet {
                        writeln!(stdout, "error[E8003]: Python runtime unavailable: {e}")?;
                    }
                    error_count += python_plugins_to_run.len();
                }
            }
        }

        #[cfg(feature = "python-plugin-wasm")]
        if !args.plugins.is_empty() || !wasm_plugins_from_file.is_empty() {
            // Execute WASM plugins declared in beancount file (each with its own config)
            for (plugin_path, config) in &wasm_plugins_from_file {
                if args.verbose && !args.quiet {
                    eprintln!("  Loading WASM plugin: {}", plugin_path.display());
                }
                let mut plugin_manager = PluginManager::new();
                if let Err(e) = plugin_manager.load(plugin_path) {
                    if !args.quiet {
                        writeln!(
                            stdout,
                            "error: failed to load WASM plugin {}: {}",
                            plugin_path.display(),
                            e
                        )?;
                    }
                    error_count += 1;
                    continue;
                }

                // Execute with this plugin's config
                let plugin_input = PluginInput {
                    directives: current_input.directives.clone(),
                    options: current_input.options.clone(),
                    config: config.clone(),
                };

                match plugin_manager.execute(0, &plugin_input) {
                    Ok(output) => {
                        for err in &output.errors {
                            if !args.quiet {
                                writeln!(stdout, "{:?}: {}", err.severity, err.message)?;
                            }
                            error_count += 1;
                        }
                        current_input.directives = output.directives;
                    }
                    Err(e) => {
                        if !args.quiet {
                            writeln!(
                                stdout,
                                "error: WASM plugin {} execution failed: {e}",
                                plugin_path.display()
                            )?;
                        }
                        error_count += 1;
                    }
                }
            }

            // Execute WASM plugins from CLI --plugin flag (no config)
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
        }

        // Convert wrappers back to Spanned directives, preserving source locations.
        // This matches the pattern in process.rs - convert per-wrapper in the loop
        // to handle errors properly and reconstruct spans from filename/lineno.
        let filename_to_file_id: std::collections::HashMap<String, u16> = source_map
            .files()
            .iter()
            .map(|f| (f.path.display().to_string(), f.id as u16))
            .collect();

        let mut spanned_directives_from_plugins: Vec<rustledger_parser::Spanned<Directive>> =
            Vec::new();
        for wrapper in &current_input.directives {
            // Convert wrapper to directive
            let directive = match rustledger_plugin::wrapper_to_directive(wrapper) {
                Ok(d) => d,
                Err(e) => {
                    if !args.quiet {
                        writeln!(stdout, "error: failed to convert plugin output: {e}")?;
                    }
                    error_count += 1;
                    continue;
                }
            };

            // Reconstruct span from wrapper's filename/lineno
            let (span, file_id) =
                if let (Some(filename), Some(lineno)) = (&wrapper.filename, wrapper.lineno) {
                    if let Some(&fid) = filename_to_file_id.get(filename) {
                        if let Some(file) = source_map.get(fid as usize) {
                            let span_start = file.line_start(lineno as usize).unwrap_or(0);
                            (rustledger_parser::Span::new(span_start, span_start), fid)
                        } else {
                            (rustledger_parser::Span::new(0, 0), 0)
                        }
                    } else {
                        // Unknown file (plugin-generated) - use zero span
                        (rustledger_parser::Span::new(0, 0), 0)
                    }
                } else {
                    // No location info - use zero span
                    (rustledger_parser::Span::new(0, 0), 0)
                };

            spanned_directives_from_plugins.push(
                rustledger_parser::Spanned::new(directive, span).with_file_id(file_id as usize),
            );
        }

        // Use the reconstructed spanned directives
        spanned_directives = spanned_directives_from_plugins;
    } else {
        // No plugins ran - restore original spanned directives from directive_spans
        spanned_directives = directives
            .into_iter()
            .zip(directive_spans)
            .map(|(d, (span, file_id))| {
                rustledger_parser::Spanned::new(d, span).with_file_id(file_id as usize)
            })
            .collect();
    }

    // Report interpolation errors from booking (which ran before plugins)
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
                    phase: "validate".to_string(),
                    code: "INTERP".to_string(),
                    message: format!("{err}"),
                    hint: None,
                    context: Some(format!("{date}, \"{narration}\"")),
                });
            }
            validate_error_count += interpolation_errors.len();
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
        eprintln!("Validating {} directives...", spanned_directives.len());
    }

    // Build validation options with account types from loader options
    // Set document_base to the file's directory for relative path resolution
    let document_base = file.parent().map(std::path::Path::to_path_buf);
    let validation_options = ValidationOptions {
        account_types,
        document_base,
        infer_tolerance_from_cost: options.infer_tolerance_from_cost,
        tolerance_multiplier: options.inferred_tolerance_multiplier,
        inferred_tolerance_default: options.inferred_tolerance_default,
        ..Default::default()
    };
    let validation_errors = validate_spanned_with_options(&spanned_directives, validation_options);

    // Normalize total prices (@@→@) AFTER validation to preserve exact totals for
    // precise residual calculation. The booking step preserves Total prices so that
    // balance checking uses the original total directly, avoiding division-then-
    // multiplication precision loss.
    for spanned in &mut spanned_directives {
        if let Directive::Transaction(txn) = &mut spanned.value {
            rustledger_booking::normalize_prices(txn);
        }
    }

    let local_validation_error_count = validation_errors
        .iter()
        .filter(|e| !e.code.is_warning())
        .count();
    let validation_warning_count = validation_errors
        .iter()
        .filter(|e| e.code.is_warning())
        .count();
    error_count += local_validation_error_count;

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
                    phase: "validate".to_string(),
                    code: err.code.code().to_string(),
                    message: err.message.clone(),
                    hint: None,
                    context: Some(format!("{}", err.date)),
                });
            }
            validate_error_count += local_validation_error_count;
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
    let warning_count = validation_warning_count;

    if json_mode {
        let output = JsonOutput {
            diagnostics,
            error_count,
            warning_count,
            parse_error_count,
            validate_error_count,
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

/// Main entry point with custom binary name (for bean-check compatibility).
pub fn main_with_name(bin_name: &str) -> ExitCode {
    let mut args = Args::parse();

    // Handle shell completion generation
    if let Some(shell) = args.generate_completions {
        crate::cmd::completions::generate_completions::<Args>(shell, bin_name);
        return ExitCode::SUCCESS;
    }

    // If no file specified, try to get from config (same as rledger)
    // Honor RLEDGER_PROFILE env var to match rledger behavior with profiles
    if args.file.is_none()
        && let Ok(loaded) = crate::config::Config::load()
    {
        let profile = std::env::var("RLEDGER_PROFILE").ok();
        args.file = loaded.config.effective_file_path(profile.as_deref());
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
