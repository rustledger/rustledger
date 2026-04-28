//! Shared implementation for bean-check and rledger check commands.

use crate::cmd::completions::ShellType;
use crate::report::{self, SourceCache};
use anyhow::{Context, Result};
use clap::{Parser, ValueEnum};
use rustledger_core::Directive;
use rustledger_loader::{
    CacheEntry, CachedOptions, CachedPlugin, LoadError, Loader, cache_disabled_by_env,
    load_cache_entry, reintern_directives, save_cache_entry,
};
#[cfg(feature = "python-plugin-wasm")]
use rustledger_plugin::PluginManager;
#[cfg(feature = "python-plugin-wasm")]
use rustledger_plugin::{PluginInput, PluginOptions};
use serde::Serialize;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

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
    /// Processing phase: "parse", "validate", or "plugin"
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

    /// Disable the binary cache for parsed directives.
    ///
    /// Also honored: the `BEANCOUNT_DISABLE_LOAD_CACHE` environment variable
    /// (matching Python beancount). Set the `BEANCOUNT_LOAD_CACHE_FILENAME`
    /// env var to redirect the cache to a custom path.
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

    // Cache is disabled by --no-cache or by setting BEANCOUNT_DISABLE_LOAD_CACHE
    // (the latter mirrors Python beancount's opt-out env var, see issue #939).
    // The loader honors the env var on its own; this CLI-level check is a
    // perf optimization that lets us skip building the cache entry entirely.
    let cache_disabled = args.no_cache || cache_disabled_by_env();

    // Try loading from cache first (unless disabled)
    let cache_entry = if cache_disabled {
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

        // Save to cache (unless disabled, parse errors, or option warnings).
        // Option warnings (E7001-E7006) are not stored in the cache, so we must
        // avoid caching files that have them — otherwise the warnings are silently
        // lost on subsequent loads.
        if !cache_disabled && result.errors.is_empty() && result.options.warnings.is_empty() {
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
                // Delegate to the canonical Display impl on
                // `LoadError::IncludeCycle` so the wording lives in
                // exactly one place (the `#[error(...)]` attribute on
                // the variant). This is load-bearing for pta-standards
                // conformance (#765): the substring `"Duplicate
                // filename"` must appear, and centralizing the format
                // string prevents it from drifting out of sync with the
                // library-level error.
                let message = load_error.to_string();
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
                        message,
                        hint: Some("break the cycle by removing one of the includes".to_string()),
                        context: None,
                    });
                    parse_error_count += 1;
                } else if !args.quiet {
                    writeln!(stdout, "error: {message}")?;
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

    // === Delegate booking, plugins, and validation to process::process() ===
    //
    // process::process() is the single source of truth for the core pipeline:
    // sort → book → plugins (native + WASM + Python) → validate.
    // check.rs handles: caching, load error reporting, JSON formatting,
    // and CLI-specified --plugin WASM files (below).

    // Build LoadOptions for the processing pipeline
    let load_options = rustledger_loader::LoadOptions {
        run_plugins: true,
        auto_accounts: args.auto,
        extra_plugins: args.native_plugins.clone(),
        extra_plugin_configs: vec![None; args.native_plugins.len()],
        validate: true,
        ..Default::default()
    };

    // Clear load errors from the result (already reported above with rich formatting)
    let mut process_input = load_result;
    process_input.errors.clear();

    let ledger = rustledger_loader::process(process_input, &load_options)
        .with_context(|| "processing pipeline failed")?;

    // Normalize total prices (@@→@) AFTER validation to preserve exact totals for
    // precise residual calculation.
    let mut spanned_directives = ledger.directives;
    for spanned in &mut spanned_directives {
        if let Directive::Transaction(txn) = &mut spanned.value {
            rustledger_booking::normalize_prices(txn);
        }
    }

    let source_map = &ledger.source_map;
    // One renderer per invocation: amortizes GraphicalReportHandler setup
    // and caches NamedSource per file_id across all errors.
    let mut ledger_error_renderer = report::LedgerErrorRenderer::new(use_color);

    // Convert process errors to diagnostics, using the phase field to
    // split into parse/validate/plugin categories.
    for err in &ledger.errors {
        let severity_str = match err.severity {
            rustledger_loader::ErrorSeverity::Error => "error",
            rustledger_loader::ErrorSeverity::Warning => "warning",
        };

        if json_mode {
            // Compute end line/column from the error's byte span when
            // available, so multi-line directives (e.g. an unbalanced
            // transaction covering 3 lines) report a real end position
            // instead of falling back to start==end (issue #901).
            let loc = err.location.as_ref();
            let fallback_end = (loc.map_or(1, |l| l.line), loc.map_or(1, |l| l.column));
            let (end_line, end_column) = err
                .source_span
                .zip(err.file_id)
                .and_then(|((_, end), fid)| source_map.get(fid as usize).map(|f| f.line_col(end)))
                .unwrap_or(fallback_end);
            diagnostics.push(JsonDiagnostic {
                file: err
                    .location
                    .as_ref()
                    .map_or_else(|| main_file_str.clone(), |l| l.file.display().to_string()),
                line: err.location.as_ref().map_or(1, |l| l.line),
                column: err.location.as_ref().map_or(1, |l| l.column),
                end_line,
                end_column,
                severity: severity_str.to_string(),
                phase: err.phase.clone(),
                code: err.code.clone(),
                message: err.message.clone(),
                hint: None,
                context: None,
            });

            match (err.severity, err.phase.as_str()) {
                (rustledger_loader::ErrorSeverity::Error, "parse") => {
                    parse_error_count += 1;
                }
                (rustledger_loader::ErrorSeverity::Error, "validate") => {
                    validate_error_count += 1;
                }
                _ => {}
            }
        } else if !args.quiet {
            // When the error carries span+file_id and we can resolve the
            // source, render via miette so the user gets a snippet of the
            // offending directive (issue #901). Fall back to a one-line
            // `file:line:col: error[CODE]: message` for errors without
            // span info (e.g. plugin errors, cross-file invariants).
            ledger_error_renderer.render(err, source_map, &mut stdout)?;
        }

        if matches!(err.severity, rustledger_loader::ErrorSeverity::Error) {
            error_count += 1;
        }
    }
    let mut warning_count = ledger
        .errors
        .iter()
        .filter(|e| matches!(e.severity, rustledger_loader::ErrorSeverity::Warning))
        .count();

    // === Run CLI-specified WASM plugins as post-processing ===
    // File-declared plugins (native, WASM, Python) are all handled by
    // process::process(). Only CLI --plugin flags need post-process handling.
    #[cfg(feature = "python-plugin-wasm")]
    if !args.plugins.is_empty() {
        let wrappers: Vec<_> = spanned_directives
            .iter()
            .map(|s| rustledger_plugin::directive_to_wrapper(&s.value))
            .collect();

        let current_input = PluginInput {
            directives: wrappers,
            options: PluginOptions {
                operating_currencies: ledger.options.operating_currency.clone(),
                title: ledger.options.title.clone(),
            },
            config: None,
        };

        let mut wasm_mgr = PluginManager::new();
        for plugin_path in &args.plugins {
            if let Err(e) = wasm_mgr.load(plugin_path) {
                let msg = format!("failed to load WASM plugin {}: {e}", plugin_path.display());
                if json_mode {
                    diagnostics.push(JsonDiagnostic {
                        file: main_file_str.clone(),
                        line: 1,
                        column: 1,
                        end_line: 1,
                        end_column: 1,
                        severity: "error".to_string(),
                        phase: "plugin".to_string(),
                        code: "PLUGIN".to_string(),
                        message: msg,
                        hint: None,
                        context: None,
                    });
                } else if !args.quiet {
                    writeln!(stdout, "error: {msg}")?;
                }
                error_count += 1;
            }
        }
        if !wasm_mgr.is_empty() {
            match wasm_mgr.execute_all(current_input) {
                Ok(output) => {
                    for err in &output.errors {
                        let sev = match err.severity {
                            rustledger_plugin::PluginErrorSeverity::Error => "error",
                            rustledger_plugin::PluginErrorSeverity::Warning => "warning",
                        };
                        if json_mode {
                            diagnostics.push(JsonDiagnostic {
                                file: main_file_str.clone(),
                                line: 1,
                                column: 1,
                                end_line: 1,
                                end_column: 1,
                                severity: sev.to_string(),
                                phase: "plugin".to_string(),
                                code: "PLUGIN".to_string(),
                                message: err.message.clone(),
                                hint: None,
                                context: None,
                            });
                        } else if !args.quiet {
                            writeln!(stdout, "{sev}: {}", err.message)?;
                        }
                        match err.severity {
                            rustledger_plugin::PluginErrorSeverity::Error => {
                                error_count += 1;
                            }
                            rustledger_plugin::PluginErrorSeverity::Warning => {
                                warning_count += 1;
                            }
                        }
                    }
                }
                Err(e) => {
                    let msg = format!("WASM plugin execution failed: {e}");
                    if json_mode {
                        diagnostics.push(JsonDiagnostic {
                            file: main_file_str,
                            line: 1,
                            column: 1,
                            end_line: 1,
                            end_column: 1,
                            severity: "error".to_string(),
                            phase: "plugin".to_string(),
                            code: "PLUGIN".to_string(),
                            message: msg,
                            hint: None,
                            context: None,
                        });
                    } else if !args.quiet {
                        writeln!(stdout, "error: {msg}")?;
                    }
                    error_count += 1;
                }
            }
        }
    }

    // Print summary / output
    let elapsed = start.elapsed();

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_json_diagnostic_phase_field_serializes() {
        let diag = JsonDiagnostic {
            file: "test.beancount".to_string(),
            line: 1,
            column: 1,
            end_line: 1,
            end_column: 1,
            severity: "error".to_string(),
            phase: "parse".to_string(),
            code: "P0001".to_string(),
            message: "test error".to_string(),
            hint: None,
            context: None,
        };
        let json = serde_json::to_value(&diag).unwrap();
        assert_eq!(json["phase"], "parse");

        let diag_validate = JsonDiagnostic {
            phase: "validate".to_string(),
            ..diag
        };
        let json = serde_json::to_value(&diag_validate).unwrap();
        assert_eq!(json["phase"], "validate");
    }

    #[test]
    fn test_json_output_includes_phase_counts() {
        let output = JsonOutput {
            diagnostics: vec![],
            error_count: 3,
            warning_count: 0,
            parse_error_count: 1,
            validate_error_count: 2,
        };
        let json = serde_json::to_value(&output).unwrap();
        assert_eq!(json["parse_error_count"], 1);
        assert_eq!(json["validate_error_count"], 2);
        assert_eq!(json["error_count"], 3);
    }
}
