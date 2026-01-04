//! Shared implementation for bean-check and rledger-check commands.

use crate::report::{self, SourceCache};
use anyhow::{Context, Result};
use clap::Parser;
use rustledger_booking::interpolate;
use rustledger_core::Directive;
use rustledger_loader::{LoadError, Loader};
use rustledger_plugin::{
    NativePluginRegistry, PluginInput, PluginManager, PluginOptions, wrappers_to_directives,
};
use rustledger_validate::validate;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;
use tracing::Level;
use tracing_subscriber::fmt::format::FmtSpan;

/// Validate beancount files and report errors.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// The beancount file to check
    #[arg(value_name = "FILE")]
    pub file: PathBuf,

    /// Show verbose output including timing information
    #[arg(short, long)]
    pub verbose: bool,

    /// Suppress all output (just use exit code)
    #[arg(short, long)]
    pub quiet: bool,

    /// Disable the cache (accepted for Python beancount compatibility, no effect in rustledger)
    #[arg(short = 'C', long = "no-cache")]
    pub no_cache: bool,

    /// Override the cache filename (accepted for Python beancount compatibility, no effect in rustledger)
    #[arg(long, value_name = "CACHE_FILE")]
    pub cache_filename: Option<PathBuf>,

    /// Implicitly enable auto-plugins (`auto_accounts`, etc.)
    #[arg(short = 'a', long)]
    pub auto: bool,

    /// Load a WASM plugin (can be specified multiple times)
    #[arg(long = "plugin", value_name = "WASM_FILE")]
    pub plugins: Vec<PathBuf>,

    /// Run built-in native plugins (e.g., `implicit_prices`, `check_commodity`)
    #[arg(long = "native-plugin", value_name = "NAME")]
    pub native_plugins: Vec<String>,
}

fn run(args: &Args) -> Result<ExitCode> {
    let mut stdout = io::stdout().lock();
    let start = std::time::Instant::now();

    // Check if file exists
    if !args.file.exists() {
        anyhow::bail!("file not found: {}", args.file.display());
    }

    // Load the file
    if args.verbose && !args.quiet {
        eprintln!("Loading {}...", args.file.display());
    }

    let mut loader = Loader::new();
    let load_result = loader
        .load(&args.file)
        .with_context(|| format!("failed to load {}", args.file.display()))?;

    // Build source cache for error reporting
    let mut cache = SourceCache::new();
    for source_file in load_result.source_map.files() {
        let content = std::fs::read_to_string(&source_file.path).unwrap_or_else(|_| String::new());
        cache.add(&source_file.path.display().to_string(), content);
    }

    // Also add the main file
    let main_content = std::fs::read_to_string(&args.file)
        .with_context(|| format!("failed to read {}", args.file.display()))?;
    cache.add(&args.file.display().to_string(), main_content);

    // Count errors
    let mut error_count = 0;

    // Report load/parse errors
    for load_error in &load_result.errors {
        match load_error {
            LoadError::ParseErrors { path, errors } => {
                if args.quiet {
                    error_count += errors.len();
                } else {
                    let source = std::fs::read_to_string(path).unwrap_or_default();
                    error_count += report::report_parse_errors(errors, path, &source, &mut stdout)?;
                }
            }
            LoadError::Io { path, source } => {
                if !args.quiet {
                    writeln!(
                        stdout,
                        "error: failed to read {}: {}",
                        path.display(),
                        source
                    )?;
                }
                error_count += 1;
            }
            LoadError::IncludeCycle { cycle } => {
                if !args.quiet {
                    writeln!(
                        stdout,
                        "error: include cycle detected: {}",
                        cycle.join(" -> ")
                    )?;
                }
                error_count += 1;
            }
        }
    }

    // Report option warnings (E7001, E7002, E7003)
    for warning in &load_result.options.warnings {
        if !args.quiet {
            writeln!(stdout, "warning[{}]: {}", warning.code, warning.message)?;
        }
    }

    // Extract directives from Spanned wrappers
    let mut directives: Vec<_> = load_result
        .directives
        .iter()
        .map(|s| s.value.clone())
        .collect();

    // Build list of native plugins to run
    let mut native_plugins_to_run = args.native_plugins.clone();

    // If --auto is set, add auto-plugins
    if args.auto && !native_plugins_to_run.contains(&"auto_accounts".to_string()) {
        native_plugins_to_run.insert(0, "auto_accounts".to_string());
    }

    // Run plugins if specified
    if !native_plugins_to_run.is_empty() || !args.plugins.is_empty() {
        if args.verbose && !args.quiet {
            eprintln!("Running plugins...");
        }

        let wrappers = rustledger_plugin::directives_to_wrappers(&directives);
        let plugin_input = PluginInput {
            directives: wrappers,
            options: PluginOptions {
                operating_currencies: load_result.options.operating_currency.clone(),
                title: load_result.options.title.clone(),
            },
            config: None,
        };

        let native_registry = NativePluginRegistry::new();
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

    // Run interpolation on transactions
    if args.verbose && !args.quiet {
        eprintln!("Interpolating {} directives...", directives.len());
    }

    let mut interpolation_errors = Vec::new();
    for directive in &mut directives {
        if let Directive::Transaction(txn) = directive {
            match interpolate(txn) {
                Ok(result) => {
                    *txn = result.transaction;
                }
                Err(e) => {
                    interpolation_errors.push((txn.date, txn.narration.clone(), e));
                }
            }
        }
    }

    if !args.quiet && !interpolation_errors.is_empty() {
        for (date, narration, err) in &interpolation_errors {
            writeln!(stdout, "error[INTERP]: {err} ({date}, \"{narration}\")")?;
            writeln!(stdout)?;
        }
    }
    error_count += interpolation_errors.len();

    // Validate the directives
    if args.verbose && !args.quiet {
        eprintln!("Validating {} directives...", directives.len());
    }

    let validation_errors = validate(&directives);
    error_count += validation_errors
        .iter()
        .filter(|e| !e.code.is_warning())
        .count();

    if !args.quiet && !validation_errors.is_empty() {
        report::report_validation_errors(&validation_errors, &cache, &mut stdout)?;
    }

    // Print summary
    let elapsed = start.elapsed();
    if !args.quiet {
        if args.verbose {
            writeln!(
                stdout,
                "\nChecked in {:.2}ms",
                elapsed.as_secs_f64() * 1000.0
            )?;
        }
        report::print_summary(error_count, 0, &mut stdout)?;
    }

    if error_count > 0 {
        Ok(ExitCode::from(1))
    } else {
        Ok(ExitCode::SUCCESS)
    }
}

/// Main entry point for the check command.
pub fn main() -> ExitCode {
    let args = Args::parse();

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
