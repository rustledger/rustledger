//! Shared implementation for bean-check and rledger-check commands.

use crate::cmd::completions::ShellType;
use crate::report::{self, SourceCache};
use anyhow::{Context, Result};
use clap::Parser;
use rustledger_booking::interpolate;
use rustledger_core::Directive;
use rustledger_loader::{LoadError, Loader};
use rustledger_plugin::{
    wrappers_to_directives, NativePluginRegistry, PluginInput, PluginManager, PluginOptions,
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

    /// Run a Python beancount plugin (slower, downloads runtime on first use)
    #[cfg(feature = "python-plugins")]
    #[arg(long = "python-plugin", value_name = "MODULE")]
    pub python_plugins: Vec<String>,

    /// Load a Python plugin from file path
    #[cfg(feature = "python-plugins")]
    #[arg(long = "python-plugin-path", value_name = "PATH")]
    pub python_plugin_paths: Vec<PathBuf>,

    /// Force Python execution for plugins (skip native Rust implementations)
    #[cfg(feature = "python-plugins")]
    #[arg(long = "force-python")]
    pub force_python: bool,

    /// Suppress Python plugin performance warning
    #[cfg(feature = "python-plugins")]
    #[arg(long = "quiet-python-warning")]
    pub quiet_python_warning: bool,
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

    // Load the file
    if args.verbose && !args.quiet {
        eprintln!("Loading {}...", file.display());
    }

    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    // Build source cache for error reporting
    let mut cache = SourceCache::new();
    for source_file in load_result.source_map.files() {
        let content = std::fs::read_to_string(&source_file.path).unwrap_or_else(|_| String::new());
        cache.add(&source_file.path.display().to_string(), content);
    }

    // Also add the main file
    let main_content = std::fs::read_to_string(file)
        .with_context(|| format!("failed to read {}", file.display()))?;
    cache.add(&file.display().to_string(), main_content);

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
            LoadError::PathTraversal {
                include_path,
                base_dir,
            } => {
                if !args.quiet {
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
                if !args.quiet {
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

    // Collect plugins to run from multiple sources:
    // 1. Plugins declared in the ledger file (load_result.plugins)
    // 2. CLI arguments (--native-plugin, --python-plugin, --python-plugin-path, --plugin)
    // 3. Auto-plugins if --auto is set

    #[derive(Debug, Clone)]
    #[allow(dead_code)] // Variants are conditionally used based on feature flags
    #[allow(clippy::items_after_statements)] // Enum is local to this function
    enum PluginSource {
        Native {
            name: String,
            config: Option<String>,
        },
        PythonModule {
            name: String,
            config: Option<String>,
        },
        PythonFile {
            path: PathBuf,
            config: Option<String>,
        },
        WasmFile {
            path: PathBuf,
        },
    }

    let mut plugins_to_run: Vec<PluginSource> = Vec::new();
    let native_registry = NativePluginRegistry::new();

    // If --auto is set, add auto_accounts first
    if args.auto {
        plugins_to_run.push(PluginSource::Native {
            name: "auto_accounts".to_string(),
            config: None,
        });
    }

    // Get the directory of the main beancount file for resolving relative paths
    let base_dir = file.parent().unwrap_or(std::path::Path::new("."));

    // Check if --force-python is set
    #[cfg(feature = "python-plugins")]
    let force_python = args.force_python;
    #[cfg(not(feature = "python-plugins"))]
    let force_python = false;

    // Process plugins declared in the ledger file
    for plugin in &load_result.plugins {
        let name = &plugin.name;
        let config = plugin.config.clone();

        // Check if this is a native Rust plugin (fastest path)
        // Skip native if --force-python is set
        if !force_python && native_registry.find(name).is_some() {
            plugins_to_run.push(PluginSource::Native {
                name: name.clone(),
                config,
            });
        } else if std::path::Path::new(name)
            .extension()
            .is_some_and(|ext| ext.eq_ignore_ascii_case("py"))
            || name.starts_with('/')
            || name.starts_with("./")
            || name.starts_with("../")
        {
            // File path to Python plugin - resolve relative to beancount file
            let path = if name.starts_with('/') {
                PathBuf::from(name)
            } else {
                base_dir.join(name)
            };
            plugins_to_run.push(PluginSource::PythonFile { path, config });
        } else if std::path::Path::new(name)
            .extension()
            .is_some_and(|ext| ext.eq_ignore_ascii_case("wasm"))
        {
            // WASM plugin - resolve relative to beancount file
            let path = if name.starts_with('/') {
                PathBuf::from(name)
            } else {
                base_dir.join(name)
            };
            plugins_to_run.push(PluginSource::WasmFile { path });
        } else {
            // Python module (e.g., "beancount.plugins.xxx" or "mymodule.plugin")
            #[cfg(feature = "python-plugins")]
            plugins_to_run.push(PluginSource::PythonModule {
                name: name.clone(),
                config,
            });
            #[cfg(not(feature = "python-plugins"))]
            {
                if !args.quiet {
                    writeln!(
                        stdout,
                        "warning: plugin '{}' requires python-plugins feature",
                        name
                    )?;
                }
            }
        }
    }

    // Add CLI-specified plugins (these run after file-declared plugins)
    for name in &args.native_plugins {
        plugins_to_run.push(PluginSource::Native {
            name: name.clone(),
            config: None,
        });
    }

    for path in &args.plugins {
        plugins_to_run.push(PluginSource::WasmFile { path: path.clone() });
    }

    #[cfg(feature = "python-plugins")]
    {
        for name in &args.python_plugins {
            plugins_to_run.push(PluginSource::PythonModule {
                name: name.clone(),
                config: None,
            });
        }
        for path in &args.python_plugin_paths {
            plugins_to_run.push(PluginSource::PythonFile {
                path: path.clone(),
                config: None,
            });
        }
    }

    // Run plugins if any are specified
    if !plugins_to_run.is_empty() {
        if args.verbose && !args.quiet {
            eprintln!("Running {} plugin(s)...", plugins_to_run.len());
        }

        let wrappers = rustledger_plugin::directives_to_wrappers(&directives);
        let mut current_input = PluginInput {
            directives: wrappers,
            options: PluginOptions {
                operating_currencies: load_result.options.operating_currency.clone(),
                title: load_result.options.title.clone(),
            },
            config: None,
        };

        // Lazy-initialize Python runtime only if needed
        #[cfg(feature = "python-plugins")]
        let mut python_runtime: Option<rustledger_plugin::python::PythonRuntime> = None;

        // Lazy-initialize WASM manager only if needed
        let mut wasm_manager: Option<PluginManager> = None;

        // Run plugins in declaration order
        for plugin_source in &plugins_to_run {
            match plugin_source {
                PluginSource::Native { name, config } => {
                    if let Some(plugin) = native_registry.find(name) {
                        if args.verbose && !args.quiet {
                            eprintln!("  Running native plugin: {}", plugin.name());
                        }

                        let input_with_config = PluginInput {
                            directives: current_input.directives.clone(),
                            options: current_input.options.clone(),
                            config: config.clone(),
                        };

                        let output = plugin.process(input_with_config);

                        for err in &output.errors {
                            if !args.quiet {
                                writeln!(stdout, "{:?}: {}", err.severity, err.message)?;
                            }
                            error_count += 1;
                        }

                        current_input.directives = output.directives;
                    } else if !args.quiet {
                        writeln!(stdout, "warning: unknown native plugin: {name}")?;
                    }
                }

                PluginSource::WasmFile { path } => {
                    if args.verbose && !args.quiet {
                        eprintln!("  Loading WASM plugin: {}", path.display());
                    }

                    let manager = wasm_manager.get_or_insert_with(PluginManager::new);

                    if let Err(e) = manager.load(path) {
                        if !args.quiet {
                            writeln!(
                                stdout,
                                "error: failed to load WASM plugin {}: {}",
                                path.display(),
                                e
                            )?;
                        }
                        error_count += 1;
                        continue;
                    }

                    // Execute immediately to maintain order
                    match manager.execute_all(current_input.clone()) {
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
                                writeln!(stdout, "error: WASM plugin execution failed: {e}")?;
                            }
                            error_count += 1;
                        }
                    }
                    // Clear manager for next WASM plugin
                    wasm_manager = None;
                }

                #[cfg(feature = "python-plugins")]
                PluginSource::PythonModule { name, config } => {
                    // Initialize Python runtime on first use
                    if python_runtime.is_none() {
                        match rustledger_plugin::python::PythonRuntime::with_options(
                            args.quiet_python_warning,
                        ) {
                            Ok(runtime) => python_runtime = Some(runtime),
                            Err(e) => {
                                if !args.quiet {
                                    writeln!(
                                        stdout,
                                        "error: failed to initialize Python runtime: {e}"
                                    )?;
                                }
                                error_count += 1;
                                continue;
                            }
                        }
                    }

                    if let Some(ref runtime) = python_runtime {
                        if args.verbose && !args.quiet {
                            eprintln!("  Running Python plugin: {name}");
                        }

                        let input_with_config = PluginInput {
                            directives: current_input.directives.clone(),
                            options: current_input.options.clone(),
                            config: config.clone(),
                        };

                        match runtime.execute_builtin(name, &input_with_config) {
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
                                    writeln!(stdout, "error: Python plugin '{name}' failed: {e}")?;
                                }
                                error_count += 1;
                            }
                        }
                    }
                }

                #[cfg(feature = "python-plugins")]
                PluginSource::PythonFile { path, config } => {
                    // Initialize Python runtime on first use
                    if python_runtime.is_none() {
                        match rustledger_plugin::python::PythonRuntime::with_options(
                            args.quiet_python_warning,
                        ) {
                            Ok(runtime) => python_runtime = Some(runtime),
                            Err(e) => {
                                if !args.quiet {
                                    writeln!(
                                        stdout,
                                        "error: failed to initialize Python runtime: {e}"
                                    )?;
                                }
                                error_count += 1;
                                continue;
                            }
                        }
                    }

                    if let Some(ref runtime) = python_runtime {
                        if args.verbose && !args.quiet {
                            eprintln!("  Loading Python plugin: {}", path.display());
                        }

                        let plugin_code = match std::fs::read_to_string(path) {
                            Ok(code) => code,
                            Err(e) => {
                                if !args.quiet {
                                    writeln!(
                                        stdout,
                                        "error: failed to read Python plugin {}: {}",
                                        path.display(),
                                        e
                                    )?;
                                }
                                error_count += 1;
                                continue;
                            }
                        };

                        let input_with_config = PluginInput {
                            directives: current_input.directives.clone(),
                            options: current_input.options.clone(),
                            config: config.clone(),
                        };

                        match runtime.execute_plugin(&plugin_code, "plugin", &input_with_config) {
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
                                        "error: Python plugin '{}' failed: {}",
                                        path.display(),
                                        e
                                    )?;
                                }
                                error_count += 1;
                            }
                        }
                    }
                }

                #[cfg(not(feature = "python-plugins"))]
                PluginSource::PythonModule { name, .. } => {
                    if !args.quiet {
                        writeln!(
                            stdout,
                            "warning: plugin '{}' requires python-plugins feature",
                            name
                        )?;
                    }
                }

                #[cfg(not(feature = "python-plugins"))]
                PluginSource::PythonFile { path, .. } => {
                    if !args.quiet {
                        writeln!(
                            stdout,
                            "warning: plugin '{}' requires python-plugins feature",
                            path.display()
                        )?;
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
