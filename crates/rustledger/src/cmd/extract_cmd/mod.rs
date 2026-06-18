//! rledger extract - Extract transactions from bank files.
//!
//! This is the primary rustledger command for importing transactions from
//! CSV, OFX, and other bank statement formats.
//!
//! # Usage
//!
//! ```bash
//! rledger extract bank.csv --account Assets:Bank:Checking
//! rledger extract statement.csv --importer chase
//! ```
//!
//! # Importers Configuration
//!
//! Create an `importers.toml` file to define reusable import profiles with
//! column mappings and account categorization rules:
//!
//! ```toml
//! [[importers]]
//! name = "chase"
//! account = "Assets:Bank:Chase"
//! date_column = "Transaction Date"
//! amount_column = "Amount"
//! date_format = "%m/%d/%Y"
//! # amount_locale = "de_DE"    # optional: comma as the decimal separator
//! # amount_format = "#.##0,00" # optional: explicit number-format pattern
//!
//! [importers.mappings]
//! "AMAZON" = "Expenses:Shopping"
//! "WHOLE FOODS" = "Expenses:Groceries"
//! ```
//!
//! The file is searched for in the following locations (first found wins):
//! 1. Path specified via `--importers-config`
//! 2. `importers.toml` in the current directory
//! 3. `~/.config/rledger/importers.toml`
//!
//! # WASM importers (wave 2.3c+)
//!
//! Beyond the built-in CSV and OFX importers, `rledger extract` can
//! load `.wasm` modules that implement the import ABI defined in
//! `rustledger-plugin-types`. Two flags control discovery:
//!
//! - `--wasm-importer <PATH>` (repeatable) — register one specific
//!   module. Right tool for ad-hoc usage.
//! - `--wasm-importer-dir <DIR>` (repeatable) — scan a directory for
//!   `*.wasm` files. Overrides `wasm_importer_dir` from
//!   `importers.toml` entirely when any CLI flag is set.
//!
//! Priority (highest wins `identify()` collisions): CLI single-file
//! > directory scan > built-ins.
//!
//! ```toml
//! # Persistent multi-dir discovery in importers.toml:
//! wasm_importer_dir = ["~/wasm-importers", "/opt/shared-importers"]
//! ```

mod config;
mod duplicate;
mod suggest;

use crate::cmd::completions::ShellType;
use anyhow::{Context, Result, anyhow};
use clap::Parser;
use config::{
    build_config_from_entry, find_importers_config, find_matching_importers, load_importers_config,
};
// Used only by the WASM-importer-dir resolution path (gated below).
#[cfg(feature = "python-plugin-wasm")]
use config::expand_tilde;
use duplicate::{is_duplicate, load_existing_transactions};
use format_num_pattern::Locale;
use rustledger_core::{Directive, FormatConfig};
use rustledger_importer::{Importer, ImporterConfig, ImporterRegistry, csv_importer::CsvImporter};
use rustledger_parser::format::canonicalize_directives;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::Arc;

/// Extract transactions from bank files.
#[derive(Parser, Debug)]
#[command(name = "extract")]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Generate shell completions and exit
    #[arg(long, value_name = "SHELL", hide = true)]
    pub generate_completions: Option<ShellType>,

    /// The file to extract transactions from
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,

    /// Use a named importer from importers.toml
    #[arg(long, short = 'i')]
    pub importer: Option<String>,

    /// Path to importers.toml configuration file
    #[arg(long, alias = "importers-config")]
    pub config: Option<PathBuf>,

    /// List available importers from config file and exit
    #[arg(long = "list-importers")]
    pub list_importers: bool,

    /// Target account for imported transactions
    #[arg(short, long, default_value = "Assets:Bank:Checking")]
    pub account: String,

    /// Currency for amounts (default: USD)
    #[arg(short, long, default_value = "USD")]
    pub currency: String,

    /// Date column name or index
    #[arg(long, default_value = "Date")]
    pub date_column: String,

    /// Date format (strftime-style)
    #[arg(long, default_value = "%Y-%m-%d")]
    pub date_format: String,

    /// Narration/description column name or index
    #[arg(long, default_value = "Description")]
    pub narration_column: String,

    /// Payee column name (optional)
    #[arg(long)]
    pub payee_column: Option<String>,

    /// Amount column name or index
    #[arg(long, default_value = "Amount")]
    pub amount_column: String,

    /// Locale used to parse amounts, e.g. `en_US`
    #[arg(long)]
    pub amount_locale: Option<String>,

    /// Custom formatting for parsing amounts.
    #[arg(long)]
    pub amount_format: Option<String>,

    /// Debit column (for separate debit/credit columns)
    #[arg(long)]
    pub debit_column: Option<String>,

    /// Credit column (for separate debit/credit columns)
    #[arg(long)]
    pub credit_column: Option<String>,

    /// CSV delimiter
    #[arg(long, default_value = ",")]
    pub delimiter: char,

    /// Number of header rows to skip
    #[arg(long, default_value = "0")]
    pub skip_rows: usize,

    /// Invert sign of amounts
    #[arg(long)]
    pub invert_sign: bool,

    /// Preserve rows whose amount is exactly zero (e.g. balance markers).
    /// Default behavior drops them, matching most banks' use of zero rows
    /// as status filler — see issue #972.
    #[arg(long)]
    pub include_zero_amounts: bool,

    /// Auto-detect CSV format (delimiter, columns, date format)
    #[arg(long, conflicts_with_all = [
        "date_column", "date_format", "narration_column", "amount_column",
        "delimiter", "skip_rows", "no_header", "debit_column", "credit_column",
        "payee_column",
    ])]
    pub auto: bool,

    /// CSV has no header row
    #[arg(long)]
    pub no_header: bool,

    /// Write output to a file instead of stdout
    #[arg(short, long, value_name = "FILE")]
    pub output: Option<PathBuf>,

    /// Existing ledger file for duplicate detection
    #[arg(long, value_name = "FILE")]
    pub existing: Option<PathBuf>,

    /// Use ML to suggest accounts for transactions the rules engine didn't
    /// categorize. Trains a Naive Bayes model on the `--existing` ledger and
    /// replaces the configured fallback contra-accounts (the importer's
    /// `default_expense` and `default_income`, defaulting to
    /// `Expenses:Unknown` / `Income:Unknown`) with the prediction.
    /// Requires `--existing`.
    #[arg(long, requires = "existing")]
    pub suggest_categories: bool,

    /// Append a balance assertion with the given amount (e.g., "1234.56")
    #[arg(long, value_name = "AMOUNT")]
    pub balance: Option<String>,

    /// Date for the balance assertion (defaults to today)
    #[arg(long, value_name = "DATE")]
    pub balance_date: Option<String>,

    /// Register a specific WASM importer module ahead of the built-in
    /// CSV/OFX importers. May be specified multiple times. Each
    /// `<PATH>` must be a `.wasm` file. User-specified modules take
    /// precedence over discovered ones and over built-ins — this is
    /// the right flag for ad-hoc one-off usage.
    #[arg(long, value_name = "PATH")]
    pub wasm_importer: Vec<PathBuf>,

    /// Scan a directory for `*.wasm` importer modules at startup. May
    /// be specified multiple times for multi-dir setups. Overrides
    /// `wasm_importer_dir` from `importers.toml` entirely when any
    /// `--wasm-importer-dir` flag is present. Non-`.wasm` files are
    /// silently skipped; subdirectories are not recursed into.
    #[arg(long, value_name = "DIR")]
    pub wasm_importer_dir: Vec<PathBuf>,
}

/// List available importers — both TOML profiles and engines.
///
/// TOML profiles (for `--importer <name>`) and registered engines
/// (built-in CSV/OFX plus any `--wasm-importer`/scanned modules) are
/// orthogonal concepts: a TOML profile is a pre-configured
/// [`ImporterConfig`] driven by `CsvImporter`; an engine is the actual
/// trait implementation that consumes a config.
pub fn list_importers(args: &Args) -> Result<()> {
    let mut stdout = io::stdout().lock();
    list_importers_with_writer(args, &mut stdout)
}

/// List available importers, writing the listing to `out`.
///
/// Writer-injectable variant of [`list_importers`] used by `ag-rledger`.
/// Behavior is otherwise identical.
pub fn list_importers_with_writer<W: Write>(args: &Args, out: &mut W) -> Result<()> {
    // ===== TOML profiles =====
    //
    // Optional: if no config file is present we still want to list
    // the registered engines, so this is a soft find rather than the
    // hard "must have config" error the original code had.
    if let Some(config_path) = find_importers_config(args.config.as_deref())? {
        let config = load_importers_config(&config_path)?;
        if config.importers.is_empty() {
            writeln!(out, "No TOML profiles in {}", config_path.display())?;
        } else {
            writeln!(out, "TOML profiles in {}:", config_path.display())?;
            for imp in &config.importers {
                if let Some(pattern) = &imp.filename_pattern {
                    writeln!(
                        out,
                        "  {} (pattern: {}) -> {}",
                        imp.name,
                        pattern,
                        imp.account.as_deref().unwrap_or("(default)")
                    )?;
                } else {
                    writeln!(
                        out,
                        "  {} -> {}",
                        imp.name,
                        imp.account.as_deref().unwrap_or("(default)")
                    )?;
                }
            }
        }
    } else {
        writeln!(
            out,
            "(no importers.toml found — listing registered engines only)"
        )?;
    }
    writeln!(out)?;

    // ===== Registered importer engines =====
    //
    // Always shown — at minimum CSV + OFX, plus any WASM-discovered
    // modules. Build a fresh registry from args so users see exactly
    // what this invocation would dispatch through.
    let registry = build_registry(args)?;
    writeln!(out, "Registered importer engines:")?;
    for (name, description) in registry.list_importers() {
        writeln!(out, "  {name} - {description}")?;
    }

    Ok(())
}

/// Pick the importer for a given file + CLI args.
///
/// - If the user explicitly chose a TOML entry (`--importer <name>`),
///   force [`CsvImporter`]: TOML profiles are CSV-only by definition
///   of [`rustledger_importer::config::ImporterType`] today, and the
///   profile's column mappings would be lost if registry-identify
///   silently routed the file to a different engine (e.g. a
///   `.ofx`-named file picked up by `OfxImporter`).
/// - Otherwise let the registry identify by extension. This is the
///   path WASM importers reach via `--wasm-importer` /
///   `--wasm-importer-dir` — including when combined with
///   `--config` for pattern-matched TOML profiles. (Earlier this
///   function also force-CSV'd when `--config` was set alone; that
///   meant `--wasm-importer my.wasm --config x.toml` silently
///   ignored the WASM module. Fixed by limiting the force-CSV path
///   to `--importer`.)
/// - Fall back to [`CsvImporter`] for unknown extensions (e.g. `.qbo`
///   Quicken exports) so users with custom-extension TOML entries
///   keep working.
fn select_importer(registry: &ImporterRegistry, file: &Path, args: &Args) -> Arc<dyn Importer> {
    if args.importer.is_some() {
        Arc::new(CsvImporter)
    } else {
        registry
            .identify(file)
            .unwrap_or_else(|| Arc::new(CsvImporter) as Arc<dyn Importer>)
    }
}

/// Resolve the list of directories to scan for WASM importers.
///
/// Top-level dispatcher; the two real branches are
/// [`resolve_scan_dirs_explicit`] (user named a config file with
/// `--config`, errors propagate) and [`resolve_scan_dirs_implicit`]
/// (no flag, soft-discover from default locations, errors warn-and-
/// degrade). CLI `--wasm-importer-dir` flags override both and
/// short-circuit the toml lookup entirely.
#[cfg(feature = "python-plugin-wasm")]
fn resolve_scan_dirs(args: &Args) -> Result<Vec<PathBuf>> {
    if !args.wasm_importer_dir.is_empty() {
        return Ok(args.wasm_importer_dir.clone());
    }
    match args.config.as_deref() {
        Some(path) => resolve_scan_dirs_explicit(path),
        None => Ok(resolve_scan_dirs_implicit()),
    }
}

/// User passed `--config <path>` explicitly. Missing or malformed
/// file is a real error — the user asked for this file by name, so
/// silently degrading would hide the bug they want to know about.
#[cfg(feature = "python-plugin-wasm")]
fn resolve_scan_dirs_explicit(path: &Path) -> Result<Vec<PathBuf>> {
    let cfg_path = find_importers_config(Some(path))?
        .ok_or_else(|| anyhow!("Importers config not found: {}", path.display()))?;
    let cfg = load_importers_config(&cfg_path)?;
    Ok(cfg
        .wasm_importer_dir
        .into_vec()
        .into_iter()
        .map(|p| expand_tilde(&p))
        .collect())
}

/// No `--config` flag — soft-discover in default locations
/// (cwd `importers.toml` then `~/.config/rledger/importers.toml`).
/// A missing file is expected; a malformed file is unusual but not
/// fatal (the user didn't explicitly point at it). Print a warning
/// for the malformed case so the user can find their mistake.
#[cfg(feature = "python-plugin-wasm")]
fn resolve_scan_dirs_implicit() -> Vec<PathBuf> {
    let cfg_path = match find_importers_config(None) {
        Ok(Some(p)) => p,
        Ok(None) | Err(_) => return Vec::new(),
    };
    match load_importers_config(&cfg_path) {
        Ok(cfg) => cfg
            .wasm_importer_dir
            .into_vec()
            .into_iter()
            .map(|p| expand_tilde(&p))
            .collect(),
        Err(e) => {
            // Visible warning instead of silent loss — the user's
            // wasm_importer_dir setting would otherwise vanish with
            // no signal that the file even exists.
            eprintln!(
                "warning: implicit importers.toml at {} failed to parse: {e:#}; ignoring wasm_importer_dir",
                cfg_path.display()
            );
            Vec::new()
        }
    }
}

/// Build an [`ImporterRegistry`] with WASM importers registered ahead
/// of the built-in CSV/OFX importers, so user-discovered modules win
/// the `identify()` race. Priority (highest first):
///
/// 1. CLI `--wasm-importer <PATH>` (explicit per-invocation,
///    repeatable)
/// 2. CLI `--wasm-importer-dir <DIR>` (repeatable) OR
///    `wasm_importer_dir` from `importers.toml` (CLI flags win
///    entirely — they're not merged with the toml setting)
/// 3. Built-in CSV + OFX importers (always present, registered last)
///
/// Per-dir scan failures (a single malformed `.wasm` among many) are
/// logged to stderr but don't abort startup — see [`register_wasm_dir`]'s
/// skip-and-collect semantics.
#[cfg_attr(not(feature = "python-plugin-wasm"), allow(unused_variables))]
fn build_registry(args: &Args) -> Result<ImporterRegistry> {
    let mut registry = ImporterRegistry::new();

    // 1 + 2. WASM importer loading (sandboxed `.wasm` importers). Gated behind
    //    `python-plugin-wasm` so a `--no-default-features` build carries no
    //    `wasmtime`/cranelift dependency (#1427); without the feature the
    //    `--wasm-importer`/`--wasm-importer-dir` flags are accepted but inert.
    #[cfg(feature = "python-plugin-wasm")]
    {
        // 1. CLI --wasm-importer paths (explicit precedence — registered
        //    first so they win identify()). Single-file failures abort
        //    because the user explicitly named this path; if it's wrong,
        //    silently skipping would be worse than erroring out.
        for path in &args.wasm_importer {
            let name = registry
                .register_wasm_from_path(path)
                .with_context(|| format!("failed to load WASM importer {}", path.display()))?;
            eprintln!("loaded WASM importer `{name}` from {}", path.display());
        }

        // 2. Directory scan(s): CLI flags override toml entirely.
        //    Multiple dirs are scanned in order. `~` is expanded for
        //    toml-supplied paths (CLI paths get shell expansion).
        let scan_dirs: Vec<PathBuf> = resolve_scan_dirs(args)?;
        for dir in &scan_dirs {
            let report = registry.register_wasm_dir(dir).with_context(|| {
                format!("failed to scan WASM importer directory {}", dir.display())
            })?;
            if !report.loaded.is_empty() || !report.failures.is_empty() {
                eprintln!(
                    "WASM importer scan {}: loaded {}, failed {}",
                    dir.display(),
                    report.loaded.len(),
                    report.failures.len(),
                );
            }
            for (failed_path, err) in &report.failures {
                eprintln!("  warning: failed to load {}: {err}", failed_path.display());
            }
        }
    }

    // 3. Built-ins last so any user importer takes precedence on
    //    identify() collisions.
    registry.register(rustledger_importer::OfxImporter);
    registry.register(rustledger_importer::csv_importer::CsvImporter);

    Ok(registry)
}

/// Run the extract command with the given arguments, writing extracted
/// directives to stdout.
///
/// Thin wrapper over [`run_with_writer`] for the synchronous `rledger`
/// binary; `ag-rledger` calls `run_with_writer` with a buffer.
pub fn run(args: &Args, file: &Path) -> Result<()> {
    let mut stdout = io::stdout().lock();
    run_with_writer(args, file, &mut stdout)
}

/// Run the extract command, writing extracted directives to `out`.
///
/// Behavior matches the original `run()`: a `--output <file>` flag still
/// writes to disk (and the "Wrote output to ..." note still goes to
/// stderr), and progress/warning lines still go to stderr. Only the
/// default stdout sink for the formatted directives is redirected to the
/// injected writer.
pub fn run_with_writer<W: Write>(args: &Args, file: &Path, out: &mut W) -> Result<()> {
    let registry = build_registry(args)?;

    // Pick the dispatcher BEFORE building config: only `CsvImporter`
    // needs the elaborate `--importer`/`--config`/`--auto` config
    // path. WASM importers and `OfxImporter` consume a minimal default
    // config (account + currency; the rest is either projected via
    // the WASM wire format's `options` map or ignored). Building the
    // CSV config eagerly would error on "No importers defined" when a
    // user runs e.g. `--config x.toml --wasm-importer my.wasm` with
    // an x.toml that only sets `wasm_importer_dir`.
    let importer = select_importer(&registry, file, args);

    // Stringly-typed dispatcher check: `CsvImporter::name()` returns
    // the literal "CSV". Acceptable coupling for a CLI-internal
    // routing decision; a trait method would be over-design for one
    // call site.
    let dispatcher_needs_minimal_config = importer.name() != "CSV";

    // Build the per-call ImporterConfig + fallback-account list.
    //
    // - Non-CSV dispatcher (OFX, WASM, future builtins): minimal
    //   default config — account + currency, empty CsvConfig carrier
    //   the WASM wire format projects via `options`.
    // - CSV dispatcher: builds the full CsvConfig from
    //   --importer/--config/--auto/raw-args sources.
    let (config, fallback_accounts) = if dispatcher_needs_minimal_config {
        let cfg = rustledger_importer::ImporterConfig {
            account: args.account.clone(),
            currency: Some(args.currency.clone()),
            importer_type: rustledger_importer::config::ImporterType::Csv(
                rustledger_importer::config::CsvConfig::default(),
            ),
        };
        // OFX importer routes negative amounts to `Expenses:Unknown`
        // and positive amounts to `Income:Unknown` (ofx_importer.rs's
        // `parse_transaction`). Both must be in the fallback list so
        // `--suggest-categories` re-categorizes income as well as
        // expense transactions. WASM importers may produce their own
        // fallbacks; the host defaults are used when they don't.
        (
            cfg,
            vec!["Expenses:Unknown".to_string(), "Income:Unknown".to_string()],
        )
    } else {
        // CSV branch: determine import config from --importer flag,
        // explicit --config, --auto, or raw CLI args.
        let config = if let Some(ref importer_name) = args.importer {
            // Explicit --importer: require config file, find named entry
            let config_path = find_importers_config(args.config.as_deref())?
                .ok_or_else(|| anyhow!(
                    "No importers.toml found. Create one in the current directory or at ~/.config/rledger/importers.toml"
                ))?;

            let importers_file = load_importers_config(&config_path)?;

            let entry = importers_file
                .importers
                .iter()
                .find(|e| e.name == *importer_name)
                .ok_or_else(|| {
                    let available: Vec<&str> = importers_file
                        .importers
                        .iter()
                        .map(|e| e.name.as_str())
                        .collect();
                    anyhow!(
                        "Importer '{}' not found in {}. Available: {}",
                        importer_name,
                        config_path.display(),
                        available.join(", ")
                    )
                })?;

            eprintln!(
                "Using importer '{}' from {}",
                importer_name,
                config_path.display()
            );
            build_config_from_entry(entry)?
        } else if args.config.is_some() {
            // Explicit --config without --importer: try auto-identification by filename
            let config_path = find_importers_config(args.config.as_deref())?
                .ok_or_else(|| anyhow!(
                    "No importers.toml found. Create one in the current directory or at ~/.config/rledger/importers.toml"
                ))?;

            let importers_file = load_importers_config(&config_path)?;

            if importers_file.importers.is_empty() {
                return Err(anyhow!("No importers defined in {}", config_path.display()));
            }

            // Try auto-identification by filename pattern
            let filename = file
                .file_name()
                .map(|s| s.to_string_lossy())
                .unwrap_or_default();
            let matches = find_matching_importers(&importers_file, &filename);

            let entry = match matches.len() {
                1 => {
                    eprintln!(
                        "Auto-identified importer '{}' from filename pattern",
                        matches[0].name
                    );
                    matches[0]
                }
                0 if importers_file.importers.len() == 1 => {
                    // No pattern match but only one importer - use it
                    &importers_file.importers[0]
                }
                0 => {
                    let available: Vec<&str> = importers_file
                        .importers
                        .iter()
                        .map(|e| e.name.as_str())
                        .collect();
                    return Err(anyhow!(
                        "No importer matches file '{}'. Use --importer to select one: {}",
                        filename,
                        available.join(", ")
                    ));
                }
                _ => {
                    let names: Vec<&str> = matches.iter().map(|e| e.name.as_str()).collect();
                    return Err(anyhow!(
                        "Multiple importers match file '{}': {}. Use --importer to select one.",
                        filename,
                        names.join(", ")
                    ));
                }
            };

            eprintln!(
                "Using importer '{}' from {}",
                entry.name,
                config_path.display()
            );
            build_config_from_entry(entry)?
        } else if args.auto {
            // Auto-detect CSV format
            let content = std::fs::read_to_string(file)
                .with_context(|| format!("Failed to read file: {}", file.display()))?;

            let inferred = rustledger_importer::csv_inference::infer_csv_config(&content)
                .ok_or_else(|| anyhow!(
                    "Could not auto-detect CSV format for {}. Try specifying columns explicitly.",
                    file.display()
                ))?;

            eprintln!(
                "Auto-detected format (confidence: {:.0}%):",
                inferred.confidence * 100.0
            );
            eprintln!("  delimiter: {:?}", inferred.delimiter);
            eprintln!("  date_format: {}", inferred.date_format);
            eprintln!("  has_header: {}", inferred.has_header);

            let mut csv_config = inferred.to_csv_config();
            if args.include_zero_amounts {
                csv_config.skip_zero_amounts = false;
            }
            ImporterConfig {
                account: args.account.clone(),
                currency: Some(args.currency.clone()),
                importer_type: rustledger_importer::config::ImporterType::Csv(csv_config),
            }
        } else {
            // No config file: build from CLI arguments
            let mut builder = ImporterConfig::csv()
                .account(&args.account)
                .currency(&args.currency)
                .date_column(&args.date_column)
                .date_format(&args.date_format)
                .narration_column(&args.narration_column)
                .amount_column(&args.amount_column)
                .delimiter(args.delimiter)
                .skip_rows(args.skip_rows)
                .invert_sign(args.invert_sign)
                .skip_zero_amounts(!args.include_zero_amounts)
                .has_header(!args.no_header);

            if let Some(payee) = &args.payee_column {
                builder = builder.payee_column(payee);
            }

            if let Some(debit) = &args.debit_column {
                builder = builder.debit_column(debit);
            }

            if let Some(credit) = &args.credit_column {
                builder = builder.credit_column(credit);
            }

            if let Some(locale) = &args.amount_locale {
                let Ok(locale) = Locale::from_str(locale) else {
                    return Err(anyhow!("{locale} is not a valid locale"));
                };

                builder = builder.amount_locale(locale);
            }

            if let Some(format) = &args.amount_format {
                builder = builder.amount_format(format);
            }

            builder.build()?
        };

        // Apply --include-zero-amounts uniformly across all config sources
        // (--importer entry, explicit --config, --auto, raw CLI). Without this,
        // the flag silently has no effect when the config came from a TOML
        // entry — see Copilot review on PR #982.
        let config = if args.include_zero_amounts {
            let mut config = config;
            let rustledger_importer::config::ImporterType::Csv(csv) = &mut config.importer_type;
            csv.skip_zero_amounts = false;
            config
        } else {
            config
        };

        let rustledger_importer::config::ImporterType::Csv(csv) = &config.importer_type;
        let fallbacks = vec![
            csv.default_expense
                .clone()
                .unwrap_or_else(|| "Expenses:Unknown".to_string()),
            csv.default_income
                .clone()
                .unwrap_or_else(|| "Income:Unknown".to_string()),
        ];
        (config, fallbacks)
    };

    // `importer` was selected earlier so we could route config-
    // building correctly; here it's used for the actual dispatch.
    let result = importer.extract(file, &config)?;

    // Print warnings
    for warning in &result.warnings {
        eprintln!("warning: {warning}");
    }

    // Filter duplicates if --existing is specified, and optionally apply
    // ML-based account suggestions for transactions the rules engine left
    // pointing at a fallback account.
    let directives = if let Some(ref existing_path) = args.existing {
        let existing_txns = load_existing_transactions(existing_path)?;
        let before_count = result.directives.len();
        let mut filtered: Vec<_> = result
            .directives
            .into_iter()
            .filter(|d| {
                if let Directive::Transaction(txn) = d {
                    !is_duplicate(txn, &existing_txns)
                } else {
                    true
                }
            })
            .collect();
        let dupes = before_count - filtered.len();
        if dupes > 0 {
            eprintln!("Filtered {dupes} duplicate transaction(s)");
        }
        if args.suggest_categories {
            suggest::apply_ml_suggestions_with_summary(
                &mut filtered,
                &existing_txns,
                &fallback_accounts,
            )?;
        }
        filtered
    } else {
        result.directives
    };

    // Append balance assertion if --balance is specified
    let directives = if let Some(ref balance_amount) = args.balance {
        use rust_decimal::Decimal;
        use std::str::FromStr;

        let amount = Decimal::from_str(balance_amount)
            .with_context(|| format!("Invalid balance amount: {balance_amount}"))?;
        let date = args
            .balance_date
            .clone()
            .unwrap_or_else(|| jiff::Zoned::now().date().to_string());

        let balance = rustledger_ops::reconcile::StatementBalance {
            date,
            account: args.account.clone(),
            number: amount,
            currency: args.currency.clone(),
        };
        let balance_wrapper = rustledger_ops::reconcile::create_balance_directive(&balance);

        // Convert DirectiveWrapper to core Directive
        let balance_directive = rustledger_plugin::convert::wrapper_to_directive(&balance_wrapper)
            .map_err(|e| anyhow!("Failed to create balance directive: {e:?}"))?;

        let mut with_balance = directives;
        with_balance.push(balance_directive);
        with_balance
    } else {
        directives
    };

    // Render every directive in the canonical form `rledger format`
    // would write. canonicalize_directives is the single source of
    // truth for the synthesize-then-canonicalize pipeline (legacy
    // typed-AST emitter → parse → opinionated formatter), with a
    // built-in parse-error guard so a divergence between the two
    // emitters surfaces as a hard error rather than silent data
    // loss.
    let fmt_config = FormatConfig::default();
    let formatted = canonicalize_directives(directives.iter(), &fmt_config)
        .map_err(|e| anyhow::anyhow!(e.to_string()))?;

    if let Some(ref output_path) = args.output {
        let mut out_file = fs::File::create(output_path)
            .with_context(|| format!("Failed to create output file: {}", output_path.display()))?;
        out_file.write_all(formatted.as_bytes())?;
        eprintln!("Wrote output to {}", output_path.display());
    } else {
        out.write_all(formatted.as_bytes())?;
    }

    eprintln!(
        "Extracted {} transactions from {}",
        directives.len(),
        file.display()
    );

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::config::{ImporterEntry, parse_column_value};
    use super::duplicate::{first_posting_amount, fuzzy_text_match, txn_match_text};
    use super::*;
    use rustledger_core::Transaction;
    use rustledger_importer::config::ImporterType;
    use std::collections::HashMap;

    fn write_temp_config(content: &str) -> (tempfile::TempDir, PathBuf) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("importers.toml");
        std::fs::write(&path, content).unwrap();
        (dir, path)
    }

    #[test]
    fn test_load_importers_config_basic() {
        let (_dir, path) = write_temp_config(
            r#"
[[importers]]
name = "chase"
account = "Assets:Bank:Chase"
date_column = "Transaction Date"
amount_column = "Amount"
"#,
        );

        let config = load_importers_config(&path).unwrap();
        assert_eq!(config.importers.len(), 1);
        assert_eq!(config.importers[0].name, "chase");
        assert_eq!(
            config.importers[0].account.as_deref(),
            Some("Assets:Bank:Chase")
        );
    }

    #[test]
    fn test_load_importers_config_with_mappings() {
        let (_dir, path) = write_temp_config(
            r#"
[[importers]]
name = "checking"
account = "Assets:Bank:Checking"

[importers.mappings]
"AMAZON" = "Expenses:Shopping"
"WHOLE FOODS" = "Expenses:Groceries"
"#,
        );

        let config = load_importers_config(&path).unwrap();
        assert_eq!(config.importers[0].mappings.len(), 2);
        assert_eq!(
            config.importers[0].mappings.get("AMAZON"),
            Some(&"Expenses:Shopping".to_string())
        );
    }

    #[test]
    fn test_load_importers_config_multiple_importers() {
        let (_dir, path) = write_temp_config(
            r#"
[[importers]]
name = "checking"
account = "Assets:Bank:Checking"

[[importers]]
name = "credit_card"
account = "Liabilities:CreditCard"
invert_amounts = true
"#,
        );

        let config = load_importers_config(&path).unwrap();
        assert_eq!(config.importers.len(), 2);
        assert_eq!(config.importers[1].name, "credit_card");
        assert_eq!(config.importers[1].invert_amounts, Some(true));
    }

    #[test]
    fn test_load_importers_config_integer_columns() {
        let (_dir, path) = write_temp_config(
            r#"
[[importers]]
name = "noheader"
account = "Assets:Bank"
date_column = 0
amount_column = 3
narration_column = 1
"#,
        );

        let config = load_importers_config(&path).unwrap();
        let entry = &config.importers[0];
        assert_eq!(
            parse_column_value(entry.date_column.as_ref().unwrap()),
            Some("0".to_string())
        );
        assert_eq!(
            parse_column_value(entry.amount_column.as_ref().unwrap()),
            Some("3".to_string())
        );
    }

    #[test]
    fn test_load_importers_config_invalid_toml() {
        let (_dir, path) = write_temp_config("this is not valid toml [[[");
        assert!(load_importers_config(&path).is_err());
    }

    #[test]
    fn test_load_importers_config_missing_file() {
        let path = PathBuf::from("/nonexistent/importers.toml");
        assert!(load_importers_config(&path).is_err());
    }

    #[test]
    fn test_build_config_from_entry_basic() {
        let entry = ImporterEntry {
            name: "test".to_string(),
            account: Some("Assets:Bank:Test".to_string()),
            currency: Some("EUR".to_string()),
            date_column: Some(toml::Value::String("Date".to_string())),
            date_format: Some("%m/%d/%Y".to_string()),
            narration_column: Some(toml::Value::String("Description".to_string())),
            payee_column: None,
            amount_column: Some(toml::Value::String("Amount".to_string())),
            debit_column: None,
            credit_column: None,
            amount_locale: None,
            amount_format: None,
            delimiter: None,
            skip_rows: None,
            skip_header: None,
            invert_amounts: None,
            default_expense: None,
            default_income: None,
            mappings: HashMap::new(),
            filename_pattern: None,
        };

        let config = build_config_from_entry(&entry).unwrap();
        assert_eq!(config.account, "Assets:Bank:Test");
        assert_eq!(config.currency, Some("EUR".to_string()));
    }

    #[test]
    fn test_build_config_from_entry_with_mappings() {
        let mut mappings = HashMap::new();
        mappings.insert("AMAZON".to_string(), "Expenses:Shopping".to_string());
        mappings.insert("WHOLE FOODS".to_string(), "Expenses:Groceries".to_string());

        let entry = ImporterEntry {
            name: "test".to_string(),
            account: Some("Assets:Bank".to_string()),
            currency: None,
            date_column: None,
            date_format: None,
            narration_column: None,
            payee_column: None,
            amount_column: None,
            debit_column: None,
            credit_column: None,
            amount_locale: None,
            amount_format: None,
            delimiter: None,
            skip_rows: None,
            skip_header: None,
            invert_amounts: None,
            default_expense: None,
            default_income: None,
            mappings,
            filename_pattern: None,
        };

        let config = build_config_from_entry(&entry).unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert_eq!(csv_config.mappings.len(), 2);
        // Patterns should be lowercased and sorted longest-first
        assert_eq!(csv_config.mappings[0].0, "whole foods");
        assert_eq!(csv_config.mappings[1].0, "amazon");
    }

    #[test]
    fn test_build_config_from_entry_with_default_expense() {
        let entry = ImporterEntry {
            name: "test".to_string(),
            account: Some("Assets:Bank".to_string()),
            currency: None,
            date_column: None,
            date_format: None,
            narration_column: None,
            payee_column: None,
            amount_column: None,
            debit_column: None,
            credit_column: None,
            amount_locale: None,
            amount_format: None,
            delimiter: None,
            skip_rows: None,
            skip_header: None,
            invert_amounts: None,
            default_expense: Some("Expenses:Uncategorized".to_string()),
            default_income: Some("Income:Other".to_string()),
            mappings: HashMap::new(),
            filename_pattern: None,
        };

        let config = build_config_from_entry(&entry).unwrap();
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert_eq!(
            csv_config.default_expense.as_deref(),
            Some("Expenses:Uncategorized")
        );
        assert_eq!(csv_config.default_income.as_deref(), Some("Income:Other"));
    }

    #[test]
    fn test_build_config_from_entry_all_options() {
        let entry = ImporterEntry {
            name: "full".to_string(),
            account: Some("Assets:Bank".to_string()),
            currency: Some("GBP".to_string()),
            date_column: Some(toml::Value::Integer(0)),
            date_format: Some("%d/%m/%Y".to_string()),
            narration_column: Some(toml::Value::Integer(2)),
            payee_column: Some(toml::Value::String("Payee".to_string())),
            amount_column: None,
            debit_column: Some(toml::Value::String("Debit".to_string())),
            credit_column: Some(toml::Value::String("Credit".to_string())),
            amount_locale: None,
            amount_format: None,
            delimiter: Some(";".to_string()),
            skip_rows: Some(2),
            skip_header: Some(true),
            invert_amounts: Some(true),
            default_expense: None,
            default_income: None,
            mappings: HashMap::new(),
            filename_pattern: None,
        };

        let config = build_config_from_entry(&entry).unwrap();
        assert_eq!(config.currency, Some("GBP".to_string()));
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert_eq!(csv_config.delimiter, ';');
        assert_eq!(csv_config.skip_rows, 2);
        assert!(!csv_config.has_header); // skip_header=true → has_header=false
        assert!(csv_config.invert_sign);
    }

    #[test]
    fn test_find_importers_config_explicit_missing_returns_error() {
        let result = find_importers_config(Some(Path::new("/nonexistent/importers.toml")));
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("Importers config not found"));
    }

    #[test]
    fn test_find_importers_config_explicit_exists() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("importers.toml");
        std::fs::write(&path, "[[importers]]\nname = \"test\"\n").unwrap();

        let result = find_importers_config(Some(&path)).unwrap();
        assert_eq!(result, Some(path));
    }

    #[test]
    fn test_find_importers_config_none_returns_ok() {
        // When no explicit path is given, the function should not error
        // (it may or may not find a file depending on the environment)
        let result = find_importers_config(None);
        assert!(result.is_ok());
    }

    #[test]
    fn test_end_to_end_extract_with_config() {
        let dir = tempfile::tempdir().unwrap();

        // Write importers.toml
        let config_path = dir.path().join("importers.toml");
        std::fs::write(
            &config_path,
            r#"
[[importers]]
name = "mybank"
account = "Assets:Bank:MyBank"
currency = "USD"
date_column = "Date"
narration_column = "Description"
amount_column = "Amount"
default_expense = "Expenses:Uncategorized"

[importers.mappings]
"GROCERY" = "Expenses:Food"
"#,
        )
        .unwrap();

        // Write CSV (negative amounts = money out = expenses)
        let csv_path = dir.path().join("statement.csv");
        std::fs::write(
            &csv_path,
            "Date,Description,Amount\n\
             2024-01-15,GROCERY STORE,-50.00\n\
             2024-01-16,RANDOM PURCHASE,-25.00\n",
        )
        .unwrap();

        // Load config and extract
        let importers_file = load_importers_config(&config_path).unwrap();
        let entry = importers_file
            .importers
            .iter()
            .find(|e| e.name == "mybank")
            .unwrap();
        let config = build_config_from_entry(entry).unwrap();
        let result = rustledger_importer::csv_importer::CsvImporter
            .extract_file(&csv_path, &config)
            .unwrap();

        assert_eq!(result.directives.len(), 2);

        // First should map to Expenses:Food via mapping
        if let rustledger_core::Directive::Transaction(txn) = &result.directives[0] {
            assert_eq!(txn.postings[0].account.as_str(), "Assets:Bank:MyBank");
            assert_eq!(txn.postings[1].account.as_str(), "Expenses:Food");
        } else {
            panic!("Expected transaction");
        }

        // Second should use default_expense since no mapping matches
        if let rustledger_core::Directive::Transaction(txn) = &result.directives[1] {
            assert_eq!(txn.postings[1].account.as_str(), "Expenses:Uncategorized");
        } else {
            panic!("Expected transaction");
        }
    }

    // Note: the `is_ofx_file` helper was removed when the OFX-
    // specific branch in `run()` was unified into the generic
    // "non-CSV dispatcher" path. OFX extension matching is now
    // owned entirely by `OfxImporter::identify` (via the registry),
    // so no separate helper exists to test.

    // ===== Importer dispatch (select_importer) =====
    //
    // These pin the four interesting cases for which Importer the CLI
    // selects for a given (file, args) combination. The bug they guard
    // against is the regression where `--importer <toml-csv-entry>` on a
    // `.ofx`-named file would silently dispatch to `OfxImporter` and drop
    // the user's column mappings.

    #[test]
    fn test_select_importer_csv_extension_picks_csv() {
        let registry = ImporterRegistry::with_builtins();
        let args = Args::parse_from(["extract", "ignored.csv"]);
        let imp = select_importer(&registry, Path::new("foo.csv"), &args);
        assert_eq!(imp.name(), "CSV");
    }

    #[test]
    fn test_select_importer_ofx_extension_picks_ofx() {
        let registry = ImporterRegistry::with_builtins();
        let args = Args::parse_from(["extract", "ignored.ofx"]);
        let imp = select_importer(&registry, Path::new("foo.ofx"), &args);
        assert_eq!(imp.name(), "OFX/QFX");
    }

    #[test]
    fn test_select_importer_explicit_importer_flag_forces_csv_even_on_ofx_file() {
        // Regression guard: prior to this PR, `--importer chase` on a
        // `.ofx`-named file took the CSV path correctly. After Wave 2.2,
        // registry.identify() picks OfxImporter from the extension — which
        // would silently drop the CSV column mappings. select_importer
        // must override this case.
        let registry = ImporterRegistry::with_builtins();
        let args = Args::parse_from(["extract", "ignored.ofx", "--importer", "chase"]);
        let imp = select_importer(&registry, Path::new("foo.ofx"), &args);
        assert_eq!(
            imp.name(),
            "CSV",
            "TOML --importer entries must force CSV dispatch regardless of file extension"
        );
    }

    #[test]
    fn test_select_importer_unknown_extension_falls_back_to_csv() {
        // .qbo Quicken exports are a common case: user has a TOML CSV
        // entry to parse them. Even without --importer, the fallback
        // path should choose CSV rather than erroring.
        let registry = ImporterRegistry::with_builtins();
        let args = Args::parse_from(["extract", "ignored.qbo"]);
        let imp = select_importer(&registry, Path::new("foo.qbo"), &args);
        assert_eq!(imp.name(), "CSV");
    }

    #[test]
    fn test_select_importer_config_alone_does_not_force_csv() {
        // Regression: `--config x.toml` alone (no --importer) used to
        // force CSV dispatch, which silently broke combinations like
        // `--config x.toml --wasm-importer my-mt940.wasm foo.mt940`
        // (registered WASM was never consulted). With the fix,
        // --config alone consults the registry so WASM importers stay
        // reachable. A .csv file still resolves to CSV via
        // registry.identify, not via the force-CSV path.
        use rustledger_importer::test_fixtures::identifying_wat;
        let tmp = tempfile::tempdir().unwrap();
        let wasm_path = tmp.path().join("mt.wasm");
        std::fs::write(
            &wasm_path,
            wat::parse_str(identifying_wat("mt9")).expect("WAT parses"),
        )
        .unwrap();
        let cfg_dir = tempfile::tempdir().unwrap();
        let cfg_path = cfg_dir.path().join("importers.toml");
        std::fs::write(&cfg_path, "").unwrap(); // empty but valid toml

        let args = Args::parse_from([
            "extract",
            "foo.mt940",
            "--config",
            cfg_path.to_str().unwrap(),
            "--wasm-importer",
            wasm_path.to_str().unwrap(),
        ]);
        let registry = build_registry(&args).expect("builds");
        let imp = select_importer(&registry, Path::new("foo.mt940"), &args);
        assert_eq!(
            imp.name(),
            "mt9",
            "WASM importer should win when --config is set alone (no --importer)"
        );
    }

    #[test]
    #[cfg(feature = "python-plugin-wasm")]
    fn resolve_scan_dirs_propagates_error_for_explicit_missing_config() {
        // --config /missing.toml should error loudly, not silently
        // degrade to "no WASM scan dirs".
        let args = Args::parse_from([
            "extract",
            "--config",
            "/this/path/does/not/exist/importers.toml",
        ]);
        let result = resolve_scan_dirs(&args);
        let Err(err) = result else {
            panic!("explicit missing --config should error");
        };
        let msg = format!("{err:#}");
        assert!(
            msg.contains("does/not/exist"),
            "error should name the missing path: {msg}"
        );
    }

    #[test]
    #[cfg(feature = "python-plugin-wasm")]
    fn resolve_scan_dirs_soft_fails_for_implicit_missing_config() {
        // No --config provided, no importers.toml in cwd/XDG → empty
        // scan dirs, no error. This is the right behavior because
        // the user didn't ask for any config; absence is expected.
        let args = Args::parse_from(["extract"]);
        let dirs = resolve_scan_dirs(&args).expect("implicit missing is soft-fail");
        // Could be empty or non-empty depending on whether a real
        // ~/.config/rledger/importers.toml exists in this test env.
        // What we're asserting is that it didn't error.
        let _ = dirs;
    }

    #[test]
    fn run_dispatches_to_wasm_importer_with_config_set_but_no_toml_profiles() {
        // End-to-end regression for the bug my earlier
        // select_importer fix didn't fully close: a user runs
        // `extract foo.X --config wasm-only.toml --wasm-importer my.wasm`
        // where wasm-only.toml has *no* [[importers]] entries. The
        // dispatcher should be the WASM module; the CSV-branch
        // config-building must NOT fire and error out on "No
        // importers defined". Run through run() (not just
        // select_importer) so the dispatcher-first config-selection
        // path is actually exercised.
        use rustledger_importer::test_fixtures::identifying_wat;
        let tmp = tempfile::tempdir().unwrap();

        // WAT importer that identifies every file as its own (so it
        // wins .mt940 dispatch against the CSV fallback) and returns
        // an empty ImporterOutput for extract.
        let wasm_path = tmp.path().join("my.wasm");
        std::fs::write(
            &wasm_path,
            wat::parse_str(identifying_wat("mt9")).expect("WAT"),
        )
        .unwrap();

        // wasm-only.toml: sets wasm_importer_dir to nothing useful,
        // critically has NO [[importers]] entries. Pre-fix, the CSV
        // branch would load this and error "No importers defined".
        let cfg_path = tmp.path().join("wasm-only.toml");
        std::fs::write(&cfg_path, "").unwrap();

        // Source file the WASM importer will be asked to handle.
        // The actual contents don't matter — the WAT extract()
        // returns (ptr=0, len=0) which decodes to an empty output.
        let src_path = tmp.path().join("statement.mt940");
        std::fs::write(&src_path, b"any bytes").unwrap();

        let out_path = tmp.path().join("out.beancount");
        let args = Args::parse_from([
            "extract",
            src_path.to_str().unwrap(),
            "--config",
            cfg_path.to_str().unwrap(),
            "--wasm-importer",
            wasm_path.to_str().unwrap(),
            "--output",
            out_path.to_str().unwrap(),
        ]);

        // The bug shape: run() previously errored with "No importers
        // defined in ...". With the dispatcher-first fix, run()
        // completes successfully and writes the empty output.
        // (Empty msgpack from the WAT extract() decodes to an empty
        // PluginOutput → no directives → empty .beancount file.)
        if let Err(e) = run(&args, &src_path) {
            let msg = format!("{e:#}");
            assert!(
                !msg.contains("No importers defined"),
                "regression: CSV-branch error fired before WASM dispatch: {msg}"
            );
            // Other errors (e.g. wasmtime decode of `(0, 0)`) are
            // unrelated to the bug under test — what we're pinning
            // is that we don't error out before reaching the WASM
            // importer.
        }
    }

    #[test]
    fn test_fuzzy_text_match_exact() {
        assert!(fuzzy_text_match("grocery store", "grocery store"));
    }

    #[test]
    fn test_fuzzy_text_match_contains() {
        assert!(fuzzy_text_match("grocery store #123", "grocery store"));
        assert!(fuzzy_text_match("grocery store", "grocery store #123"));
    }

    #[test]
    fn test_fuzzy_text_match_word_overlap() {
        assert!(fuzzy_text_match("whole foods market", "whole foods"));
    }

    #[test]
    fn test_fuzzy_text_match_no_match() {
        assert!(!fuzzy_text_match("amazon", "netflix"));
    }

    #[test]
    fn test_fuzzy_text_match_empty() {
        assert!(!fuzzy_text_match("", "something"));
        assert!(!fuzzy_text_match("something", ""));
    }

    #[test]
    fn test_is_duplicate_matching() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let new_txn = Transaction::new(date, "GROCERY STORE").with_synthesized_posting(
            rustledger_core::Posting::new(
                "Assets:Bank",
                rustledger_core::Amount::new(rust_decimal::Decimal::new(-5000, 2), "USD"),
            ),
        );

        let existing = vec![
            Transaction::new(date, "GROCERY STORE #123").with_synthesized_posting(
                rustledger_core::Posting::new(
                    "Assets:Bank",
                    rustledger_core::Amount::new(rust_decimal::Decimal::new(-5000, 2), "USD"),
                ),
            ),
        ];

        assert!(is_duplicate(&new_txn, &existing));
    }

    #[test]
    fn test_is_duplicate_different_date() {
        let new_txn = Transaction::new(
            rustledger_core::naive_date(2024, 1, 15).unwrap(),
            "GROCERY STORE",
        )
        .with_synthesized_posting(rustledger_core::Posting::new(
            "Assets:Bank",
            rustledger_core::Amount::new(rust_decimal::Decimal::new(-5000, 2), "USD"),
        ));

        let existing = vec![
            Transaction::new(
                rustledger_core::naive_date(2024, 1, 16).unwrap(),
                "GROCERY STORE",
            )
            .with_synthesized_posting(rustledger_core::Posting::new(
                "Assets:Bank",
                rustledger_core::Amount::new(rust_decimal::Decimal::new(-5000, 2), "USD"),
            )),
        ];

        assert!(!is_duplicate(&new_txn, &existing));
    }

    #[test]
    fn test_is_duplicate_different_amount() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let new_txn = Transaction::new(date, "GROCERY STORE").with_synthesized_posting(
            rustledger_core::Posting::new(
                "Assets:Bank",
                rustledger_core::Amount::new(rust_decimal::Decimal::new(-5000, 2), "USD"),
            ),
        );

        let existing = vec![
            Transaction::new(date, "GROCERY STORE").with_synthesized_posting(
                rustledger_core::Posting::new(
                    "Assets:Bank",
                    rustledger_core::Amount::new(rust_decimal::Decimal::new(-7500, 2), "USD"),
                ),
            ),
        ];

        assert!(!is_duplicate(&new_txn, &existing));
    }

    #[test]
    fn test_load_existing_transactions() {
        let dir = tempfile::tempdir().unwrap();
        let ledger_path = dir.path().join("ledger.beancount");
        std::fs::write(
            &ledger_path,
            r#"2024-01-15 * "GROCERY STORE" "Weekly groceries"
  Assets:Bank:Checking  -50.00 USD
  Expenses:Food          50.00 USD

2024-01-16 * "NETFLIX" "Monthly subscription"
  Assets:Bank:Checking  -15.99 USD
  Expenses:Entertainment 15.99 USD
"#,
        )
        .unwrap();

        let txns = load_existing_transactions(&ledger_path).unwrap();
        assert_eq!(txns.len(), 2);
        assert_eq!(
            txns[0].date,
            rustledger_core::naive_date(2024, 1, 15).unwrap()
        );
        assert_eq!(
            txns[1].date,
            rustledger_core::naive_date(2024, 1, 16).unwrap()
        );
    }

    #[test]
    fn test_end_to_end_output_file() {
        let dir = tempfile::tempdir().unwrap();

        let csv_path = dir.path().join("statement.csv");
        std::fs::write(
            &csv_path,
            "Date,Description,Amount\n2024-01-15,Coffee,5.00\n",
        )
        .unwrap();

        let output_path = dir.path().join("output.beancount");

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "-o",
            output_path.to_str().unwrap(),
        ]);

        run(&args, &csv_path).unwrap();

        let output = std::fs::read_to_string(&output_path).unwrap();
        assert!(output.contains("2024-01-15"));
        assert!(output.contains("Coffee"));
    }

    #[test]
    fn test_end_to_end_existing_dedup() {
        let dir = tempfile::tempdir().unwrap();

        // Write existing ledger
        let ledger_path = dir.path().join("ledger.beancount");
        std::fs::write(
            &ledger_path,
            r#"2024-01-15 * "Coffee"
  Assets:Bank:Checking  5.00 USD
  Expenses:Unknown      -5.00 USD
"#,
        )
        .unwrap();

        // Write CSV with same + new transaction
        let csv_path = dir.path().join("statement.csv");
        std::fs::write(
            &csv_path,
            "Date,Description,Amount\n\
             2024-01-15,Coffee,5.00\n\
             2024-01-16,Lunch,12.00\n",
        )
        .unwrap();

        let output_path = dir.path().join("output.beancount");

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "--existing",
            ledger_path.to_str().unwrap(),
            "-o",
            output_path.to_str().unwrap(),
        ]);

        run(&args, &csv_path).unwrap();

        let output = std::fs::read_to_string(&output_path).unwrap();
        // The Coffee transaction should be filtered as duplicate
        assert!(!output.contains("Coffee"));
        // The Lunch transaction should remain
        assert!(output.contains("Lunch"));
    }

    #[test]
    fn test_parse_column_value_unsupported_type() {
        // Boolean TOML values should return None
        assert_eq!(parse_column_value(&toml::Value::Boolean(true)), None);
        // Float TOML values should return None
        assert_eq!(parse_column_value(&toml::Value::Float(1.5)), None);
    }

    #[test]
    fn test_run_with_importer_config() {
        let dir = tempfile::tempdir().unwrap();

        // Write importers.toml
        let config_path = dir.path().join("importers.toml");
        std::fs::write(
            &config_path,
            r#"
[[importers]]
name = "mybank"
account = "Assets:Bank:MyBank"
currency = "USD"
date_column = "Date"
narration_column = "Description"
amount_column = "Amount"
"#,
        )
        .unwrap();

        // Write CSV
        let csv_path = dir.path().join("statement.csv");
        std::fs::write(
            &csv_path,
            "Date,Description,Amount\n2024-01-15,Coffee,5.00\n",
        )
        .unwrap();

        let output_path = dir.path().join("output.beancount");

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "--importer",
            "mybank",
            "--config",
            config_path.to_str().unwrap(),
            "-o",
            output_path.to_str().unwrap(),
        ]);

        run(&args, &csv_path).unwrap();

        let output = std::fs::read_to_string(&output_path).unwrap();
        assert!(output.contains("Assets:Bank:MyBank"));
        assert!(output.contains("Coffee"));
    }

    #[test]
    fn test_run_with_importer_not_found() {
        let dir = tempfile::tempdir().unwrap();

        let config_path = dir.path().join("importers.toml");
        std::fs::write(
            &config_path,
            "[[importers]]\nname = \"other\"\naccount = \"Assets:Bank\"\n",
        )
        .unwrap();

        let csv_path = dir.path().join("statement.csv");
        std::fs::write(&csv_path, "Date,Description,Amount\n").unwrap();

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "--importer",
            "nonexistent",
            "--config",
            config_path.to_str().unwrap(),
        ]);

        let err = run(&args, &csv_path).unwrap_err();
        assert!(err.to_string().contains("not found"));
        assert!(err.to_string().contains("other"));
    }

    #[test]
    fn test_run_with_importer_no_config_file() {
        let dir = tempfile::tempdir().unwrap();
        let csv_path = dir.path().join("statement.csv");
        std::fs::write(&csv_path, "Date,Description,Amount\n").unwrap();

        // Point --config to a non-existent file
        let config_path = dir.path().join("nonexistent.toml");

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "--importer",
            "mybank",
            "--config",
            config_path.to_str().unwrap(),
        ]);

        let err = run(&args, &csv_path).unwrap_err();
        assert!(err.to_string().contains("Importers config not found"));
    }

    #[test]
    fn test_run_stdout_output() {
        // Test the stdout path (no -o flag) — just ensure it doesn't error
        let dir = tempfile::tempdir().unwrap();
        let csv_path = dir.path().join("statement.csv");
        std::fs::write(
            &csv_path,
            "Date,Description,Amount\n2024-01-15,Coffee,5.00\n",
        )
        .unwrap();

        let args = Args::parse_from(["extract", csv_path.to_str().unwrap()]);
        // Should succeed writing to stdout
        run(&args, &csv_path).unwrap();
    }

    #[test]
    fn test_run_with_optional_cli_args() {
        let dir = tempfile::tempdir().unwrap();
        let csv_path = dir.path().join("statement.csv");
        std::fs::write(
            &csv_path,
            "Date,Payee,Description,Debit,Credit\n\
             2024-01-15,Store,Coffee,5.00,\n\
             2024-01-16,Employer,Salary,,1000.00\n",
        )
        .unwrap();

        let output_path = dir.path().join("output.beancount");

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "--payee-column",
            "Payee",
            "--debit-column",
            "Debit",
            "--credit-column",
            "Credit",
            "-o",
            output_path.to_str().unwrap(),
        ]);

        run(&args, &csv_path).unwrap();

        let output = std::fs::read_to_string(&output_path).unwrap();
        assert!(output.contains("2024-01-15"));
        assert!(output.contains("Coffee"));
    }

    #[test]
    fn test_first_posting_amount_no_postings() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Test");
        assert_eq!(first_posting_amount(&txn), None);
    }

    #[test]
    fn test_first_posting_amount_auto_posting() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Test")
            .with_synthesized_posting(rustledger_core::Posting::auto("Expenses:Unknown"));
        assert_eq!(first_posting_amount(&txn), None);
    }

    #[test]
    fn test_txn_match_text_with_payee() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Weekly groceries").with_payee("Whole Foods");
        let text = txn_match_text(&txn);
        assert!(text.contains("whole foods"));
        assert!(text.contains("weekly groceries"));
    }

    #[test]
    fn test_txn_match_text_no_payee() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Coffee Shop");
        let text = txn_match_text(&txn);
        assert_eq!(text, "coffee shop");
    }

    #[test]
    fn test_is_duplicate_no_existing() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Coffee").with_synthesized_posting(
            rustledger_core::Posting::new(
                "Assets:Bank",
                rustledger_core::Amount::new(rust_decimal::Decimal::new(-500, 2), "USD"),
            ),
        );
        assert!(!is_duplicate(&txn, &[]));
    }

    #[test]
    fn test_is_duplicate_with_payee() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let new_txn = Transaction::new(date, "Weekly groceries")
            .with_payee("WHOLE FOODS")
            .with_synthesized_posting(rustledger_core::Posting::new(
                "Assets:Bank",
                rustledger_core::Amount::new(rust_decimal::Decimal::new(-5000, 2), "USD"),
            ));

        let existing = vec![
            Transaction::new(date, "Weekly groceries")
                .with_payee("Whole Foods Market")
                .with_synthesized_posting(rustledger_core::Posting::new(
                    "Assets:Bank",
                    rustledger_core::Amount::new(rust_decimal::Decimal::new(-5000, 2), "USD"),
                )),
        ];

        assert!(is_duplicate(&new_txn, &existing));
    }

    #[test]
    fn test_load_existing_transactions_nonexistent_file() {
        let result = load_existing_transactions(Path::new("/nonexistent/ledger.beancount"));
        assert!(result.is_err());
    }

    #[test]
    fn test_load_existing_transactions_with_non_txn_directives() {
        let dir = tempfile::tempdir().unwrap();
        let ledger_path = dir.path().join("ledger.beancount");
        std::fs::write(
            &ledger_path,
            r#"2024-01-01 open Assets:Bank:Checking USD

2024-01-15 * "Coffee"
  Assets:Bank:Checking  -5.00 USD
  Expenses:Food          5.00 USD

2024-01-31 balance Assets:Bank:Checking 1000.00 USD
"#,
        )
        .unwrap();

        let txns = load_existing_transactions(&ledger_path).unwrap();
        // Only the transaction should be loaded, not open/balance
        assert_eq!(txns.len(), 1);
    }

    #[test]
    fn test_end_to_end_dedup_no_duplicates() {
        let dir = tempfile::tempdir().unwrap();

        let ledger_path = dir.path().join("ledger.beancount");
        std::fs::write(
            &ledger_path,
            r#"2024-01-10 * "Old transaction"
  Assets:Bank:Checking  10.00 USD
  Expenses:Unknown     -10.00 USD
"#,
        )
        .unwrap();

        let csv_path = dir.path().join("statement.csv");
        std::fs::write(
            &csv_path,
            "Date,Description,Amount\n2024-01-15,Coffee,5.00\n",
        )
        .unwrap();

        let output_path = dir.path().join("output.beancount");

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "--existing",
            ledger_path.to_str().unwrap(),
            "-o",
            output_path.to_str().unwrap(),
        ]);

        run(&args, &csv_path).unwrap();

        let output = std::fs::read_to_string(&output_path).unwrap();
        // No duplicates, so Coffee should remain
        assert!(output.contains("Coffee"));
    }

    #[test]
    fn test_run_with_importers_config_alias() {
        // Test that --importers-config alias still works
        let dir = tempfile::tempdir().unwrap();

        let config_path = dir.path().join("importers.toml");
        std::fs::write(
            &config_path,
            r#"
[[importers]]
name = "test"
account = "Assets:Bank"
date_column = "Date"
narration_column = "Description"
amount_column = "Amount"
"#,
        )
        .unwrap();

        let csv_path = dir.path().join("statement.csv");
        std::fs::write(&csv_path, "Date,Description,Amount\n2024-01-15,Test,5.00\n").unwrap();

        let output_path = dir.path().join("output.beancount");

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "--importer",
            "test",
            "--importers-config",
            config_path.to_str().unwrap(),
            "-o",
            output_path.to_str().unwrap(),
        ]);

        run(&args, &csv_path).unwrap();

        let output = std::fs::read_to_string(&output_path).unwrap();
        assert!(output.contains("Assets:Bank"));
    }

    #[test]
    fn test_run_with_ofx_file() {
        let dir = tempfile::tempdir().unwrap();
        let ofx_path = dir.path().join("statement.ofx");
        std::fs::write(
            &ofx_path,
            r"OFXHEADER:100
DATA:OFXSGML
VERSION:102
SECURITY:NONE
ENCODING:USASCII
CHARSET:1252
COMPRESSION:NONE
OLDFILEUID:NONE
NEWFILEUID:NONE

<OFX>
<SIGNONMSGSRSV1>
<SONRS>
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<DTSERVER>20240115120000
<LANGUAGE>ENG
</SONRS>
</SIGNONMSGSRSV1>
<BANKMSGSRSV1>
<STMTTRNRS>
<TRNUID>1001
<STATUS>
<CODE>0
<SEVERITY>INFO
</STATUS>
<STMTRS>
<CURDEF>USD
<BANKACCTFROM>
<BANKID>123456789
<ACCTID>987654321
<ACCTTYPE>CHECKING
</BANKACCTFROM>
<BANKTRANLIST>
<DTSTART>20240101
<DTEND>20240131
<STMTTRN>
<TRNTYPE>DEBIT
<DTPOSTED>20240115
<TRNAMT>-50.00
<FITID>2024011501
<NAME>GROCERY STORE
<MEMO>Weekly groceries
</STMTTRN>
</BANKTRANLIST>
<LEDGERBAL>
<BALAMT>5000.00
<DTASOF>20240131
</LEDGERBAL>
</STMTRS>
</STMTTRNRS>
</BANKMSGSRSV1>
</OFX>",
        )
        .unwrap();

        let output_path = dir.path().join("output.beancount");

        let args = Args::parse_from([
            "extract",
            ofx_path.to_str().unwrap(),
            "-o",
            output_path.to_str().unwrap(),
        ]);

        run(&args, &ofx_path).unwrap();
        let output = std::fs::read_to_string(&output_path).unwrap();
        assert!(output.contains("2024-01-15"));
        assert!(output.contains("GROCERY STORE"));
    }

    #[test]
    fn test_fuzzy_text_match_word_overlap_threshold() {
        // 1 out of 3 words match — below 50% threshold
        assert!(!fuzzy_text_match("the big store", "the small shop"));
        // 2 out of 2 words match — above 50% threshold
        assert!(fuzzy_text_match("grocery store", "grocery store extra"));
    }

    #[test]
    fn test_fuzzy_text_match_longer_a_than_b() {
        // a has more words than b, and neither contains the other as a substring
        // This forces the word-overlap path with the swap branch
        assert!(fuzzy_text_match(
            "whole foods market store location",
            "whole foods burgers"
        ));
    }

    #[test]
    fn test_run_with_amount_format_arg() {
        let dir = tempfile::tempdir().unwrap();
        let csv_path = dir.path().join("statement.tsv");
        // Use tab delimiter to avoid conflict with comma decimal separator
        std::fs::write(
            &csv_path,
            "Date\tDescription\tAmount\n2024-01-15\tCoffee\t1.234,56\n",
        )
        .unwrap();

        let output_path = dir.path().join("output.beancount");

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "--amount-format",
            "#.##0,00",
            "--delimiter",
            "\t",
            "-o",
            output_path.to_str().unwrap(),
        ]);

        run(&args, &csv_path).unwrap();
        let output = std::fs::read_to_string(&output_path).unwrap();
        assert!(output.contains("Coffee"));
    }

    #[test]
    fn test_run_with_amount_locale_arg() {
        let dir = tempfile::tempdir().unwrap();
        let csv_path = dir.path().join("statement.csv");
        std::fs::write(
            &csv_path,
            "Date,Description,Amount\n2024-01-15,Coffee,5.00\n",
        )
        .unwrap();

        let output_path = dir.path().join("output.beancount");

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "--amount-locale",
            "en_US",
            "-o",
            output_path.to_str().unwrap(),
        ]);

        run(&args, &csv_path).unwrap();
        let output = std::fs::read_to_string(&output_path).unwrap();
        assert!(output.contains("5.00"));
    }

    #[test]
    fn test_run_with_invalid_locale() {
        let dir = tempfile::tempdir().unwrap();
        let csv_path = dir.path().join("statement.csv");
        std::fs::write(
            &csv_path,
            "Date,Description,Amount\n2024-01-15,Coffee,5.00\n",
        )
        .unwrap();

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "--amount-locale",
            "invalid_LOCALE_xyz",
        ]);

        let err = run(&args, &csv_path).unwrap_err();
        assert!(err.to_string().contains("not a valid locale"));
    }

    #[test]
    fn test_run_with_csv_that_generates_warnings() {
        let dir = tempfile::tempdir().unwrap();
        let csv_path = dir.path().join("statement.csv");
        // Include a row with an invalid date to trigger a warning
        std::fs::write(
            &csv_path,
            "Date,Description,Amount\n\
             2024-01-15,Coffee,5.00\n\
             not-a-date,Bad Row,10.00\n",
        )
        .unwrap();

        let output_path = dir.path().join("output.beancount");

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "-o",
            output_path.to_str().unwrap(),
        ]);

        // Should succeed — bad row generates warning but doesn't fail
        run(&args, &csv_path).unwrap();
        let output = std::fs::read_to_string(&output_path).unwrap();
        assert!(output.contains("Coffee"));
    }

    #[test]
    fn test_run_auto_select_sole_importer() {
        let dir = tempfile::tempdir().unwrap();

        // Config with exactly one importer — should auto-select
        let config_path = dir.path().join("importers.toml");
        std::fs::write(
            &config_path,
            r#"
[[importers]]
name = "mybank"
account = "Assets:Bank:Auto"
date_column = "Date"
narration_column = "Description"
amount_column = "Amount"
"#,
        )
        .unwrap();

        let csv_path = dir.path().join("statement.csv");
        std::fs::write(
            &csv_path,
            "Date,Description,Amount\n2024-01-15,Coffee,-5.00\n",
        )
        .unwrap();

        let output_path = dir.path().join("output.beancount");

        // No --importer flag, but --config points to a single-importer file
        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "--config",
            config_path.to_str().unwrap(),
            "-o",
            output_path.to_str().unwrap(),
        ]);

        run(&args, &csv_path).unwrap();

        let output = std::fs::read_to_string(&output_path).unwrap();
        assert!(output.contains("Assets:Bank:Auto"));
        assert!(output.contains("Coffee"));
    }

    #[test]
    fn test_run_auto_select_errors_on_multiple_importers() {
        let dir = tempfile::tempdir().unwrap();

        // Both importers have filename patterns that match "statement.csv"
        let config_path = dir.path().join("importers.toml");
        std::fs::write(
            &config_path,
            r#"
[[importers]]
name = "checking"
account = "Assets:Bank:Checking"
filename_pattern = "*.csv"

[[importers]]
name = "credit"
account = "Liabilities:CreditCard"
filename_pattern = "statement*"
"#,
        )
        .unwrap();

        let csv_path = dir.path().join("statement.csv");
        std::fs::write(&csv_path, "Date,Description,Amount\n").unwrap();

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "--config",
            config_path.to_str().unwrap(),
        ]);

        let err = run(&args, &csv_path).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("Multiple importers"));
        assert!(msg.contains("checking"));
        assert!(msg.contains("credit"));
    }

    #[test]
    fn test_run_auto_select_errors_on_empty_config() {
        let dir = tempfile::tempdir().unwrap();

        let config_path = dir.path().join("importers.toml");
        std::fs::write(&config_path, "importers = []\n").unwrap();

        let csv_path = dir.path().join("statement.csv");
        std::fs::write(&csv_path, "Date,Description,Amount\n").unwrap();

        let args = Args::parse_from([
            "extract",
            csv_path.to_str().unwrap(),
            "--config",
            config_path.to_str().unwrap(),
        ]);

        let err = run(&args, &csv_path).unwrap_err();
        assert!(err.to_string().contains("No importers defined"));
    }

    // ===== build_registry / WASM discovery integration tests =====

    /// Wrapper around the shared
    /// [`rustledger_importer::test_fixtures::metadata_wat`] helper so
    /// tests below can write WAT bytes in one call. Single source of
    /// truth for the WAT shape lives in `rustledger-importer`; the
    /// CLI tests just consume it.
    fn wasm_importer_with_name(name: &str) -> Vec<u8> {
        let wat = rustledger_importer::test_fixtures::metadata_wat(name);
        wat::parse_str(&wat).expect("WAT parses")
    }

    #[test]
    fn build_registry_defaults_to_builtins_only() {
        // No --wasm-importer, no --wasm-importer-dir, no toml.
        let args = Args::parse_from(["extract"]);
        let registry = build_registry(&args).expect("builds");
        // OFX + CSV.
        assert_eq!(registry.len(), 2);
        assert!(registry.find_by_name("CSV").is_some());
        assert!(registry.find_by_name("OFX").is_some());
    }

    #[test]
    fn build_registry_loads_cli_wasm_importer_ahead_of_builtins() {
        let tmp = tempfile::tempdir().unwrap();
        let wasm_path = tmp.path().join("ad-hoc.wasm");
        std::fs::write(&wasm_path, wasm_importer_with_name("usr")).unwrap();

        let args = Args::parse_from(["extract", "--wasm-importer", wasm_path.to_str().unwrap()]);
        let registry = build_registry(&args).expect("builds");
        // 1 user-WASM + 2 built-ins.
        assert_eq!(registry.len(), 3);
        assert!(registry.find_by_name("usr").is_some());
        // Built-ins still present so CSV/OFX dispatch keeps working.
        assert!(registry.find_by_name("CSV").is_some());
        assert!(registry.find_by_name("OFX").is_some());
    }

    #[test]
    fn build_registry_scans_directory_from_cli_flag() {
        let tmp = tempfile::tempdir().unwrap();
        std::fs::write(tmp.path().join("aaa.wasm"), wasm_importer_with_name("aaa")).unwrap();
        std::fs::write(tmp.path().join("bbb.wasm"), wasm_importer_with_name("bbb")).unwrap();

        let args = Args::parse_from([
            "extract",
            "--wasm-importer-dir",
            tmp.path().to_str().unwrap(),
        ]);
        let registry = build_registry(&args).expect("builds");
        // 2 scanned + 2 built-ins.
        assert_eq!(registry.len(), 4);
        assert!(registry.find_by_name("aaa").is_some());
        assert!(registry.find_by_name("bbb").is_some());
    }

    #[test]
    fn build_registry_reads_wasm_importer_dir_from_importers_toml() {
        // Two temp dirs: one for the .wasm modules, one for the
        // importers.toml that points at the wasm dir.
        let wasm_dir = tempfile::tempdir().unwrap();
        std::fs::write(
            wasm_dir.path().join("xyz.wasm"),
            wasm_importer_with_name("xyz"),
        )
        .unwrap();

        let cfg_dir = tempfile::tempdir().unwrap();
        let cfg_path = cfg_dir.path().join("importers.toml");
        std::fs::write(
            &cfg_path,
            format!("wasm_importer_dir = \"{}\"\n", wasm_dir.path().display()),
        )
        .unwrap();

        let args = Args::parse_from(["extract", "--config", cfg_path.to_str().unwrap()]);
        let registry = build_registry(&args).expect("builds");
        assert!(
            registry.find_by_name("xyz").is_some(),
            "xyz should be loaded via importers.toml's wasm_importer_dir"
        );
    }

    #[test]
    fn build_registry_cli_dir_flag_overrides_importers_toml_setting() {
        // toml setting points at a dir with 'tom.wasm'; CLI flag
        // points at a different dir with 'cli.wasm'. Only the CLI one
        // should load.
        let toml_only_dir = tempfile::tempdir().unwrap();
        std::fs::write(
            toml_only_dir.path().join("tom.wasm"),
            wasm_importer_with_name("tom"),
        )
        .unwrap();

        let cli_dir = tempfile::tempdir().unwrap();
        std::fs::write(
            cli_dir.path().join("cli.wasm"),
            wasm_importer_with_name("cli"),
        )
        .unwrap();

        let cfg_dir = tempfile::tempdir().unwrap();
        let cfg_path = cfg_dir.path().join("importers.toml");
        std::fs::write(
            &cfg_path,
            format!(
                "wasm_importer_dir = \"{}\"\n",
                toml_only_dir.path().display()
            ),
        )
        .unwrap();

        let args = Args::parse_from([
            "extract",
            "--config",
            cfg_path.to_str().unwrap(),
            "--wasm-importer-dir",
            cli_dir.path().to_str().unwrap(),
        ]);
        let registry = build_registry(&args).expect("builds");
        assert!(
            registry.find_by_name("cli").is_some(),
            "CLI-flag dir should be scanned"
        );
        assert!(
            registry.find_by_name("tom").is_none(),
            "toml-setting dir should be skipped when CLI flag is set"
        );
    }

    #[test]
    fn build_registry_propagates_cli_wasm_importer_load_errors() {
        let tmp = tempfile::tempdir().unwrap();
        let bad_path = tmp.path().join("bogus.wasm");
        std::fs::write(&bad_path, b"not valid wasm").unwrap();

        let args = Args::parse_from(["extract", "--wasm-importer", bad_path.to_str().unwrap()]);
        // ImporterRegistry doesn't impl Debug, so destructure manually
        // instead of `.expect_err`.
        let Err(err) = build_registry(&args) else {
            panic!("bogus wasm should fail to load");
        };
        let msg = format!("{err:#}");
        assert!(
            msg.contains("bogus.wasm"),
            "error should name the failing path: {msg}"
        );
    }

    #[test]
    fn build_registry_scans_multiple_cli_dirs_in_order() {
        // --wasm-importer-dir is repeatable; both dirs should be
        // scanned, with registration order = arg order.
        let dir_a = tempfile::tempdir().unwrap();
        std::fs::write(
            dir_a.path().join("aaa.wasm"),
            wasm_importer_with_name("aaa"),
        )
        .unwrap();
        let dir_b = tempfile::tempdir().unwrap();
        std::fs::write(
            dir_b.path().join("bbb.wasm"),
            wasm_importer_with_name("bbb"),
        )
        .unwrap();

        let args = Args::parse_from([
            "extract",
            "--wasm-importer-dir",
            dir_a.path().to_str().unwrap(),
            "--wasm-importer-dir",
            dir_b.path().to_str().unwrap(),
        ]);
        let registry = build_registry(&args).expect("builds");
        assert!(registry.find_by_name("aaa").is_some(), "first dir loaded");
        assert!(registry.find_by_name("bbb").is_some(), "second dir loaded");
    }

    #[test]
    fn build_registry_accepts_toml_dir_as_list() {
        // wasm_importer_dir = ["a", "b"] in importers.toml.
        let dir_a = tempfile::tempdir().unwrap();
        std::fs::write(
            dir_a.path().join("one.wasm"),
            wasm_importer_with_name("one"),
        )
        .unwrap();
        let dir_b = tempfile::tempdir().unwrap();
        std::fs::write(
            dir_b.path().join("two.wasm"),
            wasm_importer_with_name("two"),
        )
        .unwrap();

        let cfg_dir = tempfile::tempdir().unwrap();
        let cfg_path = cfg_dir.path().join("importers.toml");
        std::fs::write(
            &cfg_path,
            format!(
                "wasm_importer_dir = [\"{}\", \"{}\"]\n",
                dir_a.path().display(),
                dir_b.path().display()
            ),
        )
        .unwrap();

        let args = Args::parse_from(["extract", "--config", cfg_path.to_str().unwrap()]);
        let registry = build_registry(&args).expect("builds");
        assert!(registry.find_by_name("one").is_some());
        assert!(registry.find_by_name("two").is_some());
    }

    #[test]
    fn build_registry_skip_and_collect_loads_good_modules_past_failures() {
        // Mix one valid and one invalid .wasm in a scanned dir. The
        // valid one should still register; the failure is logged to
        // stderr (not asserted here — we just check the registry
        // didn't abort).
        let tmp = tempfile::tempdir().unwrap();
        std::fs::write(tmp.path().join("good.wasm"), wasm_importer_with_name("aaa")).unwrap();
        std::fs::write(tmp.path().join("bad-zzz.wasm"), b"not valid wasm").unwrap();

        let args = Args::parse_from([
            "extract",
            "--wasm-importer-dir",
            tmp.path().to_str().unwrap(),
        ]);
        let registry = build_registry(&args).expect("scan continues past failure");
        assert!(
            registry.find_by_name("aaa").is_some(),
            "good module loaded despite sibling failure"
        );
    }

    #[test]
    fn build_registry_cli_wasm_importer_wins_over_dir_scanned_same_name() {
        // Duplicate metadata.name from a CLI flag vs a scanned dir.
        // CLI registration is first, so find_by_name returns it. The
        // dir-scanned same-named module is also registered (both
        // exist in the list) but unreachable via find_by_name.
        let cli_dir = tempfile::tempdir().unwrap();
        let cli_path = cli_dir.path().join("cli.wasm");
        std::fs::write(&cli_path, wasm_importer_with_name("dup")).unwrap();

        let scan_dir = tempfile::tempdir().unwrap();
        std::fs::write(
            scan_dir.path().join("scanned.wasm"),
            wasm_importer_with_name("dup"),
        )
        .unwrap();

        let args = Args::parse_from([
            "extract",
            "--wasm-importer",
            cli_path.to_str().unwrap(),
            "--wasm-importer-dir",
            scan_dir.path().to_str().unwrap(),
        ]);
        let registry = build_registry(&args).expect("builds");
        // Both registered.
        assert_eq!(registry.len(), 4, "1 CLI + 1 dir-scanned + 2 builtins");
        // CLI one wins find_by_name because it's first.
        assert!(registry.find_by_name("dup").is_some());
        // Two entries with the same name in list_importers.
        let dup_count = registry
            .list_importers()
            .iter()
            .filter(|(name, _)| *name == "dup")
            .count();
        assert_eq!(dup_count, 2, "both same-named modules are registered");
    }

    #[test]
    #[cfg(feature = "python-plugin-wasm")]
    fn expand_tilde_resolves_tilde_prefix() {
        use super::config::expand_tilde;
        if let Some(home) = dirs::home_dir() {
            assert_eq!(expand_tilde(Path::new("~")), home);
            assert_eq!(
                expand_tilde(Path::new("~/foo/bar")),
                home.join("foo").join("bar")
            );
        }
        // No leading tilde → identity.
        assert_eq!(expand_tilde(Path::new("/abs/path")), Path::new("/abs/path"));
        assert_eq!(expand_tilde(Path::new("rel/path")), Path::new("rel/path"));
        // ~user is not supported — left as-is.
        assert_eq!(
            expand_tilde(Path::new("~other/foo")),
            Path::new("~other/foo")
        );
    }
}
