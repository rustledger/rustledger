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
//! 1. Path specified via `--config` / `--importers-config`
//! 2. `importers.toml` in the current directory
//! 3. `importers.toml` in the user config directory
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
    ConfigSource, ImportersFile, apply_column, build_config_from_entry, find_importers_config,
    find_importers_config_with_source, find_matching_importers, load_importers_config,
};
// Used only by the WASM-importer-dir resolution path (gated below).
#[cfg(feature = "python-plugin-wasm")]
use config::expand_tilde;
use duplicate::load_existing_transactions;
use rustledger_core::{Directive, FormatConfig};
use rustledger_importer::config::CsvConfigBuilder;
use rustledger_importer::{Importer, ImporterConfig, ImporterRegistry, csv_importer::CsvImporter};
use rustledger_parser::format::canonicalize_directives;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
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

    /// Per-row currency column name or index (optional). When set, each row's
    /// currency is read from this column instead of the single `--currency`.
    #[arg(long)]
    pub currency_column: Option<String>,

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
        "payee_column", "currency_column",
    ])]
    pub auto: bool,

    /// CSV has no header row
    #[arg(long)]
    pub no_header: bool,

    /// Categorize transactions using the built-in merchant dictionary
    /// (e.g. NETFLIX → Expenses:Subscriptions:Streaming) instead of leaving
    /// unmatched rows at Expenses:Unknown. Can also be set per-importer in
    /// importers.toml via `use_merchant_dict = true`.
    #[arg(long)]
    pub use_merchant_dict: bool,

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

/// Resolve which config entry applies to `filename`, by the one rule.
///
/// `--importer <name>` wins; otherwise a `filename_pattern` glob, with the
/// long-standing fallbacks: exactly one match uses it, no match with exactly
/// one importer defined uses that, no match with several is an error, and
/// several matches is an error.
///
/// Extracted because it existed twice — once inline in the `--config` branch,
/// once re-implemented in [`maybe_preprocess`] — and the copies disagreed:
/// the preprocess copy had no single-importer fallback and took the first of
/// several matches instead of reporting the ambiguity. Two resolvers meant the
/// entry that RAN a command could differ from the entry that then extracted.
fn resolve_config_entry<'a>(
    args: &Args,
    importers_file: &'a ImportersFile,
    filename: &str,
) -> Result<Option<&'a rustledger_importer::toml_entry::ImporterEntry>> {
    if let Some(ref name) = args.importer {
        return Ok(importers_file.importers.iter().find(|e| e.name == *name));
    }
    if importers_file.importers.is_empty() {
        return Ok(None);
    }
    let matches = find_matching_importers(importers_file, filename);
    match matches.len() {
        1 => Ok(Some(matches[0])),
        0 if importers_file.importers.len() == 1 => Ok(Some(&importers_file.importers[0])),
        0 => {
            let available: Vec<&str> = importers_file
                .importers
                .iter()
                .map(|e| e.name.as_str())
                .collect();
            Err(anyhow!(
                "No importer matches file '{}'. Use --importer to select one: {}",
                filename,
                available.join(", ")
            ))
        }
        _ => {
            let names: Vec<&str> = matches.iter().map(|e| e.name.as_str()).collect();
            Err(anyhow!(
                "Multiple importers match file '{}': {}. Use --importer to select one.",
                filename,
                names.join(", ")
            ))
        }
    }
}

/// Run the resolved config entry's external `preprocess` command, if any.
///
/// The entry is resolved the same way the CSV config branch resolves it —
/// by `--importer` name, else by `filename_pattern` glob — from the same
/// config file. Returns a temp file (with a `.csv` suffix so extension
/// dispatch lands on the CSV importer) holding the command's stdout, or
/// `None` when no entry with `preprocess` applies. Any `{input}` argument
/// is replaced with the statement path; a missing placeholder is fine for
/// commands that read their input elsewhere.
///
/// Trust model: this executes a command from the config, so it is honored
/// ONLY when the config is the user's own — named with `--config`, or found
/// in the user config directory. A `./importers.toml` discovered by looking
/// around the current directory is IGNORED for this field, with a warning.
///
/// The difference matters more than the "same as a shell alias" framing
/// suggested. A shell alias lives in your dotfiles; a cwd-discovered config
/// belongs to whoever put a file in that directory — an unzipped statement
/// bundle, a cloned repo, a shared downloads folder. Otherwise
/// `rledger extract statement.csv` would execute an arbitrary command
/// because of where the terminal happened to be. This is the boundary
/// `direnv` requires an explicit `allow` for.
/// Replaced with the statement's path in each `preprocess` argument.
///
/// Named rather than inlined: `{input}` inside a call trips clippy's
/// `literal_string_with_formatting_args`.
const INPUT_PLACEHOLDER: &str = "{input}";

/// Shells whose `-c` argument is a COMMAND STRING, not a filename.
///
/// Splicing a path into one of those is command injection, because the shell
/// re-parses it: `a;touch PWNED;b.pdf` is three commands. The filename is not
/// under the config author's control — importing files you downloaded is the
/// whole point of this feature — so the config being trusted says nothing
/// about the path being safe.
const SHELLS: &[&str] = &[
    "sh", "bash", "zsh", "dash", "ksh", "ash", "fish", "csh", "tcsh",
];

/// Reject `{input}` spliced INTO a shell command string.
///
/// `["pdftotext", "-layout", "{input}", "-"]` is safe: there is no shell, and
/// the placeholder is a whole argv element, so the path arrives as one
/// argument whatever it contains.
///
/// `["sh", "-c", "pdftotext {input} - | to-csv"]` is not: `sh -c` parses its
/// argument as source. Verified — a file named `a;touch PWNED;b.pdf` creates
/// `PWNED`, with a config that is entirely the user's own, so every provenance
/// gate in this module passes and the command still runs.
///
/// Refusing rather than warning: this is stderr in the middle of a batch
/// import, the failure is silent when it works and catastrophic when it does
/// not, and the remedy is one line. The feature has never shipped, so nothing
/// is being broken.
///
/// `{input}` as its own argv element is still allowed after a shell, which is
/// what makes the positional form work: `sh -c '… "$1" …' _ {input}` puts the
/// path in `$1`, where the shell never re-parses it.
fn reject_shell_splice(program: &str, argv: &[String]) -> Result<()> {
    let base = Path::new(program)
        .file_name()
        .map_or(program, |f| f.to_str().unwrap_or(program));
    if !SHELLS.contains(&base) {
        return Ok(());
    }
    // A whole-element `{input}` is the safe form; only EMBEDDED placeholders
    // end up inside something the shell re-parses.
    let Some(bad) = argv
        .iter()
        .find(|a| a.contains(INPUT_PLACEHOLDER) && a.trim() != INPUT_PLACEHOLDER)
    else {
        return Ok(());
    };
    Err(anyhow!(
        "`preprocess` splices {INPUT_PLACEHOLDER} into a `{base}` command string, \
         which is command injection: the shell re-parses the statement's \
         filename, and a file named `a;rm -rf ~;b.pdf` would run `rm`.\n\
         \n\
         Found: {bad:?}\n\
         \n\
         Pass the path as a positional argument instead, so the shell never \
         re-parses it:\n\
         \n    preprocess = [\"{base}\", \"-c\", \"… \\\"$1\\\" …\", \"_\", \"{INPUT_PLACEHOLDER}\"]\n\
         \n\
         Or drop the shell entirely — {INPUT_PLACEHOLDER} as its own argv \
         element is always safe:\n\
         \n    preprocess = [\"pdftotext\", \"-layout\", \"{INPUT_PLACEHOLDER}\", \"-\"]"
    ))
}

/// Which `preprocess` argv applies to `file`, if any.
///
/// Split out of [`maybe_preprocess`] so that config discovery — the fallible
/// part — can be made TOLERANT for a config the user never pointed at, while
/// failures from actually running the command always propagate.
fn resolve_preprocess_argv(args: &Args, file: &Path) -> Result<Option<Vec<String>>> {
    let Some((config_path, source)) = find_importers_config_with_source(args.config.as_deref())?
    else {
        return Ok(None);
    };
    let importers_file = load_importers_config(&config_path)?;

    // An EARLY-OUT, not a guard — say so, because the difference matters to
    // whoever reads this next. Almost no importers.toml declares `preprocess`,
    // and this skips resolving an entry on every extract run that cannot
    // possibly need one.
    //
    // It is deliberately NOT what keeps `--auto` working: sabotaging it away
    // fails no test, because the silencing in `maybe_preprocess` already
    // covers every case this does. Anyone tempted to lean on it for
    // correctness should lean on that instead.
    if !importers_file
        .importers
        .iter()
        .any(|e| e.preprocess.is_some())
    {
        return Ok(None);
    }

    let filename = file
        .file_name()
        .map(|f| f.to_string_lossy().to_string())
        .unwrap_or_default();

    // ONE resolver, shared with the `--config` branch below, so the entry that
    // preprocesses is by construction the entry that then extracts. Resolving
    // it separately here meant this path had no single-importer fallback and
    // ran the command on the FIRST of several matches, before the other branch
    // reported the ambiguity — a side effect ahead of an error.
    let entry = resolve_config_entry(args, &importers_file, &filename)?;
    let Some(argv) = entry.and_then(|e| e.preprocess.as_ref()) else {
        return Ok(None);
    };

    if source == ConfigSource::CurrentDirectory {
        eprintln!(
            "warning: ignoring `preprocess` in {} — a config found in the \
             current directory is not run. Pass it with --config if it is \
             yours.",
            config_path.display()
        );
        return Ok(None);
    }
    Ok(Some(argv.clone()))
}

/// Run the resolved config entry's external `preprocess` command, if any.
///
/// The entry is resolved the same way the CSV config branch resolves it —
/// by `--importer` name, else by `filename_pattern` glob — from the same
/// config file. Returns a temp file (with a `.csv` suffix so extension
/// dispatch lands on the CSV importer) holding the command's stdout, or
/// `None` when no entry with `preprocess` applies. Any `{input}` argument
/// is replaced with the statement path; a missing placeholder is fine for
/// commands that read their input elsewhere.
///
/// Trust model: this executes a command from the config, so it is honored
/// ONLY when the config is the user's own — named with `--config`, or found
/// in the user config directory. A `./importers.toml` discovered by looking
/// around the current directory is IGNORED for this field, with a warning.
///
/// The difference matters more than the "same as a shell alias" framing
/// suggested. A shell alias lives in your dotfiles; a cwd-discovered config
/// belongs to whoever put a file in that directory — an unzipped statement
/// bundle, a cloned repo, a shared downloads folder. Otherwise
/// `rledger extract statement.csv` would execute an arbitrary command
/// because of where the terminal happened to be. This is the boundary
/// `direnv` requires an explicit `allow` for.
///
/// Discovery never reports its own errors. `--auto` and the raw-argument path
/// build their config without reading importers.toml at all, so a broken or
/// ambiguous file lying around must not fail them — before this split, the mere
/// presence of one did. Paths that DO use a config re-load it below and report
/// the same error from there.
fn maybe_preprocess(args: &Args, file: &Path) -> Result<Option<tempfile::NamedTempFile>> {
    // A config problem discovered HERE is never reported here.
    //
    // Not swallowing it: every path that actually uses a config loads and
    // resolves it again in the branch below, and reports the identical error
    // from there. Reporting it from preprocessing only adds the case where a
    // path that does NOT use a config — `--auto`, raw arguments — is failed by
    // a file it would never have read.
    //
    // This started life as `if !(args.config.is_some() || args.importer.is_some())`,
    // on the theory that a user who named a config should hear about it.
    // Sabotaging the condition showed it changed nothing observable: with the
    // guard made unconditional, `--config broken.toml` still errors, from the
    // branch below. A condition whose removal no test can detect is complexity
    // pretending to be caution.
    let argv = match resolve_preprocess_argv(args, file) {
        Ok(Some(argv)) => argv,
        Ok(None) | Err(_) => return Ok(None),
    };

    let [program, rest @ ..] = argv.as_slice() else {
        return Err(anyhow!("`preprocess` must name a command"));
    };
    reject_shell_splice(program, rest)?;

    let input = file.to_string_lossy();
    let cmd_args: Vec<String> = rest
        .iter()
        .map(|a| a.replace(INPUT_PLACEHOLDER, &input))
        .collect();
    eprintln!("Preprocessing with: {program} {}", cmd_args.join(" "));
    let tmp = tempfile::Builder::new()
        .prefix("rledger-preprocess-")
        .suffix(".csv")
        .tempfile()
        .context("failed to create preprocess temp file")?;

    // stdout goes STRAIGHT to the temp file. `Command::output()` buffered the
    // whole of it in memory first and then copied it back out — two full
    // copies of a statement that can be large once a PDF is flattened to text.
    // stderr is still captured, because it is only read to build an error.
    let stdout = tmp
        .reopen()
        .context("failed to open preprocess temp file for writing")?;
    let output = std::process::Command::new(program)
        .args(&cmd_args)
        .stdin(std::process::Stdio::null())
        .stdout(stdout)
        .stderr(std::process::Stdio::piped())
        .output()
        .with_context(|| format!("failed to run preprocess command `{program}`"))?;
    if !output.status.success() {
        return Err(anyhow!(
            "preprocess command `{program}` failed ({}): {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(Some(tmp))
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

fn importers_config_not_found_message() -> anyhow::Error {
    let user_path = crate::config::user_config_file("importers.toml").map_or_else(
        || "the user config directory".to_string(),
        |p| p.display().to_string(),
    );
    anyhow!("No importers.toml found. Create one in the current directory or at {user_path}")
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
/// (cwd `importers.toml` then the user config directory).
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

// `parse_amount_locale` moved to `rustledger_importer::toml_entry` (the
// canonical config-schema module, shared with the WASI component).
use rustledger_importer::toml_entry::parse_amount_locale;

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
    // External preprocessing (PDF etc.): if the resolved config entry
    // declares `preprocess`, run it FIRST and hand the rest of the
    // pipeline a temp .csv holding its stdout — so `--auto` inference,
    // dispatch, and column mapping all operate on the preprocessed
    // content unchanged. The binding keeps the temp file alive to EOF.
    let preprocessed = maybe_preprocess(args, file)?;
    // `source_file` keeps the name the user typed; `file` becomes the
    // preprocessed CONTENT. Rebinding both to the temp path meant
    // auto-identification matched `filename_pattern` against
    // `rledger-preprocess-XXXX.csv` — so `*.pdf` never matched, and a config
    // with more than one importer failed with an error naming a temp file the
    // user never saw, AFTER the command had already run. One importer hid it
    // via the single-importer fallback.
    let source_file: &Path = file;
    let file: &Path = preprocessed
        .as_ref()
        .map_or(file, tempfile::NamedTempFile::path);

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
                .ok_or_else(importers_config_not_found_message)?;

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
                .ok_or_else(importers_config_not_found_message)?;

            let importers_file = load_importers_config(&config_path)?;

            if importers_file.importers.is_empty() {
                return Err(anyhow!("No importers defined in {}", config_path.display()));
            }

            // Auto-identify from the name the USER gave, not the temp file a
            // preprocess step may have produced.
            let filename = source_file
                .file_name()
                .map(|s| s.to_string_lossy())
                .unwrap_or_default();
            let entry =
                resolve_config_entry(args, &importers_file, &filename)?.ok_or_else(|| {
                    anyhow!("No importer matches file '{filename}'. Use --importer to select one.")
                })?;

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
            if args.use_merchant_dict {
                csv_config.use_merchant_dict = true;
            }
            // An explicit --amount-locale / --amount-format overrides the
            // separator locale inferred from the data. Report the *effective*
            // locale (override if given, otherwise the inferred one) so the
            // printed summary matches what's actually used.
            if let Some(locale) = &args.amount_locale {
                let locale = parse_amount_locale(locale)?;
                csv_config.amount_locale = Some(locale);
                eprintln!("  amount_locale: {locale:?} (from --amount-locale)");
            } else if let Some(locale) = inferred.amount_locale {
                eprintln!("  amount_locale: {locale:?} (inferred)");
            }
            if let Some(format) = &args.amount_format {
                csv_config.amount_format = Some(format.clone());
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
                .date_format(&args.date_format)
                .delimiter(args.delimiter)
                .skip_rows(args.skip_rows)
                .invert_sign(args.invert_sign)
                .skip_zero_amounts(!args.include_zero_amounts)
                .has_header(!args.no_header)
                .use_merchant_dict(args.use_merchant_dict);

            // Column flags accept either a header name or a 0-based index (see
            // `apply_column`), so headerless CSVs can be imported positionally.
            builder = apply_column(
                builder,
                &args.date_column,
                CsvConfigBuilder::date_column_index,
                |b, n| b.date_column(n),
            );
            builder = apply_column(
                builder,
                &args.narration_column,
                CsvConfigBuilder::narration_column_index,
                |b, n| b.narration_column(n),
            );
            builder = apply_column(
                builder,
                &args.amount_column,
                CsvConfigBuilder::amount_column_index,
                |b, n| b.amount_column(n),
            );

            if let Some(payee) = &args.payee_column {
                builder = apply_column(
                    builder,
                    payee,
                    CsvConfigBuilder::payee_column_index,
                    |b, n| b.payee_column(n),
                );
            }

            if let Some(currency_col) = &args.currency_column {
                builder = apply_column(
                    builder,
                    currency_col,
                    CsvConfigBuilder::currency_column_index,
                    |b, n| b.currency_column(n),
                );
            }

            if let Some(debit) = &args.debit_column {
                builder = builder.debit_column(debit);
            }

            if let Some(credit) = &args.credit_column {
                builder = builder.credit_column(credit);
            }

            if let Some(locale) = &args.amount_locale {
                builder = builder.amount_locale(parse_amount_locale(locale)?);
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

    // Fail loudly when the importer produced no transactions — before
    // duplicate filtering (`--existing`) or `--balance` augmentation, either of
    // which would otherwise mask the real cause (all-duplicates, or a lone
    // balance directive with zero transactions). A garbage / wrong-type /
    // empty file otherwise makes a scripted `extract … >> ledger.beancount`
    // silently append nothing and still exit 0.
    let extracted_txns = result
        .directives
        .iter()
        .filter(|d| matches!(d, Directive::Transaction(_)))
        .count();
    if extracted_txns == 0 {
        anyhow::bail!(
            "no transactions were extracted from {}\n  \
             the file may not match a recognized importer format, be empty, or \
             use unexpected columns\n  \
             try: --auto, an explicit importer (--importer), or column flags \
             (--date-column, --amount-column, …)",
            file.display()
        );
    }

    // Filter duplicates if --existing is specified, and optionally apply
    // ML-based account suggestions for transactions the rules engine left
    // pointing at a fallback account.
    let directives = if let Some(ref existing_path) = args.existing {
        let existing_txns = load_existing_transactions(existing_path)?;
        let before_count = result.directives.len();
        // Build the dedup config once, not once per filtered directive.
        let dedup_config = rustledger_ops::dedup::FuzzyDedupConfig::default();
        let mut filtered: Vec<_> = result
            .directives
            .into_iter()
            .filter(|d| {
                if let Directive::Transaction(txn) = d {
                    !rustledger_ops::dedup::is_duplicate(txn, &existing_txns, &dedup_config)
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
        let date_str = args
            .balance_date
            .clone()
            .unwrap_or_else(|| jiff::Zoned::now().date().to_string());
        let date = date_str
            .parse::<rustledger_core::NaiveDate>()
            .with_context(|| format!("Invalid balance date: {date_str}"))?;

        let balance = rustledger_ops::reconcile::StatementBalance {
            date,
            account: args.account.clone(),
            number: amount,
            currency: args.currency.clone(),
        };
        // `create_balance_directive` returns a core `Directive` directly now — no
        // `DirectiveWrapper` round-trip through `wrapper_to_directive`.
        let balance_directive = rustledger_ops::reconcile::create_balance_directive(&balance);

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

    let written_txns = directives
        .iter()
        .filter(|d| matches!(d, Directive::Transaction(_)))
        .count();
    eprintln!(
        "Extracted {written_txns} transactions from {}",
        file.display()
    );

    Ok(())
}

#[cfg(test)]
mod tests {
    /// Serializes the tests that must run from a particular directory.
    ///
    /// `std::env::set_current_dir` is PROCESS-global and cargo runs tests on
    /// threads, so two of these interleaving means one test's `rledger` looks
    /// for `importers.toml` in the other's temp dir. That was already latent
    /// with a single cwd test present; adding a second made it fail about half
    /// the time. Poisoning is irrelevant here — a panicking test has already
    /// failed — so the guard is taken through `unwrap_or_else(PoisonError::into_inner)`
    /// rather than cascading one failure into unrelated ones.
    static CWD_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    /// Run `f` with the process working directory set to `dir`, restoring it
    /// afterwards even if `f` panics.
    fn with_cwd<T>(dir: &Path, f: impl FnOnce() -> T) -> T {
        let _guard = CWD_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let prev = std::env::current_dir().expect("a working directory");
        std::env::set_current_dir(dir).expect("can enter the temp dir");
        // `AssertUnwindSafe`: the only captured state is the temp dir, and the
        // cwd is restored before the panic is resumed.
        let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        std::env::set_current_dir(prev).expect("can return");
        match out {
            Ok(v) => v,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    use super::*;
    use rustledger_importer::config::ImporterType;
    use rustledger_importer::toml_entry::{ImporterEntry, parse_column_value};
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

    /// Auto-identification must match the name the USER gave, not the temp
    /// file preprocessing produced.
    ///
    /// The `--importer` path hid this: rebinding `file` to the temp
    /// `rledger-preprocess-XXXX.csv` meant `filename_pattern = "*.pdf"` had
    /// nothing to match, so a config with MORE THAN ONE importer failed with
    /// "No importer matches file 'rledger-preprocess-…csv'" — naming a file
    /// the user never saw, after the command had already run. A single-importer
    /// config passed anyway via the no-match fallback, which is why the
    /// original test did not catch it.
    ///
    /// Two importers here on purpose: one is the shape that passes regardless.
    #[cfg(unix)]
    #[test]
    fn test_preprocess_auto_identifies_by_the_original_filename() {
        use clap::Parser;
        let dir = tempfile::tempdir().unwrap();
        let pdf = dir.path().join("statement.pdf");
        std::fs::write(&pdf, "Date,Description,Amount\n2026-07-01,Coffee,-4.50\n").unwrap();
        let config = dir.path().join("importers.toml");
        std::fs::write(
            &config,
            r#"
[[importers]]
name = "csv-bank"
filename_pattern = "*.csv"
account = "Assets:Other"
date_column = "Date"
narration_column = "Description"
amount_column = "Amount"

[[importers]]
name = "pdf-bank"
filename_pattern = "*.pdf"
account = "Assets:Bank"
date_column = "Date"
narration_column = "Description"
amount_column = "Amount"
preprocess = ["cat", "{input}"]
"#,
        )
        .unwrap();

        // No --importer: identification must come from the *.pdf pattern.
        let args = Args::parse_from([
            "extract",
            "--config",
            config.to_str().unwrap(),
            pdf.to_str().unwrap(),
        ]);
        let mut out = Vec::new();
        run_with_writer(&args, &pdf, &mut out).expect("auto-identifies the pdf profile");
        let text = String::from_utf8(out).unwrap();
        assert!(
            text.contains("Assets:Bank"),
            "expected the pdf profile's account, got:\n{text}"
        );
    }

    /// A config found by looking around the CURRENT DIRECTORY must not run
    /// its `preprocess` command.
    ///
    /// Otherwise `rledger extract statement.csv` executes whatever an
    /// `importers.toml` in that directory says — an unzipped bundle, a cloned
    /// repo, a shared downloads folder. The entry is still usable for
    /// declaring columns; only the exec is withheld.
    ///
    /// The command writes a marker file, so the assertion is that it did not
    /// RUN, not merely that output looked unchanged.
    #[cfg(unix)]
    #[test]
    fn test_preprocess_is_ignored_from_a_cwd_discovered_config() {
        use clap::Parser;
        let dir = tempfile::tempdir().unwrap();
        let marker = dir.path().join("EXECUTED");
        let csv = dir.path().join("statement.csv");
        std::fs::write(&csv, "Date,Description,Amount\n2026-07-01,Coffee,-4.50\n").unwrap();
        std::fs::write(
            dir.path().join("importers.toml"),
            format!(
                r#"
[[importers]]
name = "hostile"
filename_pattern = "*"
account = "Assets:Bank"
date_column = "Date"
narration_column = "Description"
amount_column = "Amount"
preprocess = ["touch", "{}"]
"#,
                marker.display()
            ),
        )
        .unwrap();

        // No --config: discovery has to find it in the current directory.
        let args = Args::parse_from(["extract", csv.to_str().unwrap()]);
        let mut out = Vec::new();
        let _ = with_cwd(dir.path(), || run_with_writer(&args, &csv, &mut out));

        assert!(
            !marker.exists(),
            "a cwd-discovered config executed its preprocess command",
        );
    }

    /// The external `preprocess` hook end-to-end: a `.pdf`-named input is
    /// imported by running the entry's command (here `cat`, standing in
    /// for pdftotext|table-to-csv) and feeding its stdout through the
    /// normal CSV pipeline — the flow that makes PDF statements importable
    /// before a native parser exists.
    #[cfg(unix)]
    #[test]
    fn test_preprocess_makes_pdf_named_input_importable() {
        use clap::Parser;
        let dir = tempfile::tempdir().unwrap();
        let pdf = dir.path().join("statement.pdf");
        std::fs::write(&pdf, "Date,Description,Amount\n2026-07-01,Coffee,-4.50\n").unwrap();
        let config = dir.path().join("importers.toml");
        std::fs::write(
            &config,
            r#"
[[importers]]
name = "pdf-bank"
filename_pattern = "*.pdf"
account = "Assets:Bank"
date_column = "Date"
narration_column = "Description"
amount_column = "Amount"
preprocess = ["cat", "{input}"]
"#,
        )
        .unwrap();

        let args = Args::parse_from([
            "extract",
            "--config",
            config.to_str().unwrap(),
            "--importer",
            "pdf-bank",
            pdf.to_str().unwrap(),
        ]);
        let mut out = Vec::new();
        run_with_writer(&args, &pdf, &mut out).unwrap();
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("Coffee"), "row not imported: {text}");
        assert!(text.contains("Assets:Bank"), "account missing: {text}");
    }

    /// `{input}` spliced into a shell command string is REFUSED.
    ///
    /// This was the shape the docs recommended. `sh -c` parses its argument as
    /// source, so the statement's filename is re-parsed — and the filename is
    /// not the config author's, which is what makes the provenance gates above
    /// insufficient on their own.
    ///
    /// The assertion is that the marker file was NOT created, not merely that
    /// the command errored: a command can fail after the injected part ran.
    /// Verified against the unfixed version, where `PWNED` appears.
    #[cfg(unix)]
    #[test]
    fn test_preprocess_refuses_a_filename_spliced_into_a_shell() {
        use clap::Parser;
        let dir = tempfile::tempdir().unwrap();
        // A filename carrying shell metacharacters — an attacker-chosen name in
        // a downloads folder or an unzipped statement bundle. Relative, run
        // from inside the temp dir, so the injected `touch` has no path to
        // resolve and the marker lands where we can see it.
        let name = "a;touch PWNED;b.pdf";
        let hostile = dir.path().join(name);
        let marker = dir.path().join("PWNED");
        std::fs::write(
            &hostile,
            "Date,Description,Amount\n2026-07-01,Coffee,-4.50\n",
        )
        .unwrap();
        let config = dir.path().join("importers.toml");
        std::fs::write(
            &config,
            "[[importers]]\nname = \"pdf\"\nfilename_pattern = \"*.pdf\"\n\
             account = \"Assets:Bank\"\ndate_column = \"Date\"\n\
             narration_column = \"Description\"\namount_column = \"Amount\"\n\
             preprocess = [\"sh\", \"-c\", \"cat {input}\"]\n",
        )
        .unwrap();

        let args = Args::parse_from([
            "extract",
            "--config",
            config.to_str().unwrap(),
            hostile.to_str().unwrap(),
        ]);
        let mut out = Vec::new();
        let result = with_cwd(dir.path(), || run_with_writer(&args, &hostile, &mut out));

        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("command injection"),
            "expected the splice to be refused, got: {err}"
        );
        assert!(!marker.exists(), "the injected command ran");
    }

    /// The POSITIONAL form is allowed, and works on the same hostile name.
    ///
    /// Pinning the escape hatch as well as the refusal: a check that rejected
    /// every shell would push users back to unquoted splicing somewhere else.
    #[cfg(unix)]
    #[test]
    fn test_preprocess_allows_a_shell_when_the_path_is_positional() {
        use clap::Parser;
        let dir = tempfile::tempdir().unwrap();
        let name = "a;touch PWNED;b.pdf";
        let hostile = dir.path().join(name);
        let marker = dir.path().join("PWNED");
        std::fs::write(
            &hostile,
            "Date,Description,Amount\n2026-07-01,Coffee,-4.50\n",
        )
        .unwrap();
        let config = dir.path().join("importers.toml");
        std::fs::write(
            &config,
            "[[importers]]\nname = \"pdf\"\nfilename_pattern = \"*.pdf\"\n\
             account = \"Assets:Bank\"\ndate_column = \"Date\"\n\
             narration_column = \"Description\"\namount_column = \"Amount\"\n\
             preprocess = [\"sh\", \"-c\", \"cat \\\"$1\\\"\", \"_\", \"{input}\"]\n",
        )
        .unwrap();

        let args = Args::parse_from([
            "extract",
            "--config",
            config.to_str().unwrap(),
            hostile.to_str().unwrap(),
        ]);
        let mut out = Vec::new();
        let result = with_cwd(dir.path(), || run_with_writer(&args, &hostile, &mut out));

        result.expect("the positional form is allowed");
        let text = String::from_utf8(out).unwrap();
        assert!(text.contains("Coffee"), "row not imported: {text}");
        assert!(!marker.exists(), "the positional form still injected");
    }

    /// `--auto` must not be failed by a config it never consults.
    ///
    /// `--auto` and the raw-argument path build their config without reading
    /// importers.toml at all. Preprocessing resolved an entry up front, and
    /// resolution reports an ambiguous config as an ERROR — so merely having
    /// two matching importers in the current directory aborted a command that
    /// would never have looked at them.
    ///
    /// Neither entry declares `preprocess`, which is the point: nothing here
    /// is even a candidate for preprocessing.
    ///
    /// Two mechanisms independently keep this green — the
    /// declares-`preprocess` gate skips resolution entirely, and discovery
    /// errors are tolerated for a config the user never pointed at — so
    /// removing either ALONE still passes. That is deliberate depth, not a
    /// vacuous test: it fails with both removed. The sibling below isolates
    /// the tolerance, which is the load-bearing one.
    #[cfg(unix)]
    #[test]
    fn test_auto_is_not_failed_by_an_ambiguous_config_it_never_reads() {
        use clap::Parser;
        let dir = tempfile::tempdir().unwrap();
        let csv = dir.path().join("statement.csv");
        std::fs::write(&csv, "Date,Description,Amount\n2026-07-01,Coffee,-4.50\n").unwrap();
        std::fs::write(
            dir.path().join("importers.toml"),
            "[[importers]]\nname = \"a\"\nfilename_pattern = \"*.csv\"\n\
             account = \"Assets:A\"\ndate_column = \"Date\"\n\
             narration_column = \"Description\"\namount_column = \"Amount\"\n\
             [[importers]]\nname = \"b\"\nfilename_pattern = \"statement*\"\n\
             account = \"Assets:B\"\ndate_column = \"Date\"\n\
             narration_column = \"Description\"\namount_column = \"Amount\"\n",
        )
        .unwrap();

        let args = Args::parse_from(["extract", "--auto", csv.to_str().unwrap()]);
        let mut out = Vec::new();
        let result = with_cwd(dir.path(), || run_with_writer(&args, &csv, &mut out));

        result.expect("--auto must not read the ambiguous config at all");
        assert!(String::from_utf8(out).unwrap().contains("Coffee"));
    }

    /// A config that cannot even be PARSED must not fail `--auto` either.
    ///
    /// This isolates the tolerance. The declares-`preprocess` gate cannot help
    /// here — the file fails to load before anything can be inspected — so the
    /// only thing keeping `--auto` working is that a config the user never
    /// pointed at is not allowed to fail a command that would not have read
    /// it. Remove that and this test fails on its own.
    #[cfg(unix)]
    #[test]
    fn test_auto_is_not_failed_by_an_unparsable_config_it_never_reads() {
        use clap::Parser;
        let dir = tempfile::tempdir().unwrap();
        let csv = dir.path().join("statement.csv");
        std::fs::write(&csv, "Date,Description,Amount\n2026-07-01,Tea,-3.00\n").unwrap();
        std::fs::write(dir.path().join("importers.toml"), "not = [valid\n").unwrap();

        let args = Args::parse_from(["extract", "--auto", csv.to_str().unwrap()]);
        let mut out = Vec::new();
        let result = with_cwd(dir.path(), || run_with_writer(&args, &csv, &mut out));

        result.expect("--auto must not be failed by an unparsable config");
        assert!(String::from_utf8(out).unwrap().contains("Tea"));
    }

    /// A config the user POINTED AT still reports its own errors.
    ///
    /// Pins the end-to-end guarantee, and deliberately not a guard for the
    /// silencing in `maybe_preprocess`: the `--config` branch loads the file
    /// again and errors from there, so this stays green however that silencing
    /// is written. That is exactly what made the original
    /// `user_asked_for_config` condition removable — no test could tell the
    /// difference, because the error never depended on it.
    #[test]
    fn test_an_explicitly_named_config_still_reports_its_errors() {
        use clap::Parser;
        let dir = tempfile::tempdir().unwrap();
        let csv = dir.path().join("statement.csv");
        std::fs::write(&csv, "Date,Description,Amount\n2026-07-01,Tea,-3.00\n").unwrap();
        let config = dir.path().join("broken.toml");
        std::fs::write(&config, "not = [valid\n").unwrap();

        let args = Args::parse_from([
            "extract",
            "--config",
            config.to_str().unwrap(),
            csv.to_str().unwrap(),
        ]);
        let mut out = Vec::new();
        let err = run_with_writer(&args, &csv, &mut out).unwrap_err();
        assert!(
            err.to_string().contains("parse importers config"),
            "a named config must report its own parse error, got: {err}"
        );
    }

    /// A failing preprocess command surfaces its stderr, not a CSV error.
    #[cfg(unix)]
    #[test]
    fn test_preprocess_failure_reports_command_error() {
        use clap::Parser;
        let dir = tempfile::tempdir().unwrap();
        let pdf = dir.path().join("statement.pdf");
        std::fs::write(&pdf, "x").unwrap();
        let config = dir.path().join("importers.toml");
        std::fs::write(
            &config,
            "[[importers]]\nname = \"bad\"\nfilename_pattern = \"*.pdf\"\npreprocess = [\"false\"]\n",
        )
        .unwrap();

        let args = Args::parse_from([
            "extract",
            "--config",
            config.to_str().unwrap(),
            "--importer",
            "bad",
            pdf.to_str().unwrap(),
        ]);
        let mut out = Vec::new();
        let err = run_with_writer(&args, &pdf, &mut out).unwrap_err();
        assert!(err.to_string().contains("preprocess command"), "{err}");
    }

    #[test]
    fn test_cli_numeric_column_args_extract_by_index() {
        // Regression: numeric --date-column/--amount-column/--payee-column
        // values are treated as 0-based indices (flags documented as "name or
        // index"), so a headerless CSV imports instead of every row being
        // dropped because no header matches "0"/"1"/"2".
        use clap::Parser;
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("noheader.csv");
        std::fs::write(&path, "2024-01-15,Coffee,-5.00\n2024-01-16,Lunch,-12.00\n").unwrap();

        let args = Args::parse_from([
            "extract",
            "--no-header",
            "--date-column",
            "0",
            "--payee-column",
            "1",
            "--amount-column",
            "2",
            path.to_str().unwrap(),
        ]);
        let mut out = Vec::new();
        run_with_writer(&args, &path, &mut out).unwrap();
        let text = String::from_utf8(out).unwrap();

        assert!(text.contains("Coffee"), "first row not imported: {text}");
        assert!(text.contains("-5.00"), "first amount missing: {text}");
        assert!(text.contains("Lunch"), "second row not imported: {text}");
        assert_eq!(
            text.matches("2024-01-").count(),
            2,
            "both rows should import via positional indices: {text}"
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
            currency_column: None,
            debit_column: None,
            credit_column: None,
            secondary_date_column: None,
            secondary_date_format: None,
            secondary_date_key: None,
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
            use_merchant_dict: None,
            preprocess: None,
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
            currency_column: None,
            debit_column: None,
            credit_column: None,
            secondary_date_column: None,
            secondary_date_format: None,
            secondary_date_key: None,
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
            use_merchant_dict: None,
            preprocess: None,
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
            currency_column: None,
            debit_column: None,
            credit_column: None,
            secondary_date_column: None,
            secondary_date_format: None,
            secondary_date_key: None,
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
            use_merchant_dict: None,
            preprocess: None,
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
            currency_column: None,
            debit_column: Some(toml::Value::String("Debit".to_string())),
            credit_column: Some(toml::Value::String("Credit".to_string())),
            secondary_date_column: Some("Settle Date".to_string()),
            secondary_date_format: None,
            secondary_date_key: None,
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
            use_merchant_dict: None,
            preprocess: None,
        };

        let config = build_config_from_entry(&entry).unwrap();
        assert_eq!(config.currency, Some("GBP".to_string()));
        let ImporterType::Csv(csv_config) = &config.importer_type;
        assert_eq!(csv_config.delimiter, ';');
        assert_eq!(csv_config.skip_rows, 2);
        assert!(!csv_config.has_header); // skip_header=true → has_header=false
        assert!(csv_config.invert_sign);
        // Secondary date: format defaults to date_format, key to a column slug.
        let sd = csv_config
            .secondary_date
            .as_ref()
            .expect("secondary_date_column should produce a secondary date");
        assert_eq!(sd.format, "%d/%m/%Y");
        assert_eq!(sd.meta_key, "settle_date");
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
        // No --config provided, no importers.toml in cwd/user config dir → empty
        // scan dirs, no error. This is the right behavior because
        // the user didn't ask for any config; absence is expected.
        let args = Args::parse_from(["extract"]);
        let dirs = resolve_scan_dirs(&args).expect("implicit missing is soft-fail");
        // Could be empty or non-empty depending on whether a real
        // user importers.toml exists in this test env.
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
    fn test_load_existing_resolves_includes_and_interpolates() {
        // Regression: a raw parse only saw the top file and left elided amounts
        // as None. Routing through the loader pipeline makes `include`d
        // transactions visible AND fills the interpolated amount — both needed so
        // dedup compares against the user's real (resolved, booked) ledger.
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("sub.beancount"),
            "2024-02-01 * \"PHONE BILL\" \"Monthly\"\n  \
             Assets:Bank:Checking  -40.00 USD\n  Expenses:Phone\n",
        )
        .unwrap();
        let main_path = dir.path().join("main.beancount");
        std::fs::write(
            &main_path,
            "include \"sub.beancount\"\n\n2024-01-15 * \"GROCERY STORE\" \"Weekly\"\n  \
             Assets:Bank:Checking  -50.00 USD\n  Expenses:Food          50.00 USD\n",
        )
        .unwrap();

        let txns = load_existing_transactions(&main_path).unwrap();
        // The INCLUDED transaction is visible (a raw parse missed it entirely).
        assert_eq!(txns.len(), 2, "included transaction must be loaded");
        let phone = txns
            .iter()
            .find(|t| t.narration.as_str() == "Monthly")
            .expect("included PHONE BILL transaction must be present");
        // Its elided `Expenses:Phone` posting was interpolated (raw parse: None).
        let amount = phone
            .postings
            .iter()
            .find(|p| p.account.as_str() == "Expenses:Phone")
            .and_then(|p| p.units.as_ref())
            .and_then(rustledger_core::IncompleteAmount::number);
        assert_eq!(
            amount,
            Some("40.00".parse::<rust_decimal::Decimal>().unwrap()),
            "elided posting must be interpolated by booking",
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
