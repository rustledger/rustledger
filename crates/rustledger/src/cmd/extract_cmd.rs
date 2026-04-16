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

use crate::cmd::completions::ShellType;
use anyhow::{Context, Result, anyhow};
use clap::Parser;
use format_num_pattern::Locale;
use rust_decimal::Decimal;
use rustledger_core::{Directive, FormatConfig, Transaction, format_directive};
use rustledger_importer::{Importer, ImporterConfig, OfxImporter};
use serde::Deserialize;
use std::collections::HashMap;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::str::FromStr;

/// Extract transactions from bank files.
#[derive(Parser, Debug)]
#[command(name = "extract")]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Generate shell completions and exit
    #[arg(long, value_name = "SHELL", hide = true)]
    generate_completions: Option<ShellType>,

    /// The file to extract transactions from
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,

    /// Use a named importer from importers.toml
    #[arg(long, short = 'i')]
    importer: Option<String>,

    /// Path to importers.toml configuration file
    #[arg(long, alias = "importers-config")]
    config: Option<PathBuf>,

    /// List available importers from config file and exit
    #[arg(long = "list-importers")]
    list_importers: bool,

    /// Target account for imported transactions
    #[arg(short, long, default_value = "Assets:Bank:Checking")]
    account: String,

    /// Currency for amounts (default: USD)
    #[arg(short, long, default_value = "USD")]
    currency: String,

    /// Date column name or index
    #[arg(long, default_value = "Date")]
    date_column: String,

    /// Date format (strftime-style)
    #[arg(long, default_value = "%Y-%m-%d")]
    date_format: String,

    /// Narration/description column name or index
    #[arg(long, default_value = "Description")]
    narration_column: String,

    /// Payee column name (optional)
    #[arg(long)]
    payee_column: Option<String>,

    /// Amount column name or index
    #[arg(long, default_value = "Amount")]
    amount_column: String,

    /// Locale used to parse amounts, e.g. `en_US`
    #[arg(long)]
    amount_locale: Option<String>,

    /// Custom formatting for parsing amounts.
    #[arg(long)]
    amount_format: Option<String>,

    /// Debit column (for separate debit/credit columns)
    #[arg(long)]
    debit_column: Option<String>,

    /// Credit column (for separate debit/credit columns)
    #[arg(long)]
    credit_column: Option<String>,

    /// CSV delimiter
    #[arg(long, default_value = ",")]
    delimiter: char,

    /// Number of header rows to skip
    #[arg(long, default_value = "0")]
    skip_rows: usize,

    /// Invert sign of amounts
    #[arg(long)]
    invert_sign: bool,

    /// CSV has no header row
    #[arg(long)]
    no_header: bool,

    /// Write output to a file instead of stdout
    #[arg(short, long, value_name = "FILE")]
    output: Option<PathBuf>,

    /// Existing ledger file for duplicate detection
    #[arg(long, value_name = "FILE")]
    existing: Option<PathBuf>,
}

// --- Importers TOML configuration ---

/// Top-level importers configuration file.
#[derive(Debug, Deserialize)]
struct ImportersFile {
    importers: Vec<ImporterEntry>,
}

/// A single importer entry in importers.toml.
#[derive(Debug, Deserialize)]
struct ImporterEntry {
    /// Name used to select this importer via --importer flag.
    name: String,
    /// Optional glob pattern to auto-identify this importer by filename.
    filename_pattern: Option<String>,
    /// Target account for imported transactions.
    account: Option<String>,
    /// Currency (default: USD).
    currency: Option<String>,
    /// Date column name or 0-based index.
    date_column: Option<toml::Value>,
    /// Date format (strftime-style).
    date_format: Option<String>,
    /// Narration/description column name or index.
    narration_column: Option<toml::Value>,
    /// Payee column name or index.
    payee_column: Option<toml::Value>,
    /// Amount column name or index.
    amount_column: Option<toml::Value>,
    /// Debit column name or index.
    debit_column: Option<toml::Value>,
    /// Credit column name or index.
    credit_column: Option<toml::Value>,
    /// CSV delimiter character.
    delimiter: Option<String>,
    /// Number of rows to skip.
    skip_rows: Option<usize>,
    /// Whether the CSV has a header row.
    #[serde(default)]
    skip_header: Option<bool>,
    /// Whether to invert amount signs.
    #[serde(default)]
    invert_amounts: Option<bool>,
    /// Default expense account for unmatched negative-amount (money out) transactions.
    default_expense: Option<String>,
    /// Default income account for unmatched positive-amount (money in) transactions.
    default_income: Option<String>,
    /// Account mappings: pattern → account.
    #[serde(default)]
    mappings: HashMap<String, String>,
}

/// Parse a TOML value as a column spec string (either a string name or integer index).
fn parse_column_value(value: &toml::Value) -> Option<String> {
    match value {
        toml::Value::String(s) => Some(s.clone()),
        toml::Value::Integer(i) => Some(i.to_string()),
        _ => None,
    }
}

/// Find the importers.toml file, searching in standard locations.
///
/// If an explicit path is provided via `--importers-config`, it must exist
/// or an error is returned. Otherwise, searches the current directory and
/// then `~/.config/rledger/`.
fn find_importers_config(explicit_path: Option<&Path>) -> Result<Option<PathBuf>> {
    // 1. Explicit path from --importers-config — must exist
    if let Some(path) = explicit_path {
        if path.exists() {
            return Ok(Some(path.to_path_buf()));
        }
        return Err(anyhow!("Importers config not found: {}", path.display()));
    }

    // 2. Current directory
    if let Ok(cwd) = std::env::current_dir() {
        let local = cwd.join("importers.toml");
        if local.exists() {
            return Ok(Some(local));
        }
    }

    // 3. User config directory
    if let Some(config_dir) = dirs::config_dir() {
        let user_path = config_dir.join("rledger").join("importers.toml");
        if user_path.exists() {
            return Ok(Some(user_path));
        }
    }

    Ok(None)
}

/// Load and parse an importers.toml file.
fn load_importers_config(path: &Path) -> Result<ImportersFile> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read importers config: {}", path.display()))?;
    let config: ImportersFile = toml::from_str(&content)
        .with_context(|| format!("Failed to parse importers config: {}", path.display()))?;
    Ok(config)
}

/// Build an `ImporterConfig` from a named importer entry.
fn build_config_from_entry(entry: &ImporterEntry) -> Result<ImporterConfig> {
    let mut builder = ImporterConfig::csv();

    if let Some(ref account) = entry.account {
        builder = builder.account(account);
    }

    if let Some(ref currency) = entry.currency {
        builder = builder.currency(currency);
    }

    if let Some(ref val) = entry.date_column
        && let Some(col) = parse_column_value(val)
    {
        builder = builder.date_column(&col);
    }

    if let Some(ref fmt) = entry.date_format {
        builder = builder.date_format(fmt);
    }

    if let Some(ref val) = entry.narration_column
        && let Some(col) = parse_column_value(val)
    {
        builder = builder.narration_column(&col);
    }

    if let Some(ref val) = entry.payee_column
        && let Some(col) = parse_column_value(val)
    {
        builder = builder.payee_column(&col);
    }

    if let Some(ref val) = entry.amount_column
        && let Some(col) = parse_column_value(val)
    {
        builder = builder.amount_column(&col);
    }

    if let Some(ref val) = entry.debit_column
        && let Some(col) = parse_column_value(val)
    {
        builder = builder.debit_column(&col);
    }

    if let Some(ref val) = entry.credit_column
        && let Some(col) = parse_column_value(val)
    {
        builder = builder.credit_column(&col);
    }

    if let Some(ref delim) = entry.delimiter
        && let Some(c) = delim.chars().next()
    {
        builder = builder.delimiter(c);
    }

    if let Some(skip) = entry.skip_rows {
        builder = builder.skip_rows(skip);
    }

    if let Some(skip_header) = entry.skip_header {
        builder = builder.has_header(!skip_header);
    }

    if let Some(invert) = entry.invert_amounts {
        builder = builder.invert_sign(invert);
    }

    if let Some(ref account) = entry.default_expense {
        builder = builder.default_expense(account);
    }

    if let Some(ref account) = entry.default_income {
        builder = builder.default_income(account);
    }

    if !entry.mappings.is_empty() {
        // Sort by pattern length descending so more specific patterns match first
        let mut mappings: Vec<(String, String)> = entry
            .mappings
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        mappings.sort_by_key(|a| std::cmp::Reverse(a.0.len()));
        builder = builder.mappings(mappings);
    }

    builder.build()
}

/// Main entry point with custom binary name (for bean-extract compatibility).
pub fn main_with_name(bin_name: &str) -> ExitCode {
    let args = Args::parse();

    // Handle shell completion generation
    if let Some(shell) = args.generate_completions {
        crate::cmd::completions::generate_completions::<Args>(shell, bin_name);
        return ExitCode::SUCCESS;
    }

    // Handle --list-importers
    if args.list_importers {
        return match list_importers(&args) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("error: {e:#}");
                ExitCode::from(1)
            }
        };
    }

    // File is required when not generating completions or listing importers
    let Some(ref file) = args.file else {
        eprintln!("error: FILE is required");
        eprintln!("For more information, try '--help'");
        return ExitCode::from(2);
    };

    match run(&args, file) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(1)
        }
    }
}

/// List available importers from a config file.
fn list_importers(args: &Args) -> Result<()> {
    let config_path = find_importers_config(args.config.as_deref())?
        .context("--list-importers requires --config or an importers.toml in the current directory or ~/.config/rledger/")?;

    let config = load_importers_config(&config_path)?;

    if config.importers.is_empty() {
        println!("No importers defined in {}", config_path.display());
    } else {
        println!("Available importers in {}:", config_path.display());
        for imp in &config.importers {
            if let Some(pattern) = &imp.filename_pattern {
                println!(
                    "  {} (pattern: {}) -> {}",
                    imp.name,
                    pattern,
                    imp.account.as_deref().unwrap_or("(default)")
                );
            } else {
                println!(
                    "  {} -> {}",
                    imp.name,
                    imp.account.as_deref().unwrap_or("(default)")
                );
            }
        }
    }

    Ok(())
}

/// Check if an importer matches the given filename using its glob pattern.
fn importer_matches_filename(entry: &ImporterEntry, filename: &str) -> bool {
    if let Some(pattern) = &entry.filename_pattern {
        glob::Pattern::new(pattern).is_ok_and(|p| p.matches(filename))
    } else {
        false
    }
}

/// Find importers that match the given filename.
fn find_matching_importers<'a>(
    config: &'a ImportersFile,
    filename: &str,
) -> Vec<&'a ImporterEntry> {
    config
        .importers
        .iter()
        .filter(|imp| importer_matches_filename(imp, filename))
        .collect()
}

/// Check if a file is an OFX/QFX file based on extension.
fn is_ofx_file(path: &Path) -> bool {
    path.extension()
        .is_some_and(|ext| ext.eq_ignore_ascii_case("ofx") || ext.eq_ignore_ascii_case("qfx"))
}

/// Load existing transactions from a beancount file for duplicate detection.
fn load_existing_transactions(path: &Path) -> Result<Vec<Transaction>> {
    let content = fs::read_to_string(path)
        .with_context(|| format!("Failed to read existing ledger: {}", path.display()))?;
    let parse_result = rustledger_parser::parse(&content);
    let mut transactions = Vec::new();
    for directive in parse_result.directives {
        if let Directive::Transaction(txn) = directive.value {
            transactions.push(txn);
        }
    }
    Ok(transactions)
}

/// Check if a new transaction is a duplicate of an existing one.
///
/// Matches on: same date, same first-posting amount, and fuzzy payee/narration match.
fn is_duplicate(new_txn: &Transaction, existing: &[Transaction]) -> bool {
    let new_amount = first_posting_amount(new_txn);
    let new_text = txn_match_text(new_txn);

    existing.iter().any(|existing_txn| {
        // Date must match exactly
        if new_txn.date != existing_txn.date {
            return false;
        }
        // Amount must match (first posting)
        let existing_amount = first_posting_amount(existing_txn);
        if new_amount != existing_amount {
            return false;
        }
        // Fuzzy text match: check if payee or narration overlap
        let existing_text = txn_match_text(existing_txn);
        fuzzy_text_match(&new_text, &existing_text)
    })
}

/// Get the amount from the first posting of a transaction (for comparison).
fn first_posting_amount(txn: &Transaction) -> Option<Decimal> {
    txn.postings.first().and_then(|p| {
        p.units
            .as_ref()
            .and_then(rustledger_core::IncompleteAmount::number)
    })
}

/// Build a lowercase string combining payee and narration for fuzzy matching.
fn txn_match_text(txn: &Transaction) -> String {
    let mut text = String::new();
    if let Some(ref payee) = txn.payee {
        text.push_str(payee.as_str());
        text.push(' ');
    }
    text.push_str(txn.narration.as_str());
    text.to_lowercase()
}

/// Fuzzy text match: returns true if either string contains the other,
/// or if they share significant word overlap.
fn fuzzy_text_match(a: &str, b: &str) -> bool {
    if a.is_empty() || b.is_empty() {
        return false;
    }
    if a == b {
        return true;
    }
    if a.contains(b) || b.contains(a) {
        return true;
    }
    // Word overlap: if >50% of words in the shorter text appear in the longer
    let a_words: Vec<&str> = a.split_whitespace().collect();
    let b_words: Vec<&str> = b.split_whitespace().collect();
    let (shorter, longer) = if a_words.len() <= b_words.len() {
        (&a_words, &b_words)
    } else {
        (&b_words, &a_words)
    };
    let matches = shorter.iter().filter(|w| longer.contains(w)).count();
    matches * 2 > shorter.len()
}

/// Run the extract command with the given arguments.
pub fn run(args: &Args, file: &Path) -> Result<()> {
    // Detect OFX files and use appropriate importer
    let result = if is_ofx_file(file) && args.importer.is_none() {
        let ofx = OfxImporter::new(&args.account, &args.currency);
        ofx.extract(file)?
    } else {
        // Determine import config: --importer flag, explicit --config, or CLI args
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

        config.extract(file)?
    };

    // Print warnings
    for warning in &result.warnings {
        eprintln!("warning: {warning}");
    }

    // Filter duplicates if --existing is specified
    let directives = if let Some(ref existing_path) = args.existing {
        let existing_txns = load_existing_transactions(existing_path)?;
        let before_count = result.directives.len();
        let filtered: Vec<_> = result
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
        filtered
    } else {
        result.directives
    };

    // Write output to file or stdout
    let fmt_config = FormatConfig::default();
    if let Some(ref output_path) = args.output {
        let mut out_file = fs::File::create(output_path)
            .with_context(|| format!("Failed to create output file: {}", output_path.display()))?;
        for directive in &directives {
            writeln!(out_file, "{}", format_directive(directive, &fmt_config))?;
            writeln!(out_file)?;
        }
        eprintln!("Wrote output to {}", output_path.display());
    } else {
        let mut stdout = io::stdout().lock();
        for directive in &directives {
            writeln!(stdout, "{}", format_directive(directive, &fmt_config))?;
            writeln!(stdout)?;
        }
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
    use super::*;
    use rustledger_importer::config::ImporterType;

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
        let result = config.extract(&csv_path).unwrap();

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

    #[test]
    fn test_is_ofx_file() {
        assert!(is_ofx_file(Path::new("statement.ofx")));
        assert!(is_ofx_file(Path::new("statement.OFX")));
        assert!(is_ofx_file(Path::new("statement.qfx")));
        assert!(is_ofx_file(Path::new("statement.QFX")));
        assert!(!is_ofx_file(Path::new("statement.csv")));
        assert!(!is_ofx_file(Path::new("statement.txt")));
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
        let date = chrono::NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let new_txn =
            Transaction::new(date, "GROCERY STORE").with_posting(rustledger_core::Posting::new(
                "Assets:Bank",
                rustledger_core::Amount::new(rust_decimal::Decimal::new(-5000, 2), "USD"),
            ));

        let existing = vec![Transaction::new(date, "GROCERY STORE #123").with_posting(
            rustledger_core::Posting::new(
                "Assets:Bank",
                rustledger_core::Amount::new(rust_decimal::Decimal::new(-5000, 2), "USD"),
            ),
        )];

        assert!(is_duplicate(&new_txn, &existing));
    }

    #[test]
    fn test_is_duplicate_different_date() {
        let new_txn = Transaction::new(
            chrono::NaiveDate::from_ymd_opt(2024, 1, 15).unwrap(),
            "GROCERY STORE",
        )
        .with_posting(rustledger_core::Posting::new(
            "Assets:Bank",
            rustledger_core::Amount::new(rust_decimal::Decimal::new(-5000, 2), "USD"),
        ));

        let existing = vec![
            Transaction::new(
                chrono::NaiveDate::from_ymd_opt(2024, 1, 16).unwrap(),
                "GROCERY STORE",
            )
            .with_posting(rustledger_core::Posting::new(
                "Assets:Bank",
                rustledger_core::Amount::new(rust_decimal::Decimal::new(-5000, 2), "USD"),
            )),
        ];

        assert!(!is_duplicate(&new_txn, &existing));
    }

    #[test]
    fn test_is_duplicate_different_amount() {
        let date = chrono::NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let new_txn =
            Transaction::new(date, "GROCERY STORE").with_posting(rustledger_core::Posting::new(
                "Assets:Bank",
                rustledger_core::Amount::new(rust_decimal::Decimal::new(-5000, 2), "USD"),
            ));

        let existing = vec![Transaction::new(date, "GROCERY STORE").with_posting(
            rustledger_core::Posting::new(
                "Assets:Bank",
                rustledger_core::Amount::new(rust_decimal::Decimal::new(-7500, 2), "USD"),
            ),
        )];

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
            chrono::NaiveDate::from_ymd_opt(2024, 1, 15).unwrap()
        );
        assert_eq!(
            txns[1].date,
            chrono::NaiveDate::from_ymd_opt(2024, 1, 16).unwrap()
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
        let date = chrono::NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Test");
        assert_eq!(first_posting_amount(&txn), None);
    }

    #[test]
    fn test_first_posting_amount_auto_posting() {
        let date = chrono::NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Test")
            .with_posting(rustledger_core::Posting::auto("Expenses:Unknown"));
        assert_eq!(first_posting_amount(&txn), None);
    }

    #[test]
    fn test_txn_match_text_with_payee() {
        let date = chrono::NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Weekly groceries").with_payee("Whole Foods");
        let text = txn_match_text(&txn);
        assert!(text.contains("whole foods"));
        assert!(text.contains("weekly groceries"));
    }

    #[test]
    fn test_txn_match_text_no_payee() {
        let date = chrono::NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Coffee Shop");
        let text = txn_match_text(&txn);
        assert_eq!(text, "coffee shop");
    }

    #[test]
    fn test_is_duplicate_no_existing() {
        let date = chrono::NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Coffee").with_posting(rustledger_core::Posting::new(
            "Assets:Bank",
            rustledger_core::Amount::new(rust_decimal::Decimal::new(-500, 2), "USD"),
        ));
        assert!(!is_duplicate(&txn, &[]));
    }

    #[test]
    fn test_is_duplicate_with_payee() {
        let date = chrono::NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let new_txn = Transaction::new(date, "Weekly groceries")
            .with_payee("WHOLE FOODS")
            .with_posting(rustledger_core::Posting::new(
                "Assets:Bank",
                rustledger_core::Amount::new(rust_decimal::Decimal::new(-5000, 2), "USD"),
            ));

        let existing = vec![
            Transaction::new(date, "Weekly groceries")
                .with_payee("Whole Foods Market")
                .with_posting(rustledger_core::Posting::new(
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
}
