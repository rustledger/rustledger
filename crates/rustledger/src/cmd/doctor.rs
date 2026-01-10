//! bean-doctor - Debugging tool for beancount files.
//!
//! This is the Rust equivalent of Python beancount's `bean-doctor` command.
//!
//! # Usage
//!
//! ```bash
//! bean-doctor lex ledger.beancount         # Dump lexer tokens
//! bean-doctor context ledger.beancount 42  # Show context at line 42
//! bean-doctor linked ledger.beancount ^trip-2024  # Find linked transactions
//! bean-doctor missing-open ledger.beancount  # Generate missing Open directives
//! bean-doctor list-options                 # List available options
//! ```

use crate::cmd::completions::ShellType;
use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use rust_decimal;
use rustledger_core::{Directive, InternedStr, NaiveDate};
use rustledger_loader::Loader;
use rustledger_parser;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

/// Debugging tool for beancount files.
#[derive(Parser, Debug)]
#[command(name = "bean-doctor")]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Generate shell completions and exit
    #[arg(long, value_name = "SHELL", hide = true)]
    generate_completions: Option<ShellType>,

    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Dump the lexer output for a beancount file
    #[command(alias = "dump-lexer")]
    Lex {
        /// The beancount file to lex
        file: PathBuf,
    },

    /// Parse a ledger and show parsed directives
    Parse {
        /// The beancount file to parse
        file: PathBuf,
        /// Show detailed output
        #[arg(short, long)]
        verbose: bool,
    },

    /// Show transaction context at a location
    Context {
        /// The beancount file
        file: PathBuf,
        /// Line number to show context for
        line: usize,
    },

    /// Find transactions linked by a link or at a location
    Linked {
        /// The beancount file
        file: PathBuf,
        /// Link name (^link), tag name (#tag), or line number
        location: String,
    },

    /// Print Open directives missing in a file
    MissingOpen {
        /// The beancount file
        file: PathBuf,
    },

    /// List available beancount options
    ListOptions,

    /// Print options parsed from a ledger
    PrintOptions {
        /// The beancount file
        file: PathBuf,
    },

    /// Display statistics about a ledger
    Stats {
        /// The beancount file
        file: PathBuf,
    },

    /// Display the decimal precision context inferred from the file
    DisplayContext {
        /// The beancount file
        file: PathBuf,
    },

    /// Round-trip test on arbitrary ledger
    Roundtrip {
        /// The beancount file
        file: PathBuf,
    },

    /// Validate a directory hierarchy against the ledger's account names
    Directories {
        /// The beancount file
        file: PathBuf,
        /// Directory roots to validate
        #[arg(value_name = "DIR")]
        dirs: Vec<PathBuf>,
    },

    /// Print transactions in a line range with balances
    Region {
        /// The beancount file
        file: PathBuf,
        /// Start line number
        start_line: usize,
        /// End line number
        end_line: usize,
        /// Convert balances to market value or cost
        #[arg(long, value_enum)]
        conversion: Option<Conversion>,
    },
}

/// Conversion type for region balances
#[derive(Debug, Clone, Copy, clap::ValueEnum)]
enum Conversion {
    /// Convert to market value using price database
    Value,
    /// Convert to cost basis
    Cost,
}

/// Main entry point for the doctor command.
pub fn main() -> ExitCode {
    main_with_name("rledger-doctor")
}

/// Main entry point with custom binary name (for bean-doctor compatibility).
pub fn main_with_name(bin_name: &str) -> ExitCode {
    let args = Args::parse();

    // Handle shell completion generation
    if let Some(shell) = args.generate_completions {
        crate::cmd::completions::generate_completions::<Args>(shell, bin_name);
        return ExitCode::SUCCESS;
    }

    // Command is required when not generating completions
    let Some(command) = args.command else {
        eprintln!("error: a subcommand is required");
        eprintln!("For more information, try '--help'");
        return ExitCode::from(2);
    };

    match run(command) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(1)
        }
    }
}

fn run(command: Command) -> Result<()> {
    let mut stdout = io::stdout().lock();

    match command {
        Command::Lex { file } => cmd_lex(&file, &mut stdout),
        Command::Parse { file, verbose } => cmd_parse(&file, verbose, &mut stdout),
        Command::Context { file, line } => cmd_context(&file, line, &mut stdout),
        Command::Linked { file, location } => cmd_linked(&file, &location, &mut stdout),
        Command::MissingOpen { file } => cmd_missing_open(&file, &mut stdout),
        Command::ListOptions => cmd_list_options(&mut stdout),
        Command::PrintOptions { file } => cmd_print_options(&file, &mut stdout),
        Command::Stats { file } => cmd_stats(&file, &mut stdout),
        Command::DisplayContext { file } => cmd_display_context(&file, &mut stdout),
        Command::Roundtrip { file } => cmd_roundtrip(&file, &mut stdout),
        Command::Directories { file, dirs } => cmd_directories(&file, &dirs, &mut stdout),
        Command::Region {
            file,
            start_line,
            end_line,
            conversion,
        } => cmd_region(&file, start_line, end_line, conversion, &mut stdout),
    }
}

fn cmd_lex<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    let source =
        fs::read_to_string(file).with_context(|| format!("failed to read {}", file.display()))?;

    // Use the parser's lexer to tokenize
    let result = rustledger_parser::parse(&source);

    // Show tokens by line
    writeln!(writer, "Lexer output for {}:", file.display())?;
    writeln!(writer, "{}", "=".repeat(60))?;

    // Since we don't have direct lexer access, show the parsed result info
    writeln!(writer, "Parsed {} directives", result.directives.len())?;
    writeln!(writer, "Found {} errors", result.errors.len())?;
    writeln!(writer, "Found {} options", result.options.len())?;
    writeln!(writer, "Found {} plugins", result.plugins.len())?;
    writeln!(writer, "Found {} includes", result.includes.len())?;

    if !result.errors.is_empty() {
        writeln!(writer)?;
        writeln!(writer, "Parse errors:")?;
        for err in &result.errors {
            writeln!(writer, "  Line {}: {}", err.span.start, err.message())?;
        }
    }

    Ok(())
}

fn cmd_parse<W: Write>(file: &PathBuf, verbose: bool, writer: &mut W) -> Result<()> {
    let source =
        fs::read_to_string(file).with_context(|| format!("failed to read {}", file.display()))?;

    let result = rustledger_parser::parse(&source);

    writeln!(writer, "Parse result for {}:", file.display())?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    if verbose {
        for (i, spanned) in result.directives.iter().enumerate() {
            writeln!(writer, "[{}] {:?}", i, spanned.value)?;
        }
    } else {
        writeln!(writer, "Directives: {}", result.directives.len())?;
        writeln!(writer, "Errors: {}", result.errors.len())?;
        writeln!(writer, "Options: {}", result.options.len())?;
        writeln!(writer, "Plugins: {}", result.plugins.len())?;
        writeln!(writer, "Includes: {}", result.includes.len())?;
    }

    if !result.errors.is_empty() {
        writeln!(writer)?;
        writeln!(writer, "Errors:")?;
        for err in &result.errors {
            writeln!(writer, "  {}", err.message())?;
        }
    }

    Ok(())
}

fn cmd_context<W: Write>(file: &PathBuf, line: usize, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    // Find the directive at or near the specified line
    let source = fs::read_to_string(file)?;
    let lines: Vec<&str> = source.lines().collect();

    writeln!(writer, "Context at {}:{}", file.display(), line)?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    // Show surrounding lines
    let start = line.saturating_sub(3);
    let end = (line + 3).min(lines.len());

    for (i, src_line) in lines.iter().enumerate().skip(start).take(end - start) {
        let line_num = i + 1;
        let marker = if line_num == line { ">>>" } else { "   " };
        writeln!(writer, "{marker} {line_num:4} | {src_line}")?;
    }

    // Find which directive contains this line
    writeln!(writer)?;
    for spanned in &load_result.directives {
        let span = &spanned.span;
        // Check if line falls within directive's span (approximate)
        if span.start <= line && span.end >= line {
            writeln!(writer, "Directive at this location:")?;
            writeln!(writer, "{:?}", spanned.value)?;
            break;
        }
    }

    Ok(())
}

fn cmd_linked<W: Write>(file: &PathBuf, location: &str, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    let directives: Vec<_> = load_result.directives.iter().map(|s| &s.value).collect();

    let linked: Vec<_> = if let Some(link_name) = location.strip_prefix('^') {
        // Link name
        let link = link_name.to_string();
        directives
            .iter()
            .filter(|d| {
                if let Directive::Transaction(txn) = d {
                    txn.links.contains(&link)
                } else {
                    false
                }
            })
            .copied()
            .collect()
    } else if let Some(tag_name) = location.strip_prefix('#') {
        // Tag name
        let tag = tag_name.to_string();
        directives
            .iter()
            .filter(|d| {
                if let Directive::Transaction(txn) = d {
                    txn.tags.contains(&tag)
                } else {
                    false
                }
            })
            .copied()
            .collect()
    } else {
        // Line number - find transaction and its links
        let line: usize = location
            .parse()
            .with_context(|| format!("invalid line number: {location}"))?;

        // Find the transaction at this line, then find all linked transactions
        let mut links_to_find: HashSet<String> = HashSet::new();

        for spanned in &load_result.directives {
            if spanned.span.start <= line && spanned.span.end >= line {
                if let Directive::Transaction(txn) = &spanned.value {
                    links_to_find.extend(txn.links.iter().cloned());
                }
            }
        }

        if links_to_find.is_empty() {
            writeln!(writer, "No transaction found at line {line}")?;
            return Ok(());
        }

        directives
            .iter()
            .filter(|d| {
                if let Directive::Transaction(txn) = d {
                    txn.links.iter().any(|l| links_to_find.contains(l))
                } else {
                    false
                }
            })
            .copied()
            .collect()
    };

    writeln!(writer, "Found {} linked entries:", linked.len())?;
    writeln!(writer, "{}", "=".repeat(60))?;

    for directive in linked {
        if let Directive::Transaction(txn) = directive {
            writeln!(writer)?;
            writeln!(writer, "{} {} \"{}\"", txn.date, txn.flag, txn.narration)?;
            if !txn.links.is_empty() {
                writeln!(
                    writer,
                    "  Links: {}",
                    txn.links
                        .iter()
                        .map(|l| format!("^{l}"))
                        .collect::<Vec<_>>()
                        .join(" ")
                )?;
            }
            for posting in &txn.postings {
                if let Some(amount) = posting.amount() {
                    writeln!(
                        writer,
                        "  {} {} {}",
                        posting.account, amount.number, amount.currency
                    )?;
                } else {
                    writeln!(writer, "  {}", posting.account)?;
                }
            }
        }
    }

    Ok(())
}

fn cmd_missing_open<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    // Collect all accounts that are opened
    let mut opened_accounts: HashSet<InternedStr> = HashSet::new();

    // Collect all accounts that are used and their first use date
    let mut used_accounts: BTreeMap<InternedStr, NaiveDate> = BTreeMap::new();

    for spanned in &load_result.directives {
        match &spanned.value {
            Directive::Open(open) => {
                opened_accounts.insert(open.account.clone());
            }
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    used_accounts
                        .entry(posting.account.clone())
                        .or_insert(txn.date);
                }
            }
            Directive::Balance(bal) => {
                used_accounts.entry(bal.account.clone()).or_insert(bal.date);
            }
            Directive::Pad(pad) => {
                used_accounts.entry(pad.account.clone()).or_insert(pad.date);
                used_accounts
                    .entry(pad.source_account.clone())
                    .or_insert(pad.date);
            }
            _ => {}
        }
    }

    // Find accounts that are used but not opened
    let missing: Vec<_> = used_accounts
        .iter()
        .filter(|(account, _)| !opened_accounts.contains(*account))
        .collect();

    if missing.is_empty() {
        writeln!(writer, "; No missing Open directives")?;
    } else {
        writeln!(
            writer,
            "; Missing Open directives ({} accounts)",
            missing.len()
        )?;
        writeln!(writer)?;
        for (account, first_use_date) in missing {
            writeln!(writer, "{first_use_date} open {account}")?;
        }
    }

    Ok(())
}

fn cmd_list_options<W: Write>(writer: &mut W) -> Result<()> {
    writeln!(writer, "Available beancount options:")?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    let options = [
        ("title", "string", "The title of the ledger"),
        (
            "operating_currency",
            "string",
            "Operating currencies (can be specified multiple times)",
        ),
        ("render_commas", "bool", "Render commas in numbers"),
        (
            "name_assets",
            "string",
            "Name for Assets accounts (default: Assets)",
        ),
        (
            "name_liabilities",
            "string",
            "Name for Liabilities accounts (default: Liabilities)",
        ),
        (
            "name_equity",
            "string",
            "Name for Equity accounts (default: Equity)",
        ),
        (
            "name_income",
            "string",
            "Name for Income accounts (default: Income)",
        ),
        (
            "name_expenses",
            "string",
            "Name for Expenses accounts (default: Expenses)",
        ),
        (
            "account_previous_balances",
            "string",
            "Account for opening balances",
        ),
        (
            "account_previous_earnings",
            "string",
            "Account for previous earnings",
        ),
        (
            "account_previous_conversions",
            "string",
            "Account for previous conversions",
        ),
        (
            "account_current_earnings",
            "string",
            "Account for current earnings",
        ),
        (
            "account_current_conversions",
            "string",
            "Account for current conversions",
        ),
        (
            "account_unrealized_gains",
            "string",
            "Account for unrealized gains",
        ),
        ("account_rounding", "string", "Account for rounding errors"),
        ("conversion_currency", "string", "Currency for conversions"),
        (
            "inferred_tolerance_default",
            "string",
            "Default tolerance for balance checks",
        ),
        (
            "inferred_tolerance_multiplier",
            "decimal",
            "Multiplier for inferred tolerances",
        ),
        (
            "infer_tolerance_from_cost",
            "bool",
            "Infer tolerance from cost",
        ),
        ("documents", "string", "Directories to search for documents"),
        (
            "booking_method",
            "string",
            "Default booking method (STRICT, FIFO, LIFO, etc.)",
        ),
        ("plugin_processing_mode", "string", "Plugin processing mode"),
        (
            "long_string_maxlines",
            "int",
            "Maximum lines for long strings",
        ),
        ("insert_pythonpath", "string", "Python paths for plugins"),
    ];

    for (name, type_name, description) in options {
        writeln!(writer, "option \"{name}\" <{type_name}>")?;
        writeln!(writer, "  {description}")?;
        writeln!(writer)?;
    }

    Ok(())
}

fn cmd_print_options<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    writeln!(writer, "Options from {}:", file.display())?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    let options = &load_result.options;

    if let Some(title) = &options.title {
        writeln!(writer, "title: {title:?}")?;
    }
    if !options.operating_currency.is_empty() {
        writeln!(
            writer,
            "operating_currency: {:?}",
            options.operating_currency
        )?;
    }
    writeln!(writer, "name_assets: {:?}", options.name_assets)?;
    writeln!(writer, "name_liabilities: {:?}", options.name_liabilities)?;
    writeln!(writer, "name_equity: {:?}", options.name_equity)?;
    writeln!(writer, "name_income: {:?}", options.name_income)?;
    writeln!(writer, "name_expenses: {:?}", options.name_expenses)?;

    writeln!(
        writer,
        "account_previous_balances: {:?}",
        options.account_previous_balances
    )?;
    writeln!(
        writer,
        "account_previous_earnings: {:?}",
        options.account_previous_earnings
    )?;
    writeln!(
        writer,
        "account_current_earnings: {:?}",
        options.account_current_earnings
    )?;
    if let Some(acct) = &options.account_unrealized_gains {
        writeln!(writer, "account_unrealized_gains: {acct:?}")?;
    }

    writeln!(writer, "booking_method: {:?}", options.booking_method)?;

    if !options.documents.is_empty() {
        writeln!(writer, "documents: {:?}", options.documents)?;
    }

    Ok(())
}

fn cmd_stats<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    let mut transactions = 0;
    let mut postings = 0;
    let mut accounts = 0;
    let mut commodities_set: BTreeSet<InternedStr> = BTreeSet::new();
    let mut balance_assertions = 0;
    let mut prices = 0;
    let mut first_date: Option<NaiveDate> = None;
    let mut last_date: Option<NaiveDate> = None;

    for spanned in &load_result.directives {
        match &spanned.value {
            Directive::Transaction(txn) => {
                transactions += 1;
                postings += txn.postings.len();
                for posting in &txn.postings {
                    if let Some(amount) = posting.amount() {
                        commodities_set.insert(amount.currency.clone());
                    }
                }
                if first_date.is_none() || Some(txn.date) < first_date {
                    first_date = Some(txn.date);
                }
                if last_date.is_none() || Some(txn.date) > last_date {
                    last_date = Some(txn.date);
                }
            }
            Directive::Open(_) => accounts += 1,
            Directive::Balance(bal) => {
                balance_assertions += 1;
                commodities_set.insert(bal.amount.currency.clone());
            }
            Directive::Commodity(comm) => {
                commodities_set.insert(comm.currency.clone());
            }
            Directive::Price(price) => {
                prices += 1;
                commodities_set.insert(price.currency.clone());
                commodities_set.insert(price.amount.currency.clone());
            }
            _ => {}
        }
    }

    writeln!(writer, "Ledger Statistics for {}", file.display())?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    if let (Some(first), Some(last)) = (first_date, last_date) {
        writeln!(writer, "Date range: {first} to {last}")?;
        writeln!(writer)?;
    }

    writeln!(
        writer,
        "Directives:       {:>8}",
        load_result.directives.len()
    )?;
    writeln!(writer, "  Transactions:   {transactions:>8}")?;
    writeln!(writer, "  Postings:       {postings:>8}")?;
    writeln!(writer, "  Accounts:       {accounts:>8}")?;
    writeln!(writer, "  Commodities:    {:>8}", commodities_set.len())?;
    writeln!(writer, "  Balances:       {balance_assertions:>8}")?;
    writeln!(writer, "  Prices:         {prices:>8}")?;
    writeln!(writer)?;
    writeln!(writer, "Parse errors:     {:>8}", load_result.errors.len())?;

    Ok(())
}

fn cmd_display_context<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    // Collect decimal precision from numbers in the file
    let mut currency_scales: BTreeMap<InternedStr, i32> = BTreeMap::new();

    for spanned in &load_result.directives {
        match &spanned.value {
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    if let Some(amount) = posting.amount() {
                        let scale = amount.number.scale() as i32;
                        let entry = currency_scales.entry(amount.currency.clone()).or_insert(0);
                        if scale > *entry {
                            *entry = scale;
                        }
                    }
                }
            }
            Directive::Balance(bal) => {
                let scale = bal.amount.number.scale() as i32;
                let entry = currency_scales
                    .entry(bal.amount.currency.clone())
                    .or_insert(0);
                if scale > *entry {
                    *entry = scale;
                }
            }
            Directive::Price(price) => {
                let scale = price.amount.number.scale() as i32;
                let entry = currency_scales
                    .entry(price.amount.currency.clone())
                    .or_insert(0);
                if scale > *entry {
                    *entry = scale;
                }
            }
            _ => {}
        }
    }

    writeln!(writer, "Display Context (decimal precision by currency)")?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    if currency_scales.is_empty() {
        writeln!(writer, "No currencies found in file.")?;
    } else {
        for (currency, scale) in &currency_scales {
            writeln!(writer, "{currency}: {scale} decimal places")?;
        }
    }

    Ok(())
}

fn cmd_roundtrip<W: Write>(file: &PathBuf, writer: &mut W) -> Result<()> {
    use crate::format::{FormatConfig, format_directive};

    writeln!(writer, "Round-trip test for {}", file.display())?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    // First pass: load and parse
    writeln!(writer, "Step 1: Loading original file...")?;
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    if !load_result.errors.is_empty() {
        writeln!(
            writer,
            "  Found {} parse errors in original",
            load_result.errors.len()
        )?;
    }

    let original_count = load_result.directives.len();
    writeln!(writer, "  Parsed {original_count} directives")?;

    // Format back to string
    writeln!(writer)?;
    writeln!(writer, "Step 2: Formatting directives...")?;
    let config = FormatConfig::new(60, 2);
    let mut formatted = String::new();
    for spanned in &load_result.directives {
        formatted.push_str(&format_directive(&spanned.value, &config));
    }

    // Second pass: parse the formatted output
    writeln!(writer)?;
    writeln!(writer, "Step 3: Re-parsing formatted output...")?;
    let result2 = rustledger_parser::parse(&formatted);

    if !result2.errors.is_empty() {
        writeln!(
            writer,
            "  Found {} parse errors in round-trip",
            result2.errors.len()
        )?;
        for err in &result2.errors {
            writeln!(writer, "    {}", err.message())?;
        }
    }

    let roundtrip_count = result2.directives.len();
    writeln!(writer, "  Parsed {roundtrip_count} directives")?;

    // Compare counts
    writeln!(writer)?;
    writeln!(writer, "Step 4: Comparing results...")?;
    if original_count == roundtrip_count && result2.errors.is_empty() {
        writeln!(
            writer,
            "  SUCCESS: Round-trip produced same number of directives"
        )?;
    } else {
        writeln!(
            writer,
            "  MISMATCH: Original had {original_count} directives, round-trip has {roundtrip_count}"
        )?;
    }

    Ok(())
}

fn cmd_directories<W: Write>(file: &PathBuf, dirs: &[PathBuf], writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    // Collect all account names
    let mut accounts: BTreeSet<InternedStr> = BTreeSet::new();
    for spanned in &load_result.directives {
        match &spanned.value {
            Directive::Open(open) => {
                accounts.insert(open.account.clone());
            }
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    accounts.insert(posting.account.clone());
                }
            }
            _ => {}
        }
    }

    writeln!(
        writer,
        "Validating directories against {} accounts",
        accounts.len()
    )?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    let mut errors = 0;

    for dir in dirs {
        if !dir.exists() {
            writeln!(writer, "ERROR: Directory does not exist: {}", dir.display())?;
            errors += 1;
            continue;
        }

        writeln!(writer, "Checking {}...", dir.display())?;

        // Walk the directory and check subdirectory names
        for entry in walkdir(dir)? {
            let entry = entry?;
            if entry.file_type().is_dir() {
                let file_name = entry.file_name();
                let name = file_name.to_string_lossy();
                // Check if it looks like an account component (capitalized)
                if name.chars().next().is_some_and(char::is_uppercase) {
                    // Build account path from directory path
                    let rel_path = entry.path().strip_prefix(dir).unwrap_or(entry.path());
                    let account_path: String = rel_path
                        .components()
                        .filter_map(|c| c.as_os_str().to_str())
                        .collect::<Vec<_>>()
                        .join(":");

                    // Check if any account starts with this path
                    let has_match = accounts
                        .iter()
                        .any(|a| a.starts_with(&account_path) || a == &account_path);
                    if !has_match && !account_path.is_empty() {
                        writeln!(
                            writer,
                            "  WARNING: No matching account for directory: {account_path}"
                        )?;
                    }
                }
            }
        }
    }

    writeln!(writer)?;
    if errors == 0 {
        writeln!(writer, "Directory validation complete.")?;
    } else {
        writeln!(writer, "Found {errors} errors.")?;
    }

    Ok(())
}

/// Simple directory walker
fn walkdir(dir: &PathBuf) -> Result<Vec<Result<DirEntry, std::io::Error>>> {
    let mut entries = Vec::new();
    walk_dir_recursive(dir, &mut entries)?;
    Ok(entries)
}

struct DirEntry {
    path: PathBuf,
    file_type: std::fs::FileType,
}

impl DirEntry {
    const fn path(&self) -> &PathBuf {
        &self.path
    }

    fn file_name(&self) -> std::ffi::OsString {
        self.path.file_name().unwrap_or_default().to_os_string()
    }

    const fn file_type(&self) -> &std::fs::FileType {
        &self.file_type
    }
}

fn walk_dir_recursive(
    dir: &PathBuf,
    entries: &mut Vec<Result<DirEntry, std::io::Error>>,
) -> Result<()> {
    if dir.is_dir() {
        for entry in fs::read_dir(dir)? {
            match entry {
                Ok(e) => {
                    let path = e.path();
                    if let Ok(ft) = e.file_type() {
                        entries.push(Ok(DirEntry {
                            path: path.clone(),
                            file_type: ft,
                        }));
                        if ft.is_dir() {
                            let _ = walk_dir_recursive(&path, entries);
                        }
                    }
                }
                Err(e) => entries.push(Err(e)),
            }
        }
    }
    Ok(())
}

fn cmd_region<W: Write>(
    file: &PathBuf,
    start_line: usize,
    end_line: usize,
    conversion: Option<Conversion>,
    writer: &mut W,
) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    let conversion_str = match conversion {
        Some(Conversion::Value) => " (converted to value)",
        Some(Conversion::Cost) => " (converted to cost)",
        None => "",
    };
    writeln!(
        writer,
        "Transactions in region {}:{}-{}{}",
        file.display(),
        start_line,
        end_line,
        conversion_str
    )?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    // Get the source file for line number conversion
    let source_file = load_result.source_map.get(0);

    // Find transactions in the line range
    let mut region_transactions: Vec<&rustledger_core::Transaction> = Vec::new();

    for spanned in &load_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            // Convert byte offset to line number using source map
            let txn_line = match source_file {
                Some(sf) => sf.line_col(spanned.span.start).0,
                None => continue,
            };

            // Check if transaction line falls within the requested range
            if txn_line >= start_line && txn_line <= end_line {
                region_transactions.push(txn);
            }
        }
    }

    if region_transactions.is_empty() {
        writeln!(
            writer,
            "No transactions found in lines {start_line}-{end_line}"
        )?;
        return Ok(());
    }

    writeln!(
        writer,
        "Found {} transaction(s):",
        region_transactions.len()
    )?;
    writeln!(writer)?;

    // Calculate balances for these transactions
    let mut balances: BTreeMap<String, rust_decimal::Decimal> = BTreeMap::new();

    for txn in &region_transactions {
        writeln!(writer, "{} {} \"{}\"", txn.date, txn.flag, txn.narration)?;
        for posting in &txn.postings {
            if let Some(amount) = posting.amount() {
                // Apply conversion if specified
                let (display_number, display_currency) = match conversion {
                    Some(Conversion::Cost) => {
                        // Use cost if available, otherwise fall back to units
                        if let Some(ref cost) = posting.cost {
                            // Calculate total cost from cost spec
                            let total_cost = if let Some(total) = cost.number_total {
                                // Total cost was specified directly
                                total
                            } else if let Some(per_unit) = cost.number_per {
                                // Calculate total from per-unit cost
                                amount.number * per_unit
                            } else {
                                // No cost info, fall back to units
                                amount.number
                            };
                            let currency = cost
                                .currency
                                .clone()
                                .unwrap_or_else(|| amount.currency.clone());
                            (total_cost, currency)
                        } else {
                            (amount.number, amount.currency.clone())
                        }
                    }
                    Some(Conversion::Value) => {
                        // For value conversion, we would need a price database
                        // For now, just show a note and use the original values
                        writeln!(
                            writer,
                            "  (Note: value conversion requires price database, showing units)"
                        )?;
                        (amount.number, amount.currency.clone())
                    }
                    None => (amount.number, amount.currency.clone()),
                };
                writeln!(
                    writer,
                    "  {} {} {}",
                    posting.account, display_number, display_currency
                )?;
                *balances
                    .entry(format!("{}:{}", posting.account, display_currency))
                    .or_default() += display_number;
            } else {
                writeln!(writer, "  {}", posting.account)?;
            }
        }
        writeln!(writer)?;
    }

    // Print net balances
    writeln!(writer, "Net changes{conversion_str}:")?;
    for (key, balance) in &balances {
        if !balance.is_zero() {
            writeln!(writer, "  {key}: {balance}")?;
        }
    }

    Ok(())
}
