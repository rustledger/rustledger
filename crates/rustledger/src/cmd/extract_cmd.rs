//! rledger-extract - Extract transactions from bank files.
//!
//! This is the primary rustledger command for importing transactions from
//! CSV, OFX, and other bank statement formats.
//!
//! # Usage
//!
//! ```bash
//! rledger-extract bank.csv --account Assets:Bank:Checking
//! rledger-extract statement.csv --config bank-config.json
//! ```

use crate::cmd::completions::ShellType;
use anyhow::Result;
use clap::Parser;
use rustledger_core::{FormatConfig, format_directive};
use rustledger_importer::ImporterConfig;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

/// Extract transactions from bank files.
#[derive(Parser, Debug)]
#[command(name = "rledger-extract")]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Generate shell completions and exit
    #[arg(long, value_name = "SHELL", hide = true)]
    generate_completions: Option<ShellType>,

    /// The file to extract transactions from
    #[arg(value_name = "FILE")]
    file: Option<PathBuf>,

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
}

/// Main entry point for the extract command.
pub fn main() -> ExitCode {
    main_with_name("rledger-extract")
}

/// Main entry point with custom binary name (for bean-extract compatibility).
pub fn main_with_name(bin_name: &str) -> ExitCode {
    let args = Args::parse();

    // Handle shell completion generation
    if let Some(shell) = args.generate_completions {
        crate::cmd::completions::generate_completions::<Args>(shell, bin_name);
        return ExitCode::SUCCESS;
    }

    // File is required when not generating completions
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

fn run(args: &Args, file: &PathBuf) -> Result<()> {
    let mut stdout = io::stdout().lock();

    // Build the importer configuration
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

    let config = builder.build();

    // Extract transactions
    let result = config.extract(file)?;

    // Print warnings
    for warning in &result.warnings {
        eprintln!("warning: {}", warning);
    }

    // Print extracted directives in beancount format
    let fmt_config = FormatConfig::default();
    for directive in &result.directives {
        writeln!(stdout, "{}", format_directive(directive, &fmt_config))?;
        writeln!(stdout)?;
    }

    eprintln!(
        "Extracted {} transactions from {}",
        result.directives.len(),
        file.display()
    );

    Ok(())
}
