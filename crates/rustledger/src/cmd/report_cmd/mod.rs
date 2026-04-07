//! rledger report - Generate financial reports from beancount files.
//!
//! This is the primary rustledger command for generating reports.
//! For backwards compatibility with Python beancount, `bean-report` is also available.
//!
//! # Usage
//!
//! ```bash
//! rledger report ledger.beancount balances
//! rledger report ledger.beancount income
//! rledger report ledger.beancount holdings
//! ```
//!
//! # Reports
//!
//! - `balances` - Show account balances
//! - `accounts` - List all accounts
//! - `commodities` - List all commodities
//! - `prices` - Show price history
//! - `stats` - Show ledger statistics

// Allow inner helper functions after statements for cleaner report code organization
#![allow(clippy::items_after_statements)]

mod accounts;
mod balances;
mod balsheet;
mod commodities;
mod holdings;
mod income;
mod journal;
mod networth;
mod prices;
mod stats;

use crate::cmd::completions::ShellType;
use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use rustledger_core::NaiveDate;
use rustledger_loader::{LoadOptions, load};
use std::io;
use std::path::PathBuf;
use std::process::ExitCode;

/// Generate reports from beancount files.
#[derive(Parser, Debug)]
#[command(name = "report")]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Generate shell completions and exit
    #[arg(long, value_name = "SHELL", hide = true)]
    generate_completions: Option<ShellType>,

    /// The beancount file to process
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,

    /// The report to generate
    #[command(subcommand)]
    pub report: Option<Report>,

    /// Show verbose output
    #[arg(short, long, global = true)]
    pub verbose: bool,

    /// Output format (text, csv, json)
    #[arg(short = 'f', long, global = true)]
    pub format: Option<OutputFormat>,

    /// Disable pager for output
    #[arg(long, global = true)]
    pub no_pager: bool,
}

/// Output format for reports.
#[derive(Clone, Debug, Default, clap::ValueEnum)]
pub enum OutputFormat {
    /// Plain text output.
    #[default]
    Text,
    /// CSV output.
    Csv,
    /// JSON output.
    Json,
}

impl OutputFormat {
    /// Parse from a string (for config file values).
    #[must_use]
    pub fn from_str_config(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "text" => Some(Self::Text),
            "csv" => Some(Self::Csv),
            "json" => Some(Self::Json),
            _ => None,
        }
    }
}

/// Available report types.
#[derive(Subcommand, Debug)]
pub enum Report {
    /// Show account balances
    Balances {
        /// Filter to accounts matching this prefix
        #[arg(short, long)]
        account: Option<String>,
    },
    /// Balance sheet (Assets, Liabilities, Equity)
    #[command(alias = "bal")]
    Balsheet,
    /// Income statement (Income and Expenses)
    #[command(alias = "is")]
    Income,
    /// Transaction journal/register
    #[command(alias = "register")]
    Journal {
        /// Filter to accounts matching this prefix
        #[arg(short, long)]
        account: Option<String>,
        /// Limit number of entries
        #[arg(short, long)]
        limit: Option<usize>,
    },
    /// Investment holdings with cost basis
    Holdings {
        /// Filter to accounts matching this prefix
        #[arg(short, long)]
        account: Option<String>,
    },
    /// Net worth over time
    Networth {
        /// Group by period (daily, weekly, monthly, yearly)
        #[arg(short, long, default_value = "monthly")]
        period: String,
        /// Filter to specific currency (e.g., USD, EUR)
        #[arg(short, long)]
        currency: Option<String>,
        /// Filter to accounts matching this prefix
        #[arg(short, long)]
        account: Option<String>,
        /// Hide zero balances
        #[arg(long)]
        no_zero: bool,
    },
    /// List all accounts
    Accounts,
    /// List all commodities/currencies
    Commodities,
    /// Show ledger statistics
    Stats,
    /// Show price entries
    Prices {
        /// Filter to specific commodity
        #[arg(short, long)]
        commodity: Option<String>,
    },
}

/// Main entry point with custom binary name (for bean-report compatibility).
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

    // File and report are required when not generating completions
    let Some(file) = args.file else {
        eprintln!("error: FILE is required (or set default.file in config)");
        eprintln!("For more information, try '--help'");
        return ExitCode::from(2);
    };

    let Some(report) = args.report else {
        eprintln!("error: a report subcommand is required");
        eprintln!("For more information, try '--help'");
        return ExitCode::from(2);
    };

    let format = args.format.unwrap_or_default();
    match run(&file, &report, args.verbose, &format, args.no_pager) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) if crate::pager::is_broken_pipe(&e) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(1)
        }
    }
}

/// Run the report command with the given arguments.
pub fn run(
    file: &PathBuf,
    report: &Report,
    verbose: bool,
    format: &OutputFormat,
    no_pager: bool,
) -> Result<()> {
    // Check if file exists
    if !file.exists() {
        anyhow::bail!("file not found: {}", file.display());
    }

    // Load and fully process the file (parse → book → plugins)
    if verbose {
        eprintln!("Loading {}...", file.display());
    }

    let options = LoadOptions {
        validate: false, // Reports don't need validation
        ..Default::default()
    };

    let ledger =
        load(file, &options).with_context(|| format!("failed to load {}", file.display()))?;

    // Report any errors
    for err in &ledger.errors {
        eprintln!("{}: {}", err.code, err.message);
    }

    // Extract directives (already booked and plugins applied)
    let directives: Vec<_> = ledger.directives.into_iter().map(|s| s.value).collect();

    // Create pager AFTER loading (don't spawn pager if load fails)
    let use_pager = !no_pager && matches!(format, OutputFormat::Text);
    let pager_cmd = if use_pager {
        crate::config::Config::load()
            .ok()
            .and_then(|l| l.config.output.pager)
    } else {
        None
    };
    let mut writer = if use_pager {
        crate::pager::create_pager(pager_cmd.as_deref())
    } else {
        crate::pager::PagerWriter::Stdout(io::stdout().lock())
    };

    // Generate the requested report
    match report {
        Report::Balances { account } => {
            balances::report_balances(&directives, account.as_deref(), format, &mut writer)?;
        }
        Report::Balsheet => {
            balsheet::report_balsheet(&directives, format, &mut writer)?;
        }
        Report::Income => {
            income::report_income(&directives, format, &mut writer)?;
        }
        Report::Journal { account, limit } => {
            journal::report_journal(&directives, account.as_deref(), *limit, format, &mut writer)?;
        }
        Report::Holdings { account } => {
            holdings::report_holdings(&directives, account.as_deref(), format, &mut writer)?;
        }
        Report::Networth {
            period,
            currency,
            account,
            no_zero,
        } => {
            networth::report_networth(
                &directives,
                period,
                currency.as_deref(),
                account.as_deref(),
                *no_zero,
                format,
                &mut writer,
            )?;
        }
        Report::Accounts => {
            accounts::report_accounts(&directives, format, &mut writer)?;
        }
        Report::Commodities => {
            commodities::report_commodities(&directives, format, &mut writer)?;
        }
        Report::Stats => {
            stats::report_stats(&directives, file, &mut writer)?;
        }
        Report::Prices { commodity } => {
            prices::report_prices(&directives, commodity.as_deref(), format, &mut writer)?;
        }
    }

    writer.finish();
    Ok(())
}

/// Escape a string for CSV output.
pub(super) fn csv_escape(s: &str) -> String {
    if s.contains(',') || s.contains('"') || s.contains('\n') {
        format!("\"{}\"", s.replace('"', "\"\""))
    } else {
        s.to_string()
    }
}

/// Escape a string for JSON output.
pub(super) fn json_escape(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

#[derive(Default)]
pub(super) struct LedgerStats {
    pub transactions: usize,
    pub postings: usize,
    pub accounts: usize,
    pub commodities: usize,
    pub balance_assertions: usize,
    pub prices: usize,
    pub pads: usize,
    pub events: usize,
    pub notes: usize,
    pub documents: usize,
    pub queries: usize,
    pub custom: usize,
    pub first_date: Option<NaiveDate>,
    pub last_date: Option<NaiveDate>,
}
