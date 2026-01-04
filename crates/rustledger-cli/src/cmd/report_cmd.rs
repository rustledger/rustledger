//! rledger-report - Generate financial reports from beancount files.
//!
//! This is the primary rustledger command for generating reports.
//! For backwards compatibility with Python beancount, `bean-report` is also available.
//!
//! # Usage
//!
//! ```bash
//! rledger-report ledger.beancount balances
//! rledger-report ledger.beancount income
//! rledger-report ledger.beancount holdings
//! ```
//!
//! # Reports
//!
//! - `balances` - Show account balances
//! - `accounts` - List all accounts
//! - `commodities` - List all commodities
//! - `prices` - Show price history
//! - `stats` - Show ledger statistics

use anyhow::{Context, Result};
use rustledger_booking::interpolate;
use rustledger_core::{Directive, Inventory};
use rustledger_loader::Loader;
use clap::{Parser, Subcommand};
use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

/// Generate reports from beancount files.
#[derive(Parser, Debug)]
#[command(name = "rledger-report")]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The beancount file to process
    #[arg(value_name = "FILE")]
    file: PathBuf,

    /// The report to generate
    #[command(subcommand)]
    report: Report,

    /// Show verbose output
    #[arg(short, long, global = true)]
    verbose: bool,
}

#[derive(Subcommand, Debug)]
enum Report {
    /// Show account balances
    Balances {
        /// Filter to accounts matching this prefix
        #[arg(short, long)]
        account: Option<String>,
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

/// Main entry point for the report command.
pub fn main() -> ExitCode {
    let args = Args::parse();

    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(1)
        }
    }
}

fn run(args: &Args) -> Result<()> {
    let mut stdout = io::stdout().lock();

    // Check if file exists
    if !args.file.exists() {
        anyhow::bail!("file not found: {}", args.file.display());
    }

    // Load the file
    if args.verbose {
        eprintln!("Loading {}...", args.file.display());
    }

    let mut loader = Loader::new();
    let load_result = loader
        .load(&args.file)
        .with_context(|| format!("failed to load {}", args.file.display()))?;

    // Extract directives
    let mut directives: Vec<_> = load_result
        .directives
        .iter()
        .map(|s| s.value.clone())
        .collect();

    // Interpolate transactions
    for directive in &mut directives {
        if let Directive::Transaction(txn) = directive {
            if let Ok(result) = interpolate(txn) {
                *txn = result.transaction;
            }
        }
    }

    // Generate the requested report
    match &args.report {
        Report::Balances { account } => {
            report_balances(&directives, account.as_deref(), &mut stdout)?;
        }
        Report::Accounts => {
            report_accounts(&directives, &mut stdout)?;
        }
        Report::Commodities => {
            report_commodities(&directives, &mut stdout)?;
        }
        Report::Stats => {
            report_stats(&directives, &args.file, &mut stdout)?;
        }
        Report::Prices { commodity } => {
            report_prices(&directives, commodity.as_deref(), &mut stdout)?;
        }
    }

    Ok(())
}

/// Generate a balances report.
fn report_balances<W: Write>(
    directives: &[Directive],
    account_filter: Option<&str>,
    writer: &mut W,
) -> Result<()> {
    let mut balances: BTreeMap<String, Inventory> = BTreeMap::new();

    for directive in directives {
        match directive {
            Directive::Open(open) => {
                balances.entry(open.account.clone()).or_default();
            }
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    if let Some(amount) = posting.amount() {
                        let inv = balances.entry(posting.account.clone()).or_default();
                        let position = if let Some(cost_spec) = &posting.cost {
                            if let Some(cost) = cost_spec.resolve(amount.number, txn.date) {
                                rustledger_core::Position::with_cost(amount.clone(), cost)
                            } else {
                                rustledger_core::Position::simple(amount.clone())
                            }
                        } else {
                            rustledger_core::Position::simple(amount.clone())
                        };
                        inv.add(position);
                    }
                }
            }
            _ => {}
        }
    }

    writeln!(writer, "Account Balances")?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    for (account, inventory) in &balances {
        // Apply filter
        if let Some(filter) = account_filter {
            if !account.starts_with(filter) {
                continue;
            }
        }

        // Skip empty balances
        if inventory.is_empty() {
            continue;
        }

        writeln!(writer, "{account}")?;
        for position in inventory.positions() {
            writeln!(
                writer,
                "  {:>15} {}",
                position.units.number, position.units.currency
            )?;
        }
    }

    Ok(())
}

/// Generate an accounts list.
fn report_accounts<W: Write>(directives: &[Directive], writer: &mut W) -> Result<()> {
    let mut accounts: BTreeSet<&str> = BTreeSet::new();

    for directive in directives {
        if let Directive::Open(open) = directive {
            accounts.insert(&open.account);
        }
    }

    writeln!(writer, "Accounts ({} total)", accounts.len())?;
    writeln!(writer, "{}", "=".repeat(40))?;
    writeln!(writer)?;

    for account in accounts {
        writeln!(writer, "{account}")?;
    }

    Ok(())
}

/// Generate a commodities list.
fn report_commodities<W: Write>(directives: &[Directive], writer: &mut W) -> Result<()> {
    let mut commodities: BTreeSet<&str> = BTreeSet::new();

    for directive in directives {
        match directive {
            Directive::Commodity(comm) => {
                commodities.insert(&comm.currency);
            }
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    if let Some(amount) = posting.amount() {
                        commodities.insert(&amount.currency);
                    }
                }
            }
            Directive::Balance(bal) => {
                commodities.insert(&bal.amount.currency);
            }
            Directive::Price(price) => {
                commodities.insert(&price.currency);
                commodities.insert(&price.amount.currency);
            }
            _ => {}
        }
    }

    writeln!(writer, "Commodities ({} total)", commodities.len())?;
    writeln!(writer, "{}", "=".repeat(40))?;
    writeln!(writer)?;

    for commodity in commodities {
        writeln!(writer, "{commodity}")?;
    }

    Ok(())
}

/// Generate ledger statistics.
fn report_stats<W: Write>(
    directives: &[Directive],
    file_path: &PathBuf,
    writer: &mut W,
) -> Result<()> {
    let mut stats = LedgerStats::default();

    for directive in directives {
        match directive {
            Directive::Transaction(txn) => {
                stats.transactions += 1;
                stats.postings += txn.postings.len();
                if stats.first_date.is_none() || Some(txn.date) < stats.first_date {
                    stats.first_date = Some(txn.date);
                }
                if stats.last_date.is_none() || Some(txn.date) > stats.last_date {
                    stats.last_date = Some(txn.date);
                }
            }
            Directive::Open(_) => stats.accounts += 1,
            Directive::Balance(_) => stats.balance_assertions += 1,
            Directive::Commodity(_) => stats.commodities += 1,
            Directive::Price(_) => stats.prices += 1,
            Directive::Pad(_) => stats.pads += 1,
            Directive::Event(_) => stats.events += 1,
            Directive::Note(_) => stats.notes += 1,
            Directive::Document(_) => stats.documents += 1,
            Directive::Query(_) => stats.queries += 1,
            Directive::Custom(_) => stats.custom += 1,
            Directive::Close(_) => {}
        }
    }

    writeln!(writer, "Ledger Statistics")?;
    writeln!(writer, "{}", "=".repeat(40))?;
    writeln!(writer)?;
    writeln!(writer, "File: {}", file_path.display())?;
    writeln!(writer)?;
    writeln!(writer, "Date Range:")?;
    if let (Some(first), Some(last)) = (stats.first_date, stats.last_date) {
        writeln!(writer, "  First: {first}")?;
        writeln!(writer, "  Last:  {last}")?;
    }
    writeln!(writer)?;
    writeln!(writer, "Directives:")?;
    writeln!(writer, "  Transactions:       {:>6}", stats.transactions)?;
    writeln!(writer, "  Postings:           {:>6}", stats.postings)?;
    writeln!(writer, "  Accounts:           {:>6}", stats.accounts)?;
    writeln!(writer, "  Commodities:        {:>6}", stats.commodities)?;
    writeln!(writer, "  Balance Assertions: {:>6}", stats.balance_assertions)?;
    writeln!(writer, "  Prices:             {:>6}", stats.prices)?;
    writeln!(writer, "  Pads:               {:>6}", stats.pads)?;
    writeln!(writer, "  Events:             {:>6}", stats.events)?;
    writeln!(writer, "  Notes:              {:>6}", stats.notes)?;
    writeln!(writer, "  Documents:          {:>6}", stats.documents)?;
    writeln!(writer, "  Queries:            {:>6}", stats.queries)?;
    writeln!(writer, "  Custom:             {:>6}", stats.custom)?;
    writeln!(writer)?;
    writeln!(writer, "Total Directives:     {:>6}", directives.len())?;

    Ok(())
}

/// Generate a prices report.
fn report_prices<W: Write>(
    directives: &[Directive],
    commodity_filter: Option<&str>,
    writer: &mut W,
) -> Result<()> {
    let mut prices: Vec<_> = directives
        .iter()
        .filter_map(|d| {
            if let Directive::Price(p) = d {
                if let Some(filter) = commodity_filter {
                    if p.currency != filter {
                        return None;
                    }
                }
                Some(p)
            } else {
                None
            }
        })
        .collect();

    prices.sort_by_key(|p| (p.currency.clone(), p.date));

    writeln!(writer, "Price History")?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    if prices.is_empty() {
        writeln!(writer, "No price entries found.")?;
    } else {
        let mut current_currency = "";
        for price in prices {
            if price.currency != current_currency {
                if !current_currency.is_empty() {
                    writeln!(writer)?;
                }
                writeln!(writer, "{}:", price.currency)?;
                current_currency = &price.currency;
            }
            writeln!(
                writer,
                "  {}  {} {}",
                price.date, price.amount.number, price.amount.currency
            )?;
        }
    }

    Ok(())
}

#[derive(Default)]
struct LedgerStats {
    transactions: usize,
    postings: usize,
    accounts: usize,
    commodities: usize,
    balance_assertions: usize,
    prices: usize,
    pads: usize,
    events: usize,
    notes: usize,
    documents: usize,
    queries: usize,
    custom: usize,
    first_date: Option<rustledger_core::NaiveDate>,
    last_date: Option<rustledger_core::NaiveDate>,
}
