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

use crate::cmd::completions::ShellType;
use anyhow::{Context, Result};
use chrono::Datelike;
use clap::{Parser, Subcommand};
use rust_decimal::Decimal;
use rustledger_booking::interpolate;
use rustledger_core::{Directive, InternedStr, Inventory};
use rustledger_loader::Loader;
use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

/// Generate reports from beancount files.
#[derive(Parser, Debug)]
#[command(name = "rledger-report")]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Generate shell completions and exit
    #[arg(long, value_name = "SHELL", hide = true)]
    generate_completions: Option<ShellType>,

    /// The beancount file to process
    #[arg(value_name = "FILE")]
    file: Option<PathBuf>,

    /// The report to generate
    #[command(subcommand)]
    report: Option<Report>,

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
    main_with_name("rledger-report")
}

/// Main entry point with custom binary name (for bean-report compatibility).
pub fn main_with_name(bin_name: &str) -> ExitCode {
    let args = Args::parse();

    // Handle shell completion generation
    if let Some(shell) = args.generate_completions {
        crate::cmd::completions::generate_completions::<Args>(shell, bin_name);
        return ExitCode::SUCCESS;
    }

    // File and report are required when not generating completions
    let Some(file) = args.file else {
        eprintln!("error: FILE is required");
        eprintln!("For more information, try '--help'");
        return ExitCode::from(2);
    };

    let Some(report) = args.report else {
        eprintln!("error: a report subcommand is required");
        eprintln!("For more information, try '--help'");
        return ExitCode::from(2);
    };

    match run(&file, &report, args.verbose) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(1)
        }
    }
}

fn run(file: &PathBuf, report: &Report, verbose: bool) -> Result<()> {
    let mut stdout = io::stdout().lock();

    // Check if file exists
    if !file.exists() {
        anyhow::bail!("file not found: {}", file.display());
    }

    // Load the file
    if verbose {
        eprintln!("Loading {}...", file.display());
    }

    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

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
    match report {
        Report::Balances { account } => {
            report_balances(&directives, account.as_deref(), &mut stdout)?;
        }
        Report::Balsheet => {
            report_balsheet(&directives, &mut stdout)?;
        }
        Report::Income => {
            report_income(&directives, &mut stdout)?;
        }
        Report::Journal { account, limit } => {
            report_journal(&directives, account.as_deref(), *limit, &mut stdout)?;
        }
        Report::Holdings { account } => {
            report_holdings(&directives, account.as_deref(), &mut stdout)?;
        }
        Report::Networth { period } => {
            report_networth(&directives, period, &mut stdout)?;
        }
        Report::Accounts => {
            report_accounts(&directives, &mut stdout)?;
        }
        Report::Commodities => {
            report_commodities(&directives, &mut stdout)?;
        }
        Report::Stats => {
            report_stats(&directives, file, &mut stdout)?;
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
    let mut balances: BTreeMap<InternedStr, Inventory> = BTreeMap::new();

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
    writeln!(
        writer,
        "  Balance Assertions: {:>6}",
        stats.balance_assertions
    )?;
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

/// Generate a balance sheet report (Assets, Liabilities, Equity).
fn report_balsheet<W: Write>(directives: &[Directive], writer: &mut W) -> Result<()> {
    let mut assets: BTreeMap<InternedStr, Inventory> = BTreeMap::new();
    let mut liabilities: BTreeMap<InternedStr, Inventory> = BTreeMap::new();
    let mut equity: BTreeMap<InternedStr, Inventory> = BTreeMap::new();

    for directive in directives {
        if let Directive::Transaction(txn) = directive {
            for posting in &txn.postings {
                if let Some(amount) = posting.amount() {
                    let account_str: &str = &posting.account;
                    let balances = if account_str.starts_with("Assets:") {
                        &mut assets
                    } else if account_str.starts_with("Liabilities:") {
                        &mut liabilities
                    } else if account_str.starts_with("Equity:") {
                        &mut equity
                    } else {
                        continue;
                    };

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
    }

    // Helper to sum inventory by currency
    fn sum_by_currency(balances: &BTreeMap<InternedStr, Inventory>) -> BTreeMap<String, Decimal> {
        let mut totals: BTreeMap<String, Decimal> = BTreeMap::new();
        for inv in balances.values() {
            for pos in inv.positions() {
                *totals.entry(pos.units.currency.to_string()).or_default() += pos.units.number;
            }
        }
        totals
    }

    // Helper to write section
    fn write_section<W: Write>(
        writer: &mut W,
        title: &str,
        balances: &BTreeMap<InternedStr, Inventory>,
    ) -> Result<()> {
        writeln!(writer, "{title}")?;
        writeln!(writer, "{}", "-".repeat(60))?;
        for (account, inventory) in balances {
            if inventory.is_empty() {
                continue;
            }
            for position in inventory.positions() {
                writeln!(
                    writer,
                    "  {:>12} {:>4}  {}",
                    position.units.number, position.units.currency, account
                )?;
            }
        }
        let totals = sum_by_currency(balances);
        writeln!(writer)?;
        for (currency, total) in &totals {
            writeln!(writer, "  {:>12} {:>4}  Total {title}", total, currency)?;
        }
        writeln!(writer)?;
        Ok(())
    }

    writeln!(writer, "Balance Sheet")?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    write_section(writer, "Assets", &assets)?;
    write_section(writer, "Liabilities", &liabilities)?;
    write_section(writer, "Equity", &equity)?;

    // Net worth = Assets - Liabilities
    let asset_totals = sum_by_currency(&assets);
    let liability_totals = sum_by_currency(&liabilities);
    let mut net_worth: BTreeMap<String, Decimal> = asset_totals.clone();
    for (currency, amount) in &liability_totals {
        *net_worth.entry(currency.clone()).or_default() -= amount;
    }

    writeln!(writer, "Net Worth")?;
    writeln!(writer, "{}", "-".repeat(60))?;
    for (currency, total) in &net_worth {
        writeln!(writer, "  {:>12} {:>4}", total, currency)?;
    }

    Ok(())
}

/// Generate an income statement report (Income and Expenses).
fn report_income<W: Write>(directives: &[Directive], writer: &mut W) -> Result<()> {
    let mut income: BTreeMap<InternedStr, Inventory> = BTreeMap::new();
    let mut expenses: BTreeMap<InternedStr, Inventory> = BTreeMap::new();

    for directive in directives {
        if let Directive::Transaction(txn) = directive {
            for posting in &txn.postings {
                if let Some(amount) = posting.amount() {
                    let account_str: &str = &posting.account;
                    let balances = if account_str.starts_with("Income:") {
                        &mut income
                    } else if account_str.starts_with("Expenses:") {
                        &mut expenses
                    } else {
                        continue;
                    };

                    let inv = balances.entry(posting.account.clone()).or_default();
                    let position = rustledger_core::Position::simple(amount.clone());
                    inv.add(position);
                }
            }
        }
    }

    fn sum_by_currency(balances: &BTreeMap<InternedStr, Inventory>) -> BTreeMap<String, Decimal> {
        let mut totals: BTreeMap<String, Decimal> = BTreeMap::new();
        for inv in balances.values() {
            for pos in inv.positions() {
                *totals.entry(pos.units.currency.to_string()).or_default() += pos.units.number;
            }
        }
        totals
    }

    fn write_section<W: Write>(
        writer: &mut W,
        title: &str,
        balances: &BTreeMap<InternedStr, Inventory>,
    ) -> Result<()> {
        writeln!(writer, "{title}")?;
        writeln!(writer, "{}", "-".repeat(60))?;
        for (account, inventory) in balances {
            if inventory.is_empty() {
                continue;
            }
            for position in inventory.positions() {
                writeln!(
                    writer,
                    "  {:>12} {:>4}  {}",
                    position.units.number, position.units.currency, account
                )?;
            }
        }
        let totals = sum_by_currency(balances);
        writeln!(writer)?;
        for (currency, total) in &totals {
            writeln!(writer, "  {:>12} {:>4}  Total {title}", total, currency)?;
        }
        writeln!(writer)?;
        Ok(())
    }

    writeln!(writer, "Income Statement")?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    write_section(writer, "Income", &income)?;
    write_section(writer, "Expenses", &expenses)?;

    // Net income = -(Income) - Expenses (income is negative in double-entry)
    let income_totals = sum_by_currency(&income);
    let expense_totals = sum_by_currency(&expenses);
    let mut net_income: BTreeMap<String, Decimal> = BTreeMap::new();
    for (currency, amount) in &income_totals {
        // Income is typically negative (credits), so we negate
        *net_income.entry(currency.clone()).or_default() -= amount;
    }
    for (currency, amount) in &expense_totals {
        *net_income.entry(currency.clone()).or_default() -= amount;
    }

    writeln!(writer, "Net Income")?;
    writeln!(writer, "{}", "-".repeat(60))?;
    for (currency, total) in &net_income {
        writeln!(writer, "  {:>12} {:>4}", total, currency)?;
    }

    Ok(())
}

/// Generate a journal/register report.
fn report_journal<W: Write>(
    directives: &[Directive],
    account_filter: Option<&str>,
    limit: Option<usize>,
    writer: &mut W,
) -> Result<()> {
    let mut entries: Vec<_> = directives
        .iter()
        .filter_map(|d| {
            if let Directive::Transaction(txn) = d {
                // Filter by account if specified
                if let Some(filter) = account_filter {
                    if !txn.postings.iter().any(|p| p.account.starts_with(filter)) {
                        return None;
                    }
                }
                Some(txn)
            } else {
                None
            }
        })
        .collect();

    entries.sort_by_key(|t| t.date);

    writeln!(writer, "Transaction Journal")?;
    writeln!(writer, "{}", "=".repeat(80))?;
    writeln!(writer)?;

    let entries_to_show = if let Some(n) = limit {
        entries.into_iter().rev().take(n).collect::<Vec<_>>()
    } else {
        entries
    };

    for txn in entries_to_show {
        let payee = txn.payee.as_deref().unwrap_or("");
        let narration = &txn.narration;
        let desc = if payee.is_empty() {
            narration.to_string()
        } else {
            format!("{} | {}", payee, narration)
        };
        writeln!(writer, "{} {} {}", txn.date, txn.flag, desc)?;

        for posting in &txn.postings {
            if let Some(amount) = posting.amount() {
                writeln!(
                    writer,
                    "  {:50} {:>12} {}",
                    posting.account.as_str(),
                    amount.number,
                    amount.currency
                )?;
            } else {
                writeln!(writer, "  {:50}", posting.account.as_str())?;
            }
        }
        writeln!(writer)?;
    }

    Ok(())
}

/// Generate a holdings report with cost basis.
fn report_holdings<W: Write>(
    directives: &[Directive],
    account_filter: Option<&str>,
    writer: &mut W,
) -> Result<()> {
    // Track holdings: account -> currency -> (units, cost_basis, cost_currency)
    let mut holdings: BTreeMap<InternedStr, BTreeMap<String, (Decimal, Decimal, String)>> =
        BTreeMap::new();

    for directive in directives {
        if let Directive::Transaction(txn) = directive {
            for posting in &txn.postings {
                // Filter by account
                if let Some(filter) = account_filter {
                    if !posting.account.starts_with(filter) {
                        continue;
                    }
                }

                // Only track Assets accounts for holdings
                let account_str: &str = &posting.account;
                if !account_str.starts_with("Assets:") {
                    continue;
                }

                if let Some(amount) = posting.amount() {
                    let account_holdings = holdings.entry(posting.account.clone()).or_default();

                    // Get cost if available
                    let (cost_amount, cost_currency) = if let Some(cost_spec) = &posting.cost {
                        if let Some(cost) = cost_spec.resolve(amount.number, txn.date) {
                            (cost.number * amount.number, cost.currency.to_string())
                        } else {
                            (amount.number, amount.currency.to_string())
                        }
                    } else {
                        (amount.number, amount.currency.to_string())
                    };

                    let entry = account_holdings
                        .entry(amount.currency.to_string())
                        .or_insert((Decimal::ZERO, Decimal::ZERO, cost_currency.clone()));

                    entry.0 += amount.number;
                    entry.1 += cost_amount;
                }
            }
        }
    }

    writeln!(writer, "Holdings")?;
    writeln!(writer, "{}", "=".repeat(80))?;
    writeln!(writer)?;
    writeln!(
        writer,
        "{:50} {:>12} {:>6} {:>12} {:>6}",
        "Account", "Units", "Curr", "Cost Basis", "Curr"
    )?;
    writeln!(writer, "{}", "-".repeat(80))?;

    for (account, currencies) in &holdings {
        for (currency, (units, cost_basis, cost_currency)) in currencies {
            if *units == Decimal::ZERO {
                continue;
            }
            writeln!(
                writer,
                "{:50} {:>12} {:>6} {:>12} {:>6}",
                account.as_str(),
                units,
                currency,
                cost_basis,
                cost_currency
            )?;
        }
    }

    Ok(())
}

/// Generate a net worth over time report.
fn report_networth<W: Write>(directives: &[Directive], period: &str, writer: &mut W) -> Result<()> {
    // Collect all transactions sorted by date
    let mut transactions: Vec<_> = directives
        .iter()
        .filter_map(|d| {
            if let Directive::Transaction(txn) = d {
                Some(txn)
            } else {
                None
            }
        })
        .collect();

    transactions.sort_by_key(|t| t.date);

    if transactions.is_empty() {
        writeln!(writer, "No transactions found.")?;
        return Ok(());
    }

    // Running balance for Assets and Liabilities
    let mut asset_balance: BTreeMap<String, Decimal> = BTreeMap::new();
    let mut liability_balance: BTreeMap<String, Decimal> = BTreeMap::new();

    // Results by period
    let mut period_results: Vec<(String, BTreeMap<String, Decimal>)> = Vec::new();

    let format_period = |date: rustledger_core::NaiveDate, period: &str| -> String {
        match period {
            "daily" => date.to_string(),
            "weekly" => format!("{}-W{:02}", date.year(), date.iso_week().week()),
            "yearly" => format!("{}", date.year()),
            _ => format!("{}-{:02}", date.year(), date.month()), // monthly default
        }
    };

    let mut current_period = String::new();

    for txn in transactions {
        let txn_period = format_period(txn.date, period);

        // If period changed, record snapshot
        if txn_period != current_period && !current_period.is_empty() {
            let mut net_worth: BTreeMap<String, Decimal> = asset_balance.clone();
            for (currency, amount) in &liability_balance {
                *net_worth.entry(currency.clone()).or_default() += amount;
            }
            period_results.push((current_period.clone(), net_worth));
        }
        current_period = txn_period;

        // Update running balances
        for posting in &txn.postings {
            if let Some(amount) = posting.amount() {
                let account_str: &str = &posting.account;
                if account_str.starts_with("Assets:") {
                    *asset_balance
                        .entry(amount.currency.to_string())
                        .or_default() += amount.number;
                } else if account_str.starts_with("Liabilities:") {
                    *liability_balance
                        .entry(amount.currency.to_string())
                        .or_default() += amount.number;
                }
            }
        }
    }

    // Final period
    if !current_period.is_empty() {
        let mut net_worth: BTreeMap<String, Decimal> = asset_balance.clone();
        for (currency, amount) in &liability_balance {
            *net_worth.entry(currency.clone()).or_default() += amount;
        }
        period_results.push((current_period, net_worth));
    }

    writeln!(writer, "Net Worth Over Time ({})", period)?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    for (period_label, net_worth) in &period_results {
        write!(writer, "{:12}", period_label)?;
        for (currency, amount) in net_worth {
            write!(writer, "  {:>12} {}", amount, currency)?;
        }
        writeln!(writer)?;
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
