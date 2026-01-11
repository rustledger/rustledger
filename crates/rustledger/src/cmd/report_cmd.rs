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

    /// Output format (text, csv, json)
    #[arg(short = 'f', long, global = true, default_value = "text")]
    format: OutputFormat,
}

#[derive(Clone, Debug, Default, clap::ValueEnum)]
enum OutputFormat {
    #[default]
    Text,
    Csv,
    Json,
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

    match run(&file, &report, args.verbose, &args.format) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(1)
        }
    }
}

fn run(file: &PathBuf, report: &Report, verbose: bool, format: &OutputFormat) -> Result<()> {
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
            report_balances(&directives, account.as_deref(), format, &mut stdout)?;
        }
        Report::Balsheet => {
            report_balsheet(&directives, format, &mut stdout)?;
        }
        Report::Income => {
            report_income(&directives, format, &mut stdout)?;
        }
        Report::Journal { account, limit } => {
            report_journal(&directives, account.as_deref(), *limit, format, &mut stdout)?;
        }
        Report::Holdings { account } => {
            report_holdings(&directives, account.as_deref(), format, &mut stdout)?;
        }
        Report::Networth { period } => {
            report_networth(&directives, period, format, &mut stdout)?;
        }
        Report::Accounts => {
            report_accounts(&directives, format, &mut stdout)?;
        }
        Report::Commodities => {
            report_commodities(&directives, format, &mut stdout)?;
        }
        Report::Stats => {
            report_stats(&directives, file, &mut stdout)?;
        }
        Report::Prices { commodity } => {
            report_prices(&directives, commodity.as_deref(), format, &mut stdout)?;
        }
    }

    Ok(())
}

/// Generate a balances report.
fn report_balances<W: Write>(
    directives: &[Directive],
    account_filter: Option<&str>,
    format: &OutputFormat,
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

    // Collect data for output
    let mut rows: Vec<(&str, Decimal, &str)> = Vec::new();
    for (account, inventory) in &balances {
        if let Some(filter) = account_filter {
            if !account.starts_with(filter) {
                continue;
            }
        }
        if inventory.is_empty() {
            continue;
        }
        for position in inventory.positions() {
            rows.push((account, position.units.number, &position.units.currency));
        }
    }

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "account,amount,currency")?;
            for (account, amount, currency) in &rows {
                writeln!(writer, "{},{},{}", csv_escape(account), amount, currency)?;
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "[")?;
            for (i, (account, amount, currency)) in rows.iter().enumerate() {
                let comma = if i < rows.len() - 1 { "," } else { "" };
                writeln!(
                    writer,
                    r#"  {{"account": "{}", "amount": "{}", "currency": "{}"}}{}"#,
                    json_escape(account),
                    amount,
                    currency,
                    comma
                )?;
            }
            writeln!(writer, "]")?;
        }
        OutputFormat::Text => {
            writeln!(writer, "Account Balances")?;
            writeln!(writer, "{}", "=".repeat(60))?;
            writeln!(writer)?;
            let mut current_account = "";
            for (account, amount, currency) in &rows {
                if *account != current_account {
                    writeln!(writer, "{account}")?;
                    current_account = account;
                }
                writeln!(writer, "  {amount:>15} {currency}")?;
            }
        }
    }

    Ok(())
}

/// Escape a string for CSV output.
fn csv_escape(s: &str) -> String {
    if s.contains(',') || s.contains('"') || s.contains('\n') {
        format!("\"{}\"", s.replace('"', "\"\""))
    } else {
        s.to_string()
    }
}

/// Escape a string for JSON output.
fn json_escape(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

/// Generate an accounts list.
fn report_accounts<W: Write>(
    directives: &[Directive],
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let mut accounts: BTreeSet<&str> = BTreeSet::new();

    for directive in directives {
        if let Directive::Open(open) = directive {
            accounts.insert(&open.account);
        }
    }

    let accounts: Vec<_> = accounts.into_iter().collect();

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "account")?;
            for account in &accounts {
                writeln!(writer, "{}", csv_escape(account))?;
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "[")?;
            for (i, account) in accounts.iter().enumerate() {
                let comma = if i < accounts.len() - 1 { "," } else { "" };
                writeln!(writer, r#"  "{}"{}"#, json_escape(account), comma)?;
            }
            writeln!(writer, "]")?;
        }
        OutputFormat::Text => {
            writeln!(writer, "Accounts ({} total)", accounts.len())?;
            writeln!(writer, "{}", "=".repeat(40))?;
            writeln!(writer)?;
            for account in &accounts {
                writeln!(writer, "{account}")?;
            }
        }
    }

    Ok(())
}

/// Generate a commodities list.
fn report_commodities<W: Write>(
    directives: &[Directive],
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
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

    let commodities: Vec<_> = commodities.into_iter().collect();

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "commodity")?;
            for commodity in &commodities {
                writeln!(writer, "{commodity}")?;
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "[")?;
            for (i, commodity) in commodities.iter().enumerate() {
                let comma = if i < commodities.len() - 1 { "," } else { "" };
                writeln!(writer, r#"  "{commodity}"{comma}"#)?;
            }
            writeln!(writer, "]")?;
        }
        OutputFormat::Text => {
            writeln!(writer, "Commodities ({} total)", commodities.len())?;
            writeln!(writer, "{}", "=".repeat(40))?;
            writeln!(writer)?;
            for commodity in &commodities {
                writeln!(writer, "{commodity}")?;
            }
        }
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
    format: &OutputFormat,
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

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "commodity,date,price,currency")?;
            for price in &prices {
                writeln!(
                    writer,
                    "{},{},{},{}",
                    price.currency, price.date, price.amount.number, price.amount.currency
                )?;
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "[")?;
            for (i, price) in prices.iter().enumerate() {
                let comma = if i < prices.len() - 1 { "," } else { "" };
                writeln!(
                    writer,
                    r#"  {{"commodity": "{}", "date": "{}", "price": "{}", "currency": "{}"}}{}"#,
                    price.currency, price.date, price.amount.number, price.amount.currency, comma
                )?;
            }
            writeln!(writer, "]")?;
        }
        OutputFormat::Text => {
            writeln!(writer, "Price History")?;
            writeln!(writer, "{}", "=".repeat(60))?;
            writeln!(writer)?;
            if prices.is_empty() {
                writeln!(writer, "No price entries found.")?;
            } else {
                let mut current_currency = "";
                for price in &prices {
                    if price.currency.as_str() != current_currency {
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
        }
    }

    Ok(())
}

/// Generate a balance sheet report (Assets, Liabilities, Equity).
fn report_balsheet<W: Write>(
    directives: &[Directive],
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
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

    // Collect rows: (section, account, amount, currency)
    fn collect_rows(
        section: &str,
        balances: &BTreeMap<InternedStr, Inventory>,
    ) -> Vec<(String, String, Decimal, String)> {
        let mut rows = Vec::new();
        for (account, inventory) in balances {
            if inventory.is_empty() {
                continue;
            }
            for position in inventory.positions() {
                rows.push((
                    section.to_string(),
                    account.to_string(),
                    position.units.number,
                    position.units.currency.to_string(),
                ));
            }
        }
        rows
    }

    let mut all_rows = Vec::new();
    all_rows.extend(collect_rows("Assets", &assets));
    all_rows.extend(collect_rows("Liabilities", &liabilities));
    all_rows.extend(collect_rows("Equity", &equity));

    // Net worth = Assets - Liabilities
    let asset_totals = sum_by_currency(&assets);
    let liability_totals = sum_by_currency(&liabilities);
    let mut net_worth: BTreeMap<String, Decimal> = asset_totals;
    for (currency, amount) in &liability_totals {
        *net_worth.entry(currency.clone()).or_default() -= amount;
    }

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "section,account,amount,currency")?;
            for (section, account, amount, currency) in &all_rows {
                writeln!(
                    writer,
                    "{},{},{},{}",
                    section,
                    csv_escape(account),
                    amount,
                    currency
                )?;
            }
            // Add net worth rows
            for (currency, total) in &net_worth {
                writeln!(writer, "Net Worth,TOTAL,{total},{currency}")?;
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "{{")?;
            writeln!(writer, r#"  "accounts": ["#)?;
            for (i, (section, account, amount, currency)) in all_rows.iter().enumerate() {
                let comma = if i < all_rows.len() - 1 { "," } else { "" };
                writeln!(
                    writer,
                    r#"    {{"section": "{}", "account": "{}", "amount": "{}", "currency": "{}"}}{}"#,
                    section,
                    json_escape(account),
                    amount,
                    currency,
                    comma
                )?;
            }
            writeln!(writer, "  ],")?;
            writeln!(writer, r#"  "net_worth": {{"#)?;
            let nw_vec: Vec<_> = net_worth.iter().collect();
            for (i, (currency, total)) in nw_vec.iter().enumerate() {
                let comma = if i < nw_vec.len() - 1 { "," } else { "" };
                writeln!(writer, r#"    "{currency}": "{total}"{comma}"#)?;
            }
            writeln!(writer, "  }}")?;
            writeln!(writer, "}}")?;
        }
        OutputFormat::Text => {
            fn write_section<W: Write>(
                writer: &mut W,
                title: &str,
                balances: &BTreeMap<InternedStr, Inventory>,
            ) -> Result<BTreeMap<String, Decimal>> {
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
                let mut totals: BTreeMap<String, Decimal> = BTreeMap::new();
                for inv in balances.values() {
                    for pos in inv.positions() {
                        *totals.entry(pos.units.currency.to_string()).or_default() +=
                            pos.units.number;
                    }
                }
                writeln!(writer)?;
                for (currency, total) in &totals {
                    writeln!(writer, "  {total:>12} {currency:>4}  Total {title}")?;
                }
                writeln!(writer)?;
                Ok(totals)
            }

            writeln!(writer, "Balance Sheet")?;
            writeln!(writer, "{}", "=".repeat(60))?;
            writeln!(writer)?;

            write_section(writer, "Assets", &assets)?;
            write_section(writer, "Liabilities", &liabilities)?;
            write_section(writer, "Equity", &equity)?;

            writeln!(writer, "Net Worth")?;
            writeln!(writer, "{}", "-".repeat(60))?;
            for (currency, total) in &net_worth {
                writeln!(writer, "  {total:>12} {currency:>4}")?;
            }
        }
    }

    Ok(())
}

/// Generate an income statement report (Income and Expenses).
fn report_income<W: Write>(
    directives: &[Directive],
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
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

    fn collect_rows(
        section: &str,
        balances: &BTreeMap<InternedStr, Inventory>,
    ) -> Vec<(String, String, Decimal, String)> {
        let mut rows = Vec::new();
        for (account, inventory) in balances {
            if inventory.is_empty() {
                continue;
            }
            for position in inventory.positions() {
                rows.push((
                    section.to_string(),
                    account.to_string(),
                    position.units.number,
                    position.units.currency.to_string(),
                ));
            }
        }
        rows
    }

    let mut all_rows = Vec::new();
    all_rows.extend(collect_rows("Income", &income));
    all_rows.extend(collect_rows("Expenses", &expenses));

    // Net income = -(Income) - Expenses (income is negative in double-entry)
    let income_totals = sum_by_currency(&income);
    let expense_totals = sum_by_currency(&expenses);
    let mut net_income: BTreeMap<String, Decimal> = BTreeMap::new();
    for (currency, amount) in &income_totals {
        *net_income.entry(currency.clone()).or_default() -= amount;
    }
    for (currency, amount) in &expense_totals {
        *net_income.entry(currency.clone()).or_default() -= amount;
    }

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "section,account,amount,currency")?;
            for (section, account, amount, currency) in &all_rows {
                writeln!(
                    writer,
                    "{},{},{},{}",
                    section,
                    csv_escape(account),
                    amount,
                    currency
                )?;
            }
            for (currency, total) in &net_income {
                writeln!(writer, "Net Income,TOTAL,{total},{currency}")?;
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "{{")?;
            writeln!(writer, r#"  "accounts": ["#)?;
            for (i, (section, account, amount, currency)) in all_rows.iter().enumerate() {
                let comma = if i < all_rows.len() - 1 { "," } else { "" };
                writeln!(
                    writer,
                    r#"    {{"section": "{}", "account": "{}", "amount": "{}", "currency": "{}"}}{}"#,
                    section,
                    json_escape(account),
                    amount,
                    currency,
                    comma
                )?;
            }
            writeln!(writer, "  ],")?;
            writeln!(writer, r#"  "net_income": {{"#)?;
            let ni_vec: Vec<_> = net_income.iter().collect();
            for (i, (currency, total)) in ni_vec.iter().enumerate() {
                let comma = if i < ni_vec.len() - 1 { "," } else { "" };
                writeln!(writer, r#"    "{currency}": "{total}"{comma}"#)?;
            }
            writeln!(writer, "  }}")?;
            writeln!(writer, "}}")?;
        }
        OutputFormat::Text => {
            fn write_section<W: Write>(
                writer: &mut W,
                title: &str,
                balances: &BTreeMap<InternedStr, Inventory>,
            ) -> Result<BTreeMap<String, Decimal>> {
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
                let mut totals: BTreeMap<String, Decimal> = BTreeMap::new();
                for inv in balances.values() {
                    for pos in inv.positions() {
                        *totals.entry(pos.units.currency.to_string()).or_default() +=
                            pos.units.number;
                    }
                }
                writeln!(writer)?;
                for (currency, total) in &totals {
                    writeln!(writer, "  {total:>12} {currency:>4}  Total {title}")?;
                }
                writeln!(writer)?;
                Ok(totals)
            }

            writeln!(writer, "Income Statement")?;
            writeln!(writer, "{}", "=".repeat(60))?;
            writeln!(writer)?;

            write_section(writer, "Income", &income)?;
            write_section(writer, "Expenses", &expenses)?;

            writeln!(writer, "Net Income")?;
            writeln!(writer, "{}", "-".repeat(60))?;
            for (currency, total) in &net_income {
                writeln!(writer, "  {total:>12} {currency:>4}")?;
            }
        }
    }

    Ok(())
}

/// Generate a journal/register report.
fn report_journal<W: Write>(
    directives: &[Directive],
    account_filter: Option<&str>,
    limit: Option<usize>,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let mut entries: Vec<_> = directives
        .iter()
        .filter_map(|d| {
            if let Directive::Transaction(txn) = d {
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

    let entries_to_show = if let Some(n) = limit {
        entries.into_iter().rev().take(n).collect::<Vec<_>>()
    } else {
        entries
    };

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "date,flag,payee,narration,account,amount,currency")?;
            for txn in &entries_to_show {
                let payee = txn.payee.as_deref().unwrap_or("");
                for posting in &txn.postings {
                    let (amount, currency) = if let Some(amt) = posting.amount() {
                        (amt.number.to_string(), amt.currency.to_string())
                    } else {
                        (String::new(), String::new())
                    };
                    writeln!(
                        writer,
                        "{},{},{},{},{},{},{}",
                        txn.date,
                        txn.flag,
                        csv_escape(payee),
                        csv_escape(&txn.narration),
                        csv_escape(&posting.account),
                        amount,
                        currency
                    )?;
                }
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "[")?;
            for (i, txn) in entries_to_show.iter().enumerate() {
                let payee = txn.payee.as_deref().unwrap_or("");
                let comma = if i < entries_to_show.len() - 1 {
                    ","
                } else {
                    ""
                };
                writeln!(writer, "  {{")?;
                writeln!(writer, r#"    "date": "{}","#, txn.date)?;
                writeln!(writer, r#"    "flag": "{}","#, txn.flag)?;
                writeln!(writer, r#"    "payee": "{}","#, json_escape(payee))?;
                writeln!(
                    writer,
                    r#"    "narration": "{}","#,
                    json_escape(&txn.narration)
                )?;
                writeln!(writer, r#"    "postings": ["#)?;
                for (j, posting) in txn.postings.iter().enumerate() {
                    let pcomma = if j < txn.postings.len() - 1 { "," } else { "" };
                    let (amount, currency) = if let Some(amt) = posting.amount() {
                        (amt.number.to_string(), amt.currency.to_string())
                    } else {
                        (String::new(), String::new())
                    };
                    writeln!(
                        writer,
                        r#"      {{"account": "{}", "amount": "{}", "currency": "{}"}}{}"#,
                        json_escape(&posting.account),
                        amount,
                        currency,
                        pcomma
                    )?;
                }
                writeln!(writer, "    ]")?;
                writeln!(writer, "  }}{comma}")?;
            }
            writeln!(writer, "]")?;
        }
        OutputFormat::Text => {
            writeln!(writer, "Transaction Journal")?;
            writeln!(writer, "{}", "=".repeat(80))?;
            writeln!(writer)?;

            for txn in &entries_to_show {
                let payee = txn.payee.as_deref().unwrap_or("");
                let narration = &txn.narration;
                let desc = if payee.is_empty() {
                    narration.clone()
                } else {
                    format!("{payee} | {narration}")
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
        }
    }

    Ok(())
}

/// Generate a holdings report with cost basis.
fn report_holdings<W: Write>(
    directives: &[Directive],
    account_filter: Option<&str>,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    // Track holdings: account -> currency -> (units, cost_basis, cost_currency)
    let mut holdings: BTreeMap<InternedStr, BTreeMap<String, (Decimal, Decimal, String)>> =
        BTreeMap::new();

    for directive in directives {
        if let Directive::Transaction(txn) = directive {
            for posting in &txn.postings {
                if let Some(filter) = account_filter {
                    if !posting.account.starts_with(filter) {
                        continue;
                    }
                }

                let account_str: &str = &posting.account;
                if !account_str.starts_with("Assets:") {
                    continue;
                }

                if let Some(amount) = posting.amount() {
                    let account_holdings = holdings.entry(posting.account.clone()).or_default();

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

    // Collect rows: (account, units, currency, cost_basis, cost_currency)
    let mut rows: Vec<(String, Decimal, String, Decimal, String)> = Vec::new();
    for (account, currencies) in &holdings {
        for (currency, (units, cost_basis, cost_currency)) in currencies {
            if *units == Decimal::ZERO {
                continue;
            }
            rows.push((
                account.to_string(),
                *units,
                currency.clone(),
                *cost_basis,
                cost_currency.clone(),
            ));
        }
    }

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "account,units,currency,cost_basis,cost_currency")?;
            for (account, units, currency, cost_basis, cost_currency) in &rows {
                writeln!(
                    writer,
                    "{},{},{},{},{}",
                    csv_escape(account),
                    units,
                    currency,
                    cost_basis,
                    cost_currency
                )?;
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "[")?;
            for (i, (account, units, currency, cost_basis, cost_currency)) in
                rows.iter().enumerate()
            {
                let comma = if i < rows.len() - 1 { "," } else { "" };
                writeln!(
                    writer,
                    r#"  {{"account": "{}", "units": "{}", "currency": "{}", "cost_basis": "{}", "cost_currency": "{}"}}{}"#,
                    json_escape(account),
                    units,
                    currency,
                    cost_basis,
                    cost_currency,
                    comma
                )?;
            }
            writeln!(writer, "]")?;
        }
        OutputFormat::Text => {
            writeln!(writer, "Holdings")?;
            writeln!(writer, "{}", "=".repeat(80))?;
            writeln!(writer)?;
            writeln!(
                writer,
                "{:50} {:>12} {:>6} {:>12} {:>6}",
                "Account", "Units", "Curr", "Cost Basis", "Curr"
            )?;
            writeln!(writer, "{}", "-".repeat(80))?;

            for (account, units, currency, cost_basis, cost_currency) in &rows {
                writeln!(
                    writer,
                    "{account:50} {units:>12} {currency:>6} {cost_basis:>12} {cost_currency:>6}"
                )?;
            }
        }
    }

    Ok(())
}

/// Generate a net worth over time report.
fn report_networth<W: Write>(
    directives: &[Directive],
    period: &str,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
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
        match format {
            OutputFormat::Csv => writeln!(writer, "period,currency,amount")?,
            OutputFormat::Json => writeln!(writer, "[]")?,
            OutputFormat::Text => writeln!(writer, "No transactions found.")?,
        }
        return Ok(());
    }

    let mut asset_balance: BTreeMap<String, Decimal> = BTreeMap::new();
    let mut liability_balance: BTreeMap<String, Decimal> = BTreeMap::new();
    let mut period_results: Vec<(String, BTreeMap<String, Decimal>)> = Vec::new();

    let format_period = |date: rustledger_core::NaiveDate, period: &str| -> String {
        match period {
            "daily" => date.to_string(),
            "weekly" => format!("{}-W{:02}", date.year(), date.iso_week().week()),
            "yearly" => format!("{}", date.year()),
            _ => format!("{}-{:02}", date.year(), date.month()),
        }
    };

    let mut current_period = String::new();

    for txn in transactions {
        let txn_period = format_period(txn.date, period);

        if txn_period != current_period && !current_period.is_empty() {
            let mut net_worth: BTreeMap<String, Decimal> = asset_balance.clone();
            for (currency, amount) in &liability_balance {
                *net_worth.entry(currency.clone()).or_default() += amount;
            }
            period_results.push((current_period.clone(), net_worth));
        }
        current_period = txn_period;

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

    if !current_period.is_empty() {
        let mut net_worth: BTreeMap<String, Decimal> = asset_balance.clone();
        for (currency, amount) in &liability_balance {
            *net_worth.entry(currency.clone()).or_default() += amount;
        }
        period_results.push((current_period, net_worth));
    }

    match format {
        OutputFormat::Csv => {
            writeln!(writer, "period,currency,amount")?;
            for (period_label, net_worth) in &period_results {
                for (currency, amount) in net_worth {
                    writeln!(writer, "{period_label},{currency},{amount}")?;
                }
            }
        }
        OutputFormat::Json => {
            writeln!(writer, "[")?;
            let total_entries: usize = period_results.iter().map(|(_, nw)| nw.len()).sum();
            let mut entry_idx = 0;
            for (period_label, net_worth) in &period_results {
                for (currency, amount) in net_worth {
                    entry_idx += 1;
                    let comma = if entry_idx < total_entries { "," } else { "" };
                    writeln!(
                        writer,
                        r#"  {{"period": "{period_label}", "currency": "{currency}", "amount": "{amount}"}}{comma}"#
                    )?;
                }
            }
            writeln!(writer, "]")?;
        }
        OutputFormat::Text => {
            writeln!(writer, "Net Worth Over Time ({period})")?;
            writeln!(writer, "{}", "=".repeat(60))?;
            writeln!(writer)?;

            for (period_label, net_worth) in &period_results {
                write!(writer, "{period_label:12}")?;
                for (currency, amount) in net_worth {
                    write!(writer, "  {amount:>12} {currency}")?;
                }
                writeln!(writer)?;
            }
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
