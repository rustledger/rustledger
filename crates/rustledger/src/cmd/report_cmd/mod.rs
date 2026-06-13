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
use rustledger_loader::LoadOptions;
use std::io;
use std::path::PathBuf;
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

    /// Disable the on-disk parse cache (always re-parse)
    #[arg(long = "no-cache", global = true)]
    pub no_cache: bool,
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

/// Run the report command with the given arguments.
///
/// Loads and processes the file FIRST, then — only on a successful load —
/// builds a pager writer (for text output, unless `--no-pager`) or a plain
/// stdout writer and renders into it. The agent-native `ag-rledger` binary
/// instead calls [`run_with_writer`] with its own buffer so it can capture
/// the report.
///
/// Ordering matters: the load must happen before the pager is created.
/// Creating the pager first would flash the alternate screen (and on a
/// failed load, leave the terminal in pager mode with no output) for an
/// existing-but-invalid ledger. By loading first we never spawn the pager
/// unless we actually have a report to show.
pub fn run(
    file: &PathBuf,
    report: &Report,
    verbose: bool,
    format: &OutputFormat,
    no_pager: bool,
    no_cache: bool,
) -> Result<()> {
    // Existence check → load → (only now) create pager → render → finish.
    // Both the load and any render error surface BEFORE the pager exists,
    // so a bad file never flashes the alternate screen.
    let loaded = load(file, report, verbose, no_cache)?;

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

    // Always restore the terminal (drop the pager) even if rendering fails,
    // so a write error mid-report doesn't leave the terminal stuck in pager
    // mode.
    let result = render(&loaded, report, file, format, &mut writer);
    writer.finish();
    result
}

/// Run the report command, writing report output to the injected `out`
/// writer (no pager).
///
/// This is the writer-injectable entry point used by `ag-rledger`: it
/// produces exactly the same report bytes `run()` would emit to a
/// non-paged stdout, but routed to `out` so the caller can buffer them
/// into a JSON envelope. Verbose progress and load errors still go to
/// stderr. The on-disk parse cache stays enabled: the load phase is always
/// invoked with `no_cache = false` (this entry point takes no `no_cache`
/// parameter).
pub fn run_with_writer<W: io::Write>(
    file: &PathBuf,
    report: &Report,
    verbose: bool,
    format: &OutputFormat,
    out: &mut W,
) -> Result<()> {
    // Existence-check → load → render(buffer): the same two-phase split the
    // production `run()` uses, minus the pager. Producing identical report
    // bytes is guaranteed because both paths funnel through `load` + `render`.
    let loaded = load(file, report, verbose, false)?;
    render(&loaded, report, file, format, out)
}

/// Loaded directive views, the output of the load phase of a report.
///
/// Splitting the report into a load phase ([`load`]) that returns this and a
/// render phase ([`render`]) lets the production `run()` perform the load —
/// and surface any load error — BEFORE it creates the pager, so an
/// existing-but-invalid ledger never flashes the alternate screen.
struct LoadedReport {
    /// Source-faithful directive stream (pads remain `Pad`). Used by
    /// reports that count/list source directive kinds.
    directives: Vec<rustledger_core::Directive>,
    /// Pad-expanded view, present only when the ledger has pads AND the
    /// report is balance-computing. `None` means "use `directives`".
    balance_view: Option<Vec<rustledger_core::Directive>>,
}

/// Load and fully process the file (parse → book → plugins), producing the
/// directive views the render phase needs.
///
/// This is the load phase shared by [`run`] and [`run_with_writer`]. It
/// performs the existence check, loads via the on-disk cache, processes, and
/// computes the (optional) pad-expanded balance view — but renders nothing.
fn load(file: &PathBuf, report: &Report, verbose: bool, no_cache: bool) -> Result<LoadedReport> {
    // Check if file exists
    if !file.exists() {
        anyhow::bail!("file not found: {}", file.display());
    }

    // Load and fully process the file (parse → book → plugins).
    // Verbose progress (incl. the "Loading ..." / cache-hit lines) is
    // emitted by `load_result_cached`, so don't pre-log here - that
    // would double up on a miss and mislead on a cache hit.
    let options = LoadOptions {
        validate: false, // Reports don't need validation
        ..Default::default()
    };

    // Parse via the shared on-disk cache: `parse()` dominates load
    // cost and is identical run-to-run for an unchanged file, so a
    // repeated `report` (or a `report` after `check`) skips the parse
    // entirely. The cached `LoadResult` is the parsed (pre-booking)
    // stream; `process` books it exactly as the uncached `load` did.
    // Disable with `--no-cache` or `BEANCOUNT_DISABLE_LOAD_CACHE`.
    let (raw, _from_cache) = crate::cmd::loadcache::load_result_cached(file, no_cache, verbose)?;
    let ledger = rustledger_loader::process(raw, &options)
        .with_context(|| format!("failed to load {}", file.display()))?;

    // Report any errors
    for err in &ledger.errors {
        eprintln!("{}: {}", err.code, err.message);
    }

    // Two views of the directive stream, chosen per-report below:
    //
    // - `directives` (source-faithful): pads remain as `Pad`.
    //   Used by reports that count or list source directive kinds:
    //   stats, journal, accounts, commodities, prices.
    // - `balance_view` (pad-expanded): pads merged with synthesized
    //   P-flag transactions. Used by reports that maintain running
    //   inventories and ask "what is the balance": balances,
    //   balsheet, income, holdings, networth (#1288).
    //
    // The split mirrors the architectural rule documented on
    // `rustledger_loader::Ledger.directives`. `balance_view` is
    // expensive (an O(n) clone + `process_pads` walk + re-sort), so
    // compute it only when the chosen report actually needs it AND
    // the ledger actually has `pad` directives. With no pads there
    // are no synth transactions to merge, so the pad-expanded view
    // is byte-for-byte the source stream — building it would clone
    // and re-sort the whole stream to produce an identical result.
    // Most ledgers have no pads, so the balance reports fall through
    // to the borrowed source directly (no clone). Run both checks
    // BEFORE consuming `ledger.directives` so the borrow checker is
    // happy.
    let needs_balance_view = matches!(
        report,
        Report::Balances { .. }
            | Report::Balsheet
            | Report::Income
            | Report::Holdings { .. }
            | Report::Networth { .. }
    );
    let has_pads = needs_balance_view
        && ledger
            .directives
            .iter()
            .any(|s| matches!(&s.value, rustledger_core::Directive::Pad(_)));
    let balance_view = if has_pads {
        Some(ledger.balance_view())
    } else {
        None
    };
    let directives: Vec<_> = ledger.directives.into_iter().map(|s| s.value).collect();

    Ok(LoadedReport {
        directives,
        balance_view,
    })
}

/// Render the already-loaded report into `writer`.
///
/// This is the render phase shared by [`run`] and [`run_with_writer`]; it
/// touches no files and never spawns a pager. The caller owns writer setup
/// (pager vs. plain stdout vs. agent buffer) and any post-write `finish()`.
/// `file` is only used by the `stats` report (for the file-size line).
fn render<W: io::Write>(
    loaded: &LoadedReport,
    report: &Report,
    file: &PathBuf,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let directives = &loaded.directives;

    // Balance-computing reports read the pad-expanded view when one
    // was built (the ledger has pads), otherwise the source stream
    // directly. `unwrap_or` makes the no-pad fast path explicit: same
    // directives, no clone.
    let balance_input: &[rustledger_core::Directive] =
        loaded.balance_view.as_deref().unwrap_or(directives);

    // Generate the requested report into the caller-provided writer.
    // Balance-computing reports get `balance_input` (the pad-expanded
    // view when the ledger has pads, otherwise the borrowed source
    // stream); source-faithful reports get `&directives`.
    match report {
        Report::Balances { account } => {
            balances::report_balances(balance_input, account.as_deref(), format, writer)?;
        }
        Report::Balsheet => {
            balsheet::report_balsheet(balance_input, format, writer)?;
        }
        Report::Income => {
            income::report_income(balance_input, format, writer)?;
        }
        Report::Journal { account, limit } => {
            journal::report_journal(directives, account.as_deref(), *limit, format, writer)?;
        }
        Report::Holdings { account } => {
            holdings::report_holdings(balance_input, account.as_deref(), format, writer)?;
        }
        Report::Networth {
            period,
            currency,
            account,
            no_zero,
        } => {
            networth::report_networth(
                balance_input,
                period,
                currency.as_deref(),
                account.as_deref(),
                *no_zero,
                format,
                writer,
            )?;
        }
        Report::Accounts => {
            accounts::report_accounts(directives, format, writer)?;
        }
        Report::Commodities => {
            commodities::report_commodities(directives, format, writer)?;
        }
        Report::Stats => {
            stats::report_stats(directives, file, writer)?;
        }
        Report::Prices { commodity } => {
            prices::report_prices(directives, commodity.as_deref(), format, writer)?;
        }
    }

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
