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
mod budget;
mod capgains;
mod commodities;
mod holdings;
mod income;
mod journal;
mod networth;
mod prices;
mod returns;
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

impl From<&OutputFormat> for rustledger_core::OutputSurface {
    /// Which consumer each report output format is written for.
    ///
    /// Exhaustive on purpose: a new format must state whether it is read by a
    /// person or parsed by a program (#1892).
    fn from(f: &OutputFormat) -> Self {
        match f {
            OutputFormat::Text => Self::Human,
            OutputFormat::Csv | OutputFormat::Json => Self::Machine,
        }
    }
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
    /// Investment returns (money-weighted / XIRR) for an account scope
    Returns {
        /// Account prefix(es) holding the investment (repeatable). Required;
        /// defines the portfolio boundary, e.g. `Assets:Investments`.
        #[arg(short, long, required = true)]
        investments: Vec<String>,
        /// Account prefix(es) for the investment's income and expenses —
        /// dividends, realized gains, and broker fees (repeatable), e.g.
        /// `Income:Dividends`. These are the P&L generated by the investment,
        /// kept out of the external cash flows.
        #[arg(short = 'n', long)]
        income: Vec<String>,
        /// Reporting currency for the return. Defaults to the ledger's first
        /// `operating_currency` option.
        #[arg(short, long)]
        currency: Option<String>,
        /// Valuation date (the horizon and terminal-value date), `YYYY-MM-DD`.
        /// Defaults to today.
        #[arg(short, long)]
        end: Option<String>,
        /// Add one row per `returns-group:` group (declared on `open`
        /// directives), each an independent sub-portfolio, alongside the
        /// whole-portfolio total. Grouping is opt-in so the default output shape
        /// is unchanged.
        #[arg(long)]
        by_group: bool,
    },
    /// Realized capital gains/losses per tax lot (short vs long term)
    Capgains {
        /// Filter to disposals from accounts under this prefix (default: all).
        #[arg(short, long)]
        account: Option<String>,
        /// Only disposals in this calendar/tax year (`YYYY`).
        #[arg(short, long)]
        year: Option<i32>,
        /// Exclude disposals after this date (`YYYY-MM-DD`).
        #[arg(short, long)]
        end: Option<String>,
        /// Override the long-term threshold with a fixed day count: a lot held
        /// strictly more than this many days is long-term. The default (unset)
        /// uses the calendar rule — long-term when the sale is more than one year
        /// after acquisition — which is leap-year correct (the US "> 1 year" rule),
        /// unlike any fixed day count.
        #[arg(long)]
        long_term_days: Option<i64>,
        /// Add the annualized realized return (IRR) of each closed lot, plus a
        /// pooled IRR per term and currency. This is a **realized-only**
        /// money-weighted return over lots you actually closed; for the
        /// total-portfolio return including what you still hold, use
        /// `report returns`.
        #[arg(long)]
        irr: bool,
    },
    /// Budgeted vs actual spending, from Fava-compatible `custom "budget"` directives
    Budget {
        /// Only accounts under this prefix (default: all budgeted accounts).
        #[arg(short, long)]
        account: Option<String>,
        /// Start of the reporting window, inclusive (`YYYY-MM-DD`).
        /// Defaults to the start of the year `--to` falls in, so narrowing
        /// `--to` narrows the window with it rather than silently reporting
        /// from January of the CURRENT year against an older `--to`.
        /// (No short flag: `-f` is the global `--format`.)
        #[arg(long)]
        from: Option<String>,
        /// End of the reporting window, EXCLUSIVE (`YYYY-MM-DD`).
        /// Defaults to tomorrow, so that the default window includes today.
        /// (No short flag: `-t` is unused but `--to` stays symmetric with `--from`.)
        #[arg(long)]
        to: Option<String>,
        /// Count spending in subaccounts toward a parent's budget, summing the
        /// parent's own budget with any child budgets. Off by default, matching
        /// Fava: a budget on `Expenses:Food` covers only that exact account.
        #[arg(long)]
        children: bool,
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
    let loaded = load(
        file,
        report,
        verbose,
        no_cache,
        &mut DiagnosticsToWriter(io::stderr()),
    )?;

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
    let result = // The terminal path sends diagnostics to stderr, where they
    // interleave with the table above them.
    render(
        &loaded,
        report,
        file,
        format,
        &mut writer,
        &mut DiagnosticsToWriter(io::stderr()),
    );
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
/// One thing a report needs to tell the reader that its figures cannot.
///
/// STRUCTURED, not a formatted line. Each surface decides how to show it: the
/// terminal writes `warning: <date>: <message>` to stderr, and `ag-rledger`
/// emits a JSON object per diagnostic. A text sink forced the agent surface to
/// reconstruct records by splitting on newlines, which a message carrying its
/// own newline (the "no budgets declared" note quotes an example directive)
/// silently broke into two.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    /// The error code, for diagnostics that have one (`E11001`, `LOAD`).
    pub code: Option<String>,
    /// The date the diagnostic is about, not the date it was produced.
    pub date: Option<NaiveDate>,
    /// The account it concerns, when it can be attributed to one.
    pub account: Option<String>,
    /// What is wrong, phrased for a human.
    pub message: String,
}

impl Diagnostic {
    /// A diagnostic with only prose — what most report warnings are.
    pub fn message(message: impl Into<String>) -> Self {
        Self {
            code: None,
            date: None,
            account: None,
            message: message.into(),
        }
    }

    /// The terminal rendering: what `rledger` writes to stderr.
    #[must_use]
    pub fn to_line(&self) -> String {
        let mut out = String::from("warning: ");
        if let Some(code) = &self.code {
            out.push_str(code);
            out.push_str(": ");
        }
        if let Some(date) = self.date {
            out.push_str(&date.to_string());
            out.push_str(": ");
        }
        out.push_str(&self.message);
        out
    }
}

/// Where a report's diagnostics go.
///
/// A trait rather than a writer so the agent surface can keep the fields. The
/// CLI's implementation formats to stderr; `ag-rledger`'s collects records.
pub trait Diagnostics {
    /// Record one diagnostic.
    fn emit(&mut self, diagnostic: Diagnostic);
}

/// Writes each diagnostic as a line — the terminal's behavior.
pub struct DiagnosticsToWriter<W: io::Write>(pub W);

impl<W: io::Write> Diagnostics for DiagnosticsToWriter<W> {
    fn emit(&mut self, diagnostic: Diagnostic) {
        // A failed WARNING write must never cost the reader the REPORT.
        let _ = writeln!(self.0, "{}", diagnostic.to_line());
    }
}

/// Keeps the records, for a caller that will serialize them.
#[derive(Default)]
pub struct CollectedDiagnostics(pub Vec<Diagnostic>);

impl Diagnostics for CollectedDiagnostics {
    fn emit(&mut self, diagnostic: Diagnostic) {
        self.0.push(diagnostic);
    }
}

/// `warnings` receives the report's diagnostics — budgets on accounts that are
/// never opened, figures too large to represent, and the like.
///
/// A parameter rather than `eprintln!` because a report's warnings are part of
/// its answer, and the caller decides where they belong. The CLI sends them to
/// stderr, where a terminal interleaves them with the table. `ag-rledger`
/// buffers them into its JSON envelope, which drops the process's real stderr —
/// so before this, an agent asking for a text or CSV budget report received a
/// tidy `0.0%`-used row for a budget on a misspelled account with nothing
/// saying so. That is the silent misreport the diagnostics exist to catch,
/// reintroduced on the one surface that cannot see past it.
pub fn run_with_writer<W: io::Write>(
    file: &PathBuf,
    report: &Report,
    verbose: bool,
    format: &OutputFormat,
    out: &mut W,
    warnings: &mut dyn Diagnostics,
) -> Result<()> {
    // Existence-check → load → render(buffer): the same two-phase split the
    // production `run()` uses, minus the pager. Producing identical report
    // bytes is guaranteed because both paths funnel through `load` + `render`.
    let loaded = load(file, report, verbose, false, warnings)?;
    render(&loaded, report, file, format, out, warnings)
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
    /// Realized capital gains captured by the loader's canonical booking pass,
    /// consumed by the capgains report. Empty for every other report.
    capital_gains: Vec<rustledger_booking::CapitalGain>,
    /// Config-aware account-type classifier (honors `name_*` renames).
    /// Reports must route/sign accounts through this, never by hardcoded
    /// root-prefix matching — renamed ledgers otherwise misroute (L5:
    /// empty income statement under `option "name_income" "Revenue"`).
    account_types: rustledger_core::AccountTypes,
    /// Pad-expanded view, present only when the ledger has pads AND the
    /// report is balance-computing. `None` means "use `directives`".
    balance_view: Option<Vec<rustledger_core::Directive>>,
    /// Per-currency display precision inferred by the loader (plus
    /// `display_precision` overrides and `render_commas`). Balance-style
    /// reports render numbers through this — the same context BQL output
    /// uses — instead of raw `Decimal` `Display`, whose precision is an
    /// artifact of booking arithmetic rather than ledger convention (U4).
    display_context: rustledger_core::DisplayContext,
    /// The ledger's `operating_currency` option values, in declaration order.
    /// The returns report uses the first as the default reporting currency
    /// (overridable with `--currency`); other reports ignore it.
    operating_currency: Vec<String>,
}

/// Load and fully process the file (parse → book → plugins), producing the
/// directive views the render phase needs.
///
/// This is the load phase shared by [`run`] and [`run_with_writer`]. It
/// performs the existence check, loads via the on-disk cache, processes, and
/// computes the (optional) pad-expanded balance view — but renders nothing.
fn load(
    file: &PathBuf,
    report: &Report,
    verbose: bool,
    no_cache: bool,
    warnings: &mut dyn Diagnostics,
) -> Result<LoadedReport> {
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
        // Only the capgains report reads `Ledger::capital_gains`; opt in so no other
        // report pays to retain the vector.
        collect_capital_gains: matches!(report, Report::Capgains { .. }),
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

    // To the caller's sink, like every other diagnostic. These are the ones an
    // agent can least afford to miss: a parse failure means recovery may have
    // dropped directives, so the report below is computed over less than the
    // ledger says. Left on `eprintln!`, they reached the terminal and nothing
    // else — a confident, complete-looking report over a file that did not
    // parse, which is the failure the sink was introduced to end.
    for err in &ledger.errors {
        warnings.emit(Diagnostic {
            code: Some(err.code.clone()),
            date: None,
            account: None,
            message: err.message.clone(),
        });
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
            // Returns extraction requires the booked, pad-expanded stream (its
            // terminal valuation realizes inventory, including pad-seeded lots).
            | Report::Returns { .. }
            // Budget sums postings over a window, so pad-synthesized postings are
            // spending like any other — without this the budget report disagreed
            // with `balances`/`income` on the same ledger.
            | Report::Budget { .. }
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
    let account_types = ledger.options.to_account_types();
    let display_context = ledger.display_context.clone();
    let operating_currency = ledger.options.operating_currency.clone();
    let capital_gains = ledger.capital_gains;
    let directives: Vec<_> = ledger.directives.into_iter().map(|s| s.value).collect();

    Ok(LoadedReport {
        directives,
        capital_gains,
        account_types,
        balance_view,
        display_context,
        operating_currency,
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
    warnings: &mut dyn Diagnostics,
) -> Result<()> {
    let directives = &loaded.directives;

    // Thousands separators are resolved ONCE for the surface being written:
    // they belong in a rendered table, never in CSV/JSON a program parses
    // (#1892). Every renderer below takes this context rather than the raw
    // ledger one.
    let display_context = loaded.display_context.for_surface(format.into());

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
            balances::report_balances(
                balance_input,
                account.as_deref(),
                &display_context,
                format,
                writer,
            )?;
        }
        Report::Balsheet => {
            balsheet::report_balsheet(
                balance_input,
                &loaded.account_types,
                &display_context,
                format,
                writer,
            )?;
        }
        Report::Income => {
            income::report_income(
                balance_input,
                &loaded.account_types,
                &display_context,
                format,
                writer,
            )?;
        }
        Report::Journal { account, limit } => {
            journal::report_journal(directives, account.as_deref(), *limit, format, writer)?;
        }
        Report::Holdings { account } => {
            holdings::report_holdings(
                balance_input,
                &loaded.account_types,
                account.as_deref(),
                &display_context,
                format,
                writer,
            )?;
        }
        Report::Networth {
            period,
            currency,
            account,
            no_zero,
        } => {
            networth::report_networth(
                balance_input,
                &loaded.account_types,
                &display_context,
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
        Report::Returns {
            investments,
            income,
            currency,
            end,
            by_group,
        } => {
            let outcome = returns::report_returns(
                balance_input,
                &loaded.operating_currency,
                investments,
                income,
                currency.as_deref(),
                end.as_deref(),
                *by_group,
                &display_context,
                format,
                writer,
                warnings,
            )?;
            // The report is already written. A partial `--by-group` report exits
            // non-zero so a pipeline gating on exit status does not treat an
            // incomplete report as a success. The exit-code policy lives here, at
            // the CLI boundary, not inside the report producer.
            if let returns::ReturnsOutcome::Partial { unvaluable, total } = outcome {
                anyhow::bail!(
                    "returns report is incomplete: {unvaluable} of {total} {} could not be valued \
                     (see the n/a rows and the warnings above)",
                    if total == 1 { "scope" } else { "scopes" },
                );
            }
        }
        Report::Capgains {
            account,
            year,
            end,
            long_term_days,
            irr,
        } => {
            if let Some(n) = long_term_days
                && *n < 0
            {
                anyhow::bail!("--long-term-days must be non-negative (got {n})");
            }
            let end_date: Option<NaiveDate> = end
                .as_deref()
                .map(|s| {
                    s.parse()
                        .with_context(|| format!("invalid --end date {s:?} (expected YYYY-MM-DD)"))
                })
                .transpose()?;
            let filter = capgains::CapgainsFilter {
                account: account.as_deref(),
                year: *year,
                end: end_date,
            };
            capgains::report_capgains(
                &loaded.capital_gains,
                &filter,
                *long_term_days,
                *irr,
                &display_context,
                format,
                writer,
                warnings,
            )?;
        }
        Report::Budget {
            account,
            from,
            to,
            children,
        } => {
            let parse_date = |s: &str| -> Result<NaiveDate> {
                s.parse()
                    .with_context(|| format!("invalid date {s:?} (expected YYYY-MM-DD)"))
            };
            // Default window: the current year to date. `to` is exclusive, so the
            // default end is today + 1 day — otherwise today's own spending would
            // be silently excluded from its own budget.
            // Same clock source the returns report uses for its default horizon.
            let today = jiff::Zoned::now().date();
            let to_date = match to.as_deref() {
                Some(s) => parse_date(s)?,
                None => today
                    .checked_add(jiff::Span::new().days(1))
                    .unwrap_or(today),
            };
            // The default start is the first of the year *being reported on*, not
            // of the current year: `--to 2025-01-01` asks about 2024, and
            // anchoring the start to wall-clock `now` made that hard-error with
            // an empty window. The sibling horizon-taking reports (returns,
            // capgains) likewise derive their window from the supplied endpoint.
            let from_date = match from.as_deref() {
                Some(s) => parse_date(s)?,
                None => to_date
                    .checked_sub(jiff::Span::new().days(1))
                    .unwrap_or(to_date)
                    .first_of_year(),
            };
            // `--to` is exclusive, so `--from X --to X` is an empty window, not a
            // single day. Rendering it produced a full table of authoritative
            // all-zero rows, indistinguishable from "you budgeted nothing and
            // spent nothing" — and `--from X --to X` is exactly what a user types
            // for one day, since most CLIs read such a pair as inclusive.
            if from_date >= to_date {
                anyhow::bail!(
                    "--from ({from_date}) is not before --to ({to_date}); the window is empty \
                     (--to is EXCLUSIVE, so a single day is --from {from_date} --to <the next day>)"
                );
            }
            let filter = budget::BudgetFilter {
                account: account.as_deref(),
                from: from_date,
                to: to_date,
                children: *children,
            };
            budget::report_budget(
                balance_input,
                &filter,
                &loaded.account_types,
                &display_context,
                format,
                writer,
                warnings,
            )?;
        }
    }

    Ok(())
}

/// The single source of truth for "what does each account hold".
///
/// Every balance-computing report (`balances`, `balsheet`, `income`, …) is a
/// *view* over this map — none re-derives balances itself. That is the whole
/// point: the same "what does each account hold" logic used to live copied
/// across each report, and the copies drifted (reductions failing to net in
/// `balances`/`balsheet` while `income` summed differently — #1726). One
/// function, one behavior, no drift.
///
/// Realization goes through the **booking engine** ([`apply`]), so held
/// commodities keep their lots at cost and reductions are matched against
/// those lots by the account's booking method — the same machinery the
/// loader's book phase uses. Each `Inventory` therefore carries cost, and
/// reports render `5 AAPL {150.00 USD}` like beancount rather than a
/// cost-less `5 AAPL`. Two lots at different costs stay separate
/// (`10 AAPL {150}` + `10 AAPL {200}`), matching beancount.
///
/// `rustledger_returns::terminal_value` re-derives this realization loop (it is
/// a leaf crate and cannot call this CLI-side helper), adding an `<= end_date`
/// filter, to value a portfolio at the report date. If the realization here
/// changes, update that copy in lockstep; the returns CLI PR should add a
/// drift-guard test comparing the two on the same ledger.
///
/// [`apply`]: rustledger_booking::BookingEngine::apply
///
/// # Errors
///
/// When a running balance leaves `rust_decimal`'s range (#1863). Reports print
/// these inventories as exact totals, so an unrepresentable one must abort the
/// report rather than render a clamped figure.
pub(super) fn account_balances(
    directives: &[rustledger_core::Directive],
) -> anyhow::Result<std::collections::BTreeMap<rustledger_core::Account, rustledger_core::Inventory>>
{
    use rustledger_core::Directive;
    // Realize via the booking engine so held commodities carry their lots at
    // cost and reductions match those lots (FIFO/LIFO/etc. per each account's
    // booking method) — the same logic the loader's book phase uses, not a
    // re-implementation. The input directives are already booked (costs
    // resolved, interpolations applied), which is `apply`'s precondition.
    let mut engine = rustledger_booking::BookingEngine::new();
    engine.register_account_methods(directives.iter());
    for directive in directives {
        if let Directive::Transaction(txn) = directive {
            engine.apply(txn)?;
        }
    }
    // FxHashMap has non-deterministic order; collect into a BTreeMap so report
    // rows come out account-sorted and stable across runs.
    Ok(engine.into_inventories().into_iter().collect())
}

// CSV/JSON escaping: single-sourced in core. `escape_json` is the RFC-8259
// string escaper — the required escapes plus `\uXXXX` for every other C0
// control byte — so report JSON stays valid even when a field carries a raw
// control char (e.g. from metadata). Do NOT revert this to `escape_string`
// (the beancount-source escaper leaves control bytes other than \n\t\r raw,
// which is invalid JSON).
pub(super) use rustledger_core::format::escape_csv as csv_escape;
pub(super) use rustledger_core::format::escape_json as json_escape;

/// Replace control characters (and the Unicode line/paragraph separators) with
/// spaces so a value cannot break out of a fixed-width text row.
///
/// The text renderers lay rows out by column width, with no quoting of their
/// own — CSV and JSON escape their fields, but text does not. A label carrying a
/// raw newline therefore splits its row and can forge a convincing extra line in
/// the table, including a fake `TOTAL`. Ledger-derived labels reach these
/// renderers from places that accept arbitrary strings (metadata, and the budget
/// report's quoted-account form), so sanitizing is the renderer's job.
pub(super) fn sanitize_display(s: &str) -> String {
    s.chars()
        .map(|c| {
            if c.is_control() || c == '\u{2028}' || c == '\u{2029}' {
                ' '
            } else {
                c
            }
        })
        .collect()
}

/// Truncate a label to fit a text column, keeping the informative **tail**.
///
/// Account names share their head (`Expenses:Home:Improvements:…`), so cutting
/// the tail is what makes two distinct accounts render as identical rows; the
/// leading `…` marks the elision instead. Always sanitized first (see
/// [`sanitize_display`]).
pub(super) fn truncate_label(s: &str, width: usize) -> String {
    let s = sanitize_display(s);
    if s.chars().count() <= width {
        return s;
    }
    // A zero-width column holds nothing, not an ellipsis: the fallback below
    // returns "…" for `width == 0`, which is one character wider than the
    // column it was asked to fit.
    if width == 0 {
        return String::new();
    }
    let tail: String = s
        .chars()
        .rev()
        .take(width.saturating_sub(1))
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect();
    format!("…{tail}")
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
