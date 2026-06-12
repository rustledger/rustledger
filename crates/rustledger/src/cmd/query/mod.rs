//! rledger query - Query beancount files with BQL.
//!
//! This is the primary rustledger command for querying ledgers.
//! For backwards compatibility with Python beancount, `bean-query` is also available.
//!
//! # Usage
//!
//! ```bash
//! rledger query ledger.beancount "SELECT account, SUM(position) GROUP BY account"
//! rledger query ledger.beancount -F query.bql
//! rledger query ledger.beancount  # Interactive mode
//! ```

mod interactive;
mod output;

use crate::cmd::completions::ShellType;
use anyhow::{Context, Result};
use clap::Parser;
use rustledger_booking::merge_with_padding;
use rustledger_core::DisplayContext;
use rustledger_loader::LoadOptions;
use std::fs;
use std::io;
use std::path::PathBuf;
/// System tables available in BQL queries (prefixed with #).
const SYSTEM_TABLES: &[&str] = &[
    "#accounts",
    "#balances",
    "#commodities",
    "#documents",
    "#entries",
    "#events",
    "#notes",
    "#postings",
    "#prices",
    "#transactions",
];

/// Query beancount files with BQL.
#[derive(Parser, Debug)]
#[command(name = "query")]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// The beancount file to query (uses config default if not specified)
    #[arg(value_name = "FILE")]
    pub file: Option<PathBuf>,

    /// Generate shell completions and exit
    #[arg(long, value_name = "SHELL", hide = true)]
    pub generate_completions: Option<ShellType>,

    /// BQL query to execute (if not provided, enters interactive mode)
    #[arg(value_name = "QUERY", trailing_var_arg = true, num_args = 0..)]
    pub query: Vec<String>,

    /// Read query from file
    #[arg(short = 'F', long = "query-file", value_name = "QUERY_FILE")]
    pub query_file: Option<PathBuf>,

    /// Output file (default: stdout)
    #[arg(short = 'o', long, value_name = "OUTPUT_FILE")]
    pub output: Option<PathBuf>,

    /// Output format (text, csv, json, beancount)
    #[arg(short = 'f', long)]
    pub format: Option<OutputFormat>,

    /// Numberify output (remove currencies, output raw numbers)
    #[arg(short = 'm', long)]
    pub numberify: bool,

    /// Do not report ledger validation errors on load
    #[arg(short = 'q', long = "no-errors")]
    pub no_errors: bool,

    /// Show verbose output
    #[arg(short, long)]
    pub verbose: bool,

    /// Disable the on-disk parse cache (always re-parse)
    #[arg(long = "no-cache")]
    pub no_cache: bool,
}

/// Output format for query results.
#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
pub enum OutputFormat {
    /// Plain text output (default).
    Text,
    /// CSV output.
    Csv,
    /// JSON output.
    Json,
    /// Beancount directive output.
    Beancount,
}

impl std::fmt::Display for OutputFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Text => write!(f, "text"),
            Self::Csv => write!(f, "csv"),
            Self::Json => write!(f, "json"),
            Self::Beancount => write!(f, "beancount"),
        }
    }
}

/// Run the query command, writing results to stdout.
///
/// Thin wrapper over [`run_with_writer`] for the synchronous `rledger`
/// binary. Batch queries (a query string or `--query-file`) stream their
/// output through the writer; the interactive REPL still uses stdout
/// directly since it has no agent-native equivalent.
pub fn run(args: &Args) -> Result<()> {
    let mut stdout = io::stdout();
    run_with_writer(args, &mut stdout)
}

/// Run the query command with the given arguments, writing batch query
/// results to `out`.
///
/// Behavior matches the original `run()`: a `--output` file still takes
/// precedence over `out`, validation errors still go to stderr, and
/// interactive mode (no query text) is unchanged. Only the default
/// stdout sink for batch results is replaced by the injected writer, so
/// `ag-rledger` can capture query output into a JSON envelope.
pub fn run_with_writer<W: io::Write>(args: &Args, out: &mut W) -> Result<()> {
    // File is required (the --generate-completions flag is only for standalone bean-query)
    let Some(file) = args.file.as_ref() else {
        anyhow::bail!("FILE is required");
    };

    // Check if file exists
    if !file.exists() {
        anyhow::bail!("file not found: {}", file.display());
    }

    // Load and fully process the file (parse → book → plugins).
    let options = LoadOptions {
        validate: false, // Query doesn't need validation
        ..Default::default()
    };

    // Parse via the shared on-disk cache: `parse()` dominates load cost
    // and is identical run-to-run for an unchanged file, so a repeated
    // `query` (or a `query` after `check`/`report`) skips the parse. The
    // cached `LoadResult` is the parsed (pre-booking) stream with a
    // rebuilt display context (`CacheEntry::into_load_result`), so
    // booking and the display-context-dependent BQL output below are
    // identical to the uncached path. Disable with `--no-cache` or
    // `BEANCOUNT_DISABLE_LOAD_CACHE`.
    let (raw, _from_cache) =
        crate::cmd::loadcache::load_result_cached(file, args.no_cache, args.verbose)?;
    let ledger = rustledger_loader::process(raw, &options)
        .with_context(|| format!("failed to load {}", file.display()))?;

    // Report errors to stderr (matching bean-query behavior)
    // Continue with successfully parsed directives rather than bailing
    if !ledger.errors.is_empty() && !args.no_errors {
        for err in &ledger.errors {
            eprintln!("{}: {}", err.code, err.message);
        }
        eprintln!();
    }

    // Get directives (already booked and plugins applied)
    let booked_directives: Vec<_> = ledger.directives.into_iter().map(|s| s.value).collect();

    // Merge pad-synthesized transactions into the directive stream
    // (BQL is a balance-computing consumer). `merge_with_padding`
    // preserves the original Pad directives in the output so
    // `FROM #entries WHERE type = 'pad'` audits still enumerate them,
    // AND handles multi-pad shadowing (#1300) correctly by
    // construction via `process_pads`.
    let directives = merge_with_padding(&booked_directives);

    // Use display context from the loaded ledger
    let display_context = ledger.display_context;

    if args.verbose {
        eprintln!("Loaded {} directives", directives.len());
    }

    // Determine query source
    let query_str = if !args.query.is_empty() {
        args.query.join(" ")
    } else if let Some(ref query_file) = args.query_file {
        fs::read_to_string(query_file)
            .with_context(|| format!("failed to read query file {}", query_file.display()))?
    } else {
        // Interactive mode
        return interactive::run_interactive(file, &directives, &display_context, args);
    };

    // Batch query: no pager (matching Python bean-query behavior).
    // Pager is only used in interactive REPL mode.
    let settings = ShellSettings::from_args(args, display_context);
    if let Some(ref output_path) = settings.output_file {
        let mut file = fs::File::create(output_path)
            .with_context(|| format!("failed to create output file {}", output_path.display()))?;
        output::execute_query(&query_str, &directives, &settings, &mut file)
    } else {
        output::execute_query(&query_str, &directives, &settings, out)
    }
}

/// Shell settings for query output and interactive mode.
struct ShellSettings {
    format: OutputFormat,
    numberify: bool,
    pager: bool,
    output_file: Option<PathBuf>,
    display_context: DisplayContext,
}

impl ShellSettings {
    fn from_args(args: &Args, display_context: DisplayContext) -> Self {
        Self {
            format: args.format.unwrap_or(OutputFormat::Text),
            numberify: args.numberify,
            pager: true,
            output_file: args.output.clone(),
            display_context,
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
            "beancount" => Some(Self::Beancount),
            _ => None,
        }
    }
}
