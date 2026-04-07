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

use crate::cmd::completions::ShellType;
use anyhow::{Context, Result};
use clap::Parser;
use rustledger_booking::expand_pads;
use rustledger_core::{Directive, DisplayContext};
use rustledger_loader::{LoadOptions, load};
use rustledger_query::{Executor, Value, parse as parse_query};
use rustyline::error::ReadlineError;
use rustyline::history::DefaultHistory;
use rustyline::{DefaultEditor, Editor};
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

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
    query: Vec<String>,

    /// Read query from file
    #[arg(short = 'F', long = "query-file", value_name = "QUERY_FILE")]
    query_file: Option<PathBuf>,

    /// Output file (default: stdout)
    #[arg(short = 'o', long, value_name = "OUTPUT_FILE")]
    output: Option<PathBuf>,

    /// Output format (text, csv, json, beancount)
    #[arg(short = 'f', long)]
    pub format: Option<OutputFormat>,

    /// Numberify output (remove currencies, output raw numbers)
    #[arg(short = 'm', long)]
    numberify: bool,

    /// Do not report ledger validation errors on load
    #[arg(short = 'q', long = "no-errors")]
    no_errors: bool,

    /// Show verbose output
    #[arg(short, long)]
    verbose: bool,
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

/// Main entry point with custom binary name (for bean-query compatibility).
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

    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(1)
        }
    }
}

/// Run the query command with the given arguments.
pub fn run(args: &Args) -> Result<()> {
    // File is required (the --generate-completions flag is only for standalone bean-query)
    let Some(file) = args.file.as_ref() else {
        anyhow::bail!("FILE is required");
    };

    // Check if file exists
    if !file.exists() {
        anyhow::bail!("file not found: {}", file.display());
    }

    // Load and fully process the file (parse → book → plugins)
    // This uses the new loader API which matches Python's loader.load_file()
    let options = LoadOptions {
        validate: false, // Query doesn't need validation
        ..Default::default()
    };

    let ledger =
        load(file, &options).with_context(|| format!("failed to load {}", file.display()))?;

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

    // Expand pad directives into synthetic transactions
    let directives = expand_pads(&booked_directives);

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
        return run_interactive(file, &directives, &display_context, args);
    };

    // Batch query: no pager (matching Python bean-query behavior).
    // Pager is only used in interactive REPL mode.
    let settings = ShellSettings::from_args(args, display_context);
    execute_query(&query_str, &directives, &settings, &mut io::stdout())
}

/// Shell settings for interactive mode
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

fn execute_query<W: Write>(
    query_str: &str,
    directives: &[Directive],
    settings: &ShellSettings,
    writer: &mut W,
) -> Result<()> {
    // Parse the query
    let query = parse_query(query_str).with_context(|| "failed to parse query")?;

    // Execute
    let mut executor = Executor::new(directives);
    let result = executor
        .execute(&query)
        .with_context(|| "failed to execute query")?;

    // Output results using display context for consistent number formatting
    let ctx = &settings.display_context;
    match settings.format {
        OutputFormat::Text => write_text(&result, writer, settings.numberify, ctx)?,
        OutputFormat::Csv => write_csv(&result, writer, settings.numberify, ctx)?,
        OutputFormat::Json => write_json(&result, writer)?,
        OutputFormat::Beancount => write_beancount(&result, writer, ctx)?,
    }

    Ok(())
}

fn write_text<W: Write>(
    result: &rustledger_query::QueryResult,
    writer: &mut W,
    numberify: bool,
    ctx: &DisplayContext,
) -> Result<()> {
    if result.columns.is_empty() {
        return Ok(());
    }

    // Calculate column widths
    let mut widths: Vec<usize> = result
        .columns
        .iter()
        .map(std::string::String::len)
        .collect();

    for row in &result.rows {
        for (i, value) in row.iter().enumerate() {
            let len = format_value(value, numberify, ctx).len();
            if i < widths.len() && len > widths[i] {
                widths[i] = len;
            }
        }
    }

    // Determine which columns are numeric (for right-alignment)
    let is_numeric_col: Vec<bool> = (0..result.columns.len())
        .map(|i| {
            result.rows.first().is_some_and(|row| {
                row.get(i)
                    .is_some_and(|v| matches!(v, Value::Integer(_) | Value::Number(_)))
            })
        })
        .collect();

    // Print header (right-align numeric column headers to match Python)
    for (i, col) in result.columns.iter().enumerate() {
        if i > 0 {
            write!(writer, "  ")?;
        }
        if i < is_numeric_col.len() && is_numeric_col[i] {
            write!(writer, "{:>width$}", col, width = widths[i])?;
        } else {
            write!(writer, "{:width$}", col, width = widths[i])?;
        }
    }
    writeln!(writer)?;

    // Print separator
    for (i, width) in widths.iter().enumerate() {
        if i > 0 {
            write!(writer, "  ")?;
        }
        write!(writer, "{}", "-".repeat(*width))?;
    }
    writeln!(writer)?;

    // Print rows
    for row in &result.rows {
        for (i, value) in row.iter().enumerate() {
            if i > 0 {
                write!(writer, "  ")?;
            }
            let formatted = format_value(value, numberify, ctx);
            if i < widths.len() {
                // Right-align numeric columns to match Python beancount
                if i < is_numeric_col.len() && is_numeric_col[i] {
                    write!(writer, "{:>width$}", formatted, width = widths[i])?;
                } else {
                    write!(writer, "{:width$}", formatted, width = widths[i])?;
                }
            } else {
                write!(writer, "{formatted}")?;
            }
        }
        writeln!(writer)?;
    }

    // Print row count
    writeln!(writer)?;
    writeln!(writer, "{} row(s)", result.rows.len())?;
    Ok(())
}

fn write_csv<W: Write>(
    result: &rustledger_query::QueryResult,
    writer: &mut W,
    numberify: bool,
    ctx: &DisplayContext,
) -> Result<()> {
    // Print header
    writeln!(writer, "{}", result.columns.join(","))?;

    // Print rows
    for row in &result.rows {
        let values: Vec<String> = row
            .iter()
            .map(|v| escape_csv(&format_value(v, numberify, ctx)))
            .collect();
        writeln!(writer, "{}", values.join(","))?;
    }
    Ok(())
}

fn write_json<W: Write>(result: &rustledger_query::QueryResult, writer: &mut W) -> Result<()> {
    let rows: Vec<serde_json::Value> = result
        .rows
        .iter()
        .map(|row| {
            let obj: serde_json::Map<String, serde_json::Value> = result
                .columns
                .iter()
                .zip(row.iter())
                .map(|(col, val)| (col.clone(), value_to_json(val)))
                .collect();
            serde_json::Value::Object(obj)
        })
        .collect();

    let output = serde_json::json!({
        "columns": result.columns,
        "rows": rows,
        "row_count": result.rows.len(),
    });

    writeln!(writer, "{}", serde_json::to_string_pretty(&output)?)?;
    Ok(())
}

fn write_beancount<W: Write>(
    result: &rustledger_query::QueryResult,
    writer: &mut W,
    ctx: &DisplayContext,
) -> Result<()> {
    // Beancount format outputs entries in beancount syntax
    // This is mainly useful for PRINT queries
    for row in &result.rows {
        for value in row {
            writeln!(writer, "{}", format_value(value, false, ctx))?;
        }
    }
    Ok(())
}

/// Format a value for display using the display context for precision.
fn format_value(value: &Value, numberify: bool, ctx: &DisplayContext) -> String {
    match value {
        Value::String(s) => s.clone(),
        Value::Number(n) => n.normalize().to_string(),
        Value::Integer(i) => i.to_string(),
        Value::Date(d) => d.to_string(),
        Value::Boolean(b) => b.to_string(),
        Value::Amount(a) => {
            if numberify {
                ctx.format(a.number, a.currency.as_str())
            } else {
                ctx.format_amount(a.number, a.currency.as_str())
            }
        }
        Value::Position(p) => {
            if numberify {
                ctx.format(p.units.number, p.units.currency.as_str())
            } else {
                let mut s = ctx.format_amount(p.units.number, p.units.currency.as_str());
                if let Some(ref cost) = p.cost {
                    // Cost uses its own currency's precision
                    s.push_str(&format!(
                        " {{{}}}",
                        ctx.format_amount(cost.number, cost.currency.as_str())
                    ));
                }
                s
            }
        }
        Value::Inventory(inv) => {
            // First, aggregate positions with identical costs (matching Python beancount)
            // This is done at display time to keep core inventory operations O(1)
            use rustledger_core::Position;
            use std::collections::HashMap;

            let mut aggregated: HashMap<(String, Option<String>), Position> = HashMap::new();
            for pos in inv.positions().iter().filter(|p| !p.is_empty()) {
                // Key: (currency, cost_key) where cost_key uniquely identifies the cost
                // Use normalize() on the cost number to ensure consistent key generation
                // (e.g., 50 and 50.00 should produce the same key)
                let cost_key = pos.cost.as_ref().map(|c| {
                    format!(
                        "{}|{}|{:?}|{:?}",
                        c.number.normalize(),
                        c.currency,
                        c.date,
                        c.label
                    )
                });
                let key = (pos.units.currency.to_string(), cost_key);

                aggregated
                    .entry(key)
                    .and_modify(|existing| {
                        existing.units.number += pos.units.number;
                    })
                    .or_insert_with(|| pos.clone());
            }

            // Sort positions matching beanquery's positionsortkey():
            // 1. Currency (alphabetically)
            // 2. Quantity (descending - larger quantities first)
            // 3. Cost currency, cost number, cost date
            let mut sorted_positions: Vec<_> = aggregated.values().collect();
            sorted_positions.sort_by(|a, b| {
                // 1. Currency alphabetically
                if a.units.currency != b.units.currency {
                    return a.units.currency.cmp(&b.units.currency);
                }

                // 2. Quantity descending (larger first)
                let qty_cmp = b.units.number.cmp(&a.units.number); // Note: b before a for descending
                if qty_cmp != std::cmp::Ordering::Equal {
                    return qty_cmp;
                }

                // 3. Cost details
                match (&a.cost, &b.cost) {
                    (Some(ca), Some(cb)) => {
                        // Cost currency
                        if ca.currency != cb.currency {
                            return ca.currency.cmp(&cb.currency);
                        }
                        // Cost number (descending - larger cost first, matching Python)
                        if ca.number != cb.number {
                            return cb.number.cmp(&ca.number);
                        }
                        // Cost date
                        ca.date.cmp(&cb.date)
                    }
                    (Some(_), None) => std::cmp::Ordering::Greater,
                    (None, Some(_)) => std::cmp::Ordering::Less,
                    (None, None) => std::cmp::Ordering::Equal,
                }
            });

            let positions: Vec<String> = sorted_positions
                .iter()
                .filter(|p| !p.is_empty()) // Filter again in case aggregation resulted in zero
                .map(|p| {
                    if numberify {
                        ctx.format(p.units.number, p.units.currency.as_str())
                    } else {
                        let mut s = ctx.format_amount(p.units.number, p.units.currency.as_str());
                        if let Some(ref cost) = p.cost {
                            // Cost uses its own currency's precision
                            // Don't include date in display (matches Python beancount behavior)
                            s.push_str(&format!(
                                " {{{}}}",
                                ctx.format_amount(cost.number, cost.currency.as_str())
                            ));
                        }
                        s
                    }
                })
                .collect();
            positions.join("   ")
        }
        Value::StringSet(set) => set.join(", "),
        Value::Set(values) => {
            let strs: Vec<String> = values
                .iter()
                .map(|v| format_value(v, numberify, ctx))
                .collect();
            format!("({})", strs.join(", "))
        }
        Value::Metadata(meta) => {
            // Format metadata as key=value pairs
            meta.iter()
                .map(|(k, v)| format!("{k}: {v:?}"))
                .collect::<Vec<_>>()
                .join(", ")
        }
        Value::Interval(interval) => {
            let unit_str = match interval.unit {
                rustledger_query::IntervalUnit::Day => "day",
                rustledger_query::IntervalUnit::Week => "week",
                rustledger_query::IntervalUnit::Month => "month",
                rustledger_query::IntervalUnit::Quarter => "quarter",
                rustledger_query::IntervalUnit::Year => "year",
            };
            let plural = if interval.count.abs() == 1 { "" } else { "s" };
            format!("{} {}{}", interval.count, unit_str, plural)
        }
        Value::Object(obj) => {
            // Format object as {key: value, ...}
            let pairs: Vec<String> = obj
                .iter()
                .map(|(k, v)| format!("{k}: {}", format_value(v, numberify, ctx)))
                .collect();
            format!("{{{}}}", pairs.join(", "))
        }
        Value::Null => String::new(),
    }
}

fn value_to_json(value: &Value) -> serde_json::Value {
    match value {
        Value::String(s) => serde_json::Value::String(s.clone()),
        Value::Number(n) => serde_json::json!(n.to_string()),
        Value::Integer(i) => serde_json::json!(i),
        Value::Date(d) => serde_json::Value::String(d.to_string()),
        Value::Boolean(b) => serde_json::Value::Bool(*b),
        Value::Amount(a) => serde_json::json!({
            "number": a.number.to_string(),
            "currency": a.currency,
        }),
        Value::Position(p) => serde_json::json!({
            "units": {
                "number": p.units.number.to_string(),
                "currency": p.units.currency,
            },
            "cost": p.cost.as_ref().map(|c| serde_json::json!({
                "number": c.number.to_string(),
                "currency": c.currency,
            })),
        }),
        Value::Inventory(inv) => serde_json::json!({
            "positions": inv.positions().iter().map(|p| serde_json::json!({
                "number": p.units.number.to_string(),
                "currency": p.units.currency,
            })).collect::<Vec<_>>(),
        }),
        Value::StringSet(set) => serde_json::json!(set),
        Value::Set(values) => {
            let arr: Vec<serde_json::Value> = values.iter().map(value_to_json).collect();
            serde_json::Value::Array(arr)
        }
        Value::Metadata(meta) => {
            let obj: serde_json::Map<String, serde_json::Value> = meta
                .iter()
                .map(|(k, v)| (k.clone(), serde_json::json!(format!("{v:?}"))))
                .collect();
            serde_json::Value::Object(obj)
        }
        Value::Interval(interval) => serde_json::json!({
            "count": interval.count,
            "unit": match interval.unit {
                rustledger_query::IntervalUnit::Day => "day",
                rustledger_query::IntervalUnit::Week => "week",
                rustledger_query::IntervalUnit::Month => "month",
                rustledger_query::IntervalUnit::Quarter => "quarter",
                rustledger_query::IntervalUnit::Year => "year",
            },
        }),
        Value::Object(obj) => {
            let mut map = serde_json::Map::new();
            for (k, v) in obj.as_ref() {
                map.insert(k.clone(), value_to_json(v));
            }
            serde_json::Value::Object(map)
        }
        Value::Null => serde_json::Value::Null,
    }
}

fn escape_csv(s: &str) -> String {
    if s.contains(',') || s.contains('"') || s.contains('\n') {
        format!("\"{}\"", s.replace('"', "\"\""))
    } else {
        s.to_string()
    }
}

/// Get the history file path
fn get_history_path() -> Option<PathBuf> {
    dirs::config_dir().map(|p| p.join("beanquery").join("history"))
}

/// Get the init file path
fn get_init_path() -> Option<PathBuf> {
    dirs::config_dir().map(|p| p.join("beanquery").join("init"))
}

/// Count statistics about directives
fn count_statistics(directives: &[Directive]) -> (usize, usize, usize) {
    let mut num_transactions = 0;
    let mut num_postings = 0;

    for directive in directives {
        if let Directive::Transaction(txn) = directive {
            num_transactions += 1;
            num_postings += txn.postings.len();
        }
    }

    (directives.len(), num_transactions, num_postings)
}

fn run_interactive(
    file: &PathBuf,
    directives: &[Directive],
    display_context: &DisplayContext,
    args: &Args,
) -> Result<()> {
    // Create readline editor
    let mut rl: Editor<(), DefaultHistory> = DefaultEditor::new()?;

    // Load history
    if let Some(history_path) = get_history_path() {
        if let Some(parent) = history_path.parent() {
            let _ = fs::create_dir_all(parent);
        }
        let _ = rl.load_history(&history_path);
    }

    // Run init file if it exists
    if let Some(init_path) = get_init_path()
        && init_path.exists()
        && let Ok(init_contents) = fs::read_to_string(&init_path)
    {
        for line in init_contents.lines() {
            let line = line.trim();
            if !line.is_empty() && !line.starts_with('#') {
                // Process init commands silently
            }
        }
    }

    // Print welcome message
    let (num_directives, num_transactions, num_postings) = count_statistics(directives);
    println!("Input file: \"{}\"", file.display());
    println!(
        "Ready with {num_directives} directives ({num_postings} postings in {num_transactions} transactions)"
    );
    println!();

    // Shell settings
    let mut settings = ShellSettings::from_args(args, display_context.clone());

    loop {
        let readline = rl.readline("beanquery> ");

        match readline {
            Ok(line) => {
                let line = line.trim();
                if line.is_empty() {
                    continue;
                }

                // Add to history
                let _ = rl.add_history_entry(line);

                // Handle dot-commands
                if let Some(cmd) = line.strip_prefix('.') {
                    handle_dot_command(cmd, &mut settings, directives);
                    continue;
                }

                // Handle legacy commands (without dot prefix) with warning
                let lower = line.to_lowercase();
                if matches!(
                    lower.as_str(),
                    "exit" | "quit" | "help" | "set" | "format" | "reload" | "errors" | "tables"
                ) {
                    eprintln!(
                        "warning: commands without \".\" prefix are deprecated. use \".{lower}\" instead"
                    );

                    if lower == "exit" || lower == "quit" {
                        break;
                    }
                    handle_dot_command(&lower, &mut settings, directives);
                    continue;
                }

                // Execute as BQL query
                let result = if let Some(ref output_path) = settings.output_file {
                    // Write to file
                    match fs::File::create(output_path) {
                        Ok(mut file) => execute_query(line, directives, &settings, &mut file),
                        Err(e) => {
                            eprintln!("error: failed to open {}: {}", output_path.display(), e);
                            continue;
                        }
                    }
                } else {
                    // Write to stdout
                    let mut stdout = io::stdout();
                    execute_query(line, directives, &settings, &mut stdout)
                };
                match result {
                    Ok(()) => {}
                    Err(e) => eprintln!("error: {e:#}"),
                }
                println!();
            }
            Err(ReadlineError::Interrupted) => {
                println!("(interrupted)");
            }
            Err(ReadlineError::Eof) => {
                println!("exit");
                break;
            }
            Err(err) => {
                eprintln!("error: {err}");
                break;
            }
        }
    }

    // Save history
    if let Some(history_path) = get_history_path() {
        let _ = rl.save_history(&history_path);
    }

    Ok(())
}

fn handle_dot_command(cmd: &str, settings: &mut ShellSettings, directives: &[Directive]) {
    let parts: Vec<&str> = cmd.split_whitespace().collect();
    let command = parts.first().map(|s| s.to_lowercase()).unwrap_or_default();
    let args: Vec<&str> = parts.into_iter().skip(1).collect();

    match command.as_str() {
        "exit" | "quit" => {
            std::process::exit(0);
        }
        "help" => {
            println!("Shell utility commands (prefix with .):");
            println!("  .exit, .quit     Exit the interpreter");
            println!("  .help            Show this help");
            println!("  .set [VAR [VAL]] Show or set shell variables");
            println!("  .format [FMT]    Show or set output format (text, csv, json, beancount)");
            println!("  .output [FILE]   Set output file (use - for stdout)");
            println!("  .tables          List available tables");
            println!("  .describe TABLE  Describe a table's columns");
            println!("  .run FILE        Execute query from a file");
            println!("  .parse QUERY     Parse and display query AST");
            println!("  .explain QUERY   Explain query execution plan");
            println!("  .reload          Reload the ledger file");
            println!("  .errors          Show ledger validation errors");
            println!("  .stats           Show ledger statistics");
            println!("  .history         Show command history info");
            println!("  .clear           Clear command history");
            println!();
            println!("Beancount query commands:");
            println!("  SELECT ...       Run a BQL SELECT query");
            println!("  BALANCES ...     Show account balances");
            println!("  JOURNAL ...      Show account journal");
            println!("  PRINT ...        Print entries in beancount format");
            println!();
        }
        "set" => {
            if args.is_empty() {
                // Show all settings
                println!("format: {}", settings.format);
                println!("numberify: {}", settings.numberify);
                println!("pager: {}", settings.pager);
                match &settings.output_file {
                    Some(path) => println!("output: {}", path.display()),
                    None => println!("output: (stdout)"),
                }
            } else if args.len() == 1 {
                // Show specific setting
                match args[0] {
                    "format" => println!("format: {}", settings.format),
                    "numberify" => println!("numberify: {}", settings.numberify),
                    "pager" => println!("pager: {}", settings.pager),
                    "output" => match &settings.output_file {
                        Some(path) => println!("output: {}", path.display()),
                        None => println!("output: (stdout)"),
                    },
                    _ => eprintln!("error: unknown variable \"{}\"", args[0]),
                }
            } else if args.len() == 2 {
                // Set a setting
                match args[0] {
                    "format" => match args[1] {
                        "text" => settings.format = OutputFormat::Text,
                        "csv" => settings.format = OutputFormat::Csv,
                        "json" => settings.format = OutputFormat::Json,
                        "beancount" => settings.format = OutputFormat::Beancount,
                        _ => eprintln!("error: \"{}\" is not a valid format", args[1]),
                    },
                    "numberify" => match args[1].to_lowercase().as_str() {
                        "true" | "1" | "on" | "yes" => settings.numberify = true,
                        "false" | "0" | "off" | "no" => settings.numberify = false,
                        _ => eprintln!("error: \"{}\" is not a valid boolean", args[1]),
                    },
                    "pager" => match args[1].to_lowercase().as_str() {
                        "true" | "1" | "on" | "yes" => settings.pager = true,
                        "false" | "0" | "off" | "no" => settings.pager = false,
                        _ => eprintln!("error: \"{}\" is not a valid boolean", args[1]),
                    },
                    "output" => {
                        if args[1] == "-" {
                            settings.output_file = None;
                        } else {
                            settings.output_file = Some(PathBuf::from(args[1]));
                        }
                    }
                    _ => eprintln!("error: unknown variable \"{}\"", args[0]),
                }
            } else {
                eprintln!("error: invalid number of arguments");
            }
        }
        "format" => {
            if args.is_empty() {
                println!("format: {}", settings.format);
            } else if args.len() == 1 {
                match args[0] {
                    "text" => settings.format = OutputFormat::Text,
                    "csv" => settings.format = OutputFormat::Csv,
                    "json" => settings.format = OutputFormat::Json,
                    "beancount" => settings.format = OutputFormat::Beancount,
                    _ => eprintln!("error: \"{}\" is not a valid format", args[0]),
                }
            } else {
                eprintln!("error: invalid number of arguments");
            }
        }
        "tables" => {
            println!("entries");
            println!("postings");
            println!();
            println!("System tables (prefix with #):");
            for table in SYSTEM_TABLES {
                println!("  {table}");
            }
        }
        "describe" => {
            if args.is_empty() {
                eprintln!("error: table name required");
            } else {
                match args[0] {
                    "entries" => {
                        println!("table entries:");
                        println!("  date (date)");
                        println!("  flag (str)");
                        println!("  payee (str)");
                        println!("  narration (str)");
                        println!("  tags (set)");
                        println!("  links (set)");
                        println!("  meta (object)");
                    }
                    "postings" => {
                        println!("table postings:");
                        println!("  date (date)");
                        println!("  flag (str)");
                        println!("  payee (str)");
                        println!("  narration (str)");
                        println!("  account (str)");
                        println!("  units (amount)");
                        println!("  cost (amount)");
                        println!("  price (amount)");
                        println!("  tags (set)");
                        println!("  links (set)");
                    }
                    _ => eprintln!("error: unknown table \"{}\"", args[0]),
                }
            }
        }
        "history" => {
            // History is managed by rustyline, show a message
            println!("History is automatically saved to ~/.config/beanquery/history");
        }
        "clear" => {
            // Clear history
            if let Some(history_path) = get_history_path() {
                let _ = fs::remove_file(&history_path);
                println!("History cleared");
            }
        }
        "errors" => {
            // Show any errors (we don't keep them, so just say none)
            println!("(no errors)");
        }
        "reload" => {
            // We don't support reload in this simple implementation
            println!("Reload not supported in this version. Restart bean-query to reload.");
        }
        "stats" => {
            let (num_directives, num_transactions, num_postings) = count_statistics(directives);
            println!("Directives: {num_directives}");
            println!("Transactions: {num_transactions}");
            println!("Postings: {num_postings}");
        }
        "output" => {
            if args.is_empty() {
                // Show current output
                match &settings.output_file {
                    Some(path) => println!("output: {}", path.display()),
                    None => println!("output: (stdout)"),
                }
            } else if args.len() == 1 {
                if args[0] == "-" {
                    settings.output_file = None;
                    println!("Output set to stdout");
                } else {
                    settings.output_file = Some(PathBuf::from(args[0]));
                    println!("Output set to {}", args[0]);
                }
            } else {
                eprintln!("error: invalid number of arguments");
            }
        }
        "run" => {
            if args.is_empty() {
                eprintln!("error: filename required");
            } else {
                let query_file = args[0];
                match fs::read_to_string(query_file) {
                    Ok(query) => {
                        let query = query.trim();
                        println!("Running: {query}");
                        let result = if let Some(ref output_path) = settings.output_file {
                            match fs::File::create(output_path) {
                                Ok(mut file) => {
                                    execute_query(query, directives, settings, &mut file)
                                }
                                Err(e) => {
                                    eprintln!(
                                        "error: failed to open {}: {}",
                                        output_path.display(),
                                        e
                                    );
                                    return;
                                }
                            }
                        } else {
                            let mut stdout = io::stdout();
                            execute_query(query, directives, settings, &mut stdout)
                        };
                        if let Err(e) = result {
                            eprintln!("error: {e:#}");
                        }
                    }
                    Err(e) => eprintln!("error: failed to read {query_file}: {e}"),
                }
            }
        }
        "parse" => {
            if args.is_empty() {
                eprintln!("error: query required");
            } else {
                let query_str = args.join(" ");
                match parse_query(&query_str) {
                    Ok(query) => {
                        println!("Parsed query:");
                        println!("  {query:?}");
                    }
                    Err(e) => eprintln!("error: {e}"),
                }
            }
        }
        "explain" => {
            if args.is_empty() {
                eprintln!("error: query required");
            } else {
                let query_str = args.join(" ");
                match parse_query(&query_str) {
                    Ok(query) => {
                        println!("Query execution plan:");
                        println!();
                        // Show the query structure
                        println!("  1. Parse query");
                        println!("  2. Create executor with {} directives", directives.len());
                        println!("  3. Execute query: {query:?}");
                        println!("  4. Format results as {}", settings.format);
                        if settings.numberify {
                            println!("  5. Numberify output (remove currencies)");
                        }
                        println!();
                        println!("Tables available:");
                        println!("  entries, postings");
                        print!("  ");
                        println!("{}", SYSTEM_TABLES.join(", "));
                    }
                    Err(e) => eprintln!("error: {e}"),
                }
            }
        }
        "" => {}
        _ => {
            eprintln!("error: unknown command \".{command}\"");
        }
    }
}
