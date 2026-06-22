//! Interactive REPL mode for BQL queries.

use super::output::execute_query;
use super::{Args, OutputFormat, SYSTEM_TABLES, ShellSettings};
use anyhow::Result;
use rustledger_core::{Directive, DisplayContext, Spanned};
use rustledger_loader::SourceMap;
use rustledger_query::parse as parse_query;
use rustyline::error::ReadlineError;
use rustyline::history::DefaultHistory;
use rustyline::{DefaultEditor, Editor};
use std::fs;
use std::io;
use std::path::PathBuf;

/// Get the history file path.
fn get_history_path() -> Option<PathBuf> {
    dirs::config_dir().map(|p| p.join("beanquery").join("history"))
}

/// Get the init file path.
fn get_init_path() -> Option<PathBuf> {
    dirs::config_dir().map(|p| p.join("beanquery").join("init"))
}

/// Count statistics about directives.
fn count_statistics(directives: &[Spanned<Directive>]) -> (usize, usize, usize) {
    let mut num_transactions = 0;
    let mut num_postings = 0;

    for directive in directives {
        if let Directive::Transaction(txn) = &directive.value {
            num_transactions += 1;
            num_postings += txn.postings.len();
        }
    }

    (directives.len(), num_transactions, num_postings)
}

pub(super) fn run_interactive(
    file: &PathBuf,
    directives: &[Spanned<Directive>],
    source_map: &SourceMap,
    display_context: &DisplayContext,
    args: &Args,
) -> Result<()> {
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

    let mut settings = ShellSettings::from_args(args, display_context.clone());

    loop {
        let readline = rl.readline("beanquery> ");

        match readline {
            Ok(line) => {
                let line = line.trim();
                if line.is_empty() {
                    continue;
                }

                let _ = rl.add_history_entry(line);

                // Handle dot-commands
                if let Some(cmd) = line.strip_prefix('.') {
                    if handle_dot_command(cmd, &mut settings, directives, source_map) {
                        break;
                    }
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

                    if handle_dot_command(&lower, &mut settings, directives, source_map) {
                        break;
                    }
                    continue;
                }

                // Execute as BQL query
                let result = if let Some(ref output_path) = settings.output_file {
                    match fs::File::create(output_path) {
                        Ok(mut file) => {
                            execute_query(line, directives, source_map, &settings, &mut file)
                        }
                        Err(e) => {
                            eprintln!("error: failed to open {}: {}", output_path.display(), e);
                            continue;
                        }
                    }
                } else {
                    let mut stdout = io::stdout();
                    execute_query(line, directives, source_map, &settings, &mut stdout)
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

/// Returns `true` if the REPL should exit.
fn handle_dot_command(
    cmd: &str,
    settings: &mut ShellSettings,
    directives: &[Spanned<Directive>],
    source_map: &SourceMap,
) -> bool {
    let parts: Vec<&str> = cmd.split_whitespace().collect();
    let command = parts.first().map(|s| s.to_lowercase()).unwrap_or_default();
    let args: Vec<&str> = parts.into_iter().skip(1).collect();

    match command.as_str() {
        "exit" | "quit" => {
            return true;
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
                println!("format: {}", settings.format);
                println!("numberify: {}", settings.numberify);
                println!("pager: {}", settings.pager);
                match &settings.output_file {
                    Some(path) => println!("output: {}", path.display()),
                    None => println!("output: (stdout)"),
                }
            } else if args.len() == 1 {
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
                        println!("  type (str)");
                        println!("  id (int)");
                        println!("  date (date)");
                        println!("  year (int)");
                        println!("  month (int)");
                        println!("  day (int)");
                        println!("  filename (str)");
                        println!("  lineno (int)");
                        println!("  location (str)");
                        println!("  flag (str)");
                        println!("  payee (str)");
                        println!("  narration (str)");
                        println!("  description (str)");
                        println!("  tags (set)");
                        println!("  links (set)");
                        println!("  posting_flag (str)");
                        println!("  account (str)");
                        println!("  other_accounts (set)");
                        println!("  number (decimal)");
                        println!("  currency (str)");
                        println!("  cost_number (decimal)");
                        println!("  cost_currency (str)");
                        println!("  cost_date (date)");
                        println!("  cost_label (str)");
                        println!("  position (position)");
                        println!("  price (amount)");
                        println!("  weight (amount)");
                        println!("  balance (inventory)");
                        println!("  meta (dict)");
                        println!("  accounts (set[str])");
                    }
                    _ => eprintln!("error: unknown table \"{}\"", args[0]),
                }
            }
        }
        "history" => {
            println!("History is automatically saved to ~/.config/beanquery/history");
        }
        "clear" => {
            if let Some(history_path) = get_history_path() {
                let _ = fs::remove_file(&history_path);
                println!("History cleared");
            }
        }
        "errors" => {
            println!("(no errors)");
        }
        "reload" => {
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
                                Ok(mut file) => execute_query(
                                    query, directives, source_map, settings, &mut file,
                                ),
                                Err(e) => {
                                    eprintln!(
                                        "error: failed to open {}: {}",
                                        output_path.display(),
                                        e
                                    );
                                    return false;
                                }
                            }
                        } else {
                            let mut stdout = io::stdout();
                            execute_query(query, directives, source_map, settings, &mut stdout)
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
    false
}
