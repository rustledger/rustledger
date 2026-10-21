//! Interactive REPL mode for BQL queries.

use super::output::{execute_query, session_executor};
use super::{OutputFormat, SYSTEM_TABLES, ShellSettings};
use anyhow::Result;
use rustledger_core::{Directive, Spanned};
use rustledger_loader::SourceMap;
use rustledger_query::parse as parse_query;
use rustyline::error::ReadlineError;
use rustyline::history::DefaultHistory;
use rustyline::{DefaultEditor, Editor};
use std::fs;
use std::io;
use std::path::PathBuf;

/// Get the history file path.
///
/// Lives under the shared `…/beanquery/` app directory (NOT rledger's own
/// config dir), matching the Python `beanquery` REPL so the two tools share a
/// history/init. This is deliberately OUTSIDE `RLEDGER_CONFIG_DIR` — do not
/// relocate it into rledger's config dir in a future config-relocation pass.
fn get_history_path() -> Option<PathBuf> {
    dirs::config_dir().map(|p| p.join("beanquery").join("history"))
}

/// Get the init file path.
///
/// See [`get_history_path`]: the `…/beanquery/` location is shared with the
/// Python `beanquery` REPL on purpose and is intentionally not covered by
/// `RLEDGER_CONFIG_DIR`.
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
    // Built by the caller from the loaded ledger: display context, account
    // types, booking method, summary accounts and the balance checker's
    // discrepancies, all fixed for the session.
    mut settings: ShellSettings,
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

    // One executor for the session, so a table a statement creates is there
    // for the next (#2518).
    let mut executor = session_executor(directives, source_map, &settings);

    loop {
        let readline = rl.readline("beanquery> ");

        match readline {
            Ok(line) => {
                let line = line.trim();
                if line.is_empty() {
                    continue;
                }

                let _ = rl.add_history_entry(line);

                // A line holding only a `/* ... */` comment is no query
                // (#2403). An unclosed one is left to the parser to report.
                if rustledger_query::parser::strip_comments(line)
                    .is_ok_and(|stripped| stripped.trim().is_empty())
                {
                    continue;
                }

                // Handle dot-commands
                if let Some(cmd) = line.strip_prefix('.') {
                    if handle_dot_command(cmd, &mut settings, &mut executor, directives) {
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

                    if handle_dot_command(&lower, &mut settings, &mut executor, directives) {
                        break;
                    }
                    continue;
                }

                // Execute as BQL query
                let result = if let Some(ref output_path) = settings.output_file {
                    match fs::File::create(output_path) {
                        Ok(mut file) => execute_query(line, &mut executor, &settings, &mut file),
                        Err(e) => {
                            eprintln!("error: failed to open {}: {}", output_path.display(), e);
                            continue;
                        }
                    }
                } else {
                    let mut stdout = io::stdout();
                    execute_query(line, &mut executor, &settings, &mut stdout)
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

/// What `.tables` prints: the default tables, the system tables, and the
/// tables `CREATE TABLE` made this session (#2579), sorted.
fn tables_listing(executor: &rustledger_query::Executor<'_>) -> String {
    let mut out = String::from("entries\npostings\n\nSystem tables (prefix with #):\n");
    for table in SYSTEM_TABLES {
        out.push_str(&format!("  {table}\n"));
    }
    let created = executor.created_tables().names();
    if !created.is_empty() {
        out.push_str("\nCreated tables:\n");
        for table in created {
            out.push_str(&format!("  {table}\n"));
        }
    }
    out
}

/// What `.describe NAME` prints: `table NAME:` and a `  column (type)` line
/// per column, as bean-query prints it, or why there is nothing to describe.
///
/// A table `CREATE TABLE` made is looked up first, in any case, as a query's
/// `FROM` looks it up, so one named `entries` is the one described (#2579).
fn describe_table(executor: &rustledger_query::Executor<'_>, name: &str) -> Result<String, String> {
    use std::fmt::Write as _;
    let mut out = String::new();
    if let Some(columns) = executor.created_tables().describe(name) {
        let _ = writeln!(out, "table {name}:");
        for (column, type_name) in columns {
            let _ = writeln!(out, "  {column} ({type_name})");
        }
        return Ok(out);
    }
    match name {
        "entries" => {
            out.push_str("table entries:\n");
            for (column, type_name) in [
                ("date", "date"),
                ("flag", "str"),
                ("payee", "str"),
                ("narration", "str"),
                ("tags", "set"),
                ("links", "set"),
                ("meta", "object"),
            ] {
                let _ = writeln!(out, "  {column} ({type_name})");
            }
        }
        "postings" => {
            // The executor's own column list, so this cannot drift from what
            // a query accepts (#2505).
            out.push_str("table postings:\n");
            for column in rustledger_query::executor::POSTING_COLUMNS {
                let _ = writeln!(out, "  {} ({})", column.name, column.type_name);
            }
        }
        _ => return Err(format!("unknown table \"{name}\"")),
    }
    Ok(out)
}

/// Returns `true` if the REPL should exit.
fn handle_dot_command(
    cmd: &str,
    settings: &mut ShellSettings,
    executor: &mut rustledger_query::Executor<'_>,
    directives: &[Spanned<Directive>],
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
        "tables" => print!("{}", tables_listing(executor)),
        "describe" => {
            if args.is_empty() {
                eprintln!("error: table name required");
            } else {
                match describe_table(executor, args[0]) {
                    Ok(description) => print!("{description}"),
                    Err(e) => eprintln!("error: {e}"),
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
                                Ok(mut file) => execute_query(query, executor, settings, &mut file),
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
                            execute_query(query, executor, settings, &mut stdout)
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
                        let created = executor.created_tables().names();
                        if !created.is_empty() {
                            println!("  {}", created.join(", "));
                        }
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

#[cfg(test)]
mod tests {
    use super::{describe_table, tables_listing};
    use rustledger_core::{Amount, Directive, Open, Posting, Transaction, naive_date};
    use rustledger_query::{Executor, parse};

    fn ledger() -> Vec<Directive> {
        let date = naive_date(2024, 1, 1).unwrap();
        vec![
            Directive::Open(Open::new(date, "Assets:Cash")),
            Directive::Open(Open::new(date, "Expenses:Food")),
            Directive::Transaction(
                Transaction::new(date, "lunch")
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(rust_decimal::Decimal::TEN, "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Assets:Cash",
                        Amount::new(-rust_decimal::Decimal::TEN, "USD"),
                    )),
            ),
        ]
    }

    fn run(executor: &mut Executor<'_>, query: &str) {
        executor
            .execute(&parse(query).expect("parses"))
            .unwrap_or_else(|e| panic!("{query}: {e}"));
    }

    /// `.tables` and `.describe` list the tables `CREATE TABLE` made in the
    /// session, as bean-query's do (#2579). They listed only the built-in
    /// ones, so a table the session had just made was invisible to both.
    #[test]
    fn created_tables_are_listed_and_described() {
        let directives = ledger();
        let mut executor = Executor::new(&directives);
        assert!(!tables_listing(&executor).contains("Created tables"));
        assert_eq!(
            describe_table(&executor, "foo"),
            Err("unknown table \"foo\"".to_string())
        );

        run(
            &mut executor,
            "CREATE TABLE Foo AS SELECT account, number, position, date",
        );
        run(&mut executor, "CREATE TABLE bar (x int, y)");

        let listing = tables_listing(&executor);
        assert!(
            listing.ends_with("\nCreated tables:\n  bar\n  foo\n"),
            "{listing}"
        );

        // Types from the values, in bean-query's names.
        assert_eq!(
            describe_table(&executor, "foo").as_deref(),
            Ok(
                "table foo:\n  account (str)\n  number (decimal)\n  position (position)\n  date (date)\n"
            )
        );
        // Declared types, and `object` for an undeclared column with no value.
        assert_eq!(
            describe_table(&executor, "BAR").as_deref(),
            Ok("table BAR:\n  x (int)\n  y (object)\n")
        );
        run(&mut executor, "INSERT INTO bar VALUES (1, 'a')");
        assert_eq!(
            describe_table(&executor, "bar").as_deref(),
            Ok("table bar:\n  x (int)\n  y (str)\n")
        );

        // A created table shadows a built-in one, as in a query's FROM.
        run(&mut executor, "CREATE TABLE entries (z)");
        assert_eq!(
            describe_table(&executor, "entries").as_deref(),
            Ok("table entries:\n  z (object)\n")
        );
        // The built-in descriptions are unchanged.
        assert!(
            describe_table(&executor, "postings")
                .is_ok_and(|d| d.starts_with("table postings:\n  type (str)\n"))
        );
    }
}
