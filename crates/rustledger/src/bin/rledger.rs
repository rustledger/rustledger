//! rledger - Unified CLI for rustledger.
//!
//! A pure Rust implementation of Beancount with 10-30x faster performance.
//!
//! # Usage
//!
//! ```bash
//! rledger check ledger.beancount
//! rledger query ledger.beancount "SELECT account, sum(position)"
//! rledger format ledger.beancount
//! rledger report ledger.beancount balances
//! rledger doctor lex ledger.beancount
//! rledger config show  # Show configuration
//! rledger completions bash  # Generate shell completions
//! ```
//!
//! # Configuration
//!
//! If no file is specified, rledger will use the default file from config:
//! ```bash
//! rledger check  # Uses file from ~/.config/rledger/config.toml
//! ```
//!
//! # Aliases
//!
//! Define aliases in your config file:
//! ```toml
//! [aliases]
//! bal = "report balances"
//! expenses = "query 'SELECT account, sum(position) WHERE account ~ \"Expenses\"'"
//! ```
//!
//! Then use them:
//! ```bash
//! rledger bal  # Expands to: rledger report balances
//! ```

use clap::{CommandFactory, Parser, Subcommand};
use clap_complete::Shell;
use rustledger::config::Config;
use std::io;
use std::path::PathBuf;
use std::process::ExitCode;

/// rledger - A pure Rust implementation of Beancount
#[derive(Parser)]
#[command(name = "rledger")]
#[command(
    author,
    version,
    about = "Pure Rust implementation of Beancount, 10-30x faster"
)]
#[command(propagate_version = true)]
struct Cli {
    /// Use a specific profile from config
    #[arg(long, short = 'P', global = true)]
    profile: Option<String>,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Validate beancount files
    #[command(alias = "c")]
    Check {
        #[command(flatten)]
        args: rustledger::cmd::check::Args,
    },

    /// Query beancount files with BQL
    #[command(alias = "q")]
    Query {
        #[command(flatten)]
        args: rustledger::cmd::query::Args,
    },

    /// Format beancount files
    #[command(alias = "fmt")]
    Format {
        #[command(flatten)]
        args: rustledger::cmd::format::Args,
    },

    /// Generate financial reports
    #[command(alias = "r")]
    Report {
        #[command(flatten)]
        args: rustledger::cmd::report_cmd::Args,
    },

    /// Debugging and diagnostic tools
    #[command(alias = "d")]
    Doctor {
        #[command(flatten)]
        args: rustledger::cmd::doctor::Args,
    },

    /// Extract transactions from bank files
    #[command(alias = "x")]
    Extract {
        #[command(flatten)]
        args: Box<rustledger::cmd::extract_cmd::Args>,
    },

    /// Fetch commodity prices
    #[command(alias = "p")]
    Price {
        #[command(flatten)]
        args: rustledger::cmd::price_cmd::Args,
    },

    /// Manage configuration
    #[command(alias = "cfg")]
    Config {
        #[command(flatten)]
        args: rustledger::cmd::config_cmd::Args,
    },

    /// Add transactions to beancount files
    #[command(alias = "a")]
    Add {
        #[command(flatten)]
        args: rustledger::cmd::add_cmd::Args,
    },

    /// Generate shell completions
    Completions {
        /// Shell to generate completions for
        #[arg(value_enum)]
        shell: Shell,
    },
}

/// Get the effective file path from CLI arg or config.
fn get_file(file: Option<&PathBuf>, config: &Config, profile: Option<&str>) -> Option<PathBuf> {
    file.cloned()
        .or_else(|| config.effective_file_path(profile))
}

/// Helper to resolve file and return error if not found.
fn require_file(
    file: Option<&PathBuf>,
    config: &Config,
    profile: Option<&str>,
) -> Result<PathBuf, ExitCode> {
    get_file(file, config, profile).ok_or_else(|| {
        eprintln!("error: FILE is required (or set default.file in config)");
        eprintln!("  hint: run 'rledger config init' to create a config file");
        ExitCode::from(2)
    })
}

/// Expand aliases in command line arguments.
///
/// If the first non-flag argument matches an alias, expand it.
/// Returns the expanded arguments.
fn expand_aliases(args: Vec<String>, config: &Config) -> Vec<String> {
    // Find the first non-flag argument (the potential command/alias)
    let mut cmd_index = None;
    for (i, arg) in args.iter().enumerate().skip(1) {
        // Skip global flags
        if arg == "-P" || arg == "--profile" {
            continue;
        }
        // Skip the value after -P/--profile
        if i > 1
            && (args.get(i - 1) == Some(&"-P".to_string())
                || args.get(i - 1) == Some(&"--profile".to_string()))
        {
            continue;
        }
        // Skip flags
        if arg.starts_with('-') {
            continue;
        }
        cmd_index = Some(i);
        break;
    }

    let Some(idx) = cmd_index else {
        return args;
    };

    let potential_alias = &args[idx];

    // Check if it's an alias
    if let Some(expansion) = config.resolve_alias(potential_alias) {
        // Parse the expansion (handling quoted strings)
        let expanded_parts = parse_alias_expansion(expansion);

        // Build new args: program name + flags before alias + expanded + rest
        let mut new_args = Vec::with_capacity(args.len() + expanded_parts.len());
        new_args.extend(args[..idx].iter().cloned());
        new_args.extend(expanded_parts);
        new_args.extend(args[idx + 1..].iter().cloned());

        new_args
    } else {
        args
    }
}

/// Parse an alias expansion string, respecting quotes.
fn parse_alias_expansion(expansion: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut in_single_quote = false;
    let mut in_double_quote = false;

    for c in expansion.chars() {
        match c {
            '\'' if !in_double_quote => {
                in_single_quote = !in_single_quote;
            }
            '"' if !in_single_quote => {
                in_double_quote = !in_double_quote;
            }
            ' ' | '\t' if !in_single_quote && !in_double_quote => {
                if !current.is_empty() {
                    parts.push(std::mem::take(&mut current));
                }
            }
            _ => {
                current.push(c);
            }
        }
    }

    if !current.is_empty() {
        parts.push(current);
    }

    parts
}

fn main() -> ExitCode {
    // Load config early (before parsing) for alias expansion
    let config = Config::load().map(|l| l.config).unwrap_or_default();

    // Expand aliases in command line arguments
    let args: Vec<String> = std::env::args().collect();
    let expanded_args = expand_aliases(args, &config);

    // Parse the (possibly expanded) arguments
    let cli = match Cli::try_parse_from(&expanded_args) {
        Ok(cli) => cli,
        Err(e) => {
            e.exit();
        }
    };

    // Get effective profile: CLI flag takes precedence, then env var
    let profile = cli
        .profile
        .or_else(|| std::env::var("RLEDGER_PROFILE").ok());
    let profile_ref = profile.as_deref();

    match cli.command {
        Commands::Check { mut args } => {
            // If no file specified, try to get from config
            if args.file.is_none() && args.generate_completions.is_none() {
                args.file = config.effective_file_path(profile_ref);
            }
            match rustledger::cmd::check::run(&args) {
                Ok(code) => code,
                Err(e) => {
                    eprintln!("error: {e:#}");
                    ExitCode::from(2)
                }
            }
        }
        Commands::Query { mut args } => {
            // If no file specified, try to get from config
            if args.file.is_none() && args.generate_completions.is_none() {
                args.file = config.effective_file_path(profile_ref);
            }
            // Apply command-specific format default from config
            if args.format.is_none()
                && let Some(fmt) = config.commands.query.output.format.as_ref()
            {
                args.format = rustledger::cmd::query::OutputFormat::from_str_config(fmt);
            }
            match rustledger::cmd::query::run(&args) {
                Ok(()) => ExitCode::SUCCESS,
                Err(e) => {
                    eprintln!("error: {e:#}");
                    ExitCode::from(1)
                }
            }
        }
        Commands::Format { mut args } => {
            // If no files specified, try to get from config
            if args.files.is_empty()
                && args.generate_completions.is_none()
                && let Some(file) = config.effective_file_path(profile_ref)
            {
                args.files.push(file);
            }
            // Apply command-specific indent default from config
            if args.indent.is_none()
                && let Some(indent) = config.commands.format.indent
            {
                args.indent = Some(indent as usize);
            }
            match rustledger::cmd::format::run(&args) {
                Ok(code) => code,
                Err(e) => {
                    eprintln!("error: {e:#}");
                    ExitCode::from(2)
                }
            }
        }
        Commands::Report { mut args } => {
            // Report requires file and report subcommand
            let file = match require_file(args.file.as_ref(), &config, profile_ref) {
                Ok(f) => f,
                Err(code) => return code,
            };
            let Some(ref report) = args.report else {
                eprintln!("error: a report subcommand is required");
                return ExitCode::from(2);
            };
            // Apply command-specific format default from config
            if args.format.is_none()
                && let Some(fmt) = config.commands.report.output.format.as_ref()
            {
                args.format = rustledger::cmd::report_cmd::OutputFormat::from_str_config(fmt);
            }
            let format = args.format.unwrap_or_default();
            match rustledger::cmd::report_cmd::run(
                &file,
                report,
                args.verbose,
                &format,
                args.no_pager,
            ) {
                Ok(()) => ExitCode::SUCCESS,
                Err(e) if rustledger::pager::is_broken_pipe(&e) => ExitCode::SUCCESS,
                Err(e) => {
                    eprintln!("error: {e:#}");
                    ExitCode::from(1)
                }
            }
        }
        Commands::Doctor { args } => {
            let Some(command) = args.command else {
                eprintln!("error: a doctor subcommand is required");
                return ExitCode::from(2);
            };
            match rustledger::cmd::doctor::run(command) {
                Ok(()) => ExitCode::SUCCESS,
                Err(e) => {
                    eprintln!("error: {e:#}");
                    ExitCode::from(1)
                }
            }
        }
        Commands::Extract { args } => {
            let file = match require_file(args.file.as_ref(), &config, profile_ref) {
                Ok(f) => f,
                Err(code) => return code,
            };
            match rustledger::cmd::extract_cmd::run(&args, &file) {
                Ok(()) => ExitCode::SUCCESS,
                Err(e) => {
                    eprintln!("error: {e:#}");
                    ExitCode::from(1)
                }
            }
        }
        Commands::Price { args } => {
            match rustledger::cmd::price_cmd::run(&args.price_args, &config.price) {
                Ok(()) => ExitCode::SUCCESS,
                Err(e) => {
                    eprintln!("error: {e:#}");
                    ExitCode::from(1)
                }
            }
        }
        Commands::Config { args } => match rustledger::cmd::config_cmd::run(&args) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("error: {e:#}");
                ExitCode::from(1)
            }
        },
        Commands::Add { args } => {
            let file = match require_file(args.file.as_ref(), &config, profile_ref) {
                Ok(f) => f,
                Err(code) => return code,
            };
            match rustledger::cmd::add_cmd::run(&args, &file) {
                Ok(()) => ExitCode::SUCCESS,
                Err(e) => {
                    eprintln!("error: {e:#}");
                    ExitCode::from(1)
                }
            }
        }
        Commands::Completions { shell } => {
            clap_complete::generate(shell, &mut Cli::command(), "rledger", &mut io::stdout());
            ExitCode::SUCCESS
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_alias_expansion_simple() {
        let parts = parse_alias_expansion("report balances");
        assert_eq!(parts, vec!["report", "balances"]);
    }

    #[test]
    fn test_parse_alias_expansion_single_quotes() {
        let parts = parse_alias_expansion("query 'SELECT account'");
        assert_eq!(parts, vec!["query", "SELECT account"]);
    }

    #[test]
    fn test_parse_alias_expansion_double_quotes() {
        let parts = parse_alias_expansion("query \"SELECT account, sum(position)\"");
        assert_eq!(parts, vec!["query", "SELECT account, sum(position)"]);
    }

    #[test]
    fn test_parse_alias_expansion_nested_quotes() {
        let parts = parse_alias_expansion("query 'SELECT \"account\"'");
        assert_eq!(parts, vec!["query", "SELECT \"account\""]);
    }

    #[test]
    fn test_parse_alias_expansion_multiple_args() {
        let parts = parse_alias_expansion("report balances -f csv");
        assert_eq!(parts, vec!["report", "balances", "-f", "csv"]);
    }

    #[test]
    fn test_expand_aliases_with_alias() {
        let config = Config {
            aliases: {
                let mut aliases = std::collections::HashMap::new();
                aliases.insert("bal".to_string(), "report balances".to_string());
                aliases
            },
            ..Default::default()
        };

        let args = vec![
            "rledger".to_string(),
            "bal".to_string(),
            "main.beancount".to_string(),
        ];

        let expanded = expand_aliases(args, &config);
        assert_eq!(
            expanded,
            vec!["rledger", "report", "balances", "main.beancount"]
        );
    }

    #[test]
    fn test_expand_aliases_no_alias() {
        let config = Config::default();

        let args = vec![
            "rledger".to_string(),
            "check".to_string(),
            "main.beancount".to_string(),
        ];

        let expanded = expand_aliases(args.clone(), &config);
        assert_eq!(expanded, args);
    }

    #[test]
    fn test_expand_aliases_with_profile() {
        let config = Config {
            aliases: {
                let mut aliases = std::collections::HashMap::new();
                aliases.insert("bal".to_string(), "report balances".to_string());
                aliases
            },
            ..Default::default()
        };

        let args = vec![
            "rledger".to_string(),
            "-P".to_string(),
            "business".to_string(),
            "bal".to_string(),
        ];

        let expanded = expand_aliases(args, &config);
        assert_eq!(
            expanded,
            vec!["rledger", "-P", "business", "report", "balances"]
        );
    }

    #[test]
    fn test_parse_alias_expansion_empty() {
        let parts = parse_alias_expansion("");
        assert!(parts.is_empty());
    }

    #[test]
    fn test_parse_alias_expansion_whitespace_only() {
        let parts = parse_alias_expansion("   \t   ");
        assert!(parts.is_empty());
    }

    #[test]
    fn test_parse_alias_expansion_tabs() {
        let parts = parse_alias_expansion("report\tbalances\t-f\tcsv");
        assert_eq!(parts, vec!["report", "balances", "-f", "csv"]);
    }

    #[test]
    fn test_parse_alias_expansion_mixed_quotes() {
        let parts = parse_alias_expansion("query 'single' \"double\"");
        assert_eq!(parts, vec!["query", "single", "double"]);
    }

    #[test]
    fn test_parse_alias_expansion_complex_query() {
        let parts = parse_alias_expansion(
            "query 'SELECT account, sum(position) WHERE account ~ \"Expenses:Food\"'",
        );
        assert_eq!(parts.len(), 2);
        assert_eq!(parts[0], "query");
        assert!(parts[1].contains("Expenses:Food"));
    }

    #[test]
    fn test_expand_aliases_empty_args() {
        let config = Config::default();
        let args: Vec<String> = vec![];
        let expanded = expand_aliases(args.clone(), &config);
        assert_eq!(expanded, args);
    }

    #[test]
    fn test_expand_aliases_only_program_name() {
        let config = Config::default();
        let args = vec!["rledger".to_string()];
        let expanded = expand_aliases(args.clone(), &config);
        assert_eq!(expanded, args);
    }

    #[test]
    fn test_expand_aliases_flag_only() {
        let config = Config::default();
        let args = vec!["rledger".to_string(), "--help".to_string()];
        let expanded = expand_aliases(args.clone(), &config);
        assert_eq!(expanded, args);
    }

    #[test]
    fn test_expand_aliases_with_long_profile() {
        let config = Config {
            aliases: {
                let mut aliases = std::collections::HashMap::new();
                aliases.insert("bal".to_string(), "report balances".to_string());
                aliases
            },
            ..Default::default()
        };

        let args = vec![
            "rledger".to_string(),
            "--profile".to_string(),
            "work".to_string(),
            "bal".to_string(),
        ];

        let expanded = expand_aliases(args, &config);
        assert_eq!(
            expanded,
            vec!["rledger", "--profile", "work", "report", "balances"]
        );
    }

    #[test]
    fn test_expand_aliases_preserves_trailing_args() {
        let config = Config {
            aliases: {
                let mut aliases = std::collections::HashMap::new();
                aliases.insert("is".to_string(), "report income".to_string());
                aliases
            },
            ..Default::default()
        };

        let args = vec![
            "rledger".to_string(),
            "is".to_string(),
            "-f".to_string(),
            "csv".to_string(),
            "--verbose".to_string(),
        ];

        let expanded = expand_aliases(args, &config);
        assert_eq!(
            expanded,
            vec!["rledger", "report", "income", "-f", "csv", "--verbose"]
        );
    }

    #[test]
    fn test_expand_aliases_with_quoted_alias() {
        let config = Config {
            aliases: {
                let mut aliases = std::collections::HashMap::new();
                aliases.insert(
                    "expenses".to_string(),
                    "query 'SELECT account, sum(position)'".to_string(),
                );
                aliases
            },
            ..Default::default()
        };

        let args = vec!["rledger".to_string(), "expenses".to_string()];

        let expanded = expand_aliases(args, &config);
        assert_eq!(expanded.len(), 3);
        assert_eq!(expanded[0], "rledger");
        assert_eq!(expanded[1], "query");
        assert_eq!(expanded[2], "SELECT account, sum(position)");
    }

    #[test]
    fn test_expand_aliases_builtin_not_overridden() {
        // Even if user defines an alias named "check", it shouldn't conflict
        // since the actual command "check" isn't an alias
        let config = Config::default();

        let args = vec![
            "rledger".to_string(),
            "check".to_string(),
            "file.beancount".to_string(),
        ];

        let expanded = expand_aliases(args.clone(), &config);
        assert_eq!(expanded, args);
    }

    #[test]
    fn test_cli_parsing_profile_flag() {
        use clap::Parser;

        let cli =
            Cli::try_parse_from(["rledger", "-P", "work", "check", "file.beancount"]).unwrap();
        assert_eq!(cli.profile, Some("work".to_string()));

        let cli = Cli::try_parse_from([
            "rledger",
            "--profile",
            "business",
            "check",
            "file.beancount",
        ])
        .unwrap();
        assert_eq!(cli.profile, Some("business".to_string()));
    }

    #[test]
    fn test_cli_parsing_no_profile() {
        use clap::Parser;

        let cli = Cli::try_parse_from(["rledger", "check", "file.beancount"]).unwrap();
        assert_eq!(cli.profile, None);
    }

    #[test]
    fn test_require_file_with_config() {
        let config = Config {
            default: rustledger::config::DefaultConfig {
                file: Some("/test/file.beancount".to_string()),
                ..Default::default()
            },
            ..Default::default()
        };

        // When file is None, should get from config
        let result = require_file(None, &config, None);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), PathBuf::from("/test/file.beancount"));
    }

    #[test]
    fn test_require_file_with_profile() {
        let config = Config {
            default: rustledger::config::DefaultConfig {
                file: Some("/default.beancount".to_string()),
                ..Default::default()
            },
            profiles: {
                let mut m = std::collections::HashMap::new();
                m.insert(
                    "work".to_string(),
                    rustledger::config::ProfileConfig {
                        file: Some("/work.beancount".to_string()),
                        ..Default::default()
                    },
                );
                m
            },
            ..Default::default()
        };

        // With profile, should get profile's file
        let result = require_file(None, &config, Some("work"));
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), PathBuf::from("/work.beancount"));
    }

    #[test]
    fn test_require_file_cli_overrides_config() {
        let config = Config {
            default: rustledger::config::DefaultConfig {
                file: Some("/config.beancount".to_string()),
                ..Default::default()
            },
            ..Default::default()
        };

        let cli_file = PathBuf::from("/cli.beancount");
        let result = require_file(Some(&cli_file), &config, None);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), PathBuf::from("/cli.beancount"));
    }

    #[test]
    fn test_require_file_no_file_no_config() {
        let config = Config::default();
        let result = require_file(None, &config, None);
        assert!(result.is_err());
    }

    #[test]
    fn test_get_file_with_tilde_expansion() {
        let config = Config {
            default: rustledger::config::DefaultConfig {
                file: Some("~/ledger.beancount".to_string()),
                ..Default::default()
            },
            ..Default::default()
        };

        let result = get_file(None, &config, None);
        assert!(result.is_some());

        // Should be expanded (if home dir is available)
        let path = result.unwrap();
        if let Some(home) = dirs::home_dir() {
            assert_eq!(path, home.join("ledger.beancount"));
        }
    }
}
