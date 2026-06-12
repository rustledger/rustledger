//! bean-doctor - Debugging tool for beancount files.
//!
//! This is the Rust equivalent of Python beancount's `bean-doctor` command.
//!
//! # Usage
//!
//! ```bash
//! bean-doctor lex ledger.beancount         # Dump lexer tokens
//! bean-doctor context ledger.beancount 42  # Show context at line 42
//! bean-doctor linked ledger.beancount ^trip-2024  # Find linked transactions
//! bean-doctor missing-open ledger.beancount  # Generate missing Open directives
//! bean-doctor list-options                 # List available options
//! ```

use crate::cmd::completions::ShellType;
use anyhow::Result;
use clap::{Parser, Subcommand};
use std::io;
use std::path::PathBuf;

mod context;
mod directories;
mod display_context;
mod generate_synthetic;
mod lex;
mod linked;
mod missing_open;
mod options;
mod parse;
mod region;
mod roundtrip;
mod stats;

/// Debugging tool for beancount files.
#[derive(Parser, Debug)]
#[command(name = "bean-doctor")]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Generate shell completions and exit
    #[arg(long, value_name = "SHELL", hide = true)]
    generate_completions: Option<ShellType>,

    /// The doctor subcommand to run.
    #[command(subcommand)]
    pub command: Option<Command>,
}

/// Doctor subcommands for debugging and diagnostics.
#[derive(Subcommand, Debug)]
pub enum Command {
    /// Dump the lexer output for a beancount file
    #[command(alias = "dump-lexer")]
    Lex {
        /// The beancount file to lex
        file: PathBuf,
    },

    /// Parse a ledger and show parsed directives
    Parse {
        /// The beancount file to parse
        file: PathBuf,
        /// Show detailed output
        #[arg(short, long)]
        verbose: bool,
    },

    /// Show transaction context at a location
    Context {
        /// The beancount file
        file: PathBuf,
        /// Line number to show context for
        line: usize,
    },

    /// Find transactions linked by a link or at a location
    Linked {
        /// The beancount file
        file: PathBuf,
        /// Link name (^link), tag name (#tag), or line number
        location: String,
    },

    /// Print Open directives missing in a file
    MissingOpen {
        /// The beancount file
        file: PathBuf,
    },

    /// List available beancount options
    ListOptions,

    /// Print options parsed from a ledger
    PrintOptions {
        /// The beancount file
        file: PathBuf,
    },

    /// Display statistics about a ledger
    Stats {
        /// The beancount file
        file: PathBuf,
    },

    /// Display the decimal precision context inferred from the file
    DisplayContext {
        /// The beancount file
        file: PathBuf,
    },

    /// Round-trip test on arbitrary ledger
    Roundtrip {
        /// The beancount file
        file: PathBuf,
    },

    /// Validate a directory hierarchy against the ledger's account names
    Directories {
        /// The beancount file
        file: PathBuf,
        /// Directory roots to validate
        #[arg(value_name = "DIR")]
        dirs: Vec<PathBuf>,
    },

    /// Print transactions in a line range with balances
    Region {
        /// The beancount file
        file: PathBuf,
        /// Start line number
        start_line: usize,
        /// End line number
        end_line: usize,
        /// Convert balances to market value or cost
        #[arg(long, value_enum)]
        conversion: Option<Conversion>,
    },

    /// Generate synthetic beancount files for testing
    GenerateSynthetic {
        /// Output directory for generated files
        #[arg(short, long, default_value = "tests/compatibility/synthetic")]
        output: PathBuf,

        /// Number of files to generate (for proptest-style generation)
        #[arg(short, long, default_value = "50")]
        count: usize,

        /// Random seed for reproducibility
        #[arg(short, long)]
        seed: Option<u64>,

        /// Skip bean-check validation (faster but may produce invalid files)
        #[arg(long)]
        skip_validation: bool,

        /// Write manifest file tracking generated files
        #[arg(long)]
        manifest: bool,

        /// Generate edge case files only
        #[arg(long)]
        edge_cases_only: bool,
    },
}

/// Conversion type for region balances.
#[derive(Debug, Clone, Copy, clap::ValueEnum)]
pub enum Conversion {
    /// Convert to market value using price database
    Value,
    /// Convert to cost basis
    Cost,
}

/// Run the doctor command with the given subcommand, writing to stdout.
///
/// Thin wrapper over [`run_with_writer`] for the synchronous `rledger`
/// binary; `ag-rledger` calls `run_with_writer` with a buffer instead.
pub fn run(command: Command) -> Result<()> {
    let mut stdout = io::stdout().lock();
    run_with_writer(command, &mut stdout)
}

/// Run the doctor command, writing all output to the injected `stdout`
/// writer.
///
/// Each subcommand already renders into a `&mut impl Write`; this entry
/// point just lets the caller choose the sink (a locked stdout for
/// `rledger`, a capture buffer for `ag-rledger`). Behavior is otherwise
/// identical to the original `run()`.
pub fn run_with_writer<W: io::Write>(command: Command, stdout: &mut W) -> Result<()> {
    match command {
        Command::Lex { file } => lex::cmd_lex(&file, stdout),
        Command::Parse { file, verbose } => parse::cmd_parse(&file, verbose, stdout),
        Command::Context { file, line } => context::cmd_context(&file, line, stdout),
        Command::Linked { file, location } => linked::cmd_linked(&file, &location, stdout),
        Command::MissingOpen { file } => missing_open::cmd_missing_open(&file, stdout),
        Command::ListOptions => options::cmd_list_options(stdout),
        Command::PrintOptions { file } => options::cmd_print_options(&file, stdout),
        Command::Stats { file } => stats::cmd_stats(&file, stdout),
        Command::DisplayContext { file } => display_context::cmd_display_context(&file, stdout),
        Command::Roundtrip { file } => roundtrip::cmd_roundtrip(&file, stdout),
        Command::Directories { file, dirs } => directories::cmd_directories(&file, &dirs, stdout),
        Command::Region {
            file,
            start_line,
            end_line,
            conversion,
        } => region::cmd_region(&file, start_line, end_line, conversion, stdout),
        Command::GenerateSynthetic {
            output,
            count,
            seed,
            skip_validation,
            manifest,
            edge_cases_only,
        } => generate_synthetic::cmd_generate_synthetic(
            &output,
            count,
            seed,
            skip_validation,
            manifest,
            edge_cases_only,
            stdout,
        ),
    }
}
