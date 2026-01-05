//! Shared implementation for bean-format and rledger-format commands.

use crate::cmd::completions::ShellType;
use crate::format::{FormatConfig, format_directive};
use anyhow::{Context, Result};
use clap::Parser;
use rustledger_loader::Loader;
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

/// Format beancount files.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// The beancount file(s) to format
    #[arg(value_name = "FILE", required_unless_present = "generate_completions")]
    pub files: Vec<PathBuf>,

    /// Generate shell completions and exit
    #[arg(long, value_name = "SHELL", hide = true)]
    pub generate_completions: Option<ShellType>,

    /// Output file (only valid with single input file, default: stdout)
    #[arg(short = 'o', long, value_name = "OUTPUT")]
    pub output: Option<PathBuf>,

    /// Format file(s) in place
    #[arg(short = 'i', long)]
    pub in_place: bool,

    /// Check if file is formatted (exit 1 if not)
    #[arg(long)]
    pub check: bool,

    /// Show diff when using --check
    #[arg(long, requires = "check")]
    pub diff: bool,

    /// Column for aligning currencies (same as --currency-column)
    #[arg(short = 'c', long = "currency-column", default_value = "60")]
    pub column: usize,

    /// Force fixed prefix width (account name column width)
    #[arg(short = 'w', long)]
    pub prefix_width: Option<usize>,

    /// Force fixed numbers width
    #[arg(short = 'W', long)]
    pub num_width: Option<usize>,

    /// Number of spaces for posting indentation (default: 2)
    #[arg(long, default_value = "2")]
    pub indent: usize,

    /// Show verbose output
    #[arg(short, long)]
    pub verbose: bool,
}

fn run(args: &Args) -> Result<ExitCode> {
    if args.output.is_some() && args.files.len() > 1 {
        anyhow::bail!(
            "--output can only be used with a single input file. Use --in-place for multiple files."
        );
    }

    if args.output.is_some() && args.in_place {
        anyhow::bail!("--output and --in-place cannot be used together");
    }

    let mut any_needs_formatting = false;

    for file in &args.files {
        let result = format_file(file, args)?;
        if result == ExitCode::from(1) {
            any_needs_formatting = true;
        }
    }

    if args.check && any_needs_formatting {
        Ok(ExitCode::from(1))
    } else {
        Ok(ExitCode::SUCCESS)
    }
}

fn format_file(file: &PathBuf, args: &Args) -> Result<ExitCode> {
    if !file.exists() {
        anyhow::bail!("file not found: {}", file.display());
    }

    let original_content =
        fs::read_to_string(file).with_context(|| format!("failed to read {}", file.display()))?;

    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    if !load_result.errors.is_empty() {
        for err in &load_result.errors {
            eprintln!("error: {err}");
        }
        anyhow::bail!("file has parse errors, cannot format");
    }

    let config = FormatConfig::new(args.column, args.indent);
    let mut formatted = String::new();
    #[allow(clippy::useless_let_if_seq)]
    let mut has_preamble = false;

    if let Some(title) = &load_result.options.title {
        formatted.push_str(&format!("option \"title\" \"{title}\"\n"));
        has_preamble = true;
    }
    for currency in &load_result.options.operating_currency {
        formatted.push_str(&format!("option \"operating_currency\" \"{currency}\"\n"));
        has_preamble = true;
    }

    for plugin in &load_result.plugins {
        if let Some(cfg) = &plugin.config {
            formatted.push_str(&format!("plugin \"{}\" \"{}\"\n", plugin.name, cfg));
        } else {
            formatted.push_str(&format!("plugin \"{}\"\n", plugin.name));
        }
        has_preamble = true;
    }

    if has_preamble {
        formatted.push('\n');
    }

    for spanned in &load_result.directives {
        formatted.push_str(&format_directive(&spanned.value, &config));
    }

    if args.check {
        if formatted.trim() == original_content.trim() {
            if args.verbose {
                eprintln!("File is already formatted: {}", file.display());
            }
            Ok(ExitCode::SUCCESS)
        } else {
            if args.verbose {
                eprintln!("File needs formatting: {}", file.display());
            }
            if args.diff {
                eprintln!("--- {}", file.display());
                eprintln!("+++ {} (formatted)", file.display());
                for (i, (orig, fmt)) in original_content.lines().zip(formatted.lines()).enumerate()
                {
                    if orig != fmt {
                        eprintln!("@@ line {} @@", i + 1);
                        eprintln!("-{orig}");
                        eprintln!("+{fmt}");
                    }
                }
                let orig_lines: Vec<_> = original_content.lines().collect();
                let fmt_lines: Vec<_> = formatted.lines().collect();
                if orig_lines.len() != fmt_lines.len() {
                    let min_len = orig_lines.len().min(fmt_lines.len());
                    for (i, line) in orig_lines.iter().skip(min_len).enumerate() {
                        eprintln!("@@ line {} (removed) @@", min_len + i + 1);
                        eprintln!("-{line}");
                    }
                    for (i, line) in fmt_lines.iter().skip(min_len).enumerate() {
                        eprintln!("@@ line {} (added) @@", min_len + i + 1);
                        eprintln!("+{line}");
                    }
                }
            }
            Ok(ExitCode::from(1))
        }
    } else if args.in_place {
        fs::write(file, &formatted)
            .with_context(|| format!("failed to write {}", file.display()))?;
        if args.verbose {
            eprintln!("Formatted: {}", file.display());
        }
        Ok(ExitCode::SUCCESS)
    } else if let Some(ref output_path) = args.output {
        fs::write(output_path, &formatted)
            .with_context(|| format!("failed to write {}", output_path.display()))?;
        if args.verbose {
            eprintln!("Formatted {} -> {}", file.display(), output_path.display());
        }
        Ok(ExitCode::SUCCESS)
    } else {
        let mut stdout = io::stdout().lock();
        stdout
            .write_all(formatted.as_bytes())
            .context("failed to write to stdout")?;
        Ok(ExitCode::SUCCESS)
    }
}

/// Main entry point for the format command.
pub fn main() -> ExitCode {
    main_with_name("rledger-format")
}

/// Main entry point with custom binary name (for bean-format compatibility).
pub fn main_with_name(bin_name: &str) -> ExitCode {
    let args = Args::parse();

    // Handle shell completion generation
    if let Some(shell) = args.generate_completions {
        crate::cmd::completions::generate_completions::<Args>(shell, bin_name);
        return ExitCode::SUCCESS;
    }

    match run(&args) {
        Ok(exit_code) => exit_code,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::from(2)
        }
    }
}
