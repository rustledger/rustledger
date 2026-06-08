//! `rledger format` — opinionated whole-file formatter.
//!
//! Routes every input file through the canonical CST-backed formatter
//! ([`rustledger_parser::format_source`]). One canonical form per AST
//! shape, no knobs: see the canonical-form spec in the formatter's
//! rustdoc and in the PR-4 decision comment on #1262.

use crate::cmd::completions::ShellType;
use anyhow::{Context, Result};
use clap::Parser;
use rustledger_parser::{format_source, parse};
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

/// Format beancount files in the canonical opinionated form.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// The beancount file(s) to format (uses config default if not specified)
    #[arg(value_name = "FILE")]
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

    /// Show verbose output
    #[arg(short, long)]
    pub verbose: bool,
}

/// Run the format command with the given arguments.
pub fn run(args: &Args) -> Result<ExitCode> {
    if args.files.is_empty() {
        anyhow::bail!("FILE is required (or set default.file in config)");
    }

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

    let parse_result = parse(&original_content);

    if !parse_result.errors.is_empty() {
        for err in &parse_result.errors {
            eprintln!("error: {err}");
        }
        anyhow::bail!("file has parse errors, cannot format");
    }

    let formatted = format_source(&original_content);

    if args.check {
        // Byte-exact comparison: --check must report the same diff
        // --in-place would actually write. A trim-based comparison
        // masks trailing-blank-line / leading-blank-line differences
        // that the canonical form rewrites — exactly the kind of
        // change the new formatter introduces (one trailing newline,
        // exactly one blank between directives).
        if formatted == original_content {
            if args.verbose {
                eprintln!("File is already formatted: {}", file.display());
            }
            Ok(ExitCode::SUCCESS)
        } else {
            if args.verbose {
                eprintln!("File needs formatting: {}", file.display());
            }
            if args.diff {
                emit_diff(file, &original_content, &formatted);
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

/// Render a `--diff` block for a non-canonical file.
///
/// Handles four cases beyond the obvious per-line replacement:
///
/// - **Line-ending normalization** (CRLF and / or bare CR). The
///   canonical form normalizes every CR-bearing terminator to LF.
///   If stripping CR characters from the original makes it match
///   the formatted output, we say so explicitly instead of
///   printing a header with no hunks.
/// - **Missing trailing newline.** Canonical form ends with
///   exactly one LF. If the original lacks one, surface that.
/// - **Extra trailing newlines.** If the original ends with `\n\n…`
///   that collapses to a single `\n`, surface that.
/// - **Line-by-line replacements.** Otherwise emit the existing
///   `@@ line N @@` per-line diff hunks.
fn emit_diff(file: &PathBuf, original: &str, formatted: &str) {
    eprintln!("--- {}", file.display());
    eprintln!("+++ {} (formatted)", file.display());

    // CR-bearing line endings (CRLF or bare CR). If stripping every
    // CR (and CRLF) from the original makes it match the formatted
    // output, the only divergence is line-ending normalization.
    if original.contains('\r') {
        let lf_only = original.replace("\r\n", "\n").replace('\r', "\n");
        if lf_only == *formatted {
            eprintln!(
                "  (no per-line content change; the canonical form \
                 normalizes line endings to LF — run `rledger format -i` \
                 to rewrite)"
            );
            return;
        }
    }

    let orig_lines: Vec<&str> = original.lines().collect();
    let fmt_lines: Vec<&str> = formatted.lines().collect();
    let mut printed_hunk = false;
    for (i, (orig, fmt)) in orig_lines.iter().zip(fmt_lines.iter()).enumerate() {
        if orig != fmt {
            eprintln!("@@ line {} @@", i + 1);
            eprintln!("-{orig}");
            eprintln!("+{fmt}");
            printed_hunk = true;
        }
    }
    if orig_lines.len() != fmt_lines.len() {
        let min_len = orig_lines.len().min(fmt_lines.len());
        for (i, line) in orig_lines.iter().skip(min_len).enumerate() {
            eprintln!("@@ line {} (removed) @@", min_len + i + 1);
            eprintln!("-{line}");
            printed_hunk = true;
        }
        for (i, line) in fmt_lines.iter().skip(min_len).enumerate() {
            eprintln!("@@ line {} (added) @@", min_len + i + 1);
            eprintln!("+{line}");
            printed_hunk = true;
        }
    }
    if !printed_hunk {
        // Byte-exact comparison said the files differ, but lines()
        // produced no hunks. Distinguish the two trailing-newline
        // cases explicitly so the user sees the actual problem.
        let orig_trailing = trailing_newline_count(original);
        let fmt_trailing = trailing_newline_count(formatted);
        match orig_trailing.cmp(&fmt_trailing) {
            std::cmp::Ordering::Less => eprintln!(
                "  (no per-line content change; file is missing a final \
                 newline — the canonical form ends every file with one)"
            ),
            std::cmp::Ordering::Greater => eprintln!(
                "  (no per-line content change; the file has extra \
                 trailing newlines — the canonical form collapses them \
                 to one)"
            ),
            std::cmp::Ordering::Equal => eprintln!(
                "  (no per-line content change; the difference is in \
                 leading/trailing whitespace that `.lines()` strips)"
            ),
        }
    }
}

/// Number of consecutive `\n` characters at the END of `s`.
fn trailing_newline_count(s: &str) -> usize {
    s.bytes().rev().take_while(|&b| b == b'\n').count()
}
