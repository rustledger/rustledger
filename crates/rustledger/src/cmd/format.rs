//! `rledger format` — opinionated whole-file formatter.
//!
//! Routes every input file through the canonical CST-backed formatter
//! ([`rustledger_parser::format::format_source`]). One canonical form per AST
//! shape, no knobs: see the canonical-form spec in the formatter's
//! rustdoc and in the PR-4 decision comment on #1262.

use crate::cmd::completions::ShellType;
use anyhow::{Context, Result};
use clap::Parser;
use rustledger_parser::format::{cr_outside_strings_present, try_format_source};
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

/// Run the format command with the given arguments, writing formatted
/// output to stdout.
///
/// Thin wrapper over [`run_with_writer`] for the synchronous `rledger`
/// binary; `ag-rledger` calls `run_with_writer` with a buffer.
pub fn run(args: &Args) -> Result<ExitCode> {
    let mut stdout = io::stdout().lock();
    run_with_writer(args, &mut stdout)
}

/// Run the format command, writing any stdout-bound formatted output to
/// `out`.
///
/// Only the default "print formatted file to stdout" path is redirected
/// to `out`; `--in-place` and `--output <file>` still write to disk, and
/// `--check`/`--diff`/verbose notes still go to stderr, exactly as in the
/// original `run()`.
pub fn run_with_writer<W: Write>(args: &Args, out: &mut W) -> Result<ExitCode> {
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
        let result = format_file(file, args, out)?;
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

fn format_file<W: Write>(file: &PathBuf, args: &Args, out: &mut W) -> Result<ExitCode> {
    if !file.exists() {
        anyhow::bail!("file not found: {}", file.display());
    }

    let original_content =
        fs::read_to_string(file).with_context(|| format!("failed to read {}", file.display()))?;

    let formatted = match try_format_source(&original_content) {
        Ok(out) => out,
        Err(errors) => {
            for err in &errors {
                eprintln!("error: {err}");
            }
            anyhow::bail!("file has parse errors, cannot format");
        }
    };

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
        out.write_all(formatted.as_bytes())
            .context("failed to write to stdout")?;
        Ok(ExitCode::SUCCESS)
    }
}

/// Render a `--diff` block for a non-canonical file.
///
/// Handles four cases beyond the obvious per-line replacement:
///
/// - **Whitespace-only normalization.** The canonical form strips
///   the leading BOM, folds CR-bearing line endings to LF outside
///   strings, and emits exactly one trailing LF. If the file's
///   delta is fully explained by one or more of those passes, we
///   surface the cause explicitly instead of producing a per-line
///   diff that just shows BOMs and `\r`s.
/// - **Line-by-line replacements.** Otherwise emit `@@ line N @@`
///   per-line diff hunks.
fn emit_diff(file: &PathBuf, original: &str, formatted: &str) {
    eprintln!("--- {}", file.display());
    eprintln!("+++ {} (formatted)", file.display());

    // Compute the canonical-noise-stripped view of the original:
    // drop the BOM, normalize CR-bearing line endings to LF outside
    // strings, then trim_end_matches('\n'). The formatted side
    // gets the same trim. If the bodies match, the file's delta is
    // entirely explainable by canonical normalization; surface the
    // specific cause so the user knows what to expect from
    // `--in-place`.
    let original_no_bom = original.strip_prefix('\u{FEFF}').unwrap_or(original);
    let had_bom = original_no_bom.len() < original.len();
    let folded_cr = cr_outside_strings_present(original_no_bom);
    let lf_only: std::borrow::Cow<'_, str> = if folded_cr {
        rustledger_parser::format::crlf_to_lf_outside_strings(original_no_bom)
    } else {
        std::borrow::Cow::Borrowed(original_no_bom)
    };

    let orig_body = lf_only.trim_end_matches('\n');
    let fmt_body = formatted.trim_end_matches('\n');
    if orig_body == fmt_body {
        let mut causes: Vec<&'static str> = Vec::new();
        if had_bom {
            causes.push("leading BOM (dropped)");
        }
        // `folded_cr` comes from the explicit
        // `cr_outside_strings_present` predicate: a file whose
        // only `\r` is inside a string literal returns false (the
        // formatter doesn't fold those), so we don't surface a
        // misleading "CR folded" cause for an in-string `\r`.
        if folded_cr {
            causes.push("CR-bearing line endings (folded to LF)");
        }
        let orig_trailing = lf_only.len() - orig_body.len();
        let fmt_trailing = formatted.len() - fmt_body.len();
        match orig_trailing.cmp(&fmt_trailing) {
            std::cmp::Ordering::Less => causes.push("missing final newline (added)"),
            std::cmp::Ordering::Greater => causes.push("extra trailing newlines (collapsed)"),
            std::cmp::Ordering::Equal => {}
        }
        if causes.is_empty() {
            // Bodies equal AND no whitespace-noise cause — this
            // can only happen on byte-identical input, which the
            // caller already gates against. Defensive message in
            // case a future caller invokes emit_diff regardless.
            eprintln!(
                "  (no per-line content change; the difference is in \
                 leading/trailing whitespace that `.lines()` strips)"
            );
        } else {
            eprintln!(
                "  (no per-line content change; canonical normalization: {} — \
                 run `rledger format -i` to rewrite)",
                causes.join(", "),
            );
        }
        return;
    }

    let orig_lines: Vec<&str> = original.lines().collect();
    let fmt_lines: Vec<&str> = formatted.lines().collect();
    for (i, (orig, fmt)) in orig_lines.iter().zip(fmt_lines.iter()).enumerate() {
        if orig != fmt {
            eprintln!("@@ line {} @@", i + 1);
            eprintln!("-{orig}");
            eprintln!("+{fmt}");
        }
    }
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
