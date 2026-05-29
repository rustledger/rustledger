//! Shared implementation for bean-format and rledger format commands.
//!
//! This formatter preserves comments, blank lines, and original file structure.
//! It uses the parser directly (not the Loader) to capture all elements with their
//! source spans, then outputs them in order, only reformatting directive content
//! while preserving comments and other non-directive content.

use crate::cmd::completions::ShellType;
use crate::format::{
    Alignment, FormatConfig, FormatLine, escape_string, format_directive_lines, render_lines,
};
use anyhow::{Context, Result};
use clap::Parser;
use rustledger_parser::{Span, Spanned, parse};
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

/// Format beancount files.
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

    /// Align currencies to this fixed column (bean-format -c). When
    /// omitted, widths are chosen automatically from the file contents.
    #[arg(short = 'c', long = "currency-column", value_name = "COL")]
    pub column: Option<usize>,

    /// Force fixed prefix width (account name column width)
    #[arg(short = 'w', long)]
    pub prefix_width: Option<usize>,

    /// Force fixed numbers width
    #[arg(short = 'W', long)]
    pub num_width: Option<usize>,

    /// Number of spaces for posting indentation (default: 2)
    #[arg(long)]
    pub indent: Option<usize>,

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

/// A parsed item that can be formatted, with its source span.
enum FormattableItem {
    Directive(Spanned<rustledger_core::Directive>),
    Option(String, String, Span),
    Include(String, Span),
    Plugin(String, Option<String>, Span),
    Comment(Spanned<String>),
}

impl FormattableItem {
    const fn span(&self) -> Span {
        match self {
            Self::Directive(d) => d.span,
            Self::Option(_, _, span) => *span,
            Self::Include(_, span) => *span,
            Self::Plugin(_, _, span) => *span,
            Self::Comment(c) => c.span,
        }
    }
}

fn format_file(file: &PathBuf, args: &Args) -> Result<ExitCode> {
    if !file.exists() {
        anyhow::bail!("file not found: {}", file.display());
    }

    let original_content =
        fs::read_to_string(file).with_context(|| format!("failed to read {}", file.display()))?;

    // Parse the file directly to get all items with their spans
    let parse_result = parse(&original_content);

    if !parse_result.errors.is_empty() {
        for err in &parse_result.errors {
            eprintln!("error: {err}");
        }
        anyhow::bail!("file has parse errors, cannot format");
    }

    // Collect all items into a unified list
    let mut items: Vec<FormattableItem> = Vec::new();

    for directive in parse_result.directives {
        items.push(FormattableItem::Directive(directive));
    }

    for (key, value, span) in parse_result.options {
        items.push(FormattableItem::Option(key, value, span));
    }

    for (path, span) in parse_result.includes {
        items.push(FormattableItem::Include(path, span));
    }

    for (name, config, span) in parse_result.plugins {
        items.push(FormattableItem::Plugin(name, config, span));
    }

    for comment in parse_result.comments {
        items.push(FormattableItem::Comment(comment));
    }

    // Sort all items by their span start position to preserve original order
    items.sort_by(|a, b| {
        let a_start = a.span().start;
        let b_start = b.span().start;
        a_start.cmp(&b_start)
    });

    // Resolve the alignment mode: an explicit currency column wins (and
    // ignores -w/-W, matching bean-format); otherwise auto-size widths
    // from the file, honoring any -w/-W overrides.
    let config = FormatConfig {
        alignment: match args.column {
            Some(col) => Alignment::CurrencyColumn(col),
            None => Alignment::Auto {
                prefix_width: args.prefix_width,
                num_width: args.num_width,
            },
        },
        indent: " ".repeat(args.indent.unwrap_or(2)),
    };

    // Phase 1: render every item to a flat list of FormatLines, preserving
    // blank lines as empty entries. Phase 2 (render_lines) then aligns all
    // amount-bearing lines against file-wide column widths in one pass.
    let mut lines: Vec<FormatLine> = Vec::new();
    let mut prev_end: usize = 0;

    for item in &items {
        let item_start = item.span().start;

        // Preserve blank lines between items by counting newlines in the
        // gap. One newline terminates the previous item's last line; any
        // extras are blank lines. At the start of file (prev_end == 0)
        // every leading newline is a blank line.
        if item_start > prev_end {
            let between = &original_content[prev_end..item_start];
            let newline_count = between.chars().filter(|&c| c == '\n').count();
            let blank_lines = if prev_end == 0 {
                newline_count
            } else {
                newline_count.saturating_sub(1)
            };
            for _ in 0..blank_lines {
                lines.push(FormatLine::Plain(String::new()));
            }
        }

        match item {
            FormattableItem::Directive(d) => {
                lines.extend(format_directive_lines(&d.value, &config));

                // Preserve trailing blank lines inside the directive span.
                // Walk backwards counting '\n' (treating '\r' as part of a
                // CRLF pair) so "\r\n\r\n" yields 2. The directive's own
                // last line already terminates with one newline at render
                // time, so only the extras become blank lines.
                let original_text = &original_content[d.span.start..d.span.end];
                let mut trailing_newlines = 0usize;
                for c in original_text.chars().rev() {
                    match c {
                        '\n' => trailing_newlines += 1,
                        '\r' => {}
                        _ => break,
                    }
                }
                for _ in 1..trailing_newlines {
                    lines.push(FormatLine::Plain(String::new()));
                }
            }
            FormattableItem::Option(key, value, _) => {
                lines.push(FormatLine::Plain(format!(
                    "option \"{}\" \"{}\"",
                    escape_string(key),
                    escape_string(value)
                )));
            }
            FormattableItem::Include(path, _) => {
                lines.push(FormatLine::Plain(format!(
                    "include \"{}\"",
                    escape_string(path)
                )));
            }
            FormattableItem::Plugin(name, config_str, _) => {
                lines.push(FormatLine::Plain(if let Some(cfg) = config_str {
                    format!(
                        "plugin \"{}\" \"{}\"",
                        escape_string(name),
                        escape_string(cfg)
                    )
                } else {
                    format!("plugin \"{}\"", escape_string(name))
                }));
            }
            FormattableItem::Comment(c) => {
                // Emit verbatim; render_lines re-adds the single trailing
                // newline that the span may have captured.
                lines.push(FormatLine::Plain(
                    c.value.trim_end_matches('\n').to_string(),
                ));
            }
        }

        prev_end = item.span().end;
    }

    let mut formatted = render_lines(&lines, &config.alignment);

    // An empty file still needs a trailing newline; render_lines emits none
    // for an empty line list.
    if !formatted.ends_with('\n') {
        formatted.push('\n');
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
