//! Error reporting with beautiful diagnostics.
//!
//! Uses ariadne for pretty-printed error messages with source context.

use ariadne::{ColorGenerator, Config, Label, Report, ReportKind, Source};
use rustledger_parser::ParseError;
use rustledger_validate::{ErrorCode, ValidationError};
use std::collections::HashMap;
use std::io::Write;
use std::path::Path;

/// A source cache for ariadne.
pub struct SourceCache {
    sources: HashMap<String, Source<String>>,
}

impl SourceCache {
    /// Create a new source cache.
    pub fn new() -> Self {
        Self {
            sources: HashMap::new(),
        }
    }

    /// Add a source file to the cache.
    pub fn add(&mut self, path: &str, content: String) {
        self.sources.insert(path.to_string(), Source::from(content));
    }

    /// Get a source by path.
    #[allow(dead_code)]
    pub fn get(&self, path: &str) -> Option<&Source<String>> {
        self.sources.get(path)
    }
}

impl Default for SourceCache {
    fn default() -> Self {
        Self::new()
    }
}

/// Report parse errors to the given writer.
pub fn report_parse_errors<W: Write>(
    errors: &[ParseError],
    source_path: &Path,
    source: &str,
    writer: &mut W,
) -> std::io::Result<usize> {
    let path_str = source_path.display().to_string();
    let mut colors = ColorGenerator::new();
    let error_count = errors.len();

    for error in errors {
        let color = colors.next();
        let (start, end) = error.span();

        Report::build(ReportKind::Error, &path_str, start)
            .with_code(format!("P{:04}", error.kind_code()))
            .with_message(error.message())
            .with_label(
                Label::new((&path_str, start..end))
                    .with_message(error.label())
                    .with_color(color),
            )
            .with_config(Config::default().with_compact(false))
            .finish()
            .write((&path_str, Source::from(source)), &mut *writer)?;
    }

    Ok(error_count)
}

/// Report validation errors to the given writer.
pub fn report_validation_errors<W: Write>(
    errors: &[ValidationError],
    _cache: &SourceCache,
    writer: &mut W,
) -> std::io::Result<usize> {
    let error_count = errors.len();

    for error in errors {
        writeln!(
            writer,
            "error[{}]: {} ({})",
            format_error_code(error.code),
            error.message,
            error.date
        )?;
        if let Some(ctx) = &error.context {
            writeln!(writer, "  context: {ctx}")?;
        }
        writeln!(writer)?;
    }

    Ok(error_count)
}

/// Format an error code for display.
fn format_error_code(code: ErrorCode) -> String {
    // Use the built-in code() method
    code.code().to_string()
}

/// Print a summary of errors and warnings.
pub fn print_summary<W: Write>(
    errors: usize,
    warnings: usize,
    writer: &mut W,
) -> std::io::Result<()> {
    if errors == 0 && warnings == 0 {
        writeln!(writer, "\x1b[32m\u{2713}\x1b[0m No errors found")?;
    } else {
        let error_text = if errors == 1 { "error" } else { "errors" };
        let warning_text = if warnings == 1 { "warning" } else { "warnings" };

        if errors > 0 && warnings > 0 {
            writeln!(
                writer,
                "\x1b[31m\u{2717}\x1b[0m {errors} {error_text}, {warnings} {warning_text}"
            )?;
        } else if errors > 0 {
            writeln!(writer, "\x1b[31m\u{2717}\x1b[0m {errors} {error_text}")?;
        } else {
            writeln!(writer, "\x1b[33m\u{26A0}\x1b[0m {warnings} {warning_text}")?;
        }
    }
    Ok(())
}
