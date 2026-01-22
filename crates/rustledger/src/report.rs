//! Error reporting with beautiful diagnostics.
//!
//! Uses ariadne for pretty-printed error messages with source context.
//! Respects TTY detection and `NO_COLOR` environment variable.

use ariadne::{ColorGenerator, Config, Label, Report, ReportKind, Source};
use rustledger_loader::SourceMap;
use rustledger_parser::ParseError;
use rustledger_validate::{ErrorCode, ValidationError};
use std::collections::HashMap;
use std::io::{IsTerminal, Write};
use std::path::Path;

/// Determine if colors should be used for output.
///
/// Returns `true` if:
/// - stdout is a TTY (terminal)
/// - `NO_COLOR` environment variable is not set
///
/// See <https://no-color.org/> for the `NO_COLOR` standard.
pub fn should_use_color() -> bool {
    // Check NO_COLOR environment variable (any value disables color)
    if std::env::var_os("NO_COLOR").is_some() {
        return false;
    }
    // Check if stdout is a terminal
    std::io::stdout().is_terminal()
}

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
///
/// If `use_color` is false, ANSI color codes are disabled.
pub fn report_parse_errors<W: Write>(
    errors: &[ParseError],
    source_path: &Path,
    source: &str,
    writer: &mut W,
    use_color: bool,
) -> std::io::Result<usize> {
    let path_str = source_path.display().to_string();
    let mut colors = ColorGenerator::new();
    let error_count = errors.len();

    for error in errors {
        let (start, end) = error.span();

        let label = Label::new((&path_str, start..end)).with_message(error.label());
        // Only set label color when colors are enabled
        let label = if use_color {
            label.with_color(colors.next())
        } else {
            label
        };

        let mut report = Report::build(ReportKind::Error, (&path_str, start..end))
            .with_code(format!("P{:04}", error.kind_code()))
            .with_message(error.message())
            .with_label(label)
            .with_config(Config::default().with_compact(false).with_color(use_color));

        // Add hint if present
        if let Some(hint) = &error.hint {
            report = report.with_help(hint);
        }

        report
            .finish()
            .write((&path_str, Source::from(source)), &mut *writer)?;
    }

    Ok(error_count)
}

/// Report validation errors to the given writer.
///
/// Output format matches Python beancount for compatibility:
/// `file:line: error[CODE]: message (date)`
///
/// If `use_color` is false, ANSI color codes are disabled.
pub fn report_validation_errors<W: Write>(
    errors: &[ValidationError],
    source_map: &SourceMap,
    _cache: &SourceCache,
    writer: &mut W,
    _use_color: bool,
) -> std::io::Result<usize> {
    let error_count = errors.len();

    for error in errors {
        // Format location if available
        let location = if let (Some(span), Some(file_id)) = (error.span, error.file_id) {
            if let Some(source_file) = source_map.get(file_id as usize) {
                let (line, _col) = source_file.line_col(span.start);
                format!("{}:{}", source_file.path.display(), line)
            } else {
                String::new()
            }
        } else {
            String::new()
        };

        if location.is_empty() {
            // No location info - use original format
            writeln!(
                writer,
                "error[{}]: {} ({})",
                format_error_code(error.code),
                error.message,
                error.date
            )?;
        } else {
            // Python beancount compatible format: file:line: message
            writeln!(
                writer,
                "{}: error[{}]: {} ({})",
                location,
                format_error_code(error.code),
                error.message,
                error.date
            )?;
        }

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
///
/// If `use_color` is false, ANSI color codes are disabled.
pub fn print_summary<W: Write>(
    errors: usize,
    warnings: usize,
    writer: &mut W,
    use_color: bool,
) -> std::io::Result<()> {
    // Color codes
    let (green, red, yellow, reset) = if use_color {
        ("\x1b[32m", "\x1b[31m", "\x1b[33m", "\x1b[0m")
    } else {
        ("", "", "", "")
    };

    if errors == 0 && warnings == 0 {
        writeln!(writer, "{green}\u{2713}{reset} No errors found")?;
    } else {
        let error_text = if errors == 1 { "error" } else { "errors" };
        let warning_text = if warnings == 1 { "warning" } else { "warnings" };

        if errors > 0 && warnings > 0 {
            writeln!(
                writer,
                "{red}\u{2717}{reset} {errors} {error_text}, {warnings} {warning_text}"
            )?;
        } else if errors > 0 {
            writeln!(writer, "{red}\u{2717}{reset} {errors} {error_text}")?;
        } else {
            writeln!(writer, "{yellow}\u{26A0}{reset} {warnings} {warning_text}")?;
        }
    }
    Ok(())
}
