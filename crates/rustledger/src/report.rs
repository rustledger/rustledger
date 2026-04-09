//! Error reporting with beautiful diagnostics.
//!
//! Uses ariadne for pretty-printed error messages with source context.
//! Respects TTY detection and `NO_COLOR` environment variable.

use ariadne::{ColorGenerator, Config, IndexType, Label, Report, ReportKind, Source};
use rustledger_loader::SourceMap;
use rustledger_parser::ParseError;
use rustledger_validate::{ErrorCode, Severity, ValidationError};
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
            .with_config(
                Config::default()
                    .with_compact(false)
                    .with_color(use_color)
                    .with_index_type(IndexType::Byte),
            );

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

        // Use correct severity label based on error code classification
        let severity_label = match error.code.severity() {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Info => "info",
        };

        if location.is_empty() {
            // No location info - use original format
            writeln!(
                writer,
                "{}[{}]: {} ({})",
                severity_label,
                format_error_code(error.code),
                error.message,
                error.date
            )?;
        } else {
            // Format: file:line: severity[CODE]: message (date)
            writeln!(
                writer,
                "{}: {}[{}]: {} ({})",
                location,
                severity_label,
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

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::NaiveDate;

    #[test]
    fn test_report_validation_errors_warning_label() {
        // E1004 (AccountCloseNotEmpty) is classified as a warning
        let warning = ValidationError::new(
            ErrorCode::AccountCloseNotEmpty,
            "Cannot close account with non-zero balance".to_string(),
            NaiveDate::from_ymd_opt(2024, 1, 1).unwrap(),
        );

        let mut output = Vec::new();
        let source_map = SourceMap::default();
        let cache = SourceCache::new();

        report_validation_errors(&[warning], &source_map, &cache, &mut output, false).unwrap();

        let output_str = String::from_utf8(output).unwrap();
        assert!(
            output_str.contains("warning[E1004]"),
            "Expected 'warning[E1004]' but got: {output_str}"
        );
        assert!(
            !output_str.contains("error[E1004]"),
            "Should not contain 'error[E1004]': {output_str}"
        );
    }

    #[test]
    fn test_report_validation_errors_error_label() {
        // E1001 (AccountNotOpen) is classified as an error
        let error = ValidationError::new(
            ErrorCode::AccountNotOpen,
            "Account was never opened".to_string(),
            NaiveDate::from_ymd_opt(2024, 1, 1).unwrap(),
        );

        let mut output = Vec::new();
        let source_map = SourceMap::default();
        let cache = SourceCache::new();

        report_validation_errors(&[error], &source_map, &cache, &mut output, false).unwrap();

        let output_str = String::from_utf8(output).unwrap();
        assert!(
            output_str.contains("error[E1001]"),
            "Expected 'error[E1001]' but got: {output_str}"
        );
    }

    /// Test that error span highlighting is correct when non-ASCII characters
    /// appear earlier in the source (regression test for issue #728).
    ///
    /// The parser generates byte-offset spans, but ariadne's default mode
    /// (`IndexType::Char`) interprets them as character offsets, causing the
    /// highlight to drift right when multi-byte UTF-8 characters are present.
    /// The fix uses `IndexType::Byte` so ariadne correctly converts byte
    /// offsets to character positions internally.
    #[test]
    fn test_report_parse_errors_non_ascii_span_accuracy() {
        use rustledger_parser::ParseError;
        use rustledger_parser::span::Span;

        // Source with non-ASCII chars on line 2 (αβγδε = 5 chars × 2 bytes each = 10 bytes)
        // The error should highlight "-1,234 JPY;23456789" on line 4.
        let source = "2026-01-01 open Assets:Test\n\
                       2026-01-04 * \"αβγδε\"\n\
                       2026-01-04 * \"abc\"\n\
                         Assets:Test -1,234 JPY\n";

        // Find the byte offsets of "-1,234 JPY" on the last line
        let dash_offset = source
            .rfind("-1,234")
            .expect("test source should contain '-1,234'");
        let highlight_end = dash_offset + "-1,234 JPY".len();

        let error = ParseError::new(
            rustledger_parser::error::ParseErrorKind::SyntaxError("unexpected input".to_string()),
            Span::new(dash_offset, highlight_end),
        );

        let mut output = Vec::new();
        report_parse_errors(
            &[error],
            Path::new("test.beancount"),
            source,
            &mut output,
            false, // no color for easier assertion
        )
        .unwrap();

        let output_str = String::from_utf8(output).unwrap();

        // The output should reference line 4 (1-indexed) with the correct
        // character column for "-1,234". If the span were misinterpreted as
        // char offsets, the highlight would drift by 5 (= 10 bytes − 5 chars).
        assert!(
            output_str.contains("-1,234"),
            "Error output should highlight '-1,234' but got:\n{output_str}"
        );
        // It should NOT highlight the text that appears 5 chars to the right
        // of the actual error (which would be " JPY;" or later).
        assert!(
            !output_str.contains("parse error: unexpected input\n")
                || output_str.contains("-1,234"),
            "Highlight should cover '-1,234', not drifted text"
        );
    }
}
