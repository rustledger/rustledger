//! Error reporting with beautiful diagnostics.
//!
//! Uses miette for pretty-printed error messages with source context.
//! Respects TTY detection and `NO_COLOR` environment variable.

use miette::{GraphicalReportHandler, GraphicalTheme, LabeledSpan, Severity};
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
    if std::env::var_os("NO_COLOR").is_some() {
        return false;
    }
    std::io::stdout().is_terminal()
}

/// A source cache for error reporting.
pub struct SourceCache {
    sources: HashMap<String, String>,
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
        self.sources.insert(path.to_string(), content);
    }
}

impl Default for SourceCache {
    fn default() -> Self {
        Self::new()
    }
}

/// Build a miette report handler with the given color settings.
fn build_handler(use_color: bool) -> GraphicalReportHandler {
    if use_color {
        GraphicalReportHandler::new()
    } else {
        GraphicalReportHandler::new_themed(GraphicalTheme::none())
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
    let error_count = errors.len();
    let handler = build_handler(use_color);
    let named_source = miette::NamedSource::new(&path_str, source.to_string());

    for error in errors {
        let (start, end) = error.span();

        let diagnostic = miette::MietteDiagnostic {
            message: error.message(),
            code: Some(format!("P{:04}", error.kind_code())),
            severity: Some(Severity::Error),
            help: error.hint.as_ref().map(String::from),
            url: None,
            labels: Some(vec![LabeledSpan::at(start..end, error.label())]),
        };

        let report = miette::Report::new(diagnostic).with_source_code(named_source.clone());

        // Render to string then write
        let mut rendered = String::new();
        handler
            .render_report(&mut rendered, report.as_ref())
            .map_err(|e| std::io::Error::other(e.to_string()))?;
        write!(writer, "{rendered}")?;
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

        let severity_label = match error.code.severity() {
            rustledger_validate::Severity::Error => "error",
            rustledger_validate::Severity::Warning => "warning",
            rustledger_validate::Severity::Info => "info",
        };

        if location.is_empty() {
            writeln!(
                writer,
                "{}[{}]: {} ({})",
                severity_label,
                format_error_code(error.code),
                error.message,
                error.date
            )?;
        } else {
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
    use rustledger_core::NaiveDate;

    #[test]
    fn test_report_validation_errors_warning_label() {
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

    #[test]
    fn test_report_parse_errors_renders() {
        use rustledger_parser::parse;

        let source = "INVALID GARBAGE\n";
        let result = parse(source);
        assert!(!result.errors.is_empty());

        let mut output = Vec::new();
        let path = Path::new("test.beancount");
        report_parse_errors(&result.errors, path, source, &mut output, false).unwrap();

        let output_str = String::from_utf8(output).unwrap();
        assert!(!output_str.is_empty(), "Should produce output");
        assert!(
            output_str.contains("P0012") || output_str.contains("parse error"),
            "Should contain error code or message: {output_str}"
        );
    }

    #[test]
    fn test_report_parse_errors_cjk_no_panic() {
        use rustledger_parser::parse;

        // CJK characters in narration followed by a parse error.
        // This must not panic or produce garbled output — the motivation
        // for migrating from ariadne to miette (#728).
        let source = "2026-01-04 * \"いろは\"\n  GARBAGE\n";
        let result = parse(source);
        assert!(!result.errors.is_empty());

        let mut output = Vec::new();
        let path = Path::new("test.beancount");
        report_parse_errors(&result.errors, path, source, &mut output, false).unwrap();

        let output_str = String::from_utf8(output).unwrap();
        assert!(
            !output_str.is_empty(),
            "Should produce output for CJK source"
        );
    }
}
