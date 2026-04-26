//! Error reporting with beautiful diagnostics.
//!
//! Uses miette for pretty-printed error messages with source context.
//! Respects TTY detection and `NO_COLOR` environment variable.

use miette::{GraphicalReportHandler, GraphicalTheme, LabeledSpan, Severity};
use rustledger_loader::{LedgerError, SourceMap};
use rustledger_parser::ParseError;
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

/// Stateful renderer for a stream of [`LedgerError`]s (issue #901).
///
/// Builds the miette [`GraphicalReportHandler`] once and caches a
/// [`miette::NamedSource`] per `file_id` so repeated errors against the same
/// source file don't re-clone the file contents or re-initialize the handler
/// on every call. Intended usage is: create one renderer per `rledger check`
/// invocation and call [`LedgerErrorRenderer::render`] per error.
///
/// # Lifetime / caching
///
/// The source cache is never evicted. That's fine for a short-lived CLI
/// process that renders a bounded stream of errors for a single ledger
/// tree. Long-running consumers (e.g. an LSP server that wants to reuse
/// one renderer across sessions) should instead create a fresh renderer
/// per request to avoid unbounded growth.
pub struct LedgerErrorRenderer {
    handler: GraphicalReportHandler,
    /// Per-`file_id` cache keyed by the u16 index into the source map.
    /// Stored as `Arc` so that handing the source to miette's
    /// `with_source_code()` (which takes ownership of an `impl SourceCode`)
    /// is an `Arc::clone` rather than a full-source `memcpy`.
    sources: HashMap<u16, std::sync::Arc<miette::NamedSource<String>>>,
}

impl LedgerErrorRenderer {
    /// Create a renderer with the given color preference.
    #[must_use]
    pub fn new(use_color: bool) -> Self {
        Self {
            handler: build_handler(use_color),
            sources: HashMap::new(),
        }
    }

    /// Render a single [`LedgerError`], writing the result to `writer`.
    ///
    /// When `err.source_span` and `err.file_id` both resolve to a file in
    /// `source_map`, the error is rendered with a miette source snippet
    /// (line numbers + a caret under the offending span). Otherwise a
    /// compact `file:line:col: error[CODE]: message` header is written
    /// (or `<unknown>: error[CODE]: message` if no location is available
    /// at all — which only happens for errors with no path through the
    /// pipeline, e.g. some plugin errors).
    pub fn render<W: Write>(
        &mut self,
        err: &LedgerError,
        source_map: &SourceMap,
        writer: &mut W,
    ) -> std::io::Result<()> {
        // Rich path: we have a span AND we can resolve the source file.
        if let (Some((span_start, span_end)), Some(file_id)) = (err.source_span, err.file_id)
            && let Some(source_file) = source_map.get(file_id as usize)
        {
            // Populate the cache lazily — the String clone from `Arc<str>`
            // happens at most once per file_id per renderer lifetime.
            let named_source = self.sources.entry(file_id).or_insert_with(|| {
                std::sync::Arc::new(miette::NamedSource::new(
                    source_file.path.display().to_string(),
                    source_file.source.as_ref().to_string(),
                ))
            });
            let miette_severity = match err.severity {
                rustledger_loader::ErrorSeverity::Error => Severity::Error,
                rustledger_loader::ErrorSeverity::Warning => Severity::Warning,
            };

            let diagnostic = miette::MietteDiagnostic {
                message: err.message.clone(),
                code: Some(err.code.clone()),
                severity: Some(miette_severity),
                help: None,
                url: None,
                labels: Some(vec![LabeledSpan::at(span_start..span_end, "here")]),
            };
            let report = miette::Report::new(diagnostic)
                .with_source_code(std::sync::Arc::clone(named_source));

            let mut rendered = String::new();
            self.handler
                .render_report(&mut rendered, report.as_ref())
                .map_err(|e| std::io::Error::other(e.to_string()))?;
            write!(writer, "{rendered}")?;
            return Ok(());
        }

        // Fallback: compact header when no snippet can be rendered.
        let severity_label = match err.severity {
            rustledger_loader::ErrorSeverity::Error => "error",
            rustledger_loader::ErrorSeverity::Warning => "warning",
        };
        if let Some(loc) = &err.location {
            writeln!(
                writer,
                "{}:{}:{}: {}[{}]: {}",
                loc.file.display(),
                loc.line,
                loc.column,
                severity_label,
                err.code,
                err.message,
            )?;
        } else {
            writeln!(
                writer,
                "<unknown>: {}[{}]: {}",
                severity_label, err.code, err.message,
            )?;
        }
        Ok(())
    }
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

    #[test]
    fn test_ledger_error_renderer_fallback_no_location() {
        // An error with neither `source_span`/`file_id` nor `location` must
        // still render to a single line with `<unknown>` as the path so the
        // user knows the diagnostic is tied to *something* but the origin
        // couldn't be resolved.
        let err = rustledger_loader::LedgerError::error("E0001", "something went wrong")
            .with_phase("plugin");

        let mut output = Vec::new();
        let source_map = SourceMap::default();
        let mut renderer = LedgerErrorRenderer::new(false);
        renderer.render(&err, &source_map, &mut output).unwrap();

        let output_str = String::from_utf8(output).unwrap();
        assert!(
            output_str.starts_with("<unknown>: "),
            "fallback header should start with '<unknown>: ', got: {output_str}",
        );
        assert!(
            output_str.contains("error[E0001]"),
            "fallback header should include error code tag, got: {output_str}",
        );
        assert!(
            output_str.contains("something went wrong"),
            "fallback header should include message, got: {output_str}",
        );
    }

    #[test]
    fn test_ledger_error_renderer_fallback_with_location_no_span() {
        // When a LedgerError has a `location` but no `source_span`, the
        // renderer falls back to a `file:line:col: error[CODE]: message`
        // header without a miette snippet.
        let err = rustledger_loader::LedgerError::error("E0002", "imperfect info")
            .with_location(rustledger_loader::ErrorLocation {
                file: std::path::PathBuf::from("example.beancount"),
                line: 7,
                column: 3,
            })
            .with_phase("validate");

        let mut output = Vec::new();
        let source_map = SourceMap::default();
        let mut renderer = LedgerErrorRenderer::new(false);
        renderer.render(&err, &source_map, &mut output).unwrap();

        let output_str = String::from_utf8(output).unwrap();
        assert!(
            output_str.contains("example.beancount:7:3: error[E0002]: imperfect info"),
            "expected 'file:line:col: error[CODE]: message' single-line header, got: {output_str}",
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
