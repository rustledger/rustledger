//! Error reporting with beautiful diagnostics.
//!
//! Uses miette for pretty-printed error messages with source context.
//! Respects TTY detection and `NO_COLOR` environment variable.

use miette::{
    GraphicalReportHandler, GraphicalTheme, LabeledSpan, MietteError, MietteSpanContents, Severity,
    SourceCode, SourceSpan, SpanContents,
};
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

/// A named source file with an index of its line starts, so a snippet is
/// read in time proportional to the snippet rather than to the file (#2604).
///
/// miette's own `SourceCode` for text (`<[u8] as SourceCode>::read_span`)
/// counts lines from byte 0 on every call, because the span it is given is a
/// byte offset and the snippet needs line numbers. One call per rendered
/// error makes `check` O(errors x file size): a 1,000-lot ledger whose
/// accounts were opened after its transactions drew 2,666 errors and spent
/// 96% of 9.75G instructions there, which read as a booking quadratic.
///
/// The index finds the line holding the span by binary search; miette's own
/// routine then runs over a window that starts a few lines earlier, and the
/// result is rebased onto the whole file. The window starts at a line start
/// at least `context_lines_before` lines before the span, so the lines the
/// routine keeps, its columns and its end are the ones it computes from byte
/// 0. Lines are split exactly as miette splits them (`\n`, `\r\n`, or a
/// lone `\r`). `windowed_read_matches_miettes_whole_file_read` pins that.
#[derive(Debug)]
struct IndexedSource {
    name: String,
    source: String,
    /// Byte offset of the start of every line: 0, then the offset just past
    /// each line terminator.
    line_starts: Vec<usize>,
}

impl IndexedSource {
    fn new(name: String, source: String) -> Self {
        let bytes = source.as_bytes();
        let mut line_starts = vec![0];
        let mut i = 0;
        while i < bytes.len() {
            match bytes[i] {
                b'\n' => line_starts.push(i + 1),
                b'\r' => {
                    // `\r\n` is one terminator, as in miette.
                    if bytes.get(i + 1) == Some(&b'\n') {
                        i += 1;
                    }
                    line_starts.push(i + 1);
                }
                _ => {}
            }
            i += 1;
        }
        Self {
            name,
            source,
            line_starts,
        }
    }
}

impl SourceCode for IndexedSource {
    fn read_span<'a>(
        &'a self,
        span: &SourceSpan,
        context_lines_before: usize,
        context_lines_after: usize,
    ) -> Result<Box<dyn SpanContents<'a> + 'a>, MietteError> {
        // The line holding the span's first byte. A span past the end of the
        // file lands on the last line and is refused below exactly as miette
        // refuses it, since the window then runs to the end of the file.
        let span_line = self
            .line_starts
            .partition_point(|&start| start <= span.offset())
            .saturating_sub(1);
        // One line more than the context needs: harmless (the routine drops
        // it like any line before the context), and it keeps the window from
        // depending on where in its line the span starts.
        let window_line = span_line.saturating_sub(context_lines_before.saturating_add(1));
        let window_start = self.line_starts[window_line];
        let window = &self.source.as_bytes()[window_start..];
        let local = SourceSpan::new((span.offset() - window_start).into(), span.len());
        let contents = window.read_span(&local, context_lines_before, context_lines_after)?;
        Ok(Box::new(MietteSpanContents::new_named(
            self.name.clone(),
            contents.data(),
            SourceSpan::new(
                (contents.span().offset() + window_start).into(),
                contents.span().len(),
            ),
            // `window_line` terminators precede the window, and the routine
            // counts lines (and its running line count) from the window.
            contents.line() + window_line,
            contents.column(),
            contents.line_count() + window_line,
        )))
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
    let named_source = std::sync::Arc::new(IndexedSource::new(path_str, source.to_string()));

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

        let report =
            miette::Report::new(diagnostic).with_source_code(std::sync::Arc::clone(&named_source));

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
/// Builds the miette [`GraphicalReportHandler`] once and caches an indexed
/// source per `file_id` so repeated errors against the same
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
    sources: HashMap<u16, std::sync::Arc<IndexedSource>>,
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
                std::sync::Arc::new(IndexedSource::new(
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

    /// Every field of `IndexedSource`'s windowed read must equal miette's
    /// whole-file read, for every span and context size, over sources mixing
    /// all three line terminators (#2604). Byte-identical `check` output
    /// rests on this.
    #[test]
    fn windowed_read_matches_miettes_whole_file_read() {
        // xorshift: deterministic, so a failure reproduces.
        let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut sources: Vec<String> = [
            "",
            "a",
            "\n",
            "\r",
            "\r\n",
            "\n\n\n",
            "\r\r\n\n\r",
            "ab\ncd\r\nef\rgh",
            "2024-01-01 open Assets:Cash\n\n2024-01-02 * \"x\"\n  Assets:Cash  1 USD\n",
        ]
        .iter()
        .map(|s| (*s).to_string())
        .collect();
        for _ in 0..300 {
            let len = (next() % 40) as usize;
            sources.push(
                (0..len)
                    .map(|_| ['a', 'b', ' ', '\n', '\r'][(next() % 5) as usize])
                    .collect(),
            );
        }

        let mut compared = 0usize;
        for source in &sources {
            let indexed = IndexedSource::new("f.beancount".to_string(), source.clone());
            let whole = miette::NamedSource::new("f.beancount", source.clone());
            // Every span a ledger error can carry starts inside the file (or
            // at its end); a length past the end is miette's `OutOfBounds`,
            // which both must report. A START past the end panics inside
            // miette itself, so it is not compared.
            for offset in 0..=source.len() {
                for len in 0..4 {
                    for context in 0..4 {
                        let span = SourceSpan::new(offset.into(), len);
                        let at = format!("{source:?} span {offset}+{len} context {context}");
                        let read = |src: &dyn SourceCode| {
                            src.read_span(&span, context, context).map(|c| {
                                (
                                    c.data().to_vec(),
                                    *c.span(),
                                    c.line(),
                                    c.column(),
                                    c.line_count(),
                                    c.name().map(str::to_string),
                                )
                            })
                        };
                        match (read(&indexed), read(&whole)) {
                            (Ok(got), Ok(want)) => assert_eq!(got, want, "{at}"),
                            (Err(_), Err(_)) => {}
                            (got, want) => {
                                panic!("{at}: indexed ok={} whole ok={}", got.is_ok(), want.is_ok())
                            }
                        }
                        compared += 1;
                    }
                }
            }
        }
        assert!(compared > 50_000, "compared only {compared} reads");
    }

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
