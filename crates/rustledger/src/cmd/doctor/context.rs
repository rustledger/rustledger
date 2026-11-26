use anyhow::{Context, Result};
use rustledger_core::format::{FormatConfig, format_directives};
use rustledger_loader::{Loader, line_col_in};
use std::fs;
use std::io::Write;
use std::path::PathBuf;

/// Convert a byte offset to a 1-based line number.
fn byte_offset_to_line(source: &str, offset: usize) -> usize {
    line_col_in(source, offset).0
}

/// The 1-based first and last lines a directive spanning `start..end`
/// occupies. The span runs to the directive's trailing newline, which must
/// not count as the next line: counted, asking for the line after a
/// directive answered with that directive rather than the one on the line.
fn span_lines(source: &str, start: usize, end: usize) -> (usize, usize) {
    let text = source
        .as_bytes()
        .get(start..end.min(source.len()))
        .unwrap_or_default();
    let trimmed = text
        .iter()
        .rposition(|b| !b.is_ascii_whitespace())
        .unwrap_or(0);
    (
        byte_offset_to_line(source, start),
        byte_offset_to_line(source, start + trimmed),
    )
}

pub(super) fn cmd_context<W: Write>(file: &PathBuf, line: usize, writer: &mut W) -> Result<()> {
    let mut loader = Loader::new();
    let load_result = loader
        .load(file)
        .with_context(|| format!("failed to load {}", file.display()))?;

    // Find the directive at or near the specified line
    let source = fs::read_to_string(file)?;
    let lines: Vec<&str> = source.lines().collect();

    writeln!(writer, "Context at {}:{}", file.display(), line)?;
    writeln!(writer, "{}", "=".repeat(60))?;
    writeln!(writer)?;

    // Show surrounding lines
    let start = line.saturating_sub(3);
    let end = (line + 3).min(lines.len());

    for (i, src_line) in lines.iter().enumerate().skip(start).take(end - start) {
        let line_num = i + 1;
        let marker = if line_num == line { ">>>" } else { "   " };
        writeln!(writer, "{marker} {line_num:4} | {src_line}")?;
    }

    // Find which directive contains this line. Only the file's own
    // directives: file 0 is the root, and an included file's byte offsets
    // say nothing about this file's lines.
    writeln!(writer)?;
    let found = load_result
        .directives
        .iter()
        .filter(|spanned| spanned.file_id == 0)
        .map(|spanned| {
            let lines = span_lines(&source, spanned.span.start, spanned.span.end);
            (spanned, lines)
        })
        .find(|(_, (first, last))| *first <= line && line <= *last);
    match found {
        Some((spanned, (first, last))) => {
            let range = if first == last {
                format!("line {first}")
            } else {
                format!("lines {first}-{last}")
            };
            // The directive as beancount text (it was Rust's `Debug` dump).
            writeln!(writer, "Directive at this location ({range}):")?;
            write!(
                writer,
                "{}",
                format_directives([&spanned.value], &FormatConfig::default())
            )?;
        }
        None => writeln!(writer, "No directive at this location.")?,
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context_at(source: &str, line: usize) -> String {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("ledger.beancount");
        std::fs::write(&path, source).unwrap();
        let mut out = Vec::new();
        cmd_context(&path, line, &mut out).unwrap();
        String::from_utf8(out).unwrap()
    }

    const LEDGER: &str = "2024-01-01 open Assets:Bank USD\n\
                          2024-01-01 open Expenses:Food USD\n\
                          2024-01-02 * \"Lunch\"\n  \
                          Assets:Bank -5 USD\n  \
                          Expenses:Food\n";

    /// The part of the output after the source excerpt.
    fn directive_part(out: &str) -> &str {
        out.split_once("\n\n")
            .and_then(|(_, rest)| rest.split_once("\n\n"))
            .map_or("", |(_, rest)| rest)
    }

    #[test]
    fn test_cmd_context_prints_the_directive_as_beancount() {
        let out = context_at(LEDGER, 4);
        let part = directive_part(&out);
        assert!(
            part.starts_with("Directive at this location (lines 3-5):\n2024-01-02 * \"Lunch\"\n"),
            "{out}"
        );
        assert!(part.contains("Assets:Bank"), "{out}");
        // Not Rust's Debug dump.
        assert!(!out.contains("Transaction {"), "{out}");
        assert!(!out.contains("InternedStr"), "{out}");
    }

    #[test]
    fn test_cmd_context_line_after_a_directive_is_not_that_directive() {
        // Line 3 is the transaction; the `open` on line 2 ends with a newline
        // that once counted as line 3.
        let out = context_at(LEDGER, 3);
        let part = directive_part(&out);
        assert!(part.contains("(lines 3-5)"), "{out}");
        assert!(!part.contains("open"), "{out}");
    }

    #[test]
    fn test_cmd_context_single_line_directive() {
        let out = context_at(LEDGER, 2);
        let part = directive_part(&out);
        assert!(
            part.starts_with("Directive at this location (line 2):\n2024-01-01 open Expenses:Food"),
            "{out}"
        );
    }

    #[test]
    fn test_cmd_context_blank_line_has_no_directive() {
        let out = context_at(
            "2024-01-01 open Assets:Bank USD\n\n\n2024-01-02 open Assets:Cash\n",
            2,
        );
        assert!(out.contains("No directive at this location."), "{out}");
    }
}
