//! Document formatting handler for Beancount files.
//!
//! The handler delegates to [`rustledger_parser::format_source`], the same
//! whole-file formatter the `rledger format` CLI uses. Routing both through
//! one function gives parity-by-construction: every editor save produces
//! byte-identical output to the CLI, so neither side can drift.
//!
//! Edits are emitted as a single minimal contiguous diff (longest common
//! prefix and suffix at line granularity are stripped) so the editor's
//! cursor and undo stack stay anchored to the unchanged regions.

use lsp_types::{DocumentFormattingParams, Position, Range, TextEdit};
use rustledger_core::FormatConfig;
use rustledger_parser::{ParseResult, format_source};

use super::utils::document_format_config;

/// Handle a `textDocument/formatting` request.
///
/// Thin LSP-shaped wrapper around [`format_document`].
pub fn handle_formatting(
    params: &DocumentFormattingParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<TextEdit>> {
    let config = document_format_config(Some(&params.options));
    format_document(source, parse_result, &config)
}

/// Compute the document-format edits for a parsed source with a resolved
/// [`FormatConfig`].
///
/// Returns `None` when the source has parse errors (we don't reformat
/// half-broken files — that would risk dropping unparsable content) or when
/// the source already matches the canonical form.
pub fn format_document(
    source: &str,
    parse_result: &ParseResult,
    config: &FormatConfig,
) -> Option<Vec<TextEdit>> {
    // Gate on a clean parse: format_source ignores anything the parser
    // couldn't recognize, so reformatting a file with errors would silently
    // drop those bytes.
    if !parse_result.errors.is_empty() {
        return None;
    }

    let formatted = format_source(source, parse_result, config);
    if formatted == source {
        return None;
    }

    Some(vec![minimal_diff_edit(source, &formatted)])
}

/// Produce a single contiguous `TextEdit` covering only the lines that
/// actually changed.
///
/// Splits both texts on `\n` (preserving empty trailing chunks so trailing
/// newlines are represented as a final empty segment), strips the longest
/// common prefix and suffix, and emits one edit covering the original
/// middle. When source and formatted differ everywhere, this degrades to a
/// whole-document replacement.
fn minimal_diff_edit(source: &str, formatted: &str) -> TextEdit {
    let orig: Vec<&str> = source.split('\n').collect();
    let new: Vec<&str> = formatted.split('\n').collect();

    let mut prefix = 0;
    while prefix < orig.len() && prefix < new.len() && orig[prefix] == new[prefix] {
        prefix += 1;
    }

    // Common suffix is counted excluding the prefix region on both sides so
    // an identical document can't be double-counted.
    let mut suffix = 0;
    while suffix < orig.len() - prefix
        && suffix < new.len() - prefix
        && orig[orig.len() - 1 - suffix] == new[new.len() - 1 - suffix]
    {
        suffix += 1;
    }

    let orig_mid_start = prefix;
    let orig_mid_end = orig.len() - suffix;
    let new_mid_start = prefix;
    let new_mid_end = new.len() - suffix;

    // Range: from start of first differing line to start of first
    // unchanged-suffix line. `(line, 0)` to `(line + n, 0)` covers exactly
    // those n lines including their trailing newlines, which is what we
    // want when n new lines (joined with '\n', terminated by '\n') replace
    // them. When orig_mid_start == orig_mid_end the range is empty (pure
    // insertion); when new_mid_start == new_mid_end new_text is "" (pure
    // deletion).
    let new_text = if new_mid_end > new_mid_start {
        let mut s = new[new_mid_start..new_mid_end].join("\n");
        // Only append the terminating newline when there's an unchanged
        // suffix to follow — otherwise the middle reaches end-of-file and
        // any trailing newline is already part of the last segment.
        if suffix > 0 {
            s.push('\n');
        }
        s
    } else {
        String::new()
    };

    let start = Position::new(orig_mid_start as u32, 0);
    let end_line = orig_mid_end as u32;
    let end_char = if suffix > 0 {
        0
    } else {
        // No unchanged suffix: the edit extends to the very end of the
        // file. The end position must point past the last character of
        // the final original segment.
        orig.last().map_or(0, |s| s.len()) as u32
    };
    let end = Position::new(
        if suffix > 0 {
            end_line
        } else {
            // When the middle reaches EOF, end_line is orig.len() but
            // the last addressable line is orig.len() - 1.
            orig.len().saturating_sub(1) as u32
        },
        end_char,
    );

    TextEdit {
        range: Range { start, end },
        new_text,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    /// Apply `edits` to `source` and return the result. Edits are
    /// non-overlapping and sorted in reverse so applying them in order is
    /// safe; for these tests there is always a single edit, so the loop
    /// reduces to one application but the structure is robust if that
    /// changes.
    fn apply(source: &str, edits: &[TextEdit]) -> String {
        let mut sorted: Vec<&TextEdit> = edits.iter().collect();
        sorted.sort_by(|a, b| {
            b.range
                .start
                .line
                .cmp(&a.range.start.line)
                .then(b.range.start.character.cmp(&a.range.start.character))
        });
        let mut out = source.to_string();
        for edit in sorted {
            let lines: Vec<&str> = out.split_inclusive('\n').collect();
            let start = lines
                .iter()
                .take(edit.range.start.line as usize)
                .map(|l| l.len())
                .sum::<usize>()
                + edit.range.start.character as usize;
            let end = lines
                .iter()
                .take(edit.range.end.line as usize)
                .map(|l| l.len())
                .sum::<usize>()
                + edit.range.end.character as usize;
            out.replace_range(start..end, &edit.new_text);
        }
        out
    }

    fn params() -> DocumentFormattingParams {
        DocumentFormattingParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            options: Default::default(),
            work_done_progress_params: Default::default(),
        }
    }

    #[test]
    fn removes_trailing_whitespace() {
        let source = "2024-01-01 open Assets:Bank USD   \n";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result).expect("expected edits");
        let after = apply(source, &edits);
        assert_eq!(after, "2024-01-01 open Assets:Bank USD\n");
    }

    #[test]
    fn converts_tabs_to_spaces() {
        let source = "2024-01-15 * \"Test\"\n\tAssets:Bank  -5.00 USD\n\tExpenses:Food\n";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result).expect("expected edits");
        let after = apply(source, &edits);
        assert!(
            !after.contains('\t'),
            "tabs should be replaced with spaces, got {after:?}"
        );
    }

    /// Regression test for issue #1142.
    ///
    /// When a transaction has posting-level metadata interleaved between
    /// postings, an earlier per-line formatter computed each posting's line
    /// as `txn_start_line + 1 + posting_idx`, producing TextEdits that
    /// overwrote the metadata lines. This test pins that, after applying
    /// the emitted edits, the metadata lines remain byte-identical to the
    /// originals.
    #[test]
    fn preserves_interleaved_metadata_1142() {
        let source = "\
2024-01-15 * \"Test\"
  Assets:Bank  -50.00 USD
    effective_date: 2024-01-20
  Expenses:Food  50.00 USD
    effective_date: 2024-01-21
";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );

        let edits = handle_formatting(&params(), source, &result).unwrap_or_default();
        let after = apply(source, &edits);

        // The metadata lines must survive byte-for-byte.
        let after_lines: Vec<&str> = after.lines().collect();
        assert_eq!(
            after_lines.get(2).copied(),
            Some("    effective_date: 2024-01-20"),
            "first effective_date line was clobbered; got {:?}",
            after_lines.get(2)
        );
        assert_eq!(
            after_lines.get(4).copied(),
            Some("    effective_date: 2024-01-21"),
            "second effective_date line was clobbered; got {:?}",
            after_lines.get(4)
        );
    }

    /// Regression test: the formatter must preserve a same-line trailing
    /// comment on a posting.
    #[test]
    fn preserves_trailing_comment_on_posting() {
        let source = "\
2024-01-15 * \"Coffee\"
    Assets:Bank  -5.00 USD ; my comment
    Expenses:Food
";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );

        let edits = handle_formatting(&params(), source, &result).unwrap_or_default();
        let after = apply(source, &edits);
        assert!(
            after.contains("; my comment"),
            "trailing comment dropped after formatting; got {after:?}"
        );
    }

    /// Parity-by-construction: the LSP-applied result must be byte-equal
    /// to what `rledger format` (via `format_source`) writes.
    #[test]
    fn lsp_matches_cli_format_source() {
        let source = "\
2024-01-01 open Assets:Bank
2024-01-15 * \"Coffee\"
    Assets:Bank  -5.00 USD
  Expenses:Food
";
        let result = parse(source);
        let edits = handle_formatting(&params(), source, &result).unwrap_or_default();
        let after = apply(source, &edits);
        let cli = format_source(source, &result, &FormatConfig::default());
        assert_eq!(after, cli);
    }

    #[test]
    fn parse_errors_skip_formatting() {
        // A stray invalid token should leave the document untouched.
        let source = "2024-01-01 not_a_directive\n";
        let result = parse(source);
        assert!(!result.errors.is_empty());
        assert!(handle_formatting(&params(), source, &result).is_none());
    }
}
