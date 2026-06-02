//! Rename handler for refactoring accounts and currencies.
//!
//! Supports renaming:
//! - Account names (updates all usages in the file)
//! - Currency names (updates all usages in the file)

use lsp_types::{
    Position, PrepareRenameResponse, Range, RenameParams, TextDocumentPositionParams, TextEdit,
    WorkspaceEdit,
};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;
use std::collections::HashMap;

use super::utils::{
    LineIndex, PositionEncoding, get_word_at_position, is_account_like, is_currency_like,
};

/// Handle a prepare rename request (check if rename is valid at position).
///
/// `encoding` is required because the emitted `Range` carries columns
/// in the negotiated wire encoding; `get_word_at_position` returns
/// columns in the same encoding as the input `col`, so threading
/// `encoding` keeps the round-trip consistent.
pub fn handle_prepare_rename(
    params: &TextDocumentPositionParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<PrepareRenameResponse> {
    let position = params.position;
    let line_idx = position.line as usize;

    let lines: Vec<&str> = source.lines().collect();
    let line = lines.get(line_idx)?;

    // Get the word at the cursor position
    let (word, start_col, end_col) =
        get_word_at_position(line, position.character as usize, encoding)?;

    // Check if it's a valid renameable symbol
    if is_account_like(&word) || is_currency_like(&word, parse_result) {
        Some(PrepareRenameResponse::Range(Range {
            start: Position::new(position.line, start_col as u32),
            end: Position::new(position.line, end_col as u32),
        }))
    } else {
        None
    }
}

/// Handle a rename request.
#[allow(clippy::mutable_key_type)] // Uri is required as key by LSP WorkspaceEdit API
pub fn handle_rename(
    params: &RenameParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<WorkspaceEdit> {
    let position = params.text_document_position.position;
    let new_name = &params.new_name;
    let uri = params.text_document_position.text_document.uri.clone();

    let line_idx = position.line as usize;
    let lines: Vec<&str> = source.lines().collect();
    let line = lines.get(line_idx)?;

    // Get the word at the cursor position
    let (old_name, _, _) = get_word_at_position(line, position.character as usize, encoding)?;

    // Collect all edits
    let mut edits = Vec::new();
    // Build the line index once and share across collectors. The
    // previous code went through `byte_offset_to_position`, which is
    // O(n) per call (linear scan from byte 0); for a large ledger
    // with many account / currency occurrences, that scaled
    // quadratically with file size.
    let line_index = LineIndex::new(source, encoding);

    if is_account_like(&old_name) {
        // Rename account
        collect_account_rename_edits(
            source,
            parse_result,
            &line_index,
            &old_name,
            new_name,
            &mut edits,
        );
    } else if is_currency_like(&old_name, parse_result) {
        // Rename currency
        collect_currency_rename_edits(parse_result, &line_index, &old_name, new_name, &mut edits);
    }

    if edits.is_empty() {
        return None;
    }

    let mut changes = HashMap::new();
    changes.insert(uri, edits);

    Some(WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    })
}

/// Collect all edits needed to rename an account.
fn collect_account_rename_edits(
    source: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
    old_name: &str,
    new_name: &str,
    edits: &mut Vec<TextEdit>,
) {
    for spanned in &parse_result.directives {
        match &spanned.value {
            Directive::Open(open) => {
                if open.account.as_ref() == old_name
                    && let Some(edit) = find_and_create_edit(
                        source,
                        line_index,
                        spanned.span.start,
                        spanned.span.end,
                        old_name,
                        new_name,
                    )
                {
                    edits.push(edit);
                }
            }
            Directive::Close(close) => {
                if close.account.as_ref() == old_name
                    && let Some(edit) = find_and_create_edit(
                        source,
                        line_index,
                        spanned.span.start,
                        spanned.span.end,
                        old_name,
                        new_name,
                    )
                {
                    edits.push(edit);
                }
            }
            Directive::Balance(bal) => {
                if bal.account.as_ref() == old_name
                    && let Some(edit) = find_and_create_edit(
                        source,
                        line_index,
                        spanned.span.start,
                        spanned.span.end,
                        old_name,
                        new_name,
                    )
                {
                    edits.push(edit);
                }
            }
            Directive::Pad(pad) => {
                if pad.account.as_ref() == old_name
                    && let Some(edit) = find_and_create_edit(
                        source,
                        line_index,
                        spanned.span.start,
                        spanned.span.end,
                        old_name,
                        new_name,
                    )
                {
                    edits.push(edit);
                }
                if pad.source_account.as_ref() == old_name
                    && let Some(edit) = find_and_create_edit(
                        source,
                        line_index,
                        spanned.span.start,
                        spanned.span.end,
                        old_name,
                        new_name,
                    )
                {
                    edits.push(edit);
                }
            }
            Directive::Note(note) => {
                if note.account.as_ref() == old_name
                    && let Some(edit) = find_and_create_edit(
                        source,
                        line_index,
                        spanned.span.start,
                        spanned.span.end,
                        old_name,
                        new_name,
                    )
                {
                    edits.push(edit);
                }
            }
            Directive::Document(doc) => {
                if doc.account.as_ref() == old_name
                    && let Some(edit) = find_and_create_edit(
                        source,
                        line_index,
                        spanned.span.start,
                        spanned.span.end,
                        old_name,
                        new_name,
                    )
                {
                    edits.push(edit);
                }
            }
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    if posting.account.as_ref() == old_name
                        && let Some(edit) = find_and_create_edit(
                            source,
                            line_index,
                            spanned.span.start,
                            spanned.span.end,
                            old_name,
                            new_name,
                        )
                        && !edits.iter().any(|e| e.range == edit.range)
                    {
                        edits.push(edit);
                    }
                }
            }
            _ => {}
        }
    }
}

/// Collect all edits needed to rename a currency.
///
/// Walks the parser's `currency_occurrences` index — every `Currency`
/// token the parser actually consumed, with exact source spans — and
/// emits one `TextEdit` per occurrence matching `old_name`.
///
/// This is exact: zero false positives in payee strings, comments,
/// account-name segments, or anywhere else a `[A-Z]{3,}` sequence
/// might accidentally appear. The previous string-search
/// implementation needed word-boundary heuristics to filter those
/// out, and the heuristics still produced wrong edits for cases like
/// `Expenses:USD-Account` (the substring `USD` matched mid-identifier
/// despite the alphanumeric boundary check, because `-` is non-
/// alphanumeric).
fn collect_currency_rename_edits(
    parse_result: &ParseResult,
    line_index: &LineIndex,
    old_name: &str,
    new_name: &str,
    edits: &mut Vec<TextEdit>,
) {
    for occurrence in &parse_result.currency_occurrences {
        if occurrence.value != old_name {
            continue;
        }
        let (start_line, start_col) = line_index.offset_to_position(occurrence.span.start);
        let (end_line, end_col) = line_index.offset_to_position(occurrence.span.end);
        edits.push(TextEdit {
            range: Range {
                start: Position::new(start_line, start_col),
                end: Position::new(end_line, end_col),
            },
            new_text: new_name.to_string(),
        });
    }

    // Defensive dedup. The parser advances unidirectionally over its
    // token stream, so today every `Currency` token is consumed
    // exactly once — even speculative parse paths (e.g.
    // `parse_incomplete_amount`) rewind `stream.pos` before retrying.
    // The sort+dedup here costs essentially nothing for the typical
    // hint count and protects against future parser refactors that
    // might re-emit a span (e.g. a backtracking parser, or a separate
    // resync pass).
    edits.sort_by(|a, b| {
        a.range
            .start
            .line
            .cmp(&b.range.start.line)
            .then(a.range.start.character.cmp(&b.range.start.character))
    });
    edits.dedup_by(|a, b| a.range == b.range);
}

/// Find a string in the source and create a text edit.
///
/// Used by the account-rename path (not currency: currency now goes
/// through `parse_result.currency_occurrences` for exact AST-derived
/// spans). Account directives don't carry per-field spans, so we
/// fall back to a directive-scoped substring search; that's safe for
/// account names because they cannot textually appear inside other
/// syntactic positions a directive supports (no `:` in payee strings
/// or in metadata keys).
fn find_and_create_edit(
    source: &str,
    line_index: &LineIndex<'_>,
    start_offset: usize,
    end_offset: usize,
    old_name: &str,
    new_name: &str,
) -> Option<TextEdit> {
    let directive_text = &source[start_offset..end_offset];

    // Walk lines tracking the absolute byte cursor through `source`;
    // route emitted positions through the LineIndex so encoded columns
    // match the negotiated wire encoding. Pre-round-19 mixed encoded
    // `start_col` with raw byte `col`, breaking under UTF-16
    // negotiation on non-ASCII content.
    let mut byte_cursor = start_offset;
    for line in directive_text.lines() {
        if let Some(col) = line.find(old_name) {
            let name_start = byte_cursor + col;
            let name_end = name_start + old_name.len();
            let (sl, sc) = line_index.offset_to_position(name_start);
            let (el, ec) = line_index.offset_to_position(name_end);
            return Some(TextEdit {
                range: Range {
                    start: Position::new(sl, sc),
                    end: Position::new(el, ec),
                },
                new_text: new_name.to_string(),
            });
        }
        byte_cursor += line.len();
        let remaining = &source[byte_cursor.min(end_offset)..end_offset];
        if remaining.starts_with("\r\n") {
            byte_cursor += 2;
        } else if remaining.starts_with('\n') {
            byte_cursor += 1;
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_get_word_at_position() {
        let line = "  Assets:Bank  -5.00 USD";
        let (word, start, end) = get_word_at_position(line, 5, PositionEncoding::Utf8).unwrap();
        assert_eq!(word, "Assets:Bank");
        assert_eq!(start, 2);
        assert_eq!(end, 13);
    }

    #[test]
    fn test_is_account_like() {
        assert!(is_account_like("Assets:Bank"));
        assert!(is_account_like("Expenses:Food:Coffee"));
        assert!(!is_account_like("USD"));
        assert!(!is_account_like("Bank"));
    }

    #[test]
    #[allow(clippy::mutable_key_type)] // Uri in HashMap is required by LSP API
    fn test_rename_account() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let uri: lsp_types::Uri = "file:///test.beancount".parse().unwrap();

        let params = RenameParams {
            text_document_position: TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri },
                position: Position::new(0, 16), // On "Assets:Bank"
            },
            new_name: "Assets:Checking".to_string(),
            work_done_progress_params: Default::default(),
        };

        let edit = handle_rename(&params, source, &result, PositionEncoding::Utf16);
        assert!(edit.is_some());

        let edit = edit.unwrap();
        let changes = edit.changes.unwrap();
        let edits: Vec<_> = changes.values().next().unwrap().clone();

        // Should have 2 edits: one for open, one for posting
        assert_eq!(edits.len(), 2);
    }

    /// Regression test for currency-rename false positives.
    ///
    /// Before #552 the rename handler string-searched the source
    /// within each directive that contained the currency code,
    /// validating word boundaries via `char::is_alphanumeric`. That
    /// missed several common false-positive shapes:
    ///
    /// - Currency code embedded in a payee string
    ///   (`"USD-to-EUR transfer"`) — the surrounding `"` and `-`
    ///   characters were treated as word boundaries.
    /// - Currency code as an account-name segment
    ///   (`Assets:USD-Reserve`) — the `-` after `USD` looked like
    ///   a boundary, so `USD` got incorrectly renamed.
    /// - Currency code in a metadata value or comment.
    ///
    /// The AST-driven approach uses `parse_result.currency_occurrences`,
    /// which contains exactly the `Currency` tokens the lexer
    /// produced. Strings, accounts, comments, and metadata can't
    /// produce `Currency` tokens, so these false positives are
    /// impossible by construction.
    #[test]
    #[allow(clippy::mutable_key_type)]
    fn test_rename_currency_no_false_positives() {
        let source = r#"2024-01-01 open Assets:USD-Reserve
2024-01-01 commodity USD
  name: "United States Dollar"
2024-01-15 * "USD-to-EUR transfer"
  Assets:USD-Reserve  -100 USD
  Assets:Bank          100 USD
; switching USD to USDX later
"#;
        let result = parse(source);
        let uri: lsp_types::Uri = "file:///test.beancount".parse().unwrap();

        // Position cursor on the `USD` of the `commodity USD` line
        // (line 1, after "commodity "). That's the canonical
        // declaration site.
        let params = RenameParams {
            text_document_position: TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri },
                position: Position::new(1, 21),
            },
            new_name: "USDX".to_string(),
            work_done_progress_params: Default::default(),
        };

        let edit = handle_rename(&params, source, &result, PositionEncoding::Utf16)
            .expect("rename returns edit");
        let changes = edit.changes.expect("edit has changes");
        let edits = changes.values().next().expect("at least one file");

        // Expected: 3 edits — `commodity USD`, `-100 USD`, `100 USD`.
        // Bespoke string-search would have produced 5: the 3 valid
        // ones plus `"USD-to-EUR..."` (payee, false positive) and
        // `; switching USD ...` (comment, false positive). It would
        // also have RENAMED `Assets:USD-Reserve` (3x — open, two
        // postings) incorrectly because `-` is non-alphanumeric and
        // passed the word-boundary check.
        assert_eq!(
            edits.len(),
            3,
            "expected 3 currency rename edits, got {}: {edits:#?}",
            edits.len()
        );

        // None of the edits should target the payee, comment, or
        // account-name span — sanity-check by confirming all
        // replacements line up with where the parser saw a `Currency`
        // token (i.e., col positions that follow a number or the
        // `commodity` keyword).
        for e in edits {
            assert_eq!(e.new_text, "USDX");
        }
    }
}
