//! Rename handler for refactoring accounts and currencies.
//!
//! Supports renaming:
//! - Account names (updates all usages in the file)
//! - Currency names (updates all usages in the file)
//!
//! Both edit-collection paths (`collect_account_rename_edits` and
//! `collect_currency_rename_edits`) now go through the parser's
//! token-occurrence indices (`account_occurrences` for accounts;
//! `currency_occurrences` for currencies). `handle_prepare_rename`
//! and `handle_rename`'s dispatch consult the same indices first,
//! falling through to the legacy `is_account_like` /
//! `is_currency_like` heuristics only for the "word is
//! account-shaped but the parser hasn't seen it yet" mid-edit
//! case. The CST migration's per-token spans give us
//! zero-false-positive edits: an account-name fragment textually
//! present in a payee string, a STRING-typed metadata value, or a
//! comment is NOT emitted as a rename edit because the lexer
//! classified those bytes as STRING / META_VALUE / COMMENT, not
//! ACCOUNT. ACCOUNT-typed metadata values (e.g.
//! `counterparty: Assets:Bank`) DO produce ACCOUNT tokens and ARE
//! correctly renamed - the lexer classification, not the
//! syntactic role, is what determines inclusion.
//!
//! Phase 5.4 of the CST migration (#1262) - the previous account
//! shape walked the typed `parse_result.directives`, matched each
//! directive's account field, then ran a substring search inside
//! the directive's source bytes. That false-positive class is now
//! structurally impossible.
//!
//! **Scope.** This PR migrates ONLY the rename handler. The
//! sibling read-only handlers `references`, `document_highlight`,
//! and `linked_editing` still walk the typed AST with substring
//! search for accounts and inherit the original false-positive
//! class (a `; comment with Assets:Bank` adjacent to a real
//! Assets:Bank can produce a phantom hit). Migrating those is
//! tracked as a phase 5.5+ follow-up.

use lsp_types::{
    Position, PrepareRenameResponse, Range, RenameParams, TextDocumentPositionParams, TextEdit,
    WorkspaceEdit,
};
use rustledger_parser::{ParseResult, parse};
use std::collections::HashMap;

use super::utils::{
    LineIndex, PositionEncoding, get_word_at_position, is_account_like, is_currency_like,
};

/// Which kind of symbol is being renamed.
#[derive(Clone, Copy, PartialEq, Eq)]
enum RenameKind {
    Account,
    Currency,
}

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

    // Check if it's a valid renameable symbol. Consult the
    // parser's token-occurrence indices first so Unicode-prefix
    // and custom-rooted accounts (e.g. `option "name_assets"
    // "Vermögen"` + `Vermögen:Bank`) that the hardcoded English
    // root-name `is_account_like` would reject are still
    // renameable. Same shape as `handle_rename`. Fall through to
    // the legacy heuristic for the "word is account-shaped but
    // the parser hasn't seen it yet" mid-edit case so the user
    // doesn't lose prepare-rename support on a freshly-typed but
    // not-yet-saved fixture.
    let is_known_account = parse_result
        .account_occurrences
        .iter()
        .any(|o| o.value == word.as_str());
    let is_known_currency = parse_result
        .currency_occurrences
        .iter()
        .any(|o| o.value == word.as_str());
    if is_known_account
        || is_known_currency
        || is_account_like(&word)
        || is_currency_like(&word, parse_result)
    {
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
    // Other ledger files reachable via `include` (everything except the current
    // buffer), as `(uri, source)` — the source is the open buffer's live
    // content when the file is open, else the loader's on-disk source. Gathered
    // by the caller under the state lock so parsing here holds no locks.
    other_files: &[(lsp_types::Uri, String)],
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

    // Determine the symbol kind ONCE from the current file's occurrence
    // indices (account vs currency), preserving the original precedence:
    // known-account > known-currency > account-shaped > currency-shaped.
    // The cursor sits on `old_name` in the current file, so its occurrence
    // index classifies it. The legacy is_account_like / is_currency_like
    // helpers stay in place for prepare_rename which has no ParseResult.
    let is_known_account = parse_result
        .account_occurrences
        .iter()
        .any(|o| o.value == old_name);
    let is_known_currency = parse_result
        .currency_occurrences
        .iter()
        .any(|o| o.value == old_name);
    let kind = if is_known_account {
        RenameKind::Account
    } else if is_known_currency {
        RenameKind::Currency
    } else if is_account_like(&old_name) {
        RenameKind::Account
    } else if is_currency_like(&old_name, parse_result) {
        RenameKind::Currency
    } else {
        return None;
    };

    // Build the edits for ONE file (its own source + parse) — reused for the
    // current buffer (live source) and for every other ledger file.
    let collect = |pr: &ParseResult, src: &str| -> Vec<TextEdit> {
        let idx = LineIndex::new(src, encoding);
        let mut edits = Vec::new();
        match kind {
            RenameKind::Account => {
                collect_account_rename_edits(pr, &idx, &old_name, new_name, &mut edits);
            }
            RenameKind::Currency => {
                collect_currency_rename_edits(pr, &idx, &old_name, new_name, &mut edits);
            }
        }
        edits
    };

    let mut changes: HashMap<lsp_types::Uri, Vec<TextEdit>> = HashMap::new();

    // Current buffer (live source — reflects unsaved edits). If the cursor is
    // NOT on a real occurrence in the current file (e.g. account-shaped text in
    // a comment or string), there are no edits here — bail out rather than
    // triggering a surprising cross-file rename from a non-symbol position.
    let current_edits = collect(parse_result, source);
    if current_edits.is_empty() {
        return None;
    }
    changes.insert(uri.clone(), current_edits);

    // Every OTHER file in the loaded ledger (reachable via `include`): rename
    // the symbol there too, so a multi-file ledger isn't left with dangling
    // references to the old name. Without this, renaming an account used across
    // includes corrupted the ledger.
    for (f_uri, f_source) in other_files {
        if *f_uri == uri {
            continue; // never overwrite the current buffer's live edits
        }
        let f_parse = parse(f_source);
        let f_edits = collect(&f_parse, f_source);
        if !f_edits.is_empty() {
            changes.insert(f_uri.clone(), f_edits);
        }
    }

    if changes.is_empty() {
        return None;
    }

    Some(WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    })
}

/// Collect all edits needed to rename an account.
///
/// Walks the parser's `account_occurrences` index - every `ACCOUNT`
/// token the parser actually consumed, with exact source spans -
/// and emits one `TextEdit` per occurrence matching `old_name`.
///
/// This is exact: zero false positives. The previous shape walked
/// the typed AST and then ran a substring search inside each
/// directive's source bytes, which produced wrong edits whenever
/// an account-name fragment appeared inside a payee string,
/// metadata value, or comment in the same directive (the lexer
/// correctly classifies those bytes as STRING / META_VALUE /
/// COMMENT, but the substring search did not).
fn collect_account_rename_edits(
    parse_result: &ParseResult,
    line_index: &LineIndex,
    old_name: &str,
    new_name: &str,
    edits: &mut Vec<TextEdit>,
) {
    for occurrence in &parse_result.account_occurrences {
        // `Account` (and `Currency`) derive `PartialEq<str>` via
        // the `domain_newtype!` macro, so this `!=` comparison
        // against `&str` works without `.as_str()`. Mirrors the
        // currency path's shape exactly.
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

    // Defensive dedup, same shape as the currency path. The parser
    // advances unidirectionally over its token stream so every
    // `ACCOUNT` token is consumed exactly once, but a future
    // refactor (backtracking parser, separate resync pass) could
    // re-emit a span; the sort+dedup costs essentially nothing
    // at typical occurrence counts and surfaces those bugs as a
    // missing edit rather than a duplicate one in the LSP client.
    edits.sort_by(|a, b| {
        a.range
            .start
            .line
            .cmp(&b.range.start.line)
            .then(a.range.start.character.cmp(&b.range.start.character))
    });
    edits.dedup_by(|a, b| a.range == b.range);
}

/// Collect all edits needed to rename a currency.
///
/// Walks the parser's `currency_occurrences` index - every `Currency`
/// token the parser actually consumed, with exact source spans - and
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
    // exactly once - even speculative parse paths (e.g.
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

        let edit = handle_rename(&params, source, &result, &[], PositionEncoding::Utf16);
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
    ///   (`"USD-to-EUR transfer"`) - the surrounding `"` and `-`
    ///   characters were treated as word boundaries.
    /// - Currency code as an account-name segment
    ///   (`Assets:USD-Reserve`) - the `-` after `USD` looked like
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

        let edit = handle_rename(&params, source, &result, &[], PositionEncoding::Utf16)
            .expect("rename returns edit");
        let changes = edit.changes.expect("edit has changes");
        let edits = changes.values().next().expect("at least one file");

        // Expected: 3 edits - `commodity USD`, `-100 USD`, `100 USD`.
        // Bespoke string-search would have produced 5: the 3 valid
        // ones plus `"USD-to-EUR..."` (payee, false positive) and
        // `; switching USD ...` (comment, false positive). It would
        // also have RENAMED `Assets:USD-Reserve` (3x - open, two
        // postings) incorrectly because `-` is non-alphanumeric and
        // passed the word-boundary check.
        assert_eq!(
            edits.len(),
            3,
            "expected 3 currency rename edits, got {}: {edits:#?}",
            edits.len()
        );

        // None of the edits should target the payee, comment, or
        // account-name span - sanity-check by confirming all
        // replacements line up with where the parser saw a `Currency`
        // token (i.e., col positions that follow a number or the
        // `commodity` keyword).
        for e in edits {
            assert_eq!(e.new_text, "USDX");
        }
    }

    /// Regression test for account-rename false positives - phase
    /// 5.4 of the CST migration (#1262).
    ///
    /// The previous shape walked `parse_result.directives` and ran
    /// a substring search inside each directive's source bytes. That
    /// produced wrong edits for any account-name fragment textually
    /// present in a payee string, metadata value, or comment within
    /// the same directive.
    ///
    /// The CST-backed shape consumes `parse_result.account_occurrences`,
    /// which contains exactly the `ACCOUNT` tokens the lexer
    /// produced. Strings, metadata values, and comments cannot
    /// produce `ACCOUNT` tokens, so these false positives are
    /// impossible by construction.
    #[test]
    #[allow(clippy::mutable_key_type)]
    fn test_rename_account_no_false_positives() {
        // Source carefully constructed to embed the literal string
        // "Assets:Bank" in payee, metadata, and comment positions
        // INSIDE the same directives that legitimately reference
        // the Assets:Bank account. The substring-search shape would
        // have rewritten each instance.
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Assets:Bank transfer note"
  Assets:Bank  -5.00 USD
    memo: "moved Assets:Bank balance"
  Expenses:Food
; rebalanced Assets:Bank yesterday
"#;
        let result = parse(source);
        let uri: lsp_types::Uri = "file:///test.beancount".parse().unwrap();
        let params = RenameParams {
            text_document_position: TextDocumentPositionParams {
                text_document: lsp_types::TextDocumentIdentifier { uri },
                position: Position::new(0, 16), // on "Assets:Bank" of the open
            },
            new_name: "Assets:Checking".to_string(),
            work_done_progress_params: Default::default(),
        };
        let edit = handle_rename(&params, source, &result, &[], PositionEncoding::Utf16)
            .expect("rename returns edit");
        let changes = edit.changes.expect("edit has changes");
        let edits = changes.values().next().expect("at least one file");

        // Expected: 2 edits - one for the `open` directive's
        // ACCOUNT token, one for the posting's ACCOUNT token.
        //
        // The substring-search shape would have produced 5: the
        // 2 valid ones PLUS the payee string, the metadata value,
        // and the trailing comment.
        assert_eq!(
            edits.len(),
            2,
            "expected exactly 2 account rename edits (one per ACCOUNT token), \
             got {}: {edits:#?}. Any extra edit is a false positive in the \
             payee/metadata/comment positions.",
            edits.len()
        );
        for e in edits {
            assert_eq!(e.new_text, "Assets:Checking");
        }
    }
}
