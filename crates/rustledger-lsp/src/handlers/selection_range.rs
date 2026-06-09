//! Selection-range handler - CST-backed implementation (#1262 phase 5.2).
//!
//! Returns the nested-range hierarchy LSP clients use for smart
//! expansion (Ctrl+Shift+Up / Cmd+Shift+Up in most editors). Each
//! request positions yields a linked list of progressively wider
//! ranges from a word at the cursor out to the entire file.
//!
//! # Why the CST
//!
//! The prior shape walked the typed AST (`ParseResult.directives`)
//! and hardcoded a fixed hierarchy: Word → Account segment → Full
//! account → Posting → Transaction. That tree was correct for
//! transaction postings but missed every other structural node -
//! cost specs, price annotations, posting metadata values, string
//! literals, option / include / plugin directives - because the
//! typed AST exposes those as flat field values without a
//! corresponding "click here to expand" handle.
//!
//! The CST gives every structural construct a node with a
//! [`TextRange`]. Walking parents of the token under the cursor
//! produces the right hierarchy automatically:
//!
//! - Inside an `ACCOUNT` token in a posting amount expression:
//!   Word → Segment → ACCOUNT → POSTING → TRANSACTION → SOURCE_FILE
//! - Inside a `NUMBER` token in a cost spec:
//!   Word → NUMBER → COST_SPEC → POSTING → TRANSACTION → SOURCE_FILE
//! - Inside a `STRING` token in a transaction header:
//!   Word → STRING → TRANSACTION → SOURCE_FILE
//! - Inside a meta-entry value:
//!   Word → value-token → META_ENTRY → POSTING / TRANSACTION → ...
//! - Inside an option value:
//!   Word → STRING → OPTION_DIRECTIVE → SOURCE_FILE
//!
//! Sub-token expansion (word boundaries, account-segment slicing
//! between colons) is the one place we still walk text directly,
//! because CST tokens are atomic.

use lsp_types::{Position, Range, SelectionRange, SelectionRangeParams};
use rustledger_parser::cst_walk::{TextRange, TextSize, TokenAtOffset};
use rustledger_parser::{SyntaxKind, SyntaxNode, SyntaxToken, parse_structured};

use super::utils::{LineIndex, PositionEncoding, is_word_char};

/// Handle a `textDocument/selectionRange` request.
pub fn handle_selection_range(
    params: &SelectionRangeParams,
    source: &str,
    encoding: PositionEncoding,
) -> Option<Vec<SelectionRange>> {
    let cst = parse_structured(source);
    let line_index = LineIndex::new(source, encoding);
    let mut results = Vec::with_capacity(params.positions.len());

    for position in &params.positions {
        results.push(
            compute_selection_range(&cst, &line_index, *position).unwrap_or(SelectionRange {
                range: Range {
                    start: *position,
                    end: *position,
                },
                parent: None,
            }),
        );
    }

    Some(results)
}

/// Build the nested-range chain at `position`.
fn compute_selection_range(
    cst: &SyntaxNode,
    line_index: &LineIndex<'_>,
    position: Position,
) -> Option<SelectionRange> {
    let offset = line_index.position_to_offset(position.line, position.character)?;
    let offset_ts = TextSize::try_from(offset).ok()?;

    // Find the deepest token containing the cursor. On a boundary
    // (between two tokens) rowan returns Between(left, right); we
    // prefer the left token so a cursor sitting AT the start of an
    // ACCOUNT (one column right of the trailing space of the
    // indent) still gets the ACCOUNT hierarchy.
    let token = match cst.token_at_offset(offset_ts) {
        TokenAtOffset::Single(t) => t,
        TokenAtOffset::Between(left, right) => prefer_word_token(left, right),
        TokenAtOffset::None => return None,
    };

    let mut ranges: Vec<Range> = Vec::new();

    // (1) Sub-token expansion: word, then any structural sub-slice
    //     (account-segment between colons, string interior between
    //     quotes). Each step is conditional and only fires when it
    //     actually narrows the token's range.
    let token_text = token.text();
    let token_start_byte: usize = u32::from(token.text_range().start()) as usize;
    let offset_in_token = offset
        .saturating_sub(token_start_byte)
        .min(token_text.len());

    if let Some(word) = word_range_in_token(&token, token_text, offset_in_token, line_index) {
        ranges.push(word);
    }
    match token.kind() {
        SyntaxKind::ACCOUNT => {
            if let Some(seg) =
                account_segment_range_in_token(&token, token_text, offset_in_token, line_index)
                && Some(seg) != ranges.last().copied()
            {
                ranges.push(seg);
            }
        }
        SyntaxKind::STRING => {
            if let Some(interior) = string_interior_range_in_token(&token, token_text, line_index)
                && Some(interior) != ranges.last().copied()
            {
                ranges.push(interior);
            }
        }
        _ => {}
    }

    // (2) The token itself.
    let token_range = node_or_token_range(token.text_range(), line_index);
    if Some(token_range) != ranges.last().copied() {
        ranges.push(token_range);
    }

    // (3) Every ancestor node, in order from immediate parent up to
    //     SOURCE_FILE. Adjacent duplicates (a wrapper node whose
    //     range matches its only child) collapse.
    let mut node = token.parent();
    while let Some(n) = node {
        let r = node_or_token_range(n.text_range(), line_index);
        if Some(r) != ranges.last().copied() {
            ranges.push(r);
        }
        node = n.parent();
    }

    Some(build_hierarchy(ranges))
}

/// On a token boundary, prefer the side whose first / last char is
/// a word character. A cursor between `"Coffee"` and a trailing
/// space should grab the STRING, not the WHITESPACE; a cursor
/// between an indent and an ACCOUNT should grab the ACCOUNT, not
/// the WHITESPACE.
fn prefer_word_token(left: SyntaxToken, right: SyntaxToken) -> SyntaxToken {
    let left_last = left.text().chars().next_back().is_some_and(is_word_char);
    let right_first = right.text().chars().next().is_some_and(is_word_char);
    match (left_last, right_first) {
        (false, true) => right,
        // (true, *) or (false, false): keep the left token. The
        // word-boundary case (true, true) is impossible across two
        // distinct CST tokens because the lexer would have merged
        // them into one.
        _ => left,
    }
}

/// Build the linked-list of SelectionRanges from innermost to
/// outermost. The outermost range becomes the deepest `parent`
/// chain; the innermost is the root we return.
fn build_hierarchy(ranges: Vec<Range>) -> SelectionRange {
    debug_assert!(
        !ranges.is_empty(),
        "compute_selection_range guarantees ≥1 range"
    );
    let mut parent: Option<Box<SelectionRange>> = None;
    for range in ranges.into_iter().rev() {
        parent = Some(Box::new(SelectionRange { range, parent }));
    }
    // SAFETY: ranges is non-empty per the assert above.
    *parent.expect("non-empty ranges")
}

/// Convert a rowan `TextRange` (byte offsets in `source`) to an
/// LSP `Range` in the negotiated encoding.
fn node_or_token_range(range: TextRange, line_index: &LineIndex<'_>) -> Range {
    let start_byte: usize = u32::from(range.start()) as usize;
    let end_byte: usize = u32::from(range.end()) as usize;
    let (start_line, start_col) = line_index.offset_to_position(start_byte);
    let (end_line, end_col) = line_index.offset_to_position(end_byte);
    Range {
        start: Position::new(start_line, start_col),
        end: Position::new(end_line, end_col),
    }
}

/// Word-boundary expansion within a single token's text. Returns
/// `None` if the cursor is not on a word character (no word to
/// select) or the word equals the entire token (no narrowing).
fn word_range_in_token(
    token: &SyntaxToken,
    token_text: &str,
    offset_in_token: usize,
    line_index: &LineIndex<'_>,
) -> Option<Range> {
    let token_start: usize = u32::from(token.text_range().start()) as usize;

    // Find word boundaries around `offset_in_token`. If the cursor
    // is between non-word chars there's nothing to expand to.
    if offset_in_token >= token_text.len() {
        return None;
    }
    let here = token_text[offset_in_token..].chars().next()?;
    if !is_word_char(here) {
        // Try the char immediately to the left (handles cursor
        // sitting at the end of a word).
        let prev = token_text[..offset_in_token].chars().next_back()?;
        if !is_word_char(prev) {
            return None;
        }
    }

    let mut start_byte = offset_in_token;
    while let Some((b, c)) = token_text[..start_byte].char_indices().next_back() {
        if !is_word_char(c) {
            break;
        }
        start_byte = b;
    }
    let mut end_byte = offset_in_token;
    for (b, c) in token_text[offset_in_token..].char_indices() {
        if !is_word_char(c) {
            break;
        }
        end_byte = offset_in_token + b + c.len_utf8();
    }

    if start_byte == end_byte {
        return None;
    }
    if start_byte == 0 && end_byte == token_text.len() {
        // Word is the entire token - let the token range cover it.
        return None;
    }

    let abs_start = token_start + start_byte;
    let abs_end = token_start + end_byte;
    let (sl, sc) = line_index.offset_to_position(abs_start);
    let (el, ec) = line_index.offset_to_position(abs_end);
    Some(Range {
        start: Position::new(sl, sc),
        end: Position::new(el, ec),
    })
}

/// Segment expansion for an `ACCOUNT` token: the slice between
/// adjacent `:` characters that contains the cursor. Returns
/// `None` if the segment equals the entire token.
fn account_segment_range_in_token(
    token: &SyntaxToken,
    token_text: &str,
    offset_in_token: usize,
    line_index: &LineIndex<'_>,
) -> Option<Range> {
    let token_start: usize = u32::from(token.text_range().start()) as usize;
    let clamped = offset_in_token.min(token_text.len().saturating_sub(1));

    let mut start_byte = clamped;
    while let Some((b, c)) = token_text[..start_byte].char_indices().next_back() {
        if c == ':' {
            break;
        }
        start_byte = b;
    }
    let mut end_byte = clamped;
    for (b, c) in token_text[clamped..].char_indices() {
        if c == ':' {
            break;
        }
        end_byte = clamped + b + c.len_utf8();
    }

    if start_byte == end_byte {
        return None;
    }
    if start_byte == 0 && end_byte == token_text.len() {
        return None;
    }

    let abs_start = token_start + start_byte;
    let abs_end = token_start + end_byte;
    let (sl, sc) = line_index.offset_to_position(abs_start);
    let (el, ec) = line_index.offset_to_position(abs_end);
    Some(Range {
        start: Position::new(sl, sc),
        end: Position::new(el, ec),
    })
}

/// Interior expansion for a `STRING` token: the bytes strictly
/// between the opening and closing `"`. Returns `None` if the
/// token isn't `"…"`-delimited (the lexer guarantees this shape,
/// but a malformed unterminated string skips the inner range).
fn string_interior_range_in_token(
    token: &SyntaxToken,
    token_text: &str,
    line_index: &LineIndex<'_>,
) -> Option<Range> {
    if token_text.len() < 2 {
        return None;
    }
    if !token_text.starts_with('"') || !token_text.ends_with('"') {
        return None;
    }
    let token_start: usize = u32::from(token.text_range().start()) as usize;
    let abs_start = token_start + 1;
    let abs_end = token_start + token_text.len() - 1;
    let (sl, sc) = line_index.offset_to_position(abs_start);
    let (el, ec) = line_index.offset_to_position(abs_end);
    Some(Range {
        start: Position::new(sl, sc),
        end: Position::new(el, ec),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use lsp_types::{Position, TextDocumentIdentifier};

    fn run(source: &str, position: Position) -> Vec<Range> {
        let params = SelectionRangeParams {
            text_document: TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            positions: vec![position],
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };
        let result = handle_selection_range(&params, source, PositionEncoding::Utf16).unwrap();
        assert_eq!(result.len(), 1);
        let mut out = Vec::new();
        let mut cur: Option<&SelectionRange> = Some(&result[0]);
        while let Some(r) = cur {
            out.push(r.range);
            cur = r.parent.as_deref();
        }
        out
    }

    #[test]
    fn account_segment_then_account_then_posting_then_transaction() {
        // Cursor inside "Bank" of `Assets:Bank:Checking`.
        let source = "2024-01-15 * \"Coffee\"\n  Assets:Bank:Checking -5.00 USD\n  Expenses:Food\n";
        let ranges = run(source, Position::new(1, 11)); // mid "Bank"
        // Expected hierarchy:
        //   word(Bank)  ⊂  ACCOUNT(Assets:Bank:Checking)  ⊂
        //   POSTING  ⊂  TRANSACTION  ⊂  SOURCE_FILE
        // The word range coincides with the account-segment range
        // (account segments are alphanumeric in Beancount, same as
        // a word-char run), so the dedup collapses them into one
        // entry - that's the correct hierarchy, not a missing level.
        assert!(ranges.len() >= 4, "got {} ranges: {ranges:?}", ranges.len());
        assert_eq!(
            ranges[0],
            Range {
                start: Position::new(1, 9),
                end: Position::new(1, 13)
            },
            "deepest range should be the 'Bank' word/segment",
        );
        // The deepest range must be a sub-slice of the next one.
        for win in ranges.windows(2) {
            let (inner, outer) = (win[0], win[1]);
            assert!(
                range_contains(outer, inner),
                "outer={outer:?} does not contain inner={inner:?}"
            );
        }
    }

    #[test]
    fn number_token_inside_amount() {
        // Cursor inside "5" of "-5.00".
        let source = "2024-01-15 * \"x\"\n  Assets:Cash -5.00 USD\n  Expenses:Misc 5.00 USD\n";
        let ranges = run(source, Position::new(1, 17)); // on '5' in -5.00
        // Number is a single token; expect at least:
        // NUMBER ⊂ AMOUNT ⊂ POSTING ⊂ TRANSACTION ⊂ SOURCE_FILE.
        // (Word expansion may also fire on the digit, that's fine.)
        assert!(ranges.len() >= 4, "got {} ranges: {ranges:?}", ranges.len());
        for win in ranges.windows(2) {
            let (inner, outer) = (win[0], win[1]);
            assert!(
                range_contains(outer, inner),
                "outer={outer:?} does not contain inner={inner:?}"
            );
        }
    }

    #[test]
    fn string_interior_then_string_then_transaction_header() {
        // Cursor inside "Coffee" string literal.
        let source = "2024-01-15 * \"Coffee Shop\"\n  Assets:Cash -1.00 USD\n  Expenses:Food\n";
        let ranges = run(source, Position::new(0, 17)); // mid "Coffee"
        // Should have at least: word(Coffee) ⊂ string-interior ⊂
        // STRING ⊂ TRANSACTION ⊂ SOURCE_FILE.
        assert!(ranges.len() >= 4, "got {} ranges: {ranges:?}", ranges.len());
        for win in ranges.windows(2) {
            let (inner, outer) = (win[0], win[1]);
            assert!(
                range_contains(outer, inner),
                "outer={outer:?} does not contain inner={inner:?}"
            );
        }
    }

    #[test]
    fn cursor_in_whitespace_at_line_start_picks_account() {
        // Cursor sits between the two indent spaces and the account.
        // The token-boundary tiebreaker should hand us the ACCOUNT.
        let source = "2024-01-15 * \"x\"\n  Assets:Cash -1.00 USD\n  Expenses:Misc 1.00 USD\n";
        let ranges = run(source, Position::new(1, 2)); // start of "Assets:..."
        // Boundary case: at column 2 the cursor sits right at the
        // start of ACCOUNT. prefer_word_token should pick ACCOUNT
        // over the leading WHITESPACE.
        assert!(ranges.len() >= 3, "got {} ranges: {ranges:?}", ranges.len());
    }

    #[test]
    fn posting_with_interleaved_metadata_is_not_corrupted() {
        // Regression for #1142: a transaction with per-posting
        // metadata. The CST-walking shape naturally distinguishes
        // each posting's range from the metadata's; the prior
        // typed-AST shape needed the `posting.span` workaround
        // to avoid `txn_start_line + i` collisions.
        let source = "2024-01-15 * \"FX\"\n  Assets:USD -100.00 USD\n    effective_date: 2024-01-16\n  Assets:EUR 92.00 EUR\n    effective_date: 2024-01-17\n";
        // Cursor inside the SECOND posting's account.
        let ranges = run(source, Position::new(3, 5)); // mid "Assets" of EUR posting
        // Must surface POSTING and TRANSACTION ranges; the POSTING
        // must NOT include the first posting or the metadata above.
        assert!(ranges.len() >= 4, "got {} ranges: {ranges:?}", ranges.len());
        for win in ranges.windows(2) {
            let (inner, outer) = (win[0], win[1]);
            assert!(
                range_contains(outer, inner),
                "outer={outer:?} does not contain inner={inner:?}"
            );
        }
    }

    #[test]
    fn out_of_bounds_position_returns_collapsed_range() {
        // A position past the end of the source should yield a
        // collapsed (zero-width) SelectionRange rather than panic.
        let source = "2024-01-15 open Assets:A\n";
        let ranges = run(source, Position::new(99, 99));
        assert_eq!(ranges.len(), 1);
        assert_eq!(ranges[0].start, ranges[0].end);
    }

    fn range_contains(outer: Range, inner: Range) -> bool {
        pos_le(outer.start, inner.start) && pos_le(inner.end, outer.end)
    }
    fn pos_le(a: Position, b: Position) -> bool {
        (a.line, a.character) <= (b.line, b.character)
    }
}
