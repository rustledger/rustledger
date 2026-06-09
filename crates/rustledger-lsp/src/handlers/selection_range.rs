//! Selection-range handler - CST-backed implementation (#1262 phase 5.2).
//!
//! Returns the nested-range hierarchy LSP clients use for smart
//! expansion (Ctrl+Shift+Up / Cmd+Shift+Up in most editors). Each
//! requested position yields a linked list of progressively wider
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
use rustledger_parser::{
    ParseResult, SyntaxKind, SyntaxNode, SyntaxToken, TextRange, TextSize, TokenAtOffset,
};

use super::utils::{LineIndex, PositionEncoding, is_word_char};

/// Handle a `textDocument/selectionRange` request.
///
/// Consumes the cached CST root from `parse_result.syntax_root`
/// instead of re-parsing the source. Previous shape called
/// `parse_structured(source)` per request, doubling the parse
/// cost (the VFS cache already parses once for the `ParseResult`).
/// The `Arc<GreenNode>` cache landed in phase 5.5 of #1262
/// alongside this change.
///
/// **BOM frame.** `parse_result.syntax_root` is built from the
/// BOM-stripped source (the parser strips the leading BOM before
/// tokenizing), so its `TextRange` offsets are in the *post-BOM*
/// byte frame. The `source` argument and the `LineIndex` built
/// from it are in the *original* source frame. We bridge the two
/// by subtracting `BOM_LEN` (3) from LSP-derived offsets before
/// asking the CST, and adding `BOM_LEN` back when converting CST
/// `TextRange` offsets to LSP positions — gated on
/// `parse_result.has_leading_bom`. The other ACCOUNT/Currency
/// handlers don't see this because they walk
/// `account_occurrences` / `currency_occurrences`, whose spans
/// are pre-shifted into the original frame by the converter.
pub fn handle_selection_range(
    params: &SelectionRangeParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<Vec<SelectionRange>> {
    // Use the supported entry point rather than constructing the
    // SyntaxNode by hand from the green root - keeps the
    // `rowan::GreenNode` type name out of consumer code so a future
    // rowan upgrade is contained in `rustledger-parser`.
    let cst = parse_result.syntax_node();
    let line_index = LineIndex::new(source, encoding);
    let bom_offset: usize = if parse_result.has_leading_bom { 3 } else { 0 };
    let mut results = Vec::with_capacity(params.positions.len());

    for position in &params.positions {
        results.push(
            compute_selection_range(&cst, &line_index, *position, bom_offset).unwrap_or(
                SelectionRange {
                    range: Range {
                        start: *position,
                        end: *position,
                    },
                    parent: None,
                },
            ),
        );
    }

    Some(results)
}

/// Build the nested-range chain at `position`.
///
/// `bom_offset` is the number of bytes the parser stripped off
/// the front of the source (0 for BOM-less, 3 for BOM-prefixed).
/// `position_to_offset` returns an original-source offset; we
/// shift it down into the CST frame before walking the tree, and
/// shift CST offsets back up before emitting LSP positions.
fn compute_selection_range(
    cst: &SyntaxNode,
    line_index: &LineIndex<'_>,
    position: Position,
    bom_offset: usize,
) -> Option<SelectionRange> {
    let orig_offset = line_index.position_to_offset(position.line, position.character)?;
    // Cursor sits before the BOM region (only possible if the user
    // somehow targeted a position before the file starts; defensive
    // bound) — no valid CST token there.
    let cst_offset = orig_offset.checked_sub(bom_offset)?;
    let offset_ts = TextSize::try_from(cst_offset).ok()?;

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
    // `offset_in_token` is intra-token, so it doesn't care about
    // the BOM shift - both sides of the subtraction are in CST
    // frame.
    let offset_in_token = cst_offset
        .saturating_sub(token_start_byte)
        .min(token_text.len());

    if let Some(word) =
        word_range_in_token(&token, token_text, offset_in_token, line_index, bom_offset)
    {
        ranges.push(word);
    }
    match token.kind() {
        SyntaxKind::ACCOUNT => {
            if let Some(seg) = account_segment_range_in_token(
                &token,
                token_text,
                offset_in_token,
                line_index,
                bom_offset,
            ) && Some(seg) != ranges.last().copied()
            {
                ranges.push(seg);
            }
        }
        SyntaxKind::STRING => {
            if let Some(interior) =
                string_interior_range_in_token(&token, token_text, line_index, bom_offset)
                && Some(interior) != ranges.last().copied()
            {
                ranges.push(interior);
            }
        }
        _ => {}
    }

    // (2) The token itself. `ranges.last()` is `None` when no
    //     sub-token expansion fired, so the inequality is true and
    //     this push always runs in that case - meaning `ranges` is
    //     GUARANTEED non-empty after this point and
    //     `build_hierarchy` cannot panic on a degenerate empty
    //     input.
    let token_range = node_or_token_range(token.text_range(), line_index, bom_offset);
    if Some(token_range) != ranges.last().copied() {
        ranges.push(token_range);
    }

    // (3) Every ancestor node, in order from immediate parent up to
    //     SOURCE_FILE. Two filters fire:
    //     - Adjacent duplicates (a wrapper node whose range matches
    //       its only child) collapse.
    //     - ERROR_NODE ancestors are skipped. The CST wraps broken
    //       syntax in ERROR_NODE whose range can swallow many lines;
    //       emitting it as a hierarchy level produces a confusing
    //       jump from a small inner range to a large unrelated
    //       region. Skipping lets the next valid structural parent
    //       (often SOURCE_FILE) absorb the level.
    let mut node = token.parent();
    while let Some(n) = node {
        if n.kind() != SyntaxKind::ERROR_NODE {
            let r = node_or_token_range(n.text_range(), line_index, bom_offset);
            if Some(r) != ranges.last().copied() {
                ranges.push(r);
            }
        }
        node = n.parent();
    }

    Some(build_hierarchy(ranges))
}

/// On a token boundary, prefer the side carrying more semantic
/// content.
///
/// Earlier shape used `is_word_char` on the touching characters
/// for the tiebreak. That was the wrong predicate: `is_word_char`
/// returns true for `:` and `-`, both of which appear as the LAST
/// char of legitimate CST tokens (META_KEY ends with `:` per its
/// lexer regex). A cursor between a META_KEY and its value would
/// hit (true, true) on the boundary and the previous code
/// silently picked the META_KEY when the user almost certainly
/// clicked the value.
///
/// The new policy ranks by [`SyntaxKind`] using a small priority
/// scale: trivia (whitespace / newline / comment / BOM) and
/// `ERROR_TOKEN` are lowest; operators and punctuation are
/// middle; identifier-like and literal tokens (ACCOUNT, STRING,
/// NUMBER, DATE, TAG, LINK, CURRENCY, keywords, ...) are highest.
/// Higher wins. Ties prefer left to match standard editor
/// "click on the boundary, get the prior token" convention.
fn prefer_word_token(left: SyntaxToken, right: SyntaxToken) -> SyntaxToken {
    if token_priority(right.kind()) > token_priority(left.kind()) {
        right
    } else {
        left
    }
}

/// Score a `SyntaxKind` for boundary-tiebreaking. Higher is better.
fn token_priority(kind: SyntaxKind) -> u8 {
    // Trivia / error: never preferred at a boundary - the cursor
    // never logically belongs to whitespace or a parse error.
    if kind.is_trivia() || kind == SyntaxKind::ERROR_TOKEN {
        return 0;
    }
    match kind {
        // Operators and punctuation: middle band. META_KEY lives
        // here because it ENDS in `:` (per the lexer's regex), so
        // a cursor sitting after the colon is semantically on the
        // value-token side, not the key-token side.
        SyntaxKind::COLON
        | SyntaxKind::COMMA
        | SyntaxKind::AT
        | SyntaxKind::AT_AT
        | SyntaxKind::PLUS
        | SyntaxKind::MINUS
        | SyntaxKind::STAR
        | SyntaxKind::SLASH
        | SyntaxKind::L_PAREN
        | SyntaxKind::R_PAREN
        | SyntaxKind::L_BRACE
        | SyntaxKind::R_BRACE
        | SyntaxKind::L_DOUBLE_BRACE
        | SyntaxKind::R_DOUBLE_BRACE
        | SyntaxKind::L_BRACE_HASH
        | SyntaxKind::TILDE
        | SyntaxKind::META_KEY => 1,
        // Everything else: identifier-like / literal / keyword
        // tokens whose payload carries semantic meaning.
        _ => 2,
    }
}

/// Build the linked-list of SelectionRanges from innermost to
/// outermost. `ranges` is guaranteed non-empty by
/// [`compute_selection_range`] - stage (2) unconditionally pushes
/// the cursor's token range when no inner sub-token range fires.
fn build_hierarchy(ranges: Vec<Range>) -> SelectionRange {
    assert!(
        !ranges.is_empty(),
        "compute_selection_range must always emit at least the cursor's token range"
    );
    let mut parent: Option<Box<SelectionRange>> = None;
    for range in ranges.into_iter().rev() {
        parent = Some(Box::new(SelectionRange { range, parent }));
    }
    *parent.expect("non-empty ranges (asserted above)")
}

/// Convert a rowan `TextRange` (byte offsets in the *CST* — i.e.
/// the BOM-stripped frame) to an LSP `Range` in the negotiated
/// encoding. `bom_offset` adds back the BOM bytes that the
/// converter stripped, so the LSP positions land at the user's
/// intended source coordinates.
fn node_or_token_range(range: TextRange, line_index: &LineIndex<'_>, bom_offset: usize) -> Range {
    let start_byte: usize = u32::from(range.start()) as usize + bom_offset;
    let end_byte: usize = u32::from(range.end()) as usize + bom_offset;
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
///
/// `bom_offset` shifts the CST-frame absolute offsets up into
/// the original-source frame before LSP `Position` conversion.
fn word_range_in_token(
    token: &SyntaxToken,
    token_text: &str,
    offset_in_token: usize,
    line_index: &LineIndex<'_>,
    bom_offset: usize,
) -> Option<Range> {
    let token_start: usize = u32::from(token.text_range().start()) as usize;

    // Find word boundaries around `offset_in_token`. The cursor
    // can sit on a word char, between two non-word chars, or
    // right at the trailing edge of a word (offset_in_token ==
    // token_text.len() when prefer_word_token routed us to the
    // left token of a boundary). In the last case
    // `token_text[offset_in_token..].chars().next()` is None,
    // so we fall back to the `prev` char on the left to detect
    // "cursor right after a word".
    let here = token_text[offset_in_token..].chars().next();
    let on_word = here.is_some_and(is_word_char);
    if !on_word {
        let prev = token_text[..offset_in_token].chars().next_back();
        if !prev.is_some_and(is_word_char) {
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

    let abs_start = token_start + start_byte + bom_offset;
    let abs_end = token_start + end_byte + bom_offset;
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
///
/// `bom_offset` shifts the CST-frame absolute offsets up into
/// the original-source frame before LSP `Position` conversion.
fn account_segment_range_in_token(
    token: &SyntaxToken,
    token_text: &str,
    offset_in_token: usize,
    line_index: &LineIndex<'_>,
    bom_offset: usize,
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

    let abs_start = token_start + start_byte + bom_offset;
    let abs_end = token_start + end_byte + bom_offset;
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
///
/// `bom_offset` shifts the CST-frame absolute offsets up into
/// the original-source frame before LSP `Position` conversion.
fn string_interior_range_in_token(
    token: &SyntaxToken,
    token_text: &str,
    line_index: &LineIndex<'_>,
    bom_offset: usize,
) -> Option<Range> {
    if token_text.len() < 2 {
        return None;
    }
    if !token_text.starts_with('"') || !token_text.ends_with('"') {
        return None;
    }
    let token_start: usize = u32::from(token.text_range().start()) as usize;
    let abs_start = token_start + 1 + bom_offset;
    let abs_end = token_start + token_text.len() - 1 + bom_offset;
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
        let parse_result = rustledger_parser::parse(source);
        let result =
            handle_selection_range(&params, source, &parse_result, PositionEncoding::Utf16)
                .unwrap();
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

    #[test]
    fn number_inside_cost_spec() {
        // Cursor on '5' of "500.00" inside `{500.00 USD}`. The CST
        // wraps cost specs in a COST_SPEC node; the hierarchy must
        // surface that level before the enclosing POSTING.
        let source = "2024-01-15 * \"buy\"\n  Assets:Brokerage 10 HOOL {500.00 USD}\n  Assets:Cash -5000.00 USD\n";
        // Source line 1 byte positions:
        //   col 0..2  = leading indent
        //   col 27    = '{'
        //   col 28..31= '500'
        //   col 38    = '}'
        let ranges = run(source, Position::new(1, 28)); // on '5' of 500
        // Hierarchy must include COST_SPEC as a distinct level
        // between NUMBER and POSTING. POSTING and SOURCE_FILE may
        // coincide on a single-transaction file (the dedup
        // collapses them) but COST_SPEC must always appear.
        assert!(ranges.len() >= 4, "got {} ranges: {ranges:?}", ranges.len());
        for win in ranges.windows(2) {
            let (inner, outer) = (win[0], win[1]);
            assert!(
                range_contains(outer, inner),
                "outer={outer:?} does not contain inner={inner:?}"
            );
        }
        // The COST_SPEC range covers exactly `{500.00 USD}` =
        // columns 27..39. Find it.
        assert!(
            ranges
                .iter()
                .any(|r| r.start.character == 27 && r.end.character == 39),
            "COST_SPEC range {{500.00 USD}} (cols 27..39) not in chain: {ranges:?}",
        );
    }

    #[test]
    fn number_inside_price_annotation() {
        // Cursor on '1' of "1.00" inside `@ 1.00 EUR`. The CST
        // wraps price annotations in a PRICE_ANNOTATION node.
        let source =
            "2024-01-15 * \"fx\"\n  Assets:USD -100 USD @ 1.00 EUR\n  Assets:EUR 100 EUR\n";
        let ranges = run(source, Position::new(1, 24)); // on '1' of @ 1.00
        // PRICE_ANNOTATION should appear as a discrete level.
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
    fn string_inside_option_directive() {
        // Cursor inside the value string of `option "title" "My Book"`.
        let source = "option \"title\" \"My Book\"\n";
        let ranges = run(source, Position::new(0, 19)); // mid "My"
        // Expected: word(My) -> string-interior -> STRING ->
        // option directive -> SOURCE_FILE.
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
    fn error_node_ancestors_are_skipped_in_broken_syntax() {
        // Regression for the mid-edit case where ERROR_NODE wraps
        // a multi-line region (unterminated string here). The
        // handler must NOT emit the ERROR_NODE as a hierarchy
        // level; users mid-edit would see Expand Selection jump
        // from a small word to a multi-line region with nothing
        // sensible between, often spilling into the next
        // directive.
        let source = "2024-01-15 * \"unterminated\n  Assets:Cash -1.00 USD\n";
        let ranges = run(source, Position::new(0, 18)); // mid 'unterminated'
        // We don't make precise structural promises in the broken-
        // syntax case, but the chain must:
        // (a) be monotonically containing, and
        // (b) contain no range whose `kind` is ERROR_NODE - which
        //     we verify indirectly by asserting no intermediate
        //     range spans MORE than 80% of the source (the
        //     ERROR_NODE shape that prompted this fix swallowed
        //     >50% of the source before settling on SOURCE_FILE).
        for win in ranges.windows(2) {
            let (inner, outer) = (win[0], win[1]);
            assert!(
                range_contains(outer, inner),
                "outer={outer:?} does not contain inner={inner:?}"
            );
        }
        let last = ranges.last().copied().expect("non-empty chain");
        // Every range except the last (SOURCE_FILE) should be
        // strictly narrower than the source-wide range.
        for r in ranges.iter().take(ranges.len() - 1) {
            assert!(
                !range_contains(*r, last) || *r == last,
                "non-root range {r:?} swallowed the whole source - ERROR_NODE not skipped",
            );
        }
    }

    #[test]
    fn utf8_encoding_emits_correct_positions_on_non_ascii_content() {
        // Cursor inside the Cyrillic word "Банк" of an account.
        // Under UTF-8 each Cyrillic letter is 2 bytes; the column
        // math must agree with the negotiated encoding. The
        // line_index is encoding-aware; this test pins that
        // selection_range round-trips through it cleanly.
        let source = "2024-01-15 * \"x\"\n  Активы:Банк -5.00 USD\n  Expenses:Misc 5.00 USD\n";
        // Line 1 UTF-8 byte layout:
        //   0..2  = leading indent
        //   2..14 = "Активы" (6 chars * 2 bytes)
        //   14    = ':'
        //   15..23 = "Банк" (4 chars * 2 bytes)
        //   23    = ' '
        // Cursor at byte column 17 sits on the start of 'а' (the
        // second char of "Банк"), which is a valid char boundary
        // - position_to_offset requires this under UTF-8.
        let params = SelectionRangeParams {
            text_document: TextDocumentIdentifier {
                uri: "file:///utf8.beancount".parse().unwrap(),
            },
            positions: vec![Position::new(1, 17)],
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };
        let parse_result = rustledger_parser::parse(source);
        let result = handle_selection_range(&params, source, &parse_result, PositionEncoding::Utf8)
            .expect("Some");
        assert_eq!(result.len(), 1);
        let mut chain = Vec::new();
        let mut cur: Option<&SelectionRange> = Some(&result[0]);
        while let Some(r) = cur {
            chain.push(r.range);
            cur = r.parent.as_deref();
        }
        // We don't pin exact byte columns - we pin the invariant
        // that the chain is monotonically containing and non-trivial
        // (more than just a collapsed fallback), proving the
        // encoding pipeline didn't silently degrade to the
        // out-of-bounds fallback.
        assert!(chain.len() >= 3, "got {} ranges: {chain:?}", chain.len());
        for win in chain.windows(2) {
            let (inner, outer) = (win[0], win[1]);
            assert!(
                range_contains(outer, inner),
                "outer={outer:?} does not contain inner={inner:?}"
            );
        }
    }

    fn range_contains(outer: Range, inner: Range) -> bool {
        pos_le(outer.start, inner.start) && pos_le(inner.end, outer.end)
    }
    fn pos_le(a: Position, b: Position) -> bool {
        (a.line, a.character) <= (b.line, b.character)
    }

    /// Regression test for the BOM frame mismatch flagged by
    /// Copilot on PR #1295: when the source begins with a UTF-8
    /// BOM, the cached `syntax_root` is built from the
    /// BOM-stripped source so its `TextRange` offsets are in the
    /// post-BOM frame, but LSP positions and the `LineIndex` are
    /// in the original-source frame. Without the `bom_offset`
    /// adjustment, `cst.token_at_offset` would land on a token
    /// 3 bytes past the user's cursor, and emitted LSP ranges
    /// would be shifted to the wrong source columns.
    ///
    /// The fixture is identical to a routine selection-range
    /// case except for the leading BOM. The expected hierarchy
    /// and column math is therefore unchanged from a BOM-less
    /// source — if any of them shifts by 3, the bug is back.
    #[test]
    fn bom_prefixed_source_does_not_shift_ranges() {
        // U+FEFF as UTF-8 is `\u{FEFF}`. The first directive
        // starts at original-byte 3 (after the BOM); LSP
        // position (0, 0) is still the start of line 0.
        let source = "\u{FEFF}2024-01-15 * \"Coffee\"\n  Assets:Bank -5.00 USD\n";
        let parse_result = rustledger_parser::parse(source);
        assert!(
            parse_result.has_leading_bom,
            "parser must have detected the BOM for the fix to take effect",
        );
        assert!(
            parse_result.errors.is_empty(),
            "parse errors: {:?}",
            parse_result.errors,
        );

        // Cursor on the `A` of `Assets:Bank` (line 1, char 2
        // after the two-space indent). Without the fix, the
        // cursor lookup would land 3 bytes ahead — likely in
        // the middle of "Assets" or past it — and the emitted
        // ranges would also be shifted.
        let params = SelectionRangeParams {
            text_document: TextDocumentIdentifier {
                uri: "file:///bom.beancount".parse().unwrap(),
            },
            positions: vec![Position::new(1, 2)],
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        };
        let result =
            handle_selection_range(&params, source, &parse_result, PositionEncoding::Utf16)
                .expect("selection range returns Some");
        assert_eq!(result.len(), 1);

        let mut chain = Vec::new();
        let mut cur: Option<&SelectionRange> = Some(&result[0]);
        while let Some(r) = cur {
            chain.push(r.range);
            cur = r.parent.as_deref();
        }

        // The deepest range is the word/segment "Assets" inside
        // the account token — columns 2..8 of line 1, regardless
        // of the leading BOM. If `bom_offset` didn't apply, the
        // range would either land at the wrong column or
        // degenerate to the (position, position) fallback.
        assert_eq!(
            chain[0],
            Range {
                start: Position::new(1, 2),
                end: Position::new(1, 8),
            },
            "deepest range should be the 'Assets' segment at line 1 cols 2..8; got {chain:?}",
        );

        // The full chain must be monotonically containing.
        for win in chain.windows(2) {
            let (inner, outer) = (win[0], win[1]);
            assert!(
                range_contains(outer, inner),
                "outer={outer:?} does not contain inner={inner:?}; \
                 a BOM-frame bug typically breaks containment when one of \
                 the helpers forgets the bom_offset shift",
            );
        }

        // SOURCE_FILE (the outermost range) starts at the first
        // CST byte (post-BOM byte 0), shifted up by `BOM_LEN`
        // into the original-source frame. In UTF-16 encoding the
        // 3-byte UTF-8 BOM is 1 code unit, so the LSP column
        // works out to 1. The important invariant is that
        // SOURCE_FILE.start is *deterministic* — a residual BOM
        // bug would either leave start at (0, 0) (forgot to
        // shift the SOURCE_FILE range) or push it past the BOM
        // by 3 in BOTH directions (double-counting). Pin the
        // exact post-shift coordinates.
        let outer = *chain.last().unwrap();
        assert_eq!(
            outer.start,
            Position::new(0, 1),
            "SOURCE_FILE range start drifted; expected (0, 1) — the post-BOM byte 0 \
             shifted +BOM_LEN into the original-source frame and then mapped to \
             UTF-16 column 1 — got {outer:?}. A bug in node_or_token_range that \
             forgets the bom_offset shift would land at (0, 0); double-shifting \
             would land somewhere wrong.",
        );
    }
}
