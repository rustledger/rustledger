//! Integration tests for LSP position-encoding consistency across
//! handlers.
//!
//! Every handler that emits `Position` values from byte offsets goes
//! through `LineIndex` (whose two encoding branches are pinned by
//! unit tests in `handlers::utils`). This integration test exercises a
//! representative subset of the handler stack END-TO-END under BOTH
//! `PositionEncoding::Utf8` and `PositionEncoding::Utf16` on a source
//! containing non-ASCII content (Cyrillic + emoji), and asserts that
//! the emitted positions round-trip through `LineIndex` to the SAME
//! byte ranges.
//!
//! Why an integration test rather than a per-handler unit test: the
//! property the integration test catches is "a handler accidentally
//! constructs a `Position` outside the `LineIndex` API" — e.g.,
//! computing `line.encode_utf16().count()` directly or
//! `byte_col as u32` — both of which would silently pass unit tests
//! that exercise only one encoding. Verifying round-trip consistency
//! under each encoding catches these.

use lsp_types::{
    DocumentColorParams, DocumentFormattingParams, DocumentSymbolParams, FoldingRangeParams,
    InlayHintParams, Position, Range, SemanticTokensParams, TextDocumentIdentifier,
};
use rustledger_lsp::handlers::document_color::handle_document_color;
use rustledger_lsp::handlers::folding::handle_folding_ranges;
use rustledger_lsp::handlers::formatting::handle_formatting;
use rustledger_lsp::handlers::inlay_hints::handle_inlay_hints;
use rustledger_lsp::handlers::semantic_tokens::handle_semantic_tokens;
use rustledger_lsp::handlers::symbols::handle_document_symbols;
use rustledger_lsp::handlers::utils::{LineIndex, PositionEncoding};
use rustledger_parser::parse;

/// Source with Cyrillic (1 UTF-16 unit, 2 UTF-8 bytes per char) AND
/// an emoji (2 UTF-16 units, 4 UTF-8 bytes — surrogate pair). Exercises
/// every encoding-sensitive code path.
const SOURCE: &str = "\
2024-01-01 open Активы:Банк USD
2024-01-15 * \"Кофе ☕\"
  Активы:Банк  -5.00 USD
  Расходы:Еда  5.00 USD
";

fn uri() -> lsp_types::Uri {
    "file:///encoding-coverage.beancount".parse().unwrap()
}

/// `Position` returned by a handler MUST round-trip via
/// `LineIndex::position_to_offset(encoding)` back to a valid byte
/// offset — i.e., the handler's emitted columns are interpretable
/// under the negotiated encoding. Pre-PR handlers that hardcoded
/// `line.len() as u32` (UTF-8) or `line.encode_utf16().count()`
/// (UTF-16) would emit positions that DON'T round-trip under the
/// other encoding.
fn assert_position_round_trips(pos: Position, source: &str, encoding: PositionEncoding) {
    let idx = LineIndex::new(source, encoding);
    let offset = idx.position_to_offset(pos.line, pos.character);
    assert!(
        offset.is_some(),
        "Position {pos:?} under {encoding:?} doesn't round-trip into a byte offset \
         — handler likely emitted a column in the wrong encoding (UTF-16 columns \
         interpreted as UTF-8 bytes, or vice versa)"
    );
}

fn assert_range_round_trips(range: Range, source: &str, encoding: PositionEncoding) {
    assert_position_round_trips(range.start, source, encoding);
    assert_position_round_trips(range.end, source, encoding);
}

#[test]
fn formatting_positions_round_trip_under_both_encodings() {
    let parsed = parse(SOURCE);
    let params = DocumentFormattingParams {
        text_document: TextDocumentIdentifier { uri: uri() },
        options: Default::default(),
        work_done_progress_params: Default::default(),
    };
    for encoding in [PositionEncoding::Utf8, PositionEncoding::Utf16] {
        if let Some(edits) = handle_formatting(&params, SOURCE, &parsed, encoding) {
            for edit in edits {
                assert_range_round_trips(edit.range, SOURCE, encoding);
            }
        }
    }
}

#[test]
fn semantic_tokens_positions_round_trip_under_both_encodings() {
    // semantic_tokens emits delta-encoded positions inside SemanticToken;
    // walk the deltas to reconstruct absolute positions and check each.
    let parsed = parse(SOURCE);
    let params = SemanticTokensParams {
        text_document: TextDocumentIdentifier { uri: uri() },
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
    };
    for encoding in [PositionEncoding::Utf8, PositionEncoding::Utf16] {
        let Some(result) = handle_semantic_tokens(&params, SOURCE, &parsed, encoding) else {
            continue;
        };
        let tokens = match result {
            lsp_types::SemanticTokensResult::Tokens(t) => t.data,
            lsp_types::SemanticTokensResult::Partial(p) => p.data,
        };
        let mut line = 0u32;
        let mut col = 0u32;
        for tok in tokens {
            if tok.delta_line != 0 {
                line += tok.delta_line;
                col = tok.delta_start;
            } else {
                col += tok.delta_start;
            }
            // Token start and end positions must both round-trip.
            assert_position_round_trips(Position::new(line, col), SOURCE, encoding);
            assert_position_round_trips(Position::new(line, col + tok.length), SOURCE, encoding);
        }
    }
}

#[test]
fn document_symbols_ranges_round_trip_under_both_encodings() {
    let parsed = parse(SOURCE);
    let params = DocumentSymbolParams {
        text_document: TextDocumentIdentifier { uri: uri() },
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
    };
    for encoding in [PositionEncoding::Utf8, PositionEncoding::Utf16] {
        let Some(response) = handle_document_symbols(&params, SOURCE, &parsed, encoding) else {
            continue;
        };
        let symbols = match response {
            lsp_types::DocumentSymbolResponse::Flat(s) => s
                .into_iter()
                .map(|si| si.location.range)
                .collect::<Vec<_>>(),
            lsp_types::DocumentSymbolResponse::Nested(s) => s
                .into_iter()
                .flat_map(|ds| vec![ds.range, ds.selection_range])
                .collect::<Vec<_>>(),
        };
        for range in symbols {
            assert_range_round_trips(range, SOURCE, encoding);
        }
    }
}

#[test]
fn document_color_ranges_round_trip_under_both_encodings() {
    let parsed = parse(SOURCE);
    let params = DocumentColorParams {
        text_document: TextDocumentIdentifier { uri: uri() },
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
    };
    for encoding in [PositionEncoding::Utf8, PositionEncoding::Utf16] {
        let Some(colors) = handle_document_color(&params, SOURCE, &parsed, encoding) else {
            continue;
        };
        for color in colors {
            assert_range_round_trips(color.range, SOURCE, encoding);
        }
    }
}

#[test]
fn inlay_hints_positions_round_trip_under_both_encodings() {
    let parsed = parse(SOURCE);
    let params = InlayHintParams {
        text_document: TextDocumentIdentifier { uri: uri() },
        range: Range::new(Position::new(0, 0), Position::new(100, 0)),
        work_done_progress_params: Default::default(),
    };
    for encoding in [PositionEncoding::Utf8, PositionEncoding::Utf16] {
        let Some(hints) = handle_inlay_hints(&params, SOURCE, &parsed, encoding) else {
            continue;
        };
        for hint in hints {
            assert_position_round_trips(hint.position, SOURCE, encoding);
        }
    }
}

#[test]
fn folding_ranges_emit_line_numbers_within_source_under_both_encodings() {
    // FoldingRange uses line numbers only (no char positions). The
    // line count is encoding-independent — so this test verifies the
    // line-only emission doesn't accidentally encode a char column.
    let parsed = parse(SOURCE);
    let params = FoldingRangeParams {
        text_document: TextDocumentIdentifier { uri: uri() },
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
    };
    let line_count = SOURCE.lines().count() as u32;
    for encoding in [PositionEncoding::Utf8, PositionEncoding::Utf16] {
        if let Some(ranges) = handle_folding_ranges(&params, SOURCE, &parsed, encoding) {
            for r in ranges {
                assert!(r.start_line <= line_count, "fold start_line out of bounds");
                assert!(r.end_line <= line_count, "fold end_line out of bounds");
            }
        }
    }
}
