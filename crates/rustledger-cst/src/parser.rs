//! Phase 1 flat parser: produce a `SOURCE_FILE` node containing every
//! lossless token as a direct child, in source order.
//!
//! No structural nesting — every token is a leaf under the root. The
//! tree round-trips byte-identically to the source; phase 2 will add
//! structural node kinds (`DIRECTIVE`, `POSTING`, `AMOUNT_NODE`, ...)
//! by reorganizing the same token stream into nested nodes.

use rowan::GreenNodeBuilder;

use crate::lossless_tokens::lossless_tokens;
use crate::syntax_kind::{SyntaxKind, SyntaxNode};

/// Parse `source` to a flat lossless CST.
///
/// Every byte of `source` is reachable from the returned root node;
/// `parse_flat(source).text().to_string() == source` holds for every
/// input. The round-trip property is exercised over the full
/// compatibility corpus in `tests/round_trip.rs`.
///
/// Phase 2 of #1262 will replace this single-pass driver with a
/// structured parser that emits typed directive nodes. Until then,
/// `parse_flat` is the entry point for any consumer wanting a
/// byte-preserving view of beancount source (formatter, refactor,
/// rename).
#[must_use]
pub fn parse_flat(source: &str) -> SyntaxNode {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::SOURCE_FILE.into());

    for (kind, range) in lossless_tokens(source) {
        // `rowan::GreenNodeBuilder::token` takes the kind plus the
        // textual bytes. We slice them out of the source by the
        // adapter's range. The slice's lifetime is tied to `source`
        // for the duration of the call; rowan copies the bytes into
        // its own arena, so no borrow escapes.
        builder.token(kind.into(), &source[range]);
    }

    builder.finish_node();
    SyntaxNode::new_root(builder.finish())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Round-trip invariant for hand-picked sources.
    ///
    /// `tests/round_trip.rs` exercises the same property over the
    /// full compatibility corpus. The unit tests here cover edge
    /// cases that don't need the corpus to be downloaded.
    fn assert_round_trips(source: &str) {
        let tree = parse_flat(source);
        let reconstructed = tree.text().to_string();
        assert_eq!(
            reconstructed, source,
            "phase-1 flat CST must round-trip byte-identically",
        );
    }

    #[test]
    fn empty_source_round_trips() {
        assert_round_trips("");
    }

    #[test]
    fn whitespace_only_round_trips() {
        assert_round_trips("    \t  ");
    }

    #[test]
    fn bom_round_trips() {
        assert_round_trips("\u{FEFF}2024-01-01 open Assets:Bank\n");
    }

    #[test]
    fn full_directive_round_trips() {
        assert_round_trips(
            "\
2024-01-01 open Assets:Bank USD
2024-01-15 * \"Coffee\"
  Assets:Bank  -5.00 USD
  Expenses:Food
",
        );
    }

    #[test]
    fn line_comment_round_trips() {
        assert_round_trips("; preamble\n2024-01-01 open Assets:Bank\n");
    }

    #[test]
    fn trailing_no_newline_round_trips() {
        // A file that doesn't end with a newline — tests the trailing
        // adapter branch (cursor < source.len() when tokenize ends).
        assert_round_trips("2024-01-01 open Assets:Bank");
    }

    #[test]
    fn root_node_kind_is_source_file() {
        let tree = parse_flat("");
        assert_eq!(tree.kind(), SyntaxKind::SOURCE_FILE);
    }
}
