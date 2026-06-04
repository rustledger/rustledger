//! Phase 1 flat CST builder: every lossless token as a direct child
//! of a single `SOURCE_FILE` node. Round-trips byte-identically with
//! the input source.
//!
//! Phase 2 will introduce structural nesting (`DIRECTIVE`, `POSTING`,
//! `AMOUNT`, ...) by wrapping runs of these tokens in parent nodes —
//! the byte-preservation property is preserved by construction
//! (rowan's `GreenNodeBuilder` never drops bytes).

use rowan::GreenNodeBuilder;

use crate::cst::lossless_tokens::lossless_kind_tokens;
use crate::cst::syntax_kind::{SyntaxKind, SyntaxNode};

/// Parse `source` to a flat lossless CST. The returned node's text
/// serialization equals `source` byte-for-byte for every UTF-8 input.
#[must_use]
pub fn parse_flat(source: &str) -> SyntaxNode {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::SOURCE_FILE.into());
    for (kind, range) in lossless_kind_tokens(source) {
        builder.token(kind.into(), &source[range]);
    }
    builder.finish_node();
    SyntaxNode::new_root(builder.finish())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_round_trips(source: &str) {
        let tree = parse_flat(source);
        let reconstructed = tree.text().to_string();
        assert_eq!(reconstructed, source);
    }

    #[test]
    fn empty_source() {
        assert_round_trips("");
    }

    #[test]
    fn whitespace_only() {
        assert_round_trips("   \t  ");
    }

    #[test]
    fn bom_round_trips() {
        assert_round_trips("\u{FEFF}2024-01-01 open Assets:Bank\n");
    }

    #[test]
    fn full_directive_round_trips() {
        assert_round_trips(
            "2024-01-01 open Assets:Bank USD\n\
             2024-01-15 * \"Coffee\"\n  \
               Assets:Bank  -5.00 USD\n  \
               Expenses:Food\n",
        );
    }

    #[test]
    fn line_comment_round_trips() {
        assert_round_trips("; preamble\n2024-01-01 open Assets:Bank\n");
    }

    #[test]
    fn no_trailing_newline_round_trips() {
        assert_round_trips("2024-01-01 open Assets:Bank");
    }

    #[test]
    fn root_kind_is_source_file() {
        let tree = parse_flat("");
        assert_eq!(tree.kind(), SyntaxKind::SOURCE_FILE);
    }
}
