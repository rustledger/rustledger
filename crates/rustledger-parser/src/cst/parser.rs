//! CST builders: phase 1 flat ([`parse_flat`]) + phase 2.1a
//! structured ([`parse_structured`]).
//!
//! Both walk the lossless token stream and emit a `GreenNode` whose
//! `text()` is byte-identical to the input source. They differ in
//! what they wrap:
//!
//! - [`parse_flat`] (phase 1) puts every token as a direct child of
//!   a single `SOURCE_FILE` node. Useful for round-trip-only tests
//!   and the kind-sequence corpus baseline.
//! - [`parse_structured`] (phase 2.1a) recognizes 14 single-line
//!   directive shapes (OPEN/CLOSE/BALANCE/PAD/EVENT/QUERY/NOTE/
//!   DOCUMENT/PRICE/COMMODITY + PUSHTAG/POPTAG/PUSHMETA/POPMETA)
//!   and wraps each in its specific node kind per the
//!   Directive-Terminator Rule (see [`crate::cst::trivia`]).
//!   Unrecognized lines (TRANSACTION — PR 2.1b; OPTION/INCLUDE/
//!   PLUGIN/CUSTOM — PR 2.3; error-recovery lines) flow through
//!   as flat `SOURCE_FILE` children for now.
//!
//! Phase 2.1b adds TRANSACTION header; phase 2.2 adds posting body
//! structure; phase 5 deletes `parse_flat` once `parse_structured`
//! covers every byte in every corpus file.

use std::ops::Range;

use rowan::GreenNodeBuilder;

use crate::cst::lossless_tokens::lossless_kind_tokens;
use crate::cst::syntax_kind::{SyntaxKind, SyntaxNode};

/// Parse `source` to a flat lossless CST.
///
/// The returned node's text serialization equals `source` byte-for-
/// byte for every UTF-8 input. Every token is a direct child of
/// `SOURCE_FILE`; no structural directive wrapping.
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

/// Parse `source` to a structured lossless CST. Recognizes the 14
/// single-line directive shapes and wraps each in its specific
/// `*_DIRECTIVE` node kind. Trivia attaches per the
/// Directive-Terminator Rule.
///
/// Unrecognized content (TRANSACTION header, edge directives like
/// `option`/`include`/`plugin`/`custom`, error-recovery lines)
/// passes through as a flat token run under `SOURCE_FILE` — phase
/// 2.1b and PR 2.3 extend this. Round-trip byte-identical for
/// every UTF-8 input; the unrecognized-content path preserves
/// bytes via flat-token emission, just without structural wrapping.
#[must_use]
pub fn parse_structured(source: &str) -> SyntaxNode {
    let tokens: Vec<(SyntaxKind, Range<usize>)> = lossless_kind_tokens(source);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::SOURCE_FILE.into());

    let mut pending_leading: Vec<(SyntaxKind, Range<usize>)> = Vec::new();
    let mut seen_first_content = false;
    let mut i = 0;

    while i < tokens.len() {
        let (kind, ref range) = tokens[i];
        if kind.is_trivia() {
            pending_leading.push((kind, range.clone()));
            i += 1;
            continue;
        }

        // Non-trivia at the top level. Identify what kind of line
        // starts here.
        if let Some(directive_kind) = identify_single_line_directive(&tokens, i) {
            // Per the Directive-Terminator Rule, pending trivia is
            // FILE-LEADING (SOURCE_FILE direct child) if this is the
            // first directive we've recognized; otherwise it's
            // LEADING of this new directive (children of the
            // directive node).
            if seen_first_content {
                builder.start_node(directive_kind.into());
                emit_tokens(&mut builder, source, std::mem::take(&mut pending_leading));
            } else {
                emit_tokens(&mut builder, source, std::mem::take(&mut pending_leading));
                builder.start_node(directive_kind.into());
            }
            seen_first_content = true;

            // Consume tokens through the directive's terminator
            // NEWLINE token (rule 1) or until EOF (rule 5).
            i = emit_through_terminator(&mut builder, source, &tokens, i);
            builder.finish_node();
        } else {
            // Unrecognized line. Drain pending trivia + this entire
            // line flat under SOURCE_FILE; phase 2.1b / 2.3 / error
            // recovery will replace this branch. We DO NOT open a
            // node for this content — the current shape is
            // "everything outside a recognized directive is flat
            // under SOURCE_FILE."
            emit_tokens(&mut builder, source, std::mem::take(&mut pending_leading));
            seen_first_content = true;
            i = emit_through_terminator(&mut builder, source, &tokens, i);
        }
    }

    // File-trailing trivia: drain any pending under SOURCE_FILE.
    emit_tokens(&mut builder, source, std::mem::take(&mut pending_leading));

    builder.finish_node();
    SyntaxNode::new_root(builder.finish())
}

/// Emit a sequence of `(kind, range)` tokens into the builder.
fn emit_tokens(
    builder: &mut GreenNodeBuilder<'_>,
    source: &str,
    tokens: impl IntoIterator<Item = (SyntaxKind, Range<usize>)>,
) {
    for (kind, range) in tokens {
        builder.token(kind.into(), &source[range]);
    }
}

/// Consume `tokens[i..]` into `builder` up to and including the
/// next `NEWLINE` token (or EOF). Returns the new index `i`.
fn emit_through_terminator(
    builder: &mut GreenNodeBuilder<'_>,
    source: &str,
    tokens: &[(SyntaxKind, Range<usize>)],
    mut i: usize,
) -> usize {
    while i < tokens.len() {
        let (kind, ref range) = tokens[i];
        builder.token(kind.into(), &source[range.clone()]);
        i += 1;
        if kind == SyntaxKind::NEWLINE {
            break;
        }
    }
    i
}

/// Given the token slice and the index of a non-trivia token,
/// decide whether it starts one of the 14 single-line directives
/// PR 2.1a handles. Returns the directive `SyntaxKind` if yes,
/// `None` otherwise (TRANSACTION, OPTION, INCLUDE, PLUGIN, CUSTOM,
/// or random content that doesn't fit a known shape).
///
/// Beancount directive line shapes recognized here:
///
/// - `DATE WHITESPACE <KEYWORD> ...`: OPEN / CLOSE / BALANCE / PAD
///   / EVENT / QUERY / NOTE / DOCUMENT / PRICE / COMMODITY
/// - `<KEYWORD> ...` (no leading date): PUSHTAG / POPTAG /
///   PUSHMETA / POPMETA
fn identify_single_line_directive(
    tokens: &[(SyntaxKind, Range<usize>)],
    i: usize,
) -> Option<SyntaxKind> {
    let (head, _) = tokens.get(i)?;
    match *head {
        // Top-level keyword directives — no leading date.
        SyntaxKind::PUSHTAG_KW => Some(SyntaxKind::PUSHTAG_DIRECTIVE),
        SyntaxKind::POPTAG_KW => Some(SyntaxKind::POPTAG_DIRECTIVE),
        SyntaxKind::PUSHMETA_KW => Some(SyntaxKind::PUSHMETA_DIRECTIVE),
        SyntaxKind::POPMETA_KW => Some(SyntaxKind::POPMETA_DIRECTIVE),

        // Dated directives — peek past trivia for the keyword.
        SyntaxKind::DATE => {
            let mut j = i + 1;
            while j < tokens.len() && tokens[j].0.is_trivia() {
                j += 1;
            }
            let (next, _) = tokens.get(j)?;
            match *next {
                SyntaxKind::OPEN_KW => Some(SyntaxKind::OPEN_DIRECTIVE),
                SyntaxKind::CLOSE_KW => Some(SyntaxKind::CLOSE_DIRECTIVE),
                SyntaxKind::BALANCE_KW => Some(SyntaxKind::BALANCE_DIRECTIVE),
                SyntaxKind::PAD_KW => Some(SyntaxKind::PAD_DIRECTIVE),
                SyntaxKind::EVENT_KW => Some(SyntaxKind::EVENT_DIRECTIVE),
                SyntaxKind::QUERY_KW => Some(SyntaxKind::QUERY_DIRECTIVE),
                SyntaxKind::NOTE_KW => Some(SyntaxKind::NOTE_DIRECTIVE),
                SyntaxKind::DOCUMENT_KW => Some(SyntaxKind::DOCUMENT_DIRECTIVE),
                SyntaxKind::PRICE_KW => Some(SyntaxKind::PRICE_DIRECTIVE),
                SyntaxKind::COMMODITY_KW => Some(SyntaxKind::COMMODITY_DIRECTIVE),
                // FLAG / TXN_KW → TRANSACTION (PR 2.1b)
                // Anything else: unknown shape.
                _ => None,
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_round_trips(source: &str) {
        let tree = parse_flat(source);
        assert_eq!(tree.text().to_string(), source);
        let structured = parse_structured(source);
        assert_eq!(structured.text().to_string(), source);
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
        let structured = parse_structured("");
        assert_eq!(structured.kind(), SyntaxKind::SOURCE_FILE);
    }
}
