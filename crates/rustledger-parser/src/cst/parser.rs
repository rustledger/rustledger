//! CST builders: phase 1 flat ([`parse_flat`]) + phase 2.1a/2.1b
//! structured ([`parse_structured`]).
//!
//! Both walk the lossless token stream and emit a `GreenNode` whose
//! `text()` is byte-identical to the input source. They differ in
//! what they wrap:
//!
//! - [`parse_flat`] (phase 1) puts every token as a direct child of
//!   a single `SOURCE_FILE` node. Useful for round-trip-only tests
//!   and the kind-sequence corpus baseline.
//! - [`parse_structured`] recognizes:
//!   - **Phase 2.1a**: 14 single-line directive shapes —
//!     `OPEN`/`CLOSE`/`BALANCE`/`PAD`/`EVENT`/`QUERY`/`NOTE`/
//!     `DOCUMENT`/`PRICE`/`COMMODITY` (dated) +
//!     `PUSHTAG`/`POPTAG`/`PUSHMETA`/`POPMETA` (top-level keyword).
//!   - **Phase 2.1b**: `TRANSACTION` — DATE + `STAR` / `PENDING_KW`
//!     (`!`) / `FLAG` / `TXN_KW`, multi-line scope through the last
//!     indented sub-line (postings, metadata, indented comments).
//!
//!   Each wraps in its specific node kind per the Directive-
//!   Terminator Rule (see [`crate::cst::trivia`]).
//!
//!   Unrecognized lines (`OPTION`/`INCLUDE`/`PLUGIN`/`CUSTOM` — PR
//!   2.3; error-recovery lines) flow through as flat `SOURCE_FILE`
//!   children for now.
//!
//! Phase 2.2 adds `POSTING` / `AMOUNT` / `COST_SPEC` / `META_ENTRY`
//! sub-node structure INSIDE the TRANSACTION + dated directive
//! wrappers; phase 5 deletes `parse_flat` once `parse_structured`
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

/// Parse `source` to a structured lossless CST.
///
/// Recognizes the 14 single-line directive shapes (PR 2.1a) plus
/// `TRANSACTION` (PR 2.1b) and wraps each in its specific node
/// kind. Trivia attaches per the Directive-Terminator Rule.
///
/// Still-unrecognized content (edge directives like
/// `option`/`include`/`plugin`/`custom`, error-recovery lines)
/// passes through as a flat token run under `SOURCE_FILE` — PR
/// 2.3 extends this. Round-trip byte-identical for every UTF-8
/// input; the unrecognized-content path preserves bytes via
/// flat-token emission, just without structural wrapping.
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
        if let Some(directive_kind) = identify_directive(&tokens, i) {
            // Per the Directive-Terminator Rule, pending trivia is
            // FILE-LEADING (SOURCE_FILE direct child) only when NO
            // non-trivia content has appeared yet anywhere in the
            // file — `seen_first_content` tracks that, and it
            // flips on the FIRST non-trivia content we encounter,
            // recognized or unrecognized. Once any content has been
            // seen, subsequent pending trivia is the LEADING trivia
            // of THIS new directive (rule 2) and goes INSIDE the
            // directive node we're about to open.
            if seen_first_content {
                builder.start_node(directive_kind.into());
                emit_tokens(&mut builder, source, std::mem::take(&mut pending_leading));
            } else {
                emit_tokens(&mut builder, source, std::mem::take(&mut pending_leading));
                builder.start_node(directive_kind.into());
            }
            seen_first_content = true;

            // Consume the directive's full multi-line body. The
            // single-line-directive path consumes only `WS META_KEY`
            // (and gated indented comments). TRANSACTION consumes
            // ANY indented sub-line (postings, metadata, comments)
            // until a blank line, non-indented content, or EOF —
            // its body shape is much looser, and PR 2.2 will
            // introduce POSTING / AMOUNT / COST_SPEC / META_ENTRY
            // structure INSIDE the TRANSACTION node.
            i = if directive_kind == SyntaxKind::TRANSACTION {
                emit_transaction_body(&mut builder, source, &tokens, i)
            } else {
                emit_directive_body(&mut builder, source, &tokens, i)
            };
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

/// Consume the header line through its terminator NEWLINE, then
/// keep consuming any indented metadata sub-lines OR indented
/// `;`/`%` comment lines that follow at the same logical block.
///
/// The Directive-Terminator Rule (see `cst::trivia`) declares that
/// a directive carrying metadata spans multiple lines: its last
/// content token is the last content token of its LAST sub-line,
/// not the header. Stopping at the header NEWLINE would orphan
/// metadata under `SOURCE_FILE` and silently violate the rule. PR
/// 2.1a wraps the full multi-line span; PR 2.2 will introduce a
/// `META_ENTRY` sub-node around each `WHITESPACE META_KEY ...
/// NEWLINE` run inside.
///
/// A continuation sub-line is recognized as `WHITESPACE` (the
/// indent) followed by either:
/// - `META_KEY` — the standard metadata sub-line, or
/// - `COMMENT` / `PERCENT_COMMENT` — an indented documentation
///   comment between metadata entries (a common Beancount idiom;
///   keeping it inside the directive prevents subsequent metadata
///   from getting orphaned to `SOURCE_FILE`).
///
/// Anything else — a blank line, a non-indented top-level token,
/// EOF — terminates the directive. Blank-line separated metadata
/// blocks are currently a known limitation: a `\n` between two
/// metadata entries closes the directive and orphans the second
/// entry. PR 2.2's grammar will likely subsume this when it
/// introduces `META_ENTRY` structure.
fn emit_directive_body(
    builder: &mut GreenNodeBuilder<'_>,
    source: &str,
    tokens: &[(SyntaxKind, Range<usize>)],
    mut i: usize,
) -> usize {
    i = emit_through_terminator(builder, source, tokens, i);
    // PROSPECTIVELY scan the upcoming indented-content block for
    // any `WS META_KEY`. If the block contains metadata, any
    // indented comments anywhere in it — including BEFORE the
    // first META_KEY (the "doc-comment-for-the-following-field"
    // idiom) — are continuations that belong inside the directive.
    // If the block contains NO metadata, an indented comment is
    // inter-directive trivia (rule 2) or file-trailing (rule 4)
    // and must not be absorbed. Per-line bookkeeping was tried in
    // v4 but couldn't see the META_KEY that came AFTER a leading
    // comment, so a comment-before-first-metadata silently closed
    // the directive and orphaned the metadata.
    let block_has_meta = upcoming_indented_block_has_meta(tokens, i);
    while is_indented_directive_continuation(tokens, i, block_has_meta) {
        i = emit_through_terminator(builder, source, tokens, i);
    }
    i
}

/// Consume the transaction header through its terminator NEWLINE,
/// then keep consuming ANY indented sub-line (postings, metadata,
/// indented comments — any line starting with `WHITESPACE`
/// followed by a non-`NEWLINE` token).
///
/// Compared with `emit_directive_body` (which only continues on
/// `WS META_KEY` and gated `WS COMMENT`), transactions have a
/// looser body shape: posting lines start with `WS ACCOUNT`,
/// metadata sub-lines with `WS META_KEY`, indented comments with
/// `WS COMMENT`, etc. All belong inside `TRANSACTION` per the
/// multi-line clause of the Directive-Terminator Rule. PR 2.2
/// will introduce `POSTING` / `AMOUNT` / `COST_SPEC` /
/// `META_ENTRY` sub-nodes inside the TRANSACTION wrapper; for
/// now those tokens are flat children.
///
/// Termination: a blank line (NEWLINE alone, or WHITESPACE then
/// NEWLINE), any non-indented top-level token, or EOF.
fn emit_transaction_body(
    builder: &mut GreenNodeBuilder<'_>,
    source: &str,
    tokens: &[(SyntaxKind, Range<usize>)],
    mut i: usize,
) -> usize {
    i = emit_through_terminator(builder, source, tokens, i);
    while is_indented_transaction_body_line(tokens, i) {
        i = emit_through_terminator(builder, source, tokens, i);
    }
    i
}

/// Returns true iff `tokens[i..]` starts an indented line with
/// actual content: `WHITESPACE` followed by ANY non-`NEWLINE`
/// token. A blank line (`NEWLINE` alone, or `WHITESPACE NEWLINE`)
/// or EOF terminates the transaction body.
///
/// **Deliberate divergence from rule 4 of `cst::trivia`:** unlike
/// the single-line-directive body, a TRANSACTION body absorbs an
/// indented trailing `;`-comment AT EOF (file-trailing-ish) into
/// the directive. Rationale: documentation comments interleaved
/// with postings are a Beancount idiom, and forcing the body to
/// "back-track" the last comment if it's trailing would require
/// look-ahead the per-line predicate can't do without extra state.
/// Pinned by `transaction_trailing_indented_comment_at_eof_stays_inside`.
fn is_indented_transaction_body_line(tokens: &[(SyntaxKind, Range<usize>)], i: usize) -> bool {
    if !matches!(tokens.get(i), Some((SyntaxKind::WHITESPACE, _))) {
        return false;
    }
    !matches!(tokens.get(i + 1), Some((SyntaxKind::NEWLINE, _)) | None)
}

/// Scan forward through any indented `WS META_KEY` / `WS COMMENT`
/// / `WS PERCENT_COMMENT` sub-lines starting at `tokens[i..]`,
/// returning `true` iff at least one of them is a metadata
/// (`WS META_KEY`) sub-line. Stops at the first line that is
/// neither metadata nor an indented comment (blank line,
/// non-indented top-level content, EOF).
fn upcoming_indented_block_has_meta(tokens: &[(SyntaxKind, Range<usize>)], mut i: usize) -> bool {
    loop {
        let head = tokens.get(i).map(|(k, _)| *k);
        let next = tokens.get(i + 1).map(|(k, _)| *k);
        match (head, next) {
            (Some(SyntaxKind::WHITESPACE), Some(SyntaxKind::META_KEY)) => return true,
            (
                Some(SyntaxKind::WHITESPACE),
                Some(SyntaxKind::COMMENT | SyntaxKind::PERCENT_COMMENT),
            ) => {
                // Skip past this indented-comment line.
                while i < tokens.len() && tokens[i].0 != SyntaxKind::NEWLINE {
                    i += 1;
                }
                if i >= tokens.len() {
                    return false;
                }
                i += 1; // past the NEWLINE
            }
            _ => return false,
        }
    }
}

/// Returns true iff `tokens[i..]` starts an indented line that
/// CONTINUES the current multi-line directive: `WHITESPACE` (the
/// indent) followed by content that visually "belongs to" the
/// metadata block.
///
/// Recognizes:
/// - `WS META_KEY` — always a continuation regardless of context.
/// - `WS COMMENT` / `WS PERCENT_COMMENT` — a continuation iff the
///   surrounding indented block contains ANY `WS META_KEY` (the
///   `block_has_meta` argument). This prevents absorbing indented
///   comments that follow a header-only directive (rule 2 / rule
///   4 cases) while still keeping documentation comments BEFORE
///   the first metadata entry inside the directive.
///
/// All other shapes (blank `\n`, non-indented content, EOF)
/// terminate the directive.
fn is_indented_directive_continuation(
    tokens: &[(SyntaxKind, Range<usize>)],
    i: usize,
    block_has_meta: bool,
) -> bool {
    if !matches!(tokens.get(i), Some((SyntaxKind::WHITESPACE, _))) {
        return false;
    }
    match tokens.get(i + 1) {
        Some((SyntaxKind::META_KEY, _)) => true,
        Some((SyntaxKind::COMMENT | SyntaxKind::PERCENT_COMMENT, _)) => block_has_meta,
        _ => false,
    }
}

/// Given the token slice and the index of a non-trivia token,
/// decide whether it starts a recognized top-level directive of
/// any kind. Returns the directive `SyntaxKind` if yes, `None`
/// otherwise (OPTION / INCLUDE / PLUGIN / CUSTOM remain
/// unrecognized — PR 2.3 — as does random content that doesn't
/// fit a known shape).
///
/// Beancount directive line shapes recognized here:
///
/// - `DATE WHITESPACE <KEYWORD> ...`: OPEN / CLOSE / BALANCE / PAD
///   / EVENT / QUERY / NOTE / DOCUMENT / PRICE / COMMODITY (PR
///   2.1a)
/// - `DATE WHITESPACE <txn-trigger> ...`: TRANSACTION (PR 2.1b),
///   where `<txn-trigger>` is one of `STAR` / `PENDING_KW` (`!`)
///   / `FLAG` / `HASH` / `TXN_KW` / `STRING` ("implied" txn form
///   with no explicit flag) / single-char `CURRENCY` (ticker
///   letters). Mirrors `parse_dated_directive` in the legacy AST
///   parser at parser.rs:1707-1715.
/// - `<KEYWORD> ...` (no leading date): PUSHTAG / POPTAG /
///   PUSHMETA / POPMETA (PR 2.1a)
fn identify_directive(tokens: &[(SyntaxKind, Range<usize>)], i: usize) -> Option<SyntaxKind> {
    let (head, _) = tokens.get(i)?;
    match *head {
        // Top-level keyword directives — no leading date.
        SyntaxKind::PUSHTAG_KW => Some(SyntaxKind::PUSHTAG_DIRECTIVE),
        SyntaxKind::POPTAG_KW => Some(SyntaxKind::POPTAG_DIRECTIVE),
        SyntaxKind::PUSHMETA_KW => Some(SyntaxKind::PUSHMETA_DIRECTIVE),
        SyntaxKind::POPMETA_KW => Some(SyntaxKind::POPMETA_DIRECTIVE),

        // Dated directives — peek past SAME-LINE whitespace for the
        // keyword. Only WHITESPACE separates content tokens within a
        // directive's header line; a NEWLINE means we crossed into
        // the next line and the DATE/keyword pair is NOT a single
        // directive. Skipping `is_trivia()` (which includes NEWLINE
        // and COMMENT) would wrongly identify malformed `DATE\nopen ...`
        // as OPEN_DIRECTIVE while `emit_through_terminator` only
        // captures the first line, leaving the keyword orphaned.
        SyntaxKind::DATE => {
            let mut j = i + 1;
            while j < tokens.len() && tokens[j].0 == SyntaxKind::WHITESPACE {
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
                // Transaction triggers after the DATE. Beancount
                // accepts:
                // - `*` (STAR) for completed transactions
                // - `!` (PENDING_KW) for incomplete/warning
                // - letter flags P/S/T/C/U/R/M/?/& (FLAG)
                // - `#` (HASH) promoted to a flag in this position
                //   (cf. `Token::is_txn_flag` and the AST parser's
                //   `parse_flag` accepting Hash)
                // - the explicit `txn` keyword (TXN_KW)
                // - a bare STRING ("implied transaction": the AST
                //   parser at parser.rs:1713 dispatches
                //   `Token::String(_)` to `parse_transaction_directive`
                //   with an implied `*` flag; common shorthand
                //   form in real ledgers like
                //   `2024-01-15 "Coffee"`)
                SyntaxKind::STAR
                | SyntaxKind::PENDING_KW
                | SyntaxKind::FLAG
                | SyntaxKind::HASH
                | SyntaxKind::TXN_KW
                | SyntaxKind::STRING => Some(SyntaxKind::TRANSACTION),
                // Single-character CURRENCY: NYSE/NASDAQ-style
                // ticker letters (T, V, F, X, ...) double as
                // transaction flags. The lexer prioritizes
                // CURRENCY over FLAG for single uppercase letters
                // (logos_lexer Currency priority 3); the AST parser
                // (`parse_flag` arm `Token::Currency(s) if s.len() == 1`)
                // mirrors this. We do the same to stay consistent
                // with the established lexer/parser contract.
                SyntaxKind::CURRENCY if tokens[j].1.len() == 1 => Some(SyntaxKind::TRANSACTION),
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
