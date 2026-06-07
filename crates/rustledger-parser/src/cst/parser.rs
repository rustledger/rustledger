//! CST builders: phase 1 flat ([`parse_flat`]) + phase 2.1-2.4
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
//!   - **Phase 2.3**: edge directives —
//!     `OPTION_DIRECTIVE` / `INCLUDE_DIRECTIVE` /
//!     `PLUGIN_DIRECTIVE` (top-level keyword) +
//!     `CUSTOM_DIRECTIVE` (dated with arbitrary trailing value
//!     list). Body / metadata shape is identical to PR 2.1a's
//!     dated and standalone-keyword directives — only the header
//!     keyword recognition is new.
//!
//!   - **Phase 2.4**: error recovery — unrecognized / malformed
//!     top-level lines are wrapped in `ERROR_NODE` (terminated by
//!     NEWLINE or EOF per rule 5). Same trivia attachment policy
//!     as recognized directives (rule 2): pending leading trivia
//!     attaches inside the `ERROR_NODE` when it's not the very
//!     first content in the file. AMOUNT now also wraps full
//!     arithmetic expressions (`[sign] (NUMBER | PAREN_EXPR)
//!     ([WS] op [WS] (NUMBER | PAREN_EXPR))* [WS CURRENCY]`),
//!     closing the deferred 2.2c.1 divergence with Python
//!     beancount on `10+5 USD`-shape amounts.
//!
//! Phase 2.2a adds `META_ENTRY` sub-node structure around indented
//! `WS META_KEY ... (NEWLINE | EOF)` sub-lines inside any directive
//! or transaction (per rule 5 of `cst::trivia`, an unterminated
//! final sub-line at EOF still gets wrapped). Phase 2.2b adds
//! `POSTING` sub-node structure around each `WS [(FLAG | STAR |
//! PENDING_KW | HASH | single-char CURRENCY) WS] ACCOUNT ...`
//! posting line inside `TRANSACTION` (the flag arm mirrors
//! `parse_flag` in the legacy AST parser and `identify_directive`'s
//! transaction-trigger arm; single-char `CURRENCY` covers letters
//! like `T`/`V`/`F`/`X` that win the lexer's priority-3 Currency-
//! vs-Flag tie-break). Posting-attached metadata (strictly deeper-
//! indented `META_ENTRY` sub-lines following the posting) becomes a
//! child of that `POSTING`. Phase 2.2c adds `AMOUNT` / `COST_SPEC` /
//! `PRICE_ANNOTATION` inside `POSTING`. Phase 5 deletes
//! `parse_flat` once `parse_structured` covers every byte in
//! every corpus file.

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
/// `TRANSACTION` (PR 2.1b) plus the 4 edge directives `OPTION` /
/// `INCLUDE` / `PLUGIN` / `CUSTOM` (PR 2.3), and wraps each in its
/// specific node kind. Trivia attaches per the Directive-
/// Terminator Rule.
///
/// Unrecognized / malformed top-level lines are wrapped in an
/// `ERROR_NODE` (PR 2.4) — same trivia attachment policy as
/// recognized directives and the same rule-5 unterminated-at-EOF
/// behavior. Round-trip byte-identical for every UTF-8 input.
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
        // starts here. Both branches share the same trivia-
        // attachment + node-emission shape: drain pending trivia
        // around `start_node(kind)` per rule 2 (the FIRST
        // non-trivia content's pending trivia attaches under
        // SOURCE_FILE; subsequent runs attach INSIDE the new
        // node), emit the body, then `finish_node()`.
        let node_kind = identify_directive(&tokens, i).unwrap_or(SyntaxKind::ERROR_NODE);
        if seen_first_content {
            builder.start_node(node_kind.into());
            emit_tokens(&mut builder, source, std::mem::take(&mut pending_leading));
        } else {
            emit_tokens(&mut builder, source, std::mem::take(&mut pending_leading));
            builder.start_node(node_kind.into());
        }
        seen_first_content = true;
        i = match node_kind {
            SyntaxKind::TRANSACTION => emit_transaction_body(&mut builder, source, &tokens, i),
            SyntaxKind::ERROR_NODE => emit_through_terminator(&mut builder, source, &tokens, i),
            // Recognized directive (PR 2.1a / 2.3 single-line shapes):
            // header + optional indented META_ENTRY sub-lines.
            _ => emit_directive_body(&mut builder, source, &tokens, i),
        };
        builder.finish_node();
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

/// Consume one indented sub-line of a directive or transaction
/// body, wrapping it in a `META_ENTRY` node iff it's metadata
/// (i.e., starts `WS META_KEY ...`).
///
/// Phase 2.2a structural wrapping: each metadata sub-line becomes
/// its own `META_ENTRY` node containing the indent `WHITESPACE`,
/// the `META_KEY`, the rest of the line's content tokens, and —
/// when present — the terminator `NEWLINE`. An UNTERMINATED final
/// metadata sub-line at EOF (per rule 5 of `cst::trivia`) is still
/// wrapped: its `META_ENTRY` simply ends at the last content token
/// with no `NEWLINE` child. Token kinds inside the `META_ENTRY`
/// stay flat — phase 3's typed-AST surface will expose `key()` and
/// `value()` accessors that walk these children. Indented
/// `;`-comments flow through as flat children, NOT wrapped in
/// `META_ENTRY`. POSTING lines are recognized earlier in
/// `emit_transaction_body` and never reach this helper.
fn emit_body_sub_line(
    builder: &mut GreenNodeBuilder<'_>,
    source: &str,
    tokens: &[(SyntaxKind, Range<usize>)],
    i: usize,
) -> usize {
    if starts_meta_sub_line(tokens, i) {
        builder.start_node(SyntaxKind::META_ENTRY.into());
        let next = emit_through_terminator(builder, source, tokens, i);
        builder.finish_node();
        next
    } else {
        emit_through_terminator(builder, source, tokens, i)
    }
}

/// Returns true iff `tokens[i..]` starts an indented `WS META_KEY ...`
/// metadata sub-line.
///
/// **Single source of truth** for the `WS + META_KEY` recognition
/// pattern. Used by both `emit_body_sub_line` (decides whether to
/// open a `META_ENTRY` node around the sub-line) and
/// `is_indented_directive_continuation`'s `META_KEY` arm (decides
/// whether the directive body should keep consuming). Routing both
/// call sites through one helper prevents the predicate-pair drift
/// hazard where one widens (e.g. admits a different indent token)
/// without the other and the parser starts consuming sub-lines
/// without wrapping them, or wrapping sub-lines that the body loop
/// never reaches.
fn starts_meta_sub_line(tokens: &[(SyntaxKind, Range<usize>)], i: usize) -> bool {
    matches!(tokens.get(i), Some((SyntaxKind::WHITESPACE, _)))
        && matches!(tokens.get(i + 1), Some((SyntaxKind::META_KEY, _)))
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
/// - any comment-class trivia token (per [`is_comment_token`]: `;`,
///   `%`, `#!`, `#+`) — an indented documentation comment between
///   metadata entries (a common Beancount idiom; keeping it inside
///   the directive prevents subsequent metadata from getting
///   orphaned to `SOURCE_FILE`).
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
        i = emit_body_sub_line(builder, source, tokens, i);
    }
    i
}

/// Consume the transaction header through its terminator NEWLINE,
/// then keep consuming ANY indented sub-line (postings, metadata,
/// indented comments — any line starting with `WHITESPACE`
/// followed by a non-`NEWLINE` token).
///
/// **Phase 2.2b attributes metadata by indent depth.** Beancount
/// distinguishes TRANSACTION-level metadata (at the transaction's
/// standard indent, typically two spaces, before any posting OR
/// interspersed between postings at that same indent) from
/// POSTING-attached metadata (at a DEEPER indent following a
/// posting line). The transaction-level case stays a direct child
/// of `TRANSACTION`; the posting-attached case becomes a child of
/// the preceding `POSTING` node.
///
/// State machine: walk the body lines while tracking the indent
/// width of the most-recently-opened `POSTING` (if any). For each
/// sub-line:
///
/// - **Posting line** (`WS [(FLAG | STAR | PENDING_KW | HASH |
///   single-char CURRENCY) WS] ACCOUNT ...`, full flag set per
///   [`starts_posting_sub_line`]):
///   close the open POSTING if any, then open a new POSTING and
///   consume the line. **Sibling POSTING indents are not required
///   to be uniform**: a transaction with postings at different
///   indent depths produces sibling POSTING nodes whose
///   `open_posting_indent` reflects each one's own header indent.
///   Subsequent metadata then attributes against the
///   most-recently-opened POSTING's indent, which means
///   metadata can attribute differently depending on which
///   posting precedes it. Beancount's grammar uses uniform
///   indentation by convention, so this is a defensive (not
///   primary) shape; pinned by
///   `postings_at_increasing_indents_produce_siblings_and_meta_attributes_to_latest`.
/// - **Metadata sub-line** (`WS META_KEY ...`): if a POSTING is
///   open AND this line's indent is strictly greater than the
///   POSTING's indent, emit the `META_ENTRY` INSIDE the POSTING.
///   Otherwise (no open POSTING, or shallower/equal indent), close
///   any open POSTING and emit the `META_ENTRY` at TRANSACTION level.
/// - **Indented comment line** (`WS COMMENT` / `WS PERCENT_COMMENT`):
///   apply the same indent-attribution rule as metadata. If the
///   comment is strictly more indented than the open POSTING, it
///   stays INSIDE the POSTING (preserving the doc-comment-for-
///   following-posting-metadata idiom — a deeper-indented `; doc`
///   followed by deeper-indented `key: value` should both belong
///   to the same posting). Otherwise close any open POSTING and
///   emit the comment flat at TRANSACTION level (matches the
///   `posting_with_indented_comment_between_postings_terminates_posting`
///   test, where the comment is at the SAME indent as the postings
///   and is therefore transaction-level inter-posting trivia).
/// - **Any other indented content** (`WS STRING`, `WS NUMBER`,
///   unrecognized shape): close any open POSTING and emit the line
///   flat at TRANSACTION level. We don't know what to do with it
///   structurally; flat-passthrough preserves bytes.
///
/// Indent width is measured as the BYTE LENGTH of the leading
/// `WHITESPACE` token — sufficient when the source uses uniform
/// spaces (the standard Beancount convention). **Known divergence
/// from the legacy AST parser**: the legacy lexer's `Indent(N)` /
/// `DeepIndent(N)` variants (`logos_lexer.rs:615-616`) count tabs
/// as 4 spaces, so a tab-indented posting followed by space-
/// indented metadata is compared by VISUAL columns there but by
/// BYTE COUNT here. The two paths can disagree on mixed-indent
/// files. No test corpus file currently triggers the divergence in
/// posting-attached-metadata position; if one shows up, switching
/// `indent_width` to a column-aware count is the fix.
///
/// Compared with `emit_directive_body` (which only continues on
/// `WS META_KEY` and gated `WS COMMENT`), transactions have a
/// looser body shape. PR 2.2c will introduce `AMOUNT` /
/// `COST_SPEC` / `PRICE_ANNOTATION` sub-nodes INSIDE `POSTING`;
/// for now the POSTING's content tokens (account, amount,
/// currency, etc.) stay flat children of POSTING.
///
/// Termination: a blank line (NEWLINE alone, or WHITESPACE then
/// NEWLINE), any non-indented top-level token, or EOF. Any open
/// POSTING is closed before returning.
fn emit_transaction_body(
    builder: &mut GreenNodeBuilder<'_>,
    source: &str,
    tokens: &[(SyntaxKind, Range<usize>)],
    mut i: usize,
) -> usize {
    i = emit_through_terminator(builder, source, tokens, i);

    let mut open_posting_indent: Option<usize> = None;

    while is_indented_transaction_body_line(tokens, i) {
        let sub_line_indent = indent_width(tokens, i);

        if starts_posting_sub_line(tokens, i) {
            if open_posting_indent.is_some() {
                builder.finish_node();
            }
            builder.start_node(SyntaxKind::POSTING.into());
            open_posting_indent = Some(sub_line_indent);
            i = emit_posting_line(builder, source, tokens, i);
        } else if starts_meta_sub_line(tokens, i) {
            close_open_posting_unless_attached(builder, &mut open_posting_indent, sub_line_indent);
            i = emit_body_sub_line(builder, source, tokens, i);
        } else if starts_indented_comment(tokens, i) {
            // Same indent-attribution rule as META_ENTRY: deeper-
            // indented comments stay INSIDE the open POSTING; same-
            // or-shallower-indented comments close the POSTING and
            // emit flat at TRANSACTION level. Preserves the doc-
            // comment-for-following-posting-metadata idiom.
            close_open_posting_unless_attached(builder, &mut open_posting_indent, sub_line_indent);
            i = emit_through_terminator(builder, source, tokens, i);
        } else {
            // Catch-all: any other indented content (e.g., `WS
            // STRING`, `WS NUMBER`, or unrecognized shapes that
            // future error-recovery work might surface). Close any
            // open POSTING and emit flat at TRANSACTION level. PR
            // 2.2c (AMOUNT / COST_SPEC / PRICE_ANNOTATION) lives
            // INSIDE a `POSTING` and reaches the parser through
            // `starts_posting_sub_line`, never this branch — but
            // if a future continuation form (e.g., multi-line
            // postings) gets added, this branch is where it would
            // need to be teased apart from genuine other content.
            if open_posting_indent.is_some() {
                builder.finish_node();
                open_posting_indent = None;
            }
            i = emit_through_terminator(builder, source, tokens, i);
        }
    }

    if open_posting_indent.is_some() {
        builder.finish_node();
    }

    i
}

/// Consume a posting sub-line through its terminator NEWLINE (or
/// EOF), wrapping the `AMOUNT`, `COST_SPEC`, and `PRICE_ANNOTATION`
/// sub-structures inside the already-open `POSTING` node.
///
/// Preconditions: the caller has opened a `POSTING` node and is
/// positioned at the first token of the posting line (`WS`).
/// `starts_posting_sub_line(tokens, i)` must hold.
///
/// Body shape (after the `WS [(flag) WS] ACCOUNT` prefix):
///
/// - `AMOUNT` is the units amount: `[(MINUS | PLUS)] NUMBER
///   [WS CURRENCY]`, or a bare `CURRENCY`. Mirrors the legacy AST
///   `parse_incomplete_amount`: NUMBER + optional CURRENCY, or
///   CURRENCY alone. Wrapping skips intervening `WHITESPACE`
///   between AMOUNT and CURRENCY so the sub-node owns both.
/// - `COST_SPEC` is a bracketed cost annotation, opened by
///   `L_BRACE` (per-unit), `L_BRACE_HASH` (per-unit + total), or
///   `L_DOUBLE_BRACE` (total-only), and closed by the matching
///   `R_BRACE` / `R_DOUBLE_BRACE`. Contents stay flat children;
///   phase 3 typed-AST will surface accessors. Per rule 5 of
///   `cst::trivia`, an unclosed brace at EOF still gets wrapped
///   (the `COST_SPEC` simply has no matching close-brace child).
/// - `PRICE_ANNOTATION` is opened by `AT` (per-unit price) or
///   `AT_AT` (total price). Its trailing amount is recursively
///   wrapped in `AMOUNT` so the structure mirrors the units-amount
///   case: `PRICE_ANNOTATION(AT [WS AMOUNT])`. The typed-AST
///   decodes per-unit-vs-total by the opener token kind, then
///   walks the `AMOUNT` child for the number/currency.
///
/// Canonical order on a well-formed posting line is `ACCOUNT
/// [AMOUNT] [COST_SPEC] [PRICE_ANNOTATION]`. The state machine
/// here is order-independent at the recognition level (each sub-
/// structure wraps when its opener token is encountered), so a
/// malformed posting with reordered or duplicated sub-structures
/// still round-trips byte-identically — duplicates each get their
/// own wrapper.
///
/// Trailing tokens (`WHITESPACE`, `COMMENT`, `PERCENT_COMMENT`,
/// `NEWLINE`) that follow the last recognized sub-structure stay
/// as flat children of `POSTING`.
fn emit_posting_line(
    builder: &mut GreenNodeBuilder<'_>,
    source: &str,
    tokens: &[(SyntaxKind, Range<usize>)],
    mut i: usize,
) -> usize {
    // Emit the indent `WHITESPACE`.
    if let Some((SyntaxKind::WHITESPACE, range)) = tokens.get(i) {
        builder.token(SyntaxKind::WHITESPACE.into(), &source[range.clone()]);
        i += 1;
    }

    // Optional flag (`FLAG` / `STAR` / `PENDING_KW` / `HASH` /
    // single-char `CURRENCY`) + separating `WHITESPACE`. Mirrors
    // `starts_posting_sub_line`'s flag arm.
    let next = tokens.get(i).map(|(k, _)| *k);
    let is_flag = match next {
        Some(SyntaxKind::FLAG | SyntaxKind::STAR | SyntaxKind::PENDING_KW | SyntaxKind::HASH) => {
            true
        }
        Some(SyntaxKind::CURRENCY) => tokens[i].1.len() == 1,
        _ => false,
    };
    if is_flag {
        // Emit flag + WHITESPACE pair.
        if let Some((kind, range)) = tokens.get(i) {
            builder.token((*kind).into(), &source[range.clone()]);
            i += 1;
        }
        if let Some((SyntaxKind::WHITESPACE, range)) = tokens.get(i) {
            builder.token(SyntaxKind::WHITESPACE.into(), &source[range.clone()]);
            i += 1;
        }
    }

    // Emit the required ACCOUNT.
    if let Some((SyntaxKind::ACCOUNT, range)) = tokens.get(i) {
        builder.token(SyntaxKind::ACCOUNT.into(), &source[range.clone()]);
        i += 1;
    }

    // Scan post-ACCOUNT tokens, wrapping AMOUNT / COST_SPEC /
    // PRICE_ANNOTATION as openers appear. Anything else flows as
    // flat children of POSTING.
    while i < tokens.len() {
        let (kind, range) = (tokens[i].0, tokens[i].1.clone());
        if kind == SyntaxKind::NEWLINE {
            builder.token(kind.into(), &source[range]);
            i += 1;
            break;
        }
        if starts_amount(tokens, i) {
            i = emit_amount(builder, source, tokens, i);
            continue;
        }
        if matches!(
            kind,
            SyntaxKind::L_BRACE | SyntaxKind::L_BRACE_HASH | SyntaxKind::L_DOUBLE_BRACE,
        ) {
            i = emit_cost_spec(builder, source, tokens, i);
            continue;
        }
        if matches!(kind, SyntaxKind::AT | SyntaxKind::AT_AT) {
            i = emit_price_annotation(builder, source, tokens, i);
            continue;
        }
        // Flat passthrough (WHITESPACE, COMMENT, PERCENT_COMMENT,
        // anything else).
        builder.token(kind.into(), &source[range]);
        i += 1;
    }

    i
}

/// Returns true iff `tokens[i..]` starts an AMOUNT-shape token
/// run: an arithmetic-expression operand (`NUMBER`, `L_PAREN`, or
/// signed variants), or a bare `CURRENCY`. Used by
/// `emit_posting_line` to gate whether to open an `AMOUNT` wrapper.
fn starts_amount(tokens: &[(SyntaxKind, Range<usize>)], i: usize) -> bool {
    match tokens.get(i).map(|(k, _)| *k) {
        Some(SyntaxKind::NUMBER | SyntaxKind::CURRENCY | SyntaxKind::L_PAREN) => true,
        Some(SyntaxKind::MINUS | SyntaxKind::PLUS) => matches!(
            tokens.get(i + 1).map(|(k, _)| *k),
            Some(SyntaxKind::NUMBER | SyntaxKind::L_PAREN),
        ),
        _ => false,
    }
}

/// Returns true iff `tokens[i]` is an arithmetic operator
/// (`PLUS` / `MINUS` / `STAR` / `SLASH`).
const fn is_arith_op(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::PLUS | SyntaxKind::MINUS | SyntaxKind::STAR | SyntaxKind::SLASH,
    )
}

/// Emit an `AMOUNT` node containing the units amount.
///
/// Recognizes Python beancount's `parse_expr` grammar shape:
/// `[sign] operand ([WS] op [WS] [sign] operand)* [WS CURRENCY]`,
/// where `operand` is `NUMBER` or a parenthesized sub-expression
/// `L_PAREN expr R_PAREN`. Also accepts a bare `CURRENCY`
/// (currency-only amount). Closes the PR 2.2c.1 deferred
/// divergence: `bean-check` accepts `10+5 USD`, `-10+5 USD`, and
/// `-(10+5) USD`; this helper now wraps them as a single `AMOUNT`
/// node containing the full expression tokens flat (sign + operands
/// + operators + currency).
///
/// Stops at the first token that doesn't fit the grammar (e.g.,
/// `L_BRACE` cost-spec opener, `AT` price opener, `NEWLINE`,
/// `COMMENT`, etc.). Returns the new index.
fn emit_amount(
    builder: &mut GreenNodeBuilder<'_>,
    source: &str,
    tokens: &[(SyntaxKind, Range<usize>)],
    mut i: usize,
) -> usize {
    builder.start_node(SyntaxKind::AMOUNT.into());

    // Currency-only amount: bare `CURRENCY` and nothing more.
    if matches!(tokens.get(i).map(|(k, _)| *k), Some(SyntaxKind::CURRENCY))
        && !starts_amount_operand(tokens, i + 1)
    {
        let range = tokens[i].1.clone();
        builder.token(SyntaxKind::CURRENCY.into(), &source[range]);
        i += 1;
        builder.finish_node();
        return i;
    }

    // Optional leading sign.
    if matches!(
        tokens.get(i).map(|(k, _)| *k),
        Some(SyntaxKind::MINUS | SyntaxKind::PLUS),
    ) {
        let (kind, range) = (tokens[i].0, tokens[i].1.clone());
        builder.token(kind.into(), &source[range]);
        i += 1;
    }

    // First operand.
    i = emit_amount_operand(builder, source, tokens, i);

    // Tail: zero or more `[WS] op [WS] [sign] operand` runs. Each
    // iteration commits the WS / op / WS / sign tokens BEFORE
    // dispatching the operand emission. Lookahead-only: do NOT
    // consume any token until the full op-operand prefix is
    // confirmed, so a trailing single WHITESPACE before CURRENCY
    // (the canonical `100 USD` shape) isn't accidentally consumed
    // as a leading op-prefix.
    loop {
        let mut j = i;
        if matches!(tokens.get(j).map(|(k, _)| *k), Some(SyntaxKind::WHITESPACE)) {
            j += 1;
        }
        let Some((op_kind, _)) = tokens.get(j) else {
            break;
        };
        if !is_arith_op(*op_kind) {
            break;
        }
        let op_kind = *op_kind;
        j += 1;
        if matches!(tokens.get(j).map(|(k, _)| *k), Some(SyntaxKind::WHITESPACE)) {
            j += 1;
        }
        // Optional sign before next operand.
        let signed = matches!(
            tokens.get(j).map(|(k, _)| *k),
            Some(SyntaxKind::MINUS | SyntaxKind::PLUS),
        );
        let operand_start = if signed { j + 1 } else { j };
        if !starts_amount_operand(tokens, operand_start) {
            break;
        }
        // Commit tokens [i..j) (WS? op WS?) into AMOUNT.
        while i < j {
            let (kind, range) = (tokens[i].0, tokens[i].1.clone());
            // Sanity: the only non-op tokens we should be committing
            // here are WHITESPACE. The op token itself was already
            // verified.
            debug_assert!(
                kind == SyntaxKind::WHITESPACE || kind == op_kind || is_arith_op(kind),
                "unexpected token kind {kind:?} during op-prefix commit",
            );
            builder.token(kind.into(), &source[range]);
            i += 1;
        }
        if signed {
            let (kind, range) = (tokens[i].0, tokens[i].1.clone());
            builder.token(kind.into(), &source[range]);
            i += 1;
        }
        i = emit_amount_operand(builder, source, tokens, i);
    }

    // Optional trailing CURRENCY, either directly adjacent (`100USD`,
    // `(10+5)USD`) or separated by WHITESPACE (`100 USD`).
    if matches!(tokens.get(i).map(|(k, _)| *k), Some(SyntaxKind::WHITESPACE))
        && matches!(
            tokens.get(i + 1).map(|(k, _)| *k),
            Some(SyntaxKind::CURRENCY),
        )
    {
        let ws_range = tokens[i].1.clone();
        builder.token(SyntaxKind::WHITESPACE.into(), &source[ws_range]);
        i += 1;
        let cur_range = tokens[i].1.clone();
        builder.token(SyntaxKind::CURRENCY.into(), &source[cur_range]);
        i += 1;
    } else if matches!(tokens.get(i).map(|(k, _)| *k), Some(SyntaxKind::CURRENCY)) {
        let cur_range = tokens[i].1.clone();
        builder.token(SyntaxKind::CURRENCY.into(), &source[cur_range]);
        i += 1;
    }

    builder.finish_node();
    i
}

/// Returns true iff `tokens[i]` starts an arithmetic-expression
/// operand (a bare `NUMBER` or a parenthesized sub-expression
/// opener `L_PAREN`). Used by `emit_amount` to gate operand
/// emission inside the op-loop tail.
fn starts_amount_operand(tokens: &[(SyntaxKind, Range<usize>)], i: usize) -> bool {
    matches!(
        tokens.get(i).map(|(k, _)| *k),
        Some(SyntaxKind::NUMBER | SyntaxKind::L_PAREN),
    )
}

/// Emit one operand of an arithmetic expression: either a bare
/// `NUMBER` or a parenthesized `L_PAREN expr R_PAREN` sub-
/// expression. The sub-expression's content tokens stay flat
/// children of the surrounding `AMOUNT` node (no separate
/// `EXPR` / `PAREN_GROUP` wrapping for now). Per rule 5, an
/// unclosed paren at EOF or NEWLINE stops without emitting a
/// closing paren — round-trip preserves bytes.
fn emit_amount_operand(
    builder: &mut GreenNodeBuilder<'_>,
    source: &str,
    tokens: &[(SyntaxKind, Range<usize>)],
    mut i: usize,
) -> usize {
    match tokens.get(i).map(|(k, _)| *k) {
        Some(SyntaxKind::NUMBER) => {
            let range = tokens[i].1.clone();
            builder.token(SyntaxKind::NUMBER.into(), &source[range]);
            i += 1;
        }
        Some(SyntaxKind::L_PAREN) => {
            // Emit opener.
            let range = tokens[i].1.clone();
            builder.token(SyntaxKind::L_PAREN.into(), &source[range]);
            i += 1;
            // Consume balanced content until matching R_PAREN.
            // Track nesting depth so `((1+2))` works. Stop at
            // NEWLINE / EOF (rule 5 unterminated case).
            let mut depth = 1usize;
            while depth > 0 {
                let Some((kind, range)) = tokens.get(i) else {
                    break;
                };
                let (kind, range) = (*kind, range.clone());
                if kind == SyntaxKind::NEWLINE {
                    break;
                }
                builder.token(kind.into(), &source[range]);
                i += 1;
                match kind {
                    SyntaxKind::L_PAREN => depth += 1,
                    SyntaxKind::R_PAREN => depth -= 1,
                    _ => {}
                }
            }
        }
        _ => {}
    }
    i
}

/// Emit a `COST_SPEC` node spanning `L_BRACE` / `L_BRACE_HASH` /
/// `L_DOUBLE_BRACE` ... matching `R_BRACE` / `R_DOUBLE_BRACE`. Per
/// rule 5 (unterminated final directive), an unclosed brace at
/// EOF or hitting a NEWLINE still gets wrapped — the `COST_SPEC`
/// simply has no matching close-brace child. Contents stay flat
/// children of `COST_SPEC`.
fn emit_cost_spec(
    builder: &mut GreenNodeBuilder<'_>,
    source: &str,
    tokens: &[(SyntaxKind, Range<usize>)],
    mut i: usize,
) -> usize {
    builder.start_node(SyntaxKind::COST_SPEC.into());

    // Emit opening brace token.
    if let Some((kind, range)) = tokens.get(i) {
        builder.token((*kind).into(), &source[range.clone()]);
        i += 1;
    }

    // Emit content tokens up to and including the matching close
    // brace, or until NEWLINE / EOF (unclosed-brace case).
    while i < tokens.len() {
        let (kind, range) = (tokens[i].0, tokens[i].1.clone());
        if kind == SyntaxKind::NEWLINE {
            // Unclosed brace: stop BEFORE the NEWLINE so the
            // NEWLINE remains a sibling of COST_SPEC (the
            // posting-line terminator), not a child.
            break;
        }
        builder.token(kind.into(), &source[range]);
        i += 1;
        if matches!(kind, SyntaxKind::R_BRACE | SyntaxKind::R_DOUBLE_BRACE) {
            break;
        }
    }

    builder.finish_node();
    i
}

/// Emit a `PRICE_ANNOTATION` node opened by `AT` or `AT_AT`,
/// optionally followed by `WS` and a nested `AMOUNT`. The nested
/// `AMOUNT` mirrors the units-amount wrapping above; the typed-AST
/// decodes per-unit-vs-total by inspecting the opener token kind
/// (`AT` vs `AT_AT`) and walks the `AMOUNT` child for the number
/// and currency. Avoids absorbing a trailing-only `WHITESPACE`
/// before a comment or `NEWLINE` (only swallows WS that precedes
/// an actual amount start).
fn emit_price_annotation(
    builder: &mut GreenNodeBuilder<'_>,
    source: &str,
    tokens: &[(SyntaxKind, Range<usize>)],
    mut i: usize,
) -> usize {
    builder.start_node(SyntaxKind::PRICE_ANNOTATION.into());

    // Emit the `AT` / `AT_AT` opener.
    if let Some((kind, range)) = tokens.get(i) {
        builder.token((*kind).into(), &source[range.clone()]);
        i += 1;
    }

    // Optional intervening WHITESPACE, but only if an amount
    // follows; trailing-only WS belongs as a sibling of
    // PRICE_ANNOTATION, not a child.
    let ws_then_amount = matches!(tokens.get(i).map(|(k, _)| *k), Some(SyntaxKind::WHITESPACE),)
        && starts_amount(tokens, i + 1);
    if ws_then_amount {
        let ws_range = tokens[i].1.clone();
        builder.token(SyntaxKind::WHITESPACE.into(), &source[ws_range]);
        i += 1;
    }
    if starts_amount(tokens, i) {
        i = emit_amount(builder, source, tokens, i);
    }

    builder.finish_node();
    i
}

/// Close any currently-open POSTING node IF the next sub-line at
/// `sub_line_indent` should NOT be attached to it (i.e., the next
/// sub-line is not strictly more indented than the POSTING). Shared
/// between the `META_ENTRY` and indented-comment branches of
/// `emit_transaction_body` so the two indent-attribution rules
/// cannot drift.
///
/// "Attached" means strictly more indented than the open POSTING.
/// A same-indent or shallower sub-line closes the POSTING; a
/// deeper-indented sub-line leaves it open. Called with
/// `open_posting_indent = None` is a no-op (no POSTING to close).
fn close_open_posting_unless_attached(
    builder: &mut GreenNodeBuilder<'_>,
    open_posting_indent: &mut Option<usize>,
    sub_line_indent: usize,
) {
    let attach = open_posting_indent.is_some_and(|p_indent| sub_line_indent > p_indent);
    if !attach && open_posting_indent.is_some() {
        builder.finish_node();
        *open_posting_indent = None;
    }
}

/// Returns true iff `tokens[i..]` starts a posting sub-line:
/// `WHITESPACE` (the indent) followed by `ACCOUNT`, or by an
/// optional flag (`FLAG` / `STAR` / `PENDING_KW` / `HASH` /
/// single-char `CURRENCY`) plus another `WHITESPACE` then
/// `ACCOUNT`. Mirrors the legacy AST parser's `parse_posting` shape
/// (`parser.rs:866-880`): indent, optional flag, then a required
/// account. The flag set MUST stay in sync with `parse_flag` in the
/// legacy parser (`Token::Star | Pending | Flag(_) | Hash` plus
/// single-char `Currency`) and with `identify_directive`'s
/// transaction-trigger arm above; drift would silently leave
/// HASH-flagged or single-char-CURRENCY-flagged posting lines flat
/// under `TRANSACTION` instead of wrapped in `POSTING`. The single-
/// char `CURRENCY`-as-flag arm exists because the lexer's priority-3
/// Currency-vs-Flag tie-break makes letters like `T`/`V`/`F`/`X`
/// tokenize as `CURRENCY`, but they still function as posting flags
/// by Beancount convention.
fn starts_posting_sub_line(tokens: &[(SyntaxKind, Range<usize>)], i: usize) -> bool {
    if !matches!(tokens.get(i), Some((SyntaxKind::WHITESPACE, _))) {
        return false;
    }
    if matches!(tokens.get(i + 1), Some((SyntaxKind::ACCOUNT, _))) {
        return true;
    }
    let has_flag = match tokens.get(i + 1) {
        Some((
            SyntaxKind::FLAG | SyntaxKind::STAR | SyntaxKind::PENDING_KW | SyntaxKind::HASH,
            _,
        )) => true,
        Some((SyntaxKind::CURRENCY, range)) => range.len() == 1,
        _ => false,
    };
    if !has_flag {
        return false;
    }
    matches!(tokens.get(i + 2), Some((SyntaxKind::WHITESPACE, _)))
        && matches!(tokens.get(i + 3), Some((SyntaxKind::ACCOUNT, _)))
}

/// Byte length of the leading `WHITESPACE` token at `tokens[i]`,
/// or 0 if there is no leading whitespace. Used by
/// `emit_transaction_body` to decide whether a metadata or
/// comment sub-line's indent is strictly deeper than the
/// surrounding POSTING's indent (the posting-attached-metadata /
/// posting-attached-comment rule).
///
/// **Known divergence from the legacy AST parser**: the legacy
/// lexer's `Indent(N)` / `DeepIndent(N)` variants
/// (`logos_lexer.rs:615-616`) count tabs as 4 spaces, but this
/// helper returns raw bytes. Mixed tab+space indentation can
/// therefore produce different attribution between the two paths.
/// Acceptable for now because (a) Beancount idiom is uniform
/// spaces, (b) no corpus file currently triggers the divergence in
/// posting-attached-metadata position, and (c) the CST round-trip
/// is byte-identical regardless of how `indent_width` classifies.
/// If a file shows up, switch to a column-aware count.
fn indent_width(tokens: &[(SyntaxKind, Range<usize>)], i: usize) -> usize {
    match tokens.get(i) {
        Some((SyntaxKind::WHITESPACE, range)) => range.len(),
        _ => 0,
    }
}

/// Returns true iff `kind` is one of the four comment-class trivia
/// token kinds: `COMMENT` (`;`), `PERCENT_COMMENT` (`%`), `SHEBANG`
/// (`#!`), or `EMACS_DIRECTIVE` (`#+`). Mirrors the comment subset
/// of `SyntaxKind::is_trivia()` and is the single source of truth
/// for the three call sites that need to decide whether a token
/// "is a comment" for body-continuation / indent-attribution
/// purposes (`starts_indented_comment`,
/// `upcoming_indented_block_has_meta`,
/// `is_indented_directive_continuation`). A new comment-class
/// token would otherwise require three coordinated edits;
/// `is_comment_token_covers_all_comment_class_trivia` in this
/// module's tests asserts membership stays in sync with `is_trivia`.
///
/// **Known CST/AST divergence**: The legacy AST parser's
/// `parse_posting_metadata` / `parse_transaction_directive` paths
/// in `crates/rustledger-parser/src/parser.rs` only treat
/// `Token::Comment` and `Token::PercentComment` as in-body trivia
/// for transaction / directive bodies. `Token::Shebang` and
/// `Token::EmacsDirective` are processed only at top level
/// (`parse_directive` dispatch). So a deeper-indented `#+STARTUP:
/// overview` between two postings is INSIDE the POSTING for the
/// CST but TERMINATES the transaction for the AST. Phase-isolated
/// in practice: the loader, LSP, validator, query, booking, and
/// CLI all run through the AST path; the only current
/// `parse_structured` consumers are this crate's corpus baseline
/// test and `examples/dump_top_level_directives.rs`. Phase 5
/// deletes `parse_flat` and the AST; that reconciliation should
/// adopt the CST behavior (consistent with `is_trivia()`'s
/// classification of all four comment-class tokens) rather than
/// the AST behavior (an indented comment-class line silently
/// terminating the directive is the surprising outcome).
const fn is_comment_token(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::COMMENT
            | SyntaxKind::PERCENT_COMMENT
            | SyntaxKind::SHEBANG
            | SyntaxKind::EMACS_DIRECTIVE,
    )
}

/// Returns true iff `tokens[i..]` starts an indented comment line:
/// `WHITESPACE` (the indent) followed by a comment-class token (per
/// [`is_comment_token`]). Used by `emit_transaction_body` to apply
/// the same indent-attribution rule to comments that it applies to
/// metadata.
fn starts_indented_comment(tokens: &[(SyntaxKind, Range<usize>)], i: usize) -> bool {
    matches!(tokens.get(i), Some((SyntaxKind::WHITESPACE, _)))
        && matches!(tokens.get(i + 1), Some((k, _)) if is_comment_token(*k))
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

/// Scan forward through any indented `WS META_KEY` sub-lines or
/// `WS <comment>` sub-lines (per [`is_comment_token`]) starting at
/// `tokens[i..]`, returning `true` iff at least one of them is a
/// metadata (`WS META_KEY`) sub-line. Stops at the first line that
/// is neither metadata nor an indented comment (blank line,
/// non-indented top-level content, EOF).
fn upcoming_indented_block_has_meta(tokens: &[(SyntaxKind, Range<usize>)], mut i: usize) -> bool {
    loop {
        let head = tokens.get(i).map(|(k, _)| *k);
        let next = tokens.get(i + 1).map(|(k, _)| *k);
        match (head, next) {
            (Some(SyntaxKind::WHITESPACE), Some(SyntaxKind::META_KEY)) => return true,
            (Some(SyntaxKind::WHITESPACE), Some(k)) if is_comment_token(k) => {
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
/// - `WS <comment>` (per [`is_comment_token`]) — a continuation iff
///   the surrounding indented block contains ANY `WS META_KEY` (the
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
    // The META_KEY arm routes through `starts_meta_sub_line` so the
    // continuation predicate and the wrapping predicate
    // (`emit_body_sub_line`) cannot drift.
    if starts_meta_sub_line(tokens, i) {
        return true;
    }
    if !matches!(tokens.get(i), Some((SyntaxKind::WHITESPACE, _))) {
        return false;
    }
    match tokens.get(i + 1) {
        Some((k, _)) if is_comment_token(*k) => block_has_meta,
        _ => false,
    }
}

/// Given the token slice and the index of a non-trivia token,
/// decide whether it starts a recognized top-level directive of
/// any kind. Returns the directive `SyntaxKind` if yes, `None`
/// otherwise (random content that doesn't fit a known shape — the
/// caller wraps such content in an `ERROR_NODE` per PR 2.4).
///
/// Beancount directive line shapes recognized here:
///
/// - `DATE WHITESPACE <KEYWORD> ...`: OPEN / CLOSE / BALANCE / PAD
///   / EVENT / QUERY / NOTE / DOCUMENT / PRICE / COMMODITY (PR
///   2.1a) + CUSTOM (PR 2.3)
/// - `DATE WHITESPACE <txn-trigger> ...`: TRANSACTION (PR 2.1b),
///   where `<txn-trigger>` is one of `STAR` / `PENDING_KW` (`!`)
///   / `FLAG` / `HASH` / `TXN_KW` / `STRING` ("implied" txn form
///   with no explicit flag) / single-char `CURRENCY` (ticker
///   letters). Mirrors `parse_dated_directive` in the legacy AST
///   parser at parser.rs:1707-1715.
/// - `<KEYWORD> ...` (no leading date): PUSHTAG / POPTAG /
///   PUSHMETA / POPMETA (PR 2.1a) + OPTION / INCLUDE / PLUGIN
///   (PR 2.3)
fn identify_directive(tokens: &[(SyntaxKind, Range<usize>)], i: usize) -> Option<SyntaxKind> {
    let (head, _) = tokens.get(i)?;
    match *head {
        // Top-level keyword directives — no leading date.
        SyntaxKind::PUSHTAG_KW => Some(SyntaxKind::PUSHTAG_DIRECTIVE),
        SyntaxKind::POPTAG_KW => Some(SyntaxKind::POPTAG_DIRECTIVE),
        SyntaxKind::PUSHMETA_KW => Some(SyntaxKind::PUSHMETA_DIRECTIVE),
        SyntaxKind::POPMETA_KW => Some(SyntaxKind::POPMETA_DIRECTIVE),

        // Phase 2.3: edge directives (option / include / plugin).
        // These are top-level keyword directives — like
        // pushtag/poptag/pushmeta/popmeta above — so the same
        // single-line directive body shape applies. Their full
        // header is consumed by `emit_through_terminator`; trailing
        // indented metadata lines (a rare but legal Beancount idiom
        // for option / include / plugin) are absorbed by
        // `emit_directive_body`'s look-ahead, same as the other
        // top-level-keyword directives.
        SyntaxKind::OPTION_KW => Some(SyntaxKind::OPTION_DIRECTIVE),
        SyntaxKind::INCLUDE_KW => Some(SyntaxKind::INCLUDE_DIRECTIVE),
        SyntaxKind::PLUGIN_KW => Some(SyntaxKind::PLUGIN_DIRECTIVE),

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
                // Phase 2.3: CUSTOM is a dated directive with a
                // type-name STRING followed by an arbitrary value
                // list (STRING / ACCOUNT / amount / DATE / CURRENCY
                // / BOOL_TRUE / BOOL_FALSE). The header consumption
                // is identical to the other dated single-line
                // directives; only the value list is open-ended,
                // which is fine for the CST since the trailing
                // tokens stay flat.
                SyntaxKind::CUSTOM_KW => Some(SyntaxKind::CUSTOM_DIRECTIVE),
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

    /// Drift guard: `is_comment_token` and `is_trivia` must agree on
    /// what counts as comment-class trivia. Enforces two invariants:
    ///
    /// 1. `is_trivia() ⊆ is_comment_token ∪ non_comment_trivia`:
    ///    every trivia kind is either a comment or in the explicit
    ///    whitespace-class allow-list. Catches a new lexer-level
    ///    addition to `is_trivia()` that's silently forgotten in
    ///    `is_comment_token`.
    /// 2. `is_comment_token ⊆ is_trivia()`: every kind
    ///    `is_comment_token` says yes to is actually trivia. Catches
    ///    a future edit to `is_comment_token`'s match arm that
    ///    accidentally pulls in a non-trivia content token,
    ///    silently extending indent-attribution to real content
    ///    inside POSTING / directive bodies.
    ///
    /// On failure (1), if the new trivia kind is neither comment-
    /// class nor whitespace-class (e.g., some future
    /// `SECTION_HEADER` that should NOT be absorbed as a
    /// continuation), don't reflexively add it to either set —
    /// revisit whether the body-continuation predicates need a
    /// different abstraction (`is_body_continuation_trivia` or
    /// similar) and propagate the choice to the three call sites.
    #[test]
    fn is_comment_token_covers_all_comment_class_trivia() {
        let non_comment_trivia = [SyntaxKind::BOM, SyntaxKind::WHITESPACE, SyntaxKind::NEWLINE];

        let mut trivia_missed_from_comment: Vec<SyntaxKind> = Vec::new();
        let mut comment_not_trivia: Vec<SyntaxKind> = Vec::new();
        for d in 0u16..=u16::MAX {
            let Ok(kind) = SyntaxKind::try_from(d) else {
                continue;
            };
            // Invariant 1: trivia (minus whitespace allow-list) ⊆ comment.
            if kind.is_trivia() && !non_comment_trivia.contains(&kind) && !is_comment_token(kind) {
                trivia_missed_from_comment.push(kind);
            }
            // Invariant 2: comment ⊆ trivia.
            if is_comment_token(kind) && !kind.is_trivia() {
                comment_not_trivia.push(kind);
            }
        }
        assert!(
            trivia_missed_from_comment.is_empty(),
            "trivia kinds present in is_trivia() but missing from \
             is_comment_token: {trivia_missed_from_comment:?}. Three \
             options: (a) add them to is_comment_token if they are \
             comment-class; (b) extend the non_comment_trivia allow- \
             list in this test if they are whitespace-class; (c) if \
             they are neither, revisit whether the body-continuation \
             predicates need a different abstraction and propagate \
             the decision to the three call sites.",
        );
        assert!(
            comment_not_trivia.is_empty(),
            "is_comment_token claims these kinds are comments but \
             is_trivia() disagrees: {comment_not_trivia:?}. Either \
             add them to is_trivia() (if they really are trivia) or \
             remove them from is_comment_token (if they are content \
             tokens that should not be absorbed as comment \
             continuations).",
        );
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
