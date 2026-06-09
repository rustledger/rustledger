//! Opinionated CST-backed formatter (phase 4.1 of #1262).
//!
//! [`format_source`] is a pure function `&str → String`: it
//! reparses the input into a CST and emits text in one canonical
//! form per AST shape. Two semantically-equivalent inputs produce
//! byte-identical output; idempotence (`f(f(x)) == f(x)`) follows
//! trivially.
//!
//! Replaces the pre-#1262 source-level formatter that took
//! `(source, ParseResult, FormatConfig)` and re-emitted via the
//! AST-driven `rustledger_core::format` path. Typed-directive
//! synthesis (`rustledger_core::format::format_directives`) still
//! lives in `rustledger-core` for callers that build a directive
//! from scratch (e.g., `rledger add`, importer extract, FFI
//! `format.entry`) — that's a different shape of input and is
//! out of scope here.
//!
//! # Typed-directive emit: known coupling
//!
//! The typed-directive path is a two-pass shim: callers run
//! `core::format::format_directives` to get bean-format-style text,
//! then run that text back through [`format_source`] for the
//! canonical pass. This keeps the FINAL byte sequence single-
//! sourced (always emitted by this module), but it means
//! `core::format` is permanently load-bearing as a parser-clean
//! intermediate and every canonical-form rule needs the legacy
//! emitter to produce SOMETHING the new parser accepts.
//!
//! Call sites (`rustledger-ffi-wasi::router::canonical_format_directives`,
//! `rustledger::cmd::add_cmd::canonical_format_directive`,
//! `rustledger::cmd::extract_cmd`) all guard the round-trip with
//! an explicit `parse(&raw)` step that bails on parse errors, so a
//! divergence between the two emitters surfaces as a hard error
//! instead of silently dropping content.
//!
//! The eventual fix is a typed-directive emit path on this module
//! (`format_directive(&Directive) -> String`) that bypasses the
//! source-string round-trip. Tracked in a follow-up issue.
//!
//! # Canonical form (locked in the PR-decision comment on #1262)
//!
//! - Indent inside a directive body: 2 spaces. Tabs converted.
//! - Blank lines between directives: exactly 1.
//! - Blank lines inside a directive: 0.
//! - Number lexical form: thousands separators dropped; user
//!   decimal-place count preserved.
//! - Comment content: verbatim.
//! - Comment positions: normalized to the attachment slot
//!   (header-trailing / inter-directive / body-internal /
//!   posting-trailing).
//! - Cost spec spacing: `{cost CCY}` (no inner padding).
//! - Tag/link order on a transaction header: source order, after
//!   the strings.
//! - Trailing newline at EOF: always exactly one.
//! - Line endings: LF; CRLF inputs normalized.
//! - Leading BOM: dropped.
//!
//! No `FormatConfig` parameter. One canonical form, no knobs.

use crate::cst::ast::{self, AstNode, AstToken, MetaEntry, SourceFile};

/// Pre-computed alignment data for a whole source file.
///
/// Bean-format-style two-axis alignment. The **number field** is a
/// fixed-width slot starting at column `number_col` and `number_width`
/// chars wide, into which each posting's number / arithmetic
/// expression is right-justified. Shorter numbers are left-padded
/// with spaces, so the currency column (right after the field) is
/// uniform across the whole file even when individual numbers have
/// different widths or signs.
///
/// - `number_col`   = INDENT + max(account width with optional `flag `) + 2
/// - `number_width` = max rendered width of any posting's number /
///   arithmetic expression (sign included)
#[derive(Debug, Clone, Copy, Default)]
struct Alignment {
    /// 0-indexed column at which the right-justified number field
    /// starts.
    number_col: usize,
    /// Width of the number field; shorter numbers are left-padded
    /// with spaces so the currency column stays uniform.
    number_width: usize,
}

/// Two-space indent for directive bodies (postings, metadata).
const INDENT: &str = "  ";

/// Format a Beancount source file in opinionated canonical form.
///
/// Reparses internally — callers that already have a CST in hand
/// and want to avoid the double-parse can use [`format_node`].
///
/// Returns canonical text; output always ends with exactly one
/// trailing newline (even for an empty file, where the output is
/// just `"\n"`).
///
/// **Line-ending normalization runs BEFORE parsing.** The lexer
/// does not treat bare `\r` as a line terminator, so a classic-
/// Mac-authored `directive\r…\rdirective\r` would otherwise parse
/// as a single broken directive and the rest of the user's ledger
/// would be silently dropped. We normalize `\r\n` and bare `\r`
/// to `\n` first, then parse — matching the canonical-form
/// promise that line endings are LF-only on output.
#[must_use]
pub fn format_source(source: &str) -> String {
    let (stripped, _had_bom) = crate::bom::strip_leading(source);
    let normalized = crlf_to_lf_outside_strings(stripped);
    let parsed = SourceFile::parse(&normalized);
    format_node(parsed.syntax())
}

/// Like [`format_source`], but returns the parse errors instead
/// of silently formatting around them.
///
/// `format_source` is intentionally infallible — the canonical
/// formatter must still emit *something* for a file the parser
/// could only recover from. Tooling that wants to refuse to
/// rewrite a file with parse errors (the `rledger format` CLI,
/// the LSP `format` handler) previously had to call `parse`
/// out-of-band, inspect `errors`, then call `format_source` on
/// the SAME input — a contract two functions cooperated on
/// implicitly, and the kind of pairing a future caller could
/// easily forget. This helper makes the contract explicit.
///
/// Returns `Ok(formatted)` if and only if `parse(source).errors`
/// would be empty. Otherwise returns the parse errors verbatim,
/// in the same order the parser emitted them.
///
/// # Errors
///
/// Returns `Err(Vec<ParseError>)` containing every parse error
/// the underlying [`parse`](crate::parse) call would surface for
/// `source`. The caller decides whether to abort, render the
/// errors, or fall back to a non-canonical pass.
pub fn try_format_source(source: &str) -> Result<String, Vec<crate::ParseError>> {
    let result = crate::parse(source);
    if !result.errors.is_empty() {
        return Err(result.errors);
    }
    Ok(format_source(source))
}

/// Convert every `\n` line terminator OUTSIDE string literals back
/// to `\r\n`, leaving `\n` characters inside strings (and inside
/// comments… see below) untouched.
///
/// The canonical form emitted by [`format_source`] is LF-only.
/// Editors that round-trip Windows-authored files want to see CRLF
/// echoed back on every line. This helper bridges the two by
/// walking the canonical output with the shared `SourceState`
/// state machine. The walker respects:
///
/// - String literals: bytes pass through verbatim. The user's
///   original line endings inside a multi-line narration / note /
///   document string are preserved.
/// - Line comments (`;`, `%`, `#!`, `#+`): the comment's
///   terminating newline IS a real structural line terminator, so
///   it gets converted to CRLF; bytes inside the comment region
///   (which can include arbitrary characters, notably stray `"`)
///   pass through without flipping the in-string state. `#!` and
///   `#+` open a comment at any column — the lexer's
///   `SHEBANG` / `EMACS_DIRECTIVE` regexes carry no line-start
///   anchor, and the state machine matches that classification.
///
/// The helper lives in this module rather than the LSP crate
/// because its correctness depends on the lexer's `STRING` and
/// comment rules. Keep it co-located with the formatter so a
/// lexer change forces a co-evaluation here.
#[must_use]
pub fn lf_to_crlf_outside_strings(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + s.matches('\n').count());
    // BOM is data, not classification input. We re-prepend it
    // verbatim and let the body start fresh in Code state. The
    // sibling crlf_to_lf_outside_strings does the same so the two
    // walkers handle a leading-BOM file identically.
    let (body, bom) = match s.strip_prefix('\u{FEFF}') {
        Some(rest) => (rest, "\u{FEFF}"),
        None => (s, ""),
    };
    out.push_str(bom);
    let mut chars = body.chars().peekable();
    let mut state = SourceState::Code;
    let mut prev_was_backslash = false;
    while let Some(ch) = chars.next() {
        let peek = chars.peek().copied();
        match state {
            SourceState::InString => out.push(ch),
            SourceState::InComment | SourceState::Code => {
                if ch == '\n' {
                    out.push_str("\r\n");
                } else {
                    out.push(ch);
                }
            }
        }
        state = advance_source_state(ch, peek, state, &mut prev_was_backslash);
    }
    out
}

/// Render typed Beancount `Directive`s in the canonical form
/// emitted by [`format_source`].
///
/// Two-pass pipeline:
///
/// 1. Synthesize a source string via the typed-directive emitter
///    in `rustledger_core::format::format_directives`. That
///    emitter is `Directive → text`; its output is bean-format-
///    style, parser-clean, and used here purely as an
///    intermediate.
/// 2. Re-parse the synthesized text. If the legacy emitter
///    produced something the new parser cannot fully accept,
///    return [`CanonicalizeError::ReparseFailed`] rather than
///    silently emitting the recoverable subset — that silent-loss
///    failure mode is what the deleted `format_compat` test used
///    to guard against.
/// 3. Run the re-parsed text through [`format_source`] for the
///    canonical pass.
///
/// Single source of truth for the synthesize → canonicalize
/// shim. Every consumer that builds a typed `Directive` in memory
/// and wants canonical text — `rledger add`, `rledger extract`,
/// the FFI `format.entry` / `format.entries` endpoints — should
/// call this function instead of reinventing the pipeline.
pub fn canonicalize_directives<'a, I>(
    directives: I,
    config: &rustledger_core::format::FormatConfig,
) -> Result<String, CanonicalizeError>
where
    I: IntoIterator<Item = &'a rustledger_core::Directive>,
    I::IntoIter: ExactSizeIterator,
{
    // Take the count off the ExactSizeIterator without
    // collecting — the legacy emitter only walks the iterator
    // once, so we don't need to materialize a Vec just to know
    // how many directives the caller passed.
    let iter = directives.into_iter();
    let input_count = iter.len();
    let raw = rustledger_core::format::format_directives(iter, config);
    let parse_result = crate::parse(&raw);
    if !parse_result.errors.is_empty() {
        return Err(CanonicalizeError::ReparseFailed {
            errors: parse_result
                .errors
                .iter()
                .map(ToString::to_string)
                .collect(),
        });
    }
    // Count check covers the only Directive variants we have
    // today (12, all of which surface on parse_result.directives).
    // If a future `rustledger_core::Directive` variant is added
    // that the parser routes to a different `ParseResult`
    // collection (e.g., a typed Pushtag whose legacy text the
    // parser puts on a `pragmas` field), this check needs to
    // include that field too — otherwise a perfectly healthy
    // round-trip would always report DirectiveCountMismatch. The
    // compile-time `_directive_variant_fixture_coverage` match
    // pins the variant set we're committed to here; any new
    // variant breaks that match and surfaces this same
    // maintenance need.
    let reparsed_count = parse_result.directives.len();
    if reparsed_count != input_count {
        return Err(CanonicalizeError::DirectiveCountMismatch {
            input: input_count,
            reparsed: reparsed_count,
        });
    }
    Ok(format_source(&raw))
}

/// Error returned by [`canonicalize_directives`].
///
/// Marked `#[non_exhaustive]` so that adding a future variant
/// (e.g. a `CanonicalizationTimeout` for an async path, or a new
/// guard for a future canonical-form rule) does not become a
/// SemVer-breaking change. Consumers must use a `_ => …` arm.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum CanonicalizeError {
    /// The synthesized intermediate failed to re-parse cleanly.
    /// Carries the rendered error messages so callers can surface
    /// a diagnostic; the source text itself is not retained
    /// because it's an internal intermediate the caller has no
    /// control over.
    ReparseFailed {
        /// One rendered message per parse error from the
        /// intermediate text. Capped at the parser's own error
        /// limit so this field is bounded.
        errors: Vec<String>,
    },
    /// The synthesized intermediate parsed cleanly but produced a
    /// different directive count than the input. This indicates
    /// the legacy emitter and the new parser disagree on what
    /// constitutes a directive — typically a future
    /// `rustledger_core::Directive` variant whose legacy text the
    /// CST parser silently swallows as comments / error-recovery
    /// trivia. Without this guard, the call would round-trip to
    /// truncated text with no error returned.
    DirectiveCountMismatch {
        /// Number of directives the caller passed in.
        input: usize,
        /// Number of directives the parser recovered from the
        /// synthesized text.
        reparsed: usize,
    },
}

impl std::fmt::Display for CanonicalizeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ReparseFailed { errors } => {
                let preview: Vec<&str> = errors.iter().take(3).map(String::as_str).collect();
                write!(
                    f,
                    "canonical formatter failed to re-parse the synthesized \
                     directive text ({} error(s)): {}",
                    errors.len(),
                    preview.join("; ")
                )
            }
            Self::DirectiveCountMismatch { input, reparsed } => write!(
                f,
                "the canonical formatter could not emit {input} directive(s) \
                 without loss ({reparsed} survived the round-trip). This is \
                 an rledger bug; please report it with the input directives.",
            ),
        }
    }
}

impl std::error::Error for CanonicalizeError {}

/// Replace CRLF and bare-CR line terminators with LF, but ONLY
/// outside string literals.
///
/// String literals (`"…"`) can contain raw `\r` and `\n` per the
/// lexer's `STRING` rule; folding CR inside a string would mutate
/// the user's data. Uses the shared `SourceState` state machine
/// to track string / comment boundaries.
///
/// Cheap fast path: if the input contains no `\r`, returns the
/// source slice borrowed (no allocation). Used by
/// [`format_source`] before parsing so the lexer never has to see
/// legacy line endings. Exposed publicly under [`crlf_to_lf_outside_strings`]
/// for tooling (CLI `--diff`, format-equivalence checks) that
/// needs the same string-aware normalization.
pub fn crlf_to_lf_outside_strings(src: &str) -> std::borrow::Cow<'_, str> {
    if !src.contains('\r') {
        return std::borrow::Cow::Borrowed(src);
    }
    // Re-prepend the BOM verbatim and let the body start fresh in
    // Code state. The state machine no longer needs line-start
    // tracking — the lexer's `SHEBANG` / `EMACS_DIRECTIVE` regexes
    // have no line-start anchor, so `#!`/`#+` open a comment at
    // any column, and the state machine mirrors that.
    let (body, bom) = match src.strip_prefix('\u{FEFF}') {
        Some(rest) => (rest, "\u{FEFF}"),
        None => (src, ""),
    };
    let mut out = String::with_capacity(src.len());
    out.push_str(bom);
    let mut chars = body.chars().peekable();
    let mut state = SourceState::Code;
    let mut prev_was_backslash = false;
    while let Some(ch) = chars.next() {
        let peek = chars.peek().copied();
        match state {
            SourceState::InString => out.push(ch),
            _ => {
                if ch == '\r' {
                    out.push('\n');
                    if peek == Some('\n') {
                        chars.next();
                    }
                } else {
                    out.push(ch);
                }
            }
        }
        state = advance_source_state(ch, peek, state, &mut prev_was_backslash);
    }
    std::borrow::Cow::Owned(out)
}

/// `true` iff `src` contains at least one `\r` byte OUTSIDE a
/// string literal — i.e. the byte sequence the canonical
/// formatter would fold to `\n` via
/// [`crlf_to_lf_outside_strings`].
///
/// This is the explicit predicate companion to the Cow return of
/// [`crlf_to_lf_outside_strings`]. Tooling that only needs to
/// know whether the fold would change bytes (the CLI `--diff`
/// "CR-bearing line endings folded" cause line, the LSP
/// did-the-formatter-touch-this guard) should call this instead
/// of matching on `Cow::Owned`, which conflates allocation with
/// semantic change. A future optimization that pre-allocated the
/// Cow even on a no-op fold would silently invert that
/// match-on-Cow guard; this predicate keeps the question
/// answered by the bytes, not by allocation behavior.
#[must_use]
pub fn cr_outside_strings_present(src: &str) -> bool {
    if !src.contains('\r') {
        return false;
    }
    let body = src.strip_prefix('\u{FEFF}').unwrap_or(src);
    let mut chars = body.chars().peekable();
    let mut state = SourceState::Code;
    let mut prev_was_backslash = false;
    while let Some(ch) = chars.next() {
        let peek = chars.peek().copied();
        if matches!(state, SourceState::Code | SourceState::InComment) && ch == '\r' {
            return true;
        }
        state = advance_source_state(ch, peek, state, &mut prev_was_backslash);
    }
    false
}

/// Per-character walker state for line-ending normalization passes
/// that must respect string-literal and comment boundaries.
///
/// Used by both line-ending helpers: a flat `is_in_string` boolean
/// is not enough because a quote character inside a `;`/`%` /
/// `#!` / `#+` comment is data, not a string delimiter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SourceState {
    /// In normal code. `"` opens a string; `;` / `%` / `#!` /
    /// `#+` opens a comment; everything else is just bytes.
    Code,
    /// Inside `"…"`. Bytes pass through; an unescaped `"` exits.
    InString,
    /// Inside `;…\n`, `%…\n`, `#!…\n`, or `#+…\n`. Bytes pass
    /// through until LF/CR.
    InComment,
}

/// One-step state transition shared by both line-ending helpers.
///
/// Returns the state AFTER consuming `ch`. The string-escape
/// bookkeeping (`prev_was_backslash`) updates in place. Comment
/// opener detection covers all four line-comment lexemes: `;` and
/// `%` open a comment unconditionally; `#!` and `#+` open one at
/// any column — the lexer's `#![^\n\r]*` / `#\+[^\n\r]*` regexes
/// have NO line-start anchor, so a mid-line `#!` or `#+` is still
/// a `SHEBANG` / `EMACS_DIRECTIVE` token. A `#` followed by
/// anything else is a `TAG` / `HASH` token, not a comment.
const fn advance_source_state(
    ch: char,
    peek: Option<char>,
    state: SourceState,
    prev_was_backslash: &mut bool,
) -> SourceState {
    match state {
        SourceState::InString => {
            let is_close = ch == '"' && !*prev_was_backslash;
            *prev_was_backslash = ch == '\\' && !*prev_was_backslash;
            if is_close {
                SourceState::Code
            } else {
                SourceState::InString
            }
        }
        SourceState::InComment => {
            if matches!(ch, '\n' | '\r') {
                SourceState::Code
            } else {
                SourceState::InComment
            }
        }
        SourceState::Code => {
            let is_hash_line_comment = ch == '#' && matches!(peek, Some('!' | '+'));
            if ch == '"' {
                *prev_was_backslash = false;
                SourceState::InString
            } else if matches!(ch, ';' | '%') || is_hash_line_comment {
                SourceState::InComment
            } else {
                SourceState::Code
            }
        }
    }
}

/// Format a `SOURCE_FILE` syntax node in opinionated canonical form.
///
/// The bare-node entry for callers that already parsed the CST
/// (typically LSP formatting providers). Output rules are the
/// same as [`format_source`].
#[must_use]
pub fn format_node(node: &crate::SyntaxNode) -> String {
    let mut out = String::new();
    let source_file =
        SourceFile::cast(node.clone()).expect("format_node called on non-SOURCE_FILE node");
    let alignment = compute_alignment(&source_file);
    // Walk every direct child in source order so file-level comments
    // (file-leading per phase-2.0 trivia attachment, plus file-
    // trailing) interleave correctly with directives. Inter-directive
    // and same-line trailing comments live INSIDE the next/owning
    // directive and surface from `emit_directive`'s leading-trivia
    // pass.
    //
    // Blank-line policy at the top level: insert exactly one blank
    // line BEFORE a directive iff the previously emitted item was
    // also a directive. Adjacent file-level comments stay tight as
    // a group (so a `; ====\n; HEADER\n; ====` section header keeps
    // its visual grouping), and a comment group sitting against a
    // directive on either side stays flush.
    let mut prev_was_directive = false;
    for el in source_file.syntax().children_with_tokens() {
        match el {
            rowan::NodeOrToken::Node(n) => {
                let Some(directive) = ast::Directive::cast(n) else {
                    continue;
                };
                if prev_was_directive {
                    out.push('\n');
                }
                emit_directive(&directive, alignment, &mut out);
                prev_was_directive = true;
            }
            rowan::NodeOrToken::Token(t) => {
                if matches!(
                    t.kind(),
                    crate::SyntaxKind::COMMENT
                        | crate::SyntaxKind::PERCENT_COMMENT
                        | crate::SyntaxKind::SHEBANG
                        | crate::SyntaxKind::EMACS_DIRECTIVE
                ) {
                    out.push_str(t.text().trim_end_matches(['\n', '\r']));
                    out.push('\n');
                    prev_was_directive = false;
                }
            }
        }
    }
    if !out.ends_with('\n') {
        out.push('\n');
    }
    out
}

/// Pre-pass: walk every posting in the file, take max LHS width
/// (account + optional `flag `) and max number-text width, and
/// derive the file-wide alignment columns from them.
fn compute_alignment(sf: &SourceFile) -> Alignment {
    let mut max_lhs: usize = 0;
    let mut max_num: usize = 0;
    let mut any_posting = false;
    for directive in sf.directives() {
        let ast::Directive::Transaction(t) = directive else {
            continue;
        };
        for child in t.syntax().children() {
            let Some(p) = ast::Posting::cast(child) else {
                continue;
            };
            any_posting = true;
            let mut lhs = 0usize;
            if let Some(flag) = p.flag() {
                lhs += flag.text().chars().count() + 1; // `! ` etc.
            }
            if let Some(account) = p.account() {
                lhs += account.text().chars().count();
            }
            max_lhs = max_lhs.max(lhs);

            if let Some(amt) = p.amount() {
                let w = amount_value_width(&amt);
                max_num = max_num.max(w);
            }
        }
    }
    if !any_posting {
        return Alignment::default();
    }
    // 2 spaces between the longest account end and the number field,
    // matching the conventional Beancount layout.
    Alignment {
        number_col: INDENT.len() + max_lhs + 2,
        number_width: max_num,
    }
}

/// Width of the rendered number / arithmetic-expression text of
/// an amount, EXCLUDING the trailing currency. Sign (if any) is
/// included. Used for the file-wide right-justify pre-pass and
/// for the per-posting padding math in [`emit_posting`].
fn amount_value_width(amt: &ast::Amount) -> usize {
    amount_value_text(amt).chars().count()
}

/// Render an amount's value portion (number or arithmetic
/// expression) as a string, EXCLUDING the trailing currency.
/// Mirrors the value half of [`format_amount`].
fn amount_value_text(amt: &ast::Amount) -> String {
    let mut buf = String::new();
    if amt.is_arithmetic() {
        emit_amount_subnode_expression(amt.syntax(), &mut buf);
        return buf;
    }
    if let Some(sign) = amt.sign()
        && sign.is_minus()
    {
        buf.push('-');
    }
    if let Some(n) = amt.number() {
        buf.push_str(&canonical_number(n.text()));
    }
    buf
}

fn emit_directive(d: &ast::Directive, align: Alignment, out: &mut String) {
    // Leading inter-directive trivia: COMMENT tokens that sit
    // BEFORE the directive's first content token. Per phase-2.0
    // trivia attachment, these live inside the directive's syntax
    // node — emit them as their own lines BEFORE the canonical
    // content.
    emit_leading_comments(d.syntax(), out);

    // Capture an optional same-line trailing comment so we can
    // splice it back in immediately before the directive's
    // terminating NEWLINE — see the comment-aware emit loop at
    // the bottom of this function.
    let trailing = collect_trailing_comment(d.syntax());

    let len_before = out.len();
    match d {
        ast::Directive::Open(d) => emit_open(d, out),
        ast::Directive::Close(d) => emit_close(d, out),
        ast::Directive::Commodity(d) => emit_commodity(d, out),
        ast::Directive::Note(d) => emit_note(d, out),
        ast::Directive::Event(d) => emit_event(d, out),
        ast::Directive::Query(d) => emit_query(d, out),
        ast::Directive::Pad(d) => emit_pad(d, out),
        ast::Directive::Document(d) => emit_document(d, out),
        ast::Directive::Price(d) => emit_price(d, out),
        ast::Directive::Balance(d) => emit_balance(d, out),
        ast::Directive::Custom(d) => emit_custom(d, out),
        ast::Directive::Option(d) => emit_option(d, out),
        ast::Directive::Include(d) => emit_include(d, out),
        ast::Directive::Plugin(d) => emit_plugin(d, out),
        ast::Directive::Pushtag(d) => emit_pushtag(d, out),
        ast::Directive::Poptag(d) => emit_poptag(d, out),
        ast::Directive::Pushmeta(d) => emit_pushmeta(d, out),
        ast::Directive::Popmeta(d) => emit_popmeta(d, out),
        ast::Directive::Transaction(d) => emit_transaction(d, align, out),
    }
    // Splice the same-line trailing comment in: find the FIRST '\n'
    // after `len_before` (= end of the directive's header line in
    // the emitted bytes) and insert `" ; comment"` before it. For
    // single-line directives the first '\n' is also the only one
    // and this lands the comment on the directive line. For multi-
    // line transactions it lands the comment on the header line
    // (where the source had it), not after the body.
    if let Some(c) = trailing
        && let Some(newline_rel) = out[len_before..].find('\n')
    {
        let insert_at = len_before + newline_rel;
        let mut splice = String::with_capacity(c.len() + 1);
        splice.push(' ');
        splice.push_str(&c);
        out.insert_str(insert_at, &splice);
    }
}

/// Walk the directive's direct-child tokens until the first
/// non-trivia token, emitting each `COMMENT` (and `PERCENT_COMMENT`)
/// on its own line. Whitespace and newlines in the leading region
/// are ignored — the canonical form controls inter-directive
/// blank-line spacing separately.
fn emit_leading_comments(node: &crate::SyntaxNode, out: &mut String) {
    for el in node.children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            break;
        };
        match t.kind() {
            crate::SyntaxKind::COMMENT | crate::SyntaxKind::PERCENT_COMMENT => {
                out.push_str(t.text().trim_end_matches(['\n', '\r']));
                out.push('\n');
            }
            crate::SyntaxKind::WHITESPACE | crate::SyntaxKind::NEWLINE => {}
            _ => break,
        }
    }
}

/// Return the directive's same-line trailing comment (if any) —
/// the COMMENT token that appears between the LAST non-trivia
/// content token and the directive-terminating NEWLINE on the
/// header line. Returns the verbatim comment text (no trailing
/// newline).
fn collect_trailing_comment(node: &crate::SyntaxNode) -> Option<String> {
    // Find the directive-header terminating NEWLINE: the FIRST
    // direct-child NEWLINE that follows at least one non-trivia
    // content token. (For single-line directives there's only one
    // NEWLINE; for transactions the header line is the first
    // NEWLINE, after which postings/metadata follow.)
    let mut header_nl_idx: Option<usize> = None;
    let mut saw_content = false;
    let tokens: Vec<crate::SyntaxToken> = node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .collect();
    for (i, t) in tokens.iter().enumerate() {
        let k = t.kind();
        if k == crate::SyntaxKind::NEWLINE && saw_content {
            header_nl_idx = Some(i);
            break;
        }
        if !matches!(
            k,
            crate::SyntaxKind::WHITESPACE
                | crate::SyntaxKind::NEWLINE
                | crate::SyntaxKind::COMMENT
                | crate::SyntaxKind::PERCENT_COMMENT
        ) {
            saw_content = true;
        }
    }
    // EOF-without-newline fallback: if there is no header-
    // terminating NEWLINE, the directive runs to the end of the
    // file. Scan from the LAST token instead. A `?` early-return
    // here previously dropped same-line trailing comments at the
    // final line of a file that lacked a trailing newline, e.g.
    // `2024-01-15 open Assets:A ; trailing` (no `\n`). The
    // canonical formatter restores the trailing newline, but the
    // comment was already gone.
    let nl_idx = header_nl_idx.unwrap_or(tokens.len());
    // Scan backwards from the header NEWLINE (or EOF): the
    // trailing comment is the last COMMENT before the NEWLINE
    // separated only by WHITESPACE.
    for i in (0..nl_idx).rev() {
        let k = tokens[i].kind();
        if matches!(
            k,
            crate::SyntaxKind::COMMENT | crate::SyntaxKind::PERCENT_COMMENT
        ) {
            return Some(tokens[i].text().to_string());
        }
        if k != crate::SyntaxKind::WHITESPACE {
            return None;
        }
    }
    None
}

// ---- Single-line directives ------------------------------------

fn emit_open(d: &ast::OpenDirective, out: &mut String) {
    let date = d.date().map(|t| t.text().to_string()).unwrap_or_default();
    let account = d
        .account()
        .map(|t| t.text().to_string())
        .unwrap_or_default();
    out.push_str(&date);
    out.push_str(" open ");
    out.push_str(&account);
    for currency in d.currencies() {
        out.push(' ');
        out.push_str(currency.text());
    }
    if let Some(booking) = d.booking_method() {
        // `booking.text()` includes the surrounding quotes.
        out.push(' ');
        out.push_str(booking.text());
    }
    out.push('\n');
    emit_meta_entries_of(d.syntax(), out);
}

fn emit_close(d: &ast::CloseDirective, out: &mut String) {
    let date = d.date().map(|t| t.text().to_string()).unwrap_or_default();
    let account = d
        .account()
        .map(|t| t.text().to_string())
        .unwrap_or_default();
    out.push_str(&date);
    out.push_str(" close ");
    out.push_str(&account);
    out.push('\n');
    emit_meta_entries_of(d.syntax(), out);
}

fn emit_commodity(d: &ast::CommodityDirective, out: &mut String) {
    let date = d.date().map(|t| t.text().to_string()).unwrap_or_default();
    let currency = d
        .currency()
        .map(|t| t.text().to_string())
        .unwrap_or_default();
    out.push_str(&date);
    out.push_str(" commodity ");
    out.push_str(&currency);
    out.push('\n');
    emit_meta_entries_of(d.syntax(), out);
}

fn emit_note(d: &ast::NoteDirective, out: &mut String) {
    let date = d.date().map(|t| t.text().to_string()).unwrap_or_default();
    let account = d
        .account()
        .map(|t| t.text().to_string())
        .unwrap_or_default();
    let text = d.text().map(|s| s.text().to_string()).unwrap_or_default();
    out.push_str(&date);
    out.push_str(" note ");
    out.push_str(&account);
    out.push(' ');
    out.push_str(&text);
    out.push('\n');
    emit_meta_entries_of(d.syntax(), out);
}

fn emit_event(d: &ast::EventDirective, out: &mut String) {
    let date = d.date().map(|t| t.text().to_string()).unwrap_or_default();
    let event_type = d
        .event_type()
        .map(|s| s.text().to_string())
        .unwrap_or_default();
    let value = d.value().map(|s| s.text().to_string()).unwrap_or_default();
    out.push_str(&date);
    out.push_str(" event ");
    out.push_str(&event_type);
    out.push(' ');
    out.push_str(&value);
    out.push('\n');
    emit_meta_entries_of(d.syntax(), out);
}

fn emit_query(d: &ast::QueryDirective, out: &mut String) {
    let date = d.date().map(|t| t.text().to_string()).unwrap_or_default();
    let name = d.name().map(|s| s.text().to_string()).unwrap_or_default();
    let query = d.query().map(|s| s.text().to_string()).unwrap_or_default();
    out.push_str(&date);
    out.push_str(" query ");
    out.push_str(&name);
    out.push(' ');
    out.push_str(&query);
    out.push('\n');
    emit_meta_entries_of(d.syntax(), out);
}

fn emit_pad(d: &ast::PadDirective, out: &mut String) {
    let date = d.date().map(|t| t.text().to_string()).unwrap_or_default();
    let target = d
        .target_account()
        .map(|t| t.text().to_string())
        .unwrap_or_default();
    let source = d
        .source_account()
        .map(|t| t.text().to_string())
        .unwrap_or_default();
    out.push_str(&date);
    out.push_str(" pad ");
    out.push_str(&target);
    out.push(' ');
    out.push_str(&source);
    out.push('\n');
    emit_meta_entries_of(d.syntax(), out);
}

fn emit_document(d: &ast::DocumentDirective, out: &mut String) {
    let date = d.date().map(|t| t.text().to_string()).unwrap_or_default();
    let account = d
        .account()
        .map(|t| t.text().to_string())
        .unwrap_or_default();
    let path = d.path().map(|s| s.text().to_string()).unwrap_or_default();
    out.push_str(&date);
    out.push_str(" document ");
    out.push_str(&account);
    out.push(' ');
    out.push_str(&path);
    // Trailing TAG / LINK tokens — typed AST has no accessor, so
    // walk direct-child tokens until the first NEWLINE.
    for el in d.syntax().children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        match t.kind() {
            crate::SyntaxKind::NEWLINE => break,
            crate::SyntaxKind::TAG | crate::SyntaxKind::LINK => {
                out.push(' ');
                out.push_str(t.text());
            }
            _ => {}
        }
    }
    out.push('\n');
    emit_meta_entries_of(d.syntax(), out);
}

fn emit_price(d: &ast::PriceDirective, out: &mut String) {
    let date = d.date().map(|t| t.text().to_string()).unwrap_or_default();
    let base = d
        .base_currency()
        .map(|t| t.text().to_string())
        .unwrap_or_default();
    let quote = d
        .quote_currency()
        .map(|t| t.text().to_string())
        .unwrap_or_default();
    out.push_str(&date);
    out.push_str(" price ");
    out.push_str(&base);
    out.push(' ');
    emit_amount_expression(d.syntax(), out);
    out.push(' ');
    out.push_str(&quote);
    out.push('\n');
    emit_meta_entries_of(d.syntax(), out);
}

fn emit_balance(d: &ast::BalanceDirective, out: &mut String) {
    let date = d.date().map(|t| t.text().to_string()).unwrap_or_default();
    let account = d
        .account()
        .map(|t| t.text().to_string())
        .unwrap_or_default();
    let currency = d
        .currency()
        .map(|t| t.text().to_string())
        .unwrap_or_default();
    out.push_str(&date);
    out.push_str(" balance ");
    out.push_str(&account);
    out.push(' ');
    emit_amount_expression(d.syntax(), out);
    out.push(' ');
    out.push_str(&currency);
    // Optional `~ tolerance [CCY]` — walk raw tokens.
    if let Some((tolerance, tol_currency)) = balance_tolerance(d.syntax()) {
        out.push_str(" ~ ");
        out.push_str(&tolerance);
        if let Some(c) = tol_currency {
            out.push(' ');
            out.push_str(&c);
        }
    }
    out.push('\n');
    emit_meta_entries_of(d.syntax(), out);
}

fn emit_custom(d: &ast::CustomDirective, out: &mut String) {
    let date = d.date().map(|t| t.text().to_string()).unwrap_or_default();
    let custom_type = d
        .custom_type()
        .map(|s| s.text().to_string())
        .unwrap_or_default();
    out.push_str(&date);
    out.push_str(" custom ");
    out.push_str(&custom_type);
    // Walk raw tokens after the type STRING and emit each value
    // with single-space separation. NUMBER + CURRENCY adjacent
    // counts as an Amount; emitted together with one space.
    let tokens: Vec<crate::SyntaxToken> = d
        .syntax()
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| !is_trivia_kind(t.kind()))
        .collect();
    // `seen_type` skips the leading DATE + CUSTOM_KW + type-STRING
    // tokens (already emitted above as the directive header); once
    // it flips true, every subsequent non-trivia token is a value
    // argument and gets emitted with single-space separation. An
    // adjacent NUMBER + CURRENCY pair is glued with a single space
    // (canonical Amount shape); the CURRENCY is NOT eaten as a
    // standalone arg next iteration.
    //
    // Beancount custom directives accept any mix of value kinds
    // including DATE — a `custom "type" 2024-06-15 100.00 USD`
    // shape has a DATE in value position. The previous version
    // skipped every DATE after seen_type, silently dropping such
    // user-provided date arguments.
    let mut seen_type = false;
    let mut i = 0;
    while i < tokens.len() {
        let t = &tokens[i];
        if !seen_type {
            if t.kind() == crate::SyntaxKind::STRING {
                seen_type = true;
            }
            i += 1;
            continue;
        }
        out.push(' ');
        if t.kind() == crate::SyntaxKind::NUMBER {
            out.push_str(&canonical_number(t.text()));
            if matches!(
                tokens.get(i + 1).map(rowan::SyntaxToken::kind),
                Some(crate::SyntaxKind::CURRENCY)
            ) {
                out.push(' ');
                out.push_str(tokens[i + 1].text());
                i += 2;
                continue;
            }
        } else {
            out.push_str(t.text());
        }
        i += 1;
    }
    out.push('\n');
    emit_meta_entries_of(d.syntax(), out);
}

// ---- Top-level non-dated directives -----------------------------

fn emit_option(d: &ast::OptionDirective, out: &mut String) {
    let key = d.key().map(|s| s.text().to_string()).unwrap_or_default();
    let value = d.value().map(|s| s.text().to_string()).unwrap_or_default();
    out.push_str("option ");
    out.push_str(&key);
    out.push(' ');
    out.push_str(&value);
    out.push('\n');
}

fn emit_include(d: &ast::IncludeDirective, out: &mut String) {
    let path = d.path().map(|s| s.text().to_string()).unwrap_or_default();
    out.push_str("include ");
    out.push_str(&path);
    out.push('\n');
}

fn emit_plugin(d: &ast::PluginDirective, out: &mut String) {
    let module = d.module().map(|s| s.text().to_string()).unwrap_or_default();
    out.push_str("plugin ");
    out.push_str(&module);
    if let Some(config) = d.config() {
        out.push(' ');
        out.push_str(config.text());
    }
    out.push('\n');
}

// ---- State directives (no metadata) -----------------------------

fn emit_pushtag(d: &ast::PushtagDirective, out: &mut String) {
    let tag = d.tag().map(|t| t.text().to_string()).unwrap_or_default();
    out.push_str("pushtag ");
    out.push_str(&tag);
    out.push('\n');
}

fn emit_poptag(d: &ast::PoptagDirective, out: &mut String) {
    let tag = d.tag().map(|t| t.text().to_string()).unwrap_or_default();
    out.push_str("poptag ");
    out.push_str(&tag);
    out.push('\n');
}

fn emit_pushmeta(d: &ast::PushmetaDirective, out: &mut String) {
    let key = d.key().map(|t| t.text().to_string()).unwrap_or_default();
    out.push_str("pushmeta ");
    out.push_str(&key);
    // Walk the value tokens after META_KEY, single-space separated.
    let mut past_key = false;
    for el in d.syntax().children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        if !past_key {
            if t.kind() == crate::SyntaxKind::META_KEY {
                past_key = true;
            }
            continue;
        }
        if is_trivia_kind(t.kind()) {
            continue;
        }
        out.push(' ');
        if t.kind() == crate::SyntaxKind::NUMBER {
            out.push_str(&canonical_number(t.text()));
        } else {
            out.push_str(t.text());
        }
    }
    out.push('\n');
}

fn emit_popmeta(d: &ast::PopmetaDirective, out: &mut String) {
    let key = d.key().map(|t| t.text().to_string()).unwrap_or_default();
    out.push_str("popmeta ");
    out.push_str(&key);
    out.push('\n');
}

// ---- Transaction + Posting --------------------------------------

fn emit_transaction(d: &ast::Transaction, align: Alignment, out: &mut String) {
    let date = d.date().map(|t| t.text().to_string()).unwrap_or_default();
    out.push_str(&date);
    out.push(' ');
    out.push_str(&transaction_flag_string(d));
    if let Some(payee) = d.payee() {
        out.push(' ');
        out.push_str(payee.text());
    }
    if let Some(narration) = d.narration() {
        out.push(' ');
        out.push_str(narration.text());
    }
    // Header-region tags/links — emitted in source order
    // (typed `.tags()` / `.links()` accessors return each kind
    // grouped, which loses interleaving like `#a ^l #b`). Walk
    // direct-child tokens, stopping at the header-terminating
    // NEWLINE.
    for el in d.syntax().children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        match t.kind() {
            crate::SyntaxKind::TAG | crate::SyntaxKind::LINK => {
                out.push(' ');
                out.push_str(t.text());
            }
            crate::SyntaxKind::NEWLINE => break,
            _ => {}
        }
    }
    out.push('\n');
    // Body: walk source-order children, emitting POSTING /
    // META_ENTRY child nodes. Trailing body-line TAG / LINK
    // tokens (valid Beancount per the body-line exemption) emit
    // as continuation lines.
    for child in d.syntax().children() {
        if let Some(p) = ast::Posting::cast(child.clone()) {
            emit_posting(&p, align, out);
        } else if let Some(m) = ast::MetaEntry::cast(child) {
            emit_meta_entry(&m, INDENT, out);
        }
    }
    // Trailing body-line TAG / LINK tokens (direct-child tokens
    // after the header NEWLINE that aren't trivia and aren't
    // already inside a POSTING / META_ENTRY child). Emit each on
    // its own indented line — that's the canonical form for the
    // "continuation tags" syntax.
    let mut past_header = false;
    for el in d.syntax().children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            past_header = true;
            continue;
        };
        if !past_header {
            if t.kind() == crate::SyntaxKind::NEWLINE {
                past_header = true;
            }
            continue;
        }
        match t.kind() {
            crate::SyntaxKind::TAG | crate::SyntaxKind::LINK => {
                out.push_str(INDENT);
                out.push_str(t.text());
                out.push('\n');
            }
            _ => {}
        }
    }
}

fn transaction_flag_string(d: &ast::Transaction) -> String {
    use crate::cst::ast::TransactionFlagKind;
    match d.flag() {
        None => "*".to_string(),
        Some(f) => match f.classify() {
            TransactionFlagKind::Star | TransactionFlagKind::Txn => "*".to_string(),
            TransactionFlagKind::Pending => "!".to_string(),
            TransactionFlagKind::Hash => "#".to_string(),
            TransactionFlagKind::Letter | TransactionFlagKind::CurrencyLetter => {
                f.text().to_string()
            }
        },
    }
}

fn emit_posting(p: &ast::Posting, align: Alignment, out: &mut String) {
    // Posting-trailing comment (same-line, before the posting-line
    // NEWLINE) — capture upfront so we can splice it back in just
    // before that NEWLINE, preserving the user's attachment intent.
    let trailing = collect_trailing_comment(p.syntax());
    let posting_start = out.len();

    out.push_str(INDENT);
    let mut col = INDENT.len();
    if let Some(flag) = p.flag() {
        out.push_str(flag.text());
        out.push(' ');
        col += flag.text().chars().count() + 1;
    }
    let account_text = p
        .account()
        .map(|a| a.text().to_string())
        .unwrap_or_default();
    out.push_str(&account_text);
    col += account_text.chars().count();

    if let Some(amt) = p.amount() {
        let value = amount_value_text(&amt);
        if !value.is_empty() {
            // Two stages of padding:
            //   1) Account end → start of number field (`number_col`).
            //      Fall back to 2 spaces when the LHS already exceeds
            //      the file-wide max (over-long account name).
            //   2) Inside the number field, left-pad to right-justify
            //      to `number_width`. Effect: the currency column
            //      lands at a single uniform position file-wide even
            //      when numbers have different widths or signs.
            let field_pad = align.number_col.saturating_sub(col).max(2);
            let justify_pad = align.number_width.saturating_sub(value.chars().count());
            for _ in 0..(field_pad + justify_pad) {
                out.push(' ');
            }
            out.push_str(&value);
            if let Some(c) = amt.currency() {
                out.push(' ');
                out.push_str(c.text());
            }
            if let Some(cs) = p.cost_spec() {
                out.push(' ');
                out.push_str(&format_cost_spec(&cs));
            }
            if let Some(pa) = p.price_annotation() {
                out.push(' ');
                out.push_str(&format_price_annotation(&pa));
            }
        }
    }
    out.push('\n');
    // Splice the trailing comment in BEFORE the posting-line
    // NEWLINE (the first '\n' in the emitted posting region).
    if let Some(c) = trailing
        && let Some(rel) = out[posting_start..].find('\n')
    {
        let mut splice = String::with_capacity(c.len() + 1);
        splice.push(' ');
        splice.push_str(&c);
        out.insert_str(posting_start + rel, &splice);
    }
    // Posting-attached metadata: indent 4 (deeper than posting's 2).
    for m in p.meta_entries() {
        emit_meta_entry(&m, "    ", out);
    }
}

/// Format an `AMOUNT` (units + currency) in canonical form. For
/// arithmetic shapes, emits the expression with single-space
/// separators (parens tight); for plain shapes, emits
/// `NUMBER CURRENCY` with thousands separators stripped.
fn format_amount(amt: &ast::Amount) -> String {
    let mut out = String::new();
    if amt.is_arithmetic() {
        emit_amount_subnode_expression(amt.syntax(), &mut out);
        if let Some(c) = amt.currency() {
            if !out.is_empty() {
                out.push(' ');
            }
            out.push_str(c.text());
        }
        return out;
    }
    if let Some(sign) = amt.sign()
        && sign.is_minus()
    {
        out.push('-');
    }
    if let Some(n) = amt.number() {
        out.push_str(&canonical_number(n.text()));
    }
    if let Some(c) = amt.currency() {
        if !out.is_empty() && !out.ends_with('-') {
            out.push(' ');
        }
        out.push_str(c.text());
    }
    out
}

/// Canonical form for cost specs: `{cost CCY}` (single-brace
/// per-unit), `{{cost CCY}}` (double-brace total), `{# cost CCY}`
/// (per-unit + total via opener), or the in-brace `{N # T CCY}`
/// shape preserved as-is with single-space normalization.
///
/// Commas separating cost components (`{N CCY, DATE, "label"}`)
/// stay tight against the preceding token; every other adjacent
/// token pair is joined with a single space.
fn format_cost_spec(cs: &ast::CostSpec) -> String {
    let (open, close) = if cs.is_total() {
        ("{{", "}}")
    } else if cs.is_per_unit_plus_total() {
        ("{#", "}")
    } else {
        ("{", "}")
    };
    // Collect inner content tokens (skip opener/closer/whitespace),
    // then route through write_canonical_token_sequence so the spacing rule
    // is identical to balance/price/AMOUNT-subnode arithmetic — most
    // importantly, unary `+`/`-` stays tight (`{-500 USD}`, not
    // `{- 500 USD}`) and COMMA stays tight.
    let inner_tokens: Vec<crate::SyntaxToken> = cs
        .syntax()
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| {
            !matches!(
                t.kind(),
                crate::SyntaxKind::L_BRACE
                    | crate::SyntaxKind::R_BRACE
                    | crate::SyntaxKind::L_DOUBLE_BRACE
                    | crate::SyntaxKind::R_DOUBLE_BRACE
                    | crate::SyntaxKind::L_BRACE_HASH
                    | crate::SyntaxKind::WHITESPACE
                    | crate::SyntaxKind::NEWLINE
            )
        })
        .collect();
    let mut inner = String::new();
    write_canonical_token_sequence(&inner_tokens, &mut inner);
    // The `{#` opener is a two-character marker; canonical form
    // separates it from the first inner token with a single space
    // (matching the rendering in this function's rustdoc). `{` and
    // `{{` don't get inner padding per the canonical-form spec.
    if cs.is_per_unit_plus_total() && !inner.is_empty() {
        format!("{open} {inner}{close}")
    } else {
        format!("{open}{inner}{close}")
    }
}

/// Canonical price annotation: `@ amount` (per-unit) or
/// `@@ amount` (total).
fn format_price_annotation(pa: &ast::PriceAnnotation) -> String {
    let op = if pa.is_total() { "@@" } else { "@" };
    match pa.amount() {
        Some(a) => format!("{op} {}", format_amount(&a)),
        None => op.to_string(),
    }
}

// ---- Helpers ---------------------------------------------------

/// True for tokens that don't contribute content to the canonical
/// form: whitespace, newlines, every comment kind, and the
/// leading-file `BOM` token.
const fn is_trivia_kind(kind: crate::SyntaxKind) -> bool {
    matches!(
        kind,
        crate::SyntaxKind::WHITESPACE
            | crate::SyntaxKind::NEWLINE
            | crate::SyntaxKind::COMMENT
            | crate::SyntaxKind::PERCENT_COMMENT
            | crate::SyntaxKind::SHEBANG
            | crate::SyntaxKind::EMACS_DIRECTIVE
            | crate::SyntaxKind::BOM
    )
}

/// Strip thousands-separator commas from a NUMBER token's text;
/// preserve the user's decimal-place count. Per the locked
/// canonical-form decision: `1,000.00` → `1000.00`, `1.0` → `1.0`.
fn canonical_number(text: &str) -> String {
    if text.contains(',') {
        text.replace(',', "")
    } else {
        text.to_string()
    }
}

/// Emit the arithmetic expression of a `PRICE` / `BALANCE`
/// directive: tokens from the first expression-starting token
/// (`NUMBER`, unary `+`/`-`, or `(`) up to (but not including) the
/// first `CURRENCY` at paren-depth 0. Spacing rules per
/// [`write_canonical_token_sequence`].
///
/// **Why the predicate must allow `PLUS` / `MINUS` / `L_PAREN`,
/// not just `NUMBER`.** A previous version skipped tokens until
/// it hit a `NUMBER`, which silently dropped leading unary signs
/// and opening parens — flipping the sign on inputs like
/// `2024-01-15 price USD -1.00 EUR` (formatted to `1.00 EUR`) and
/// corrupting parenthesized expressions like
/// `2024-01-15 balance Assets:A (1 + 2) USD` (formatted to
/// `1 + 2) USD USD`). Sign drift in BALANCE / PRICE is silent data
/// corruption — a balance assertion that previously asserted a
/// debit would assert a credit after a round-trip.
fn emit_amount_expression(node: &crate::SyntaxNode, out: &mut String) {
    let raw: Vec<crate::SyntaxToken> = node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| !is_trivia_kind(t.kind()))
        .skip_while(|t| {
            !matches!(
                t.kind(),
                crate::SyntaxKind::NUMBER
                    | crate::SyntaxKind::PLUS
                    | crate::SyntaxKind::MINUS
                    | crate::SyntaxKind::L_PAREN
            )
        })
        .collect();
    let mut depth: i32 = 0;
    let mut first_currency_idx: Option<usize> = None;
    for (i, t) in raw.iter().enumerate() {
        match t.kind() {
            crate::SyntaxKind::L_PAREN => depth += 1,
            crate::SyntaxKind::R_PAREN => depth -= 1,
            crate::SyntaxKind::CURRENCY if depth == 0 && first_currency_idx.is_none() => {
                first_currency_idx = Some(i);
            }
            _ => {}
        }
    }
    let end = first_currency_idx.unwrap_or(raw.len());
    write_canonical_token_sequence(&raw[..end], out);
}

/// Emit an `AMOUNT` subnode's expression region: every non-trivia
/// token minus the trailing `CURRENCY` (caller re-emits the
/// currency itself). Used by [`format_amount`] for arithmetic
/// posting amounts like `-(1.00 + 2.00) USD`.
fn emit_amount_subnode_expression(node: &crate::SyntaxNode, out: &mut String) {
    let mut tokens: Vec<crate::SyntaxToken> = node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| !is_trivia_kind(t.kind()))
        .collect();
    if let Some(last) = tokens.last()
        && last.kind() == crate::SyntaxKind::CURRENCY
    {
        tokens.pop();
    }
    write_canonical_token_sequence(&tokens, out);
}

/// Single dispatcher for the canonical spacing rules used by EVERY
/// token-sequence emit path: balance / price arithmetic, AMOUNT
/// subnodes, cost-spec interiors, and metadata values. There is no
/// separate path; each call site collects the relevant non-trivia
/// tokens and routes them through here so the rules cannot drift
/// between contexts.
///
/// Rules:
///
/// - single space between adjacent operands / binary operators
/// - no space after `(` or before `)` (parens stay tight)
/// - no space after a unary `+` / `-` (one that opens the run
///   or follows `(` or another operator)
/// - no space before `,` (commas in cost-spec component lists
///   stay tight against the preceding token)
///
/// **Adding a new `SyntaxKind` to the formatter implies thinking
/// about its effect on every call site of this function.** A new
/// operator-like kind added to `is_op` will silently change cost-
/// spec and metadata spacing too; a new bracket-like kind needs
/// its own rule. The corpus-level idempotence test
/// (`idempotence_corpus_sweep`) is the safety net that catches
/// drifts.
fn write_canonical_token_sequence(tokens: &[crate::SyntaxToken], out: &mut String) {
    let is_op = |k: crate::SyntaxKind| {
        matches!(
            k,
            crate::SyntaxKind::PLUS
                | crate::SyntaxKind::MINUS
                | crate::SyntaxKind::STAR
                | crate::SyntaxKind::SLASH
        )
    };
    let mut prev_kind: Option<crate::SyntaxKind> = None;
    let mut prev_was_unary = false;
    for t in tokens {
        let kind = t.kind();
        let is_unary = is_op(kind)
            && match prev_kind {
                None => true,
                Some(p) => p == crate::SyntaxKind::L_PAREN || is_op(p),
            };
        let need_space = match prev_kind {
            None => false,
            Some(prev) => {
                prev != crate::SyntaxKind::L_PAREN
                    && kind != crate::SyntaxKind::R_PAREN
                    && kind != crate::SyntaxKind::COMMA
                    && !prev_was_unary
            }
        };
        if need_space {
            out.push(' ');
        }
        if kind == crate::SyntaxKind::NUMBER {
            out.push_str(&canonical_number(t.text()));
        } else {
            out.push_str(t.text());
        }
        prev_kind = Some(kind);
        prev_was_unary = is_unary;
    }
}

/// Extract a balance directive's optional tolerance — the
/// `NUMBER` after the first `TILDE`, plus an optional trailing
/// `CURRENCY` at paren-depth 0.
fn balance_tolerance(node: &crate::SyntaxNode) -> Option<(String, Option<String>)> {
    let mut past_tilde = false;
    let mut number: Option<String> = None;
    let mut currency: Option<String> = None;
    for el in node.children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        if !past_tilde {
            if t.kind() == crate::SyntaxKind::TILDE {
                past_tilde = true;
            }
            continue;
        }
        match t.kind() {
            crate::SyntaxKind::NUMBER if number.is_none() => {
                number = Some(canonical_number(t.text()));
            }
            crate::SyntaxKind::CURRENCY if number.is_some() && currency.is_none() => {
                currency = Some(t.text().to_string());
            }
            _ => {}
        }
    }
    number.map(|n| (n, currency))
}

// ---- Metadata --------------------------------------------------

/// Walk a directive's direct-child `META_ENTRY` nodes and emit
/// each on its own indented line in canonical form (`indent + KEY:
/// value\n`). Most directive types don't have a `.meta_entries()`
/// accessor on their typed wrapper; we walk the syntax node
/// directly to stay uniform.
fn emit_meta_entries_of(node: &crate::SyntaxNode, out: &mut String) {
    for entry in node.children().filter_map(MetaEntry::cast) {
        emit_meta_entry(&entry, INDENT, out);
    }
}

/// Canonical emit for a single `META_ENTRY`. Walks non-trivia
/// tokens, prints them with single-space separation, and
/// normalizes numbers via [`canonical_number`]. The `META_KEY`
/// token already includes the trailing colon (e.g. `note:`); the
/// value side gets the same NUMBER + CURRENCY gluing rule the
/// rest of the formatter uses elsewhere.
///
/// Two semantically-equivalent inputs (e.g. `foo: "bar"` and
/// `foo:    "bar"`) produce byte-identical output — the
/// gofmt-style invariant the file rustdoc promises.
fn emit_meta_entry(m: &MetaEntry, indent: &str, out: &mut String) {
    out.push_str(indent);
    // Split the META_ENTRY's non-trivia tokens into [META_KEY,
    // value*]. The META_KEY token already includes the trailing
    // colon (e.g. `note:`); the value tokens go through
    // write_canonical_token_sequence so the spacing rules — unary +/-
    // tight, COMMA tight, paren-tight, NUMBER canonicalized — are
    // shared with the balance/price/cost-spec/posting-amount paths.
    let content: Vec<crate::SyntaxToken> = m
        .syntax()
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| {
            !matches!(
                t.kind(),
                crate::SyntaxKind::WHITESPACE | crate::SyntaxKind::NEWLINE
            )
        })
        .collect();
    let mut iter = content.iter();
    if let Some(key) = iter.next() {
        out.push_str(key.text());
    }
    let value_tokens: Vec<crate::SyntaxToken> = iter.cloned().collect();
    if !value_tokens.is_empty() {
        out.push(' ');
        write_canonical_token_sequence(&value_tokens, out);
    }
    out.push('\n');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_input_yields_single_newline() {
        assert_eq!(format_source(""), "\n");
    }

    #[test]
    fn open_directive_canonical() {
        let src = "2024-01-15   open    Assets:Cash\n";
        assert_eq!(format_source(src), "2024-01-15 open Assets:Cash\n");
    }

    #[test]
    fn open_with_currencies_and_booking_canonical() {
        let src = "2024-01-15 open Assets:Brokerage USD,EUR \"STRICT\"\n";
        assert_eq!(
            format_source(src),
            "2024-01-15 open Assets:Brokerage USD EUR \"STRICT\"\n"
        );
    }

    #[test]
    fn close_directive_canonical() {
        let src = "2024-12-31 close Assets:Cash\n";
        assert_eq!(format_source(src), "2024-12-31 close Assets:Cash\n");
    }

    #[test]
    fn commodity_directive_canonical() {
        let src = "2024-01-01 commodity HOOL\n";
        assert_eq!(format_source(src), "2024-01-01 commodity HOOL\n");
    }

    #[test]
    fn blank_line_between_directives() {
        let src = "2024-01-01 open Assets:A\n2024-01-02 open Assets:B\n";
        assert_eq!(
            format_source(src),
            "2024-01-01 open Assets:A\n\n2024-01-02 open Assets:B\n"
        );
    }

    #[test]
    fn trailing_newline_always_present() {
        let src = "2024-01-01 open Assets:A";
        let formatted = format_source(src);
        assert!(formatted.ends_with('\n'));
        assert!(!formatted.ends_with("\n\n"));
    }

    #[test]
    fn idempotent_on_canonical_input() {
        let src = "2024-01-01 open Assets:A\n\n2024-01-02 close Assets:A\n";
        let once = format_source(src);
        let twice = format_source(&once);
        assert_eq!(once, twice);
    }

    #[test]
    fn note_canonical() {
        let src = "2024-01-15   note   Assets:Cash   \"a note\"\n";
        assert_eq!(
            format_source(src),
            "2024-01-15 note Assets:Cash \"a note\"\n"
        );
    }

    #[test]
    fn event_canonical() {
        let src = "2024-01-15  event  \"location\"   \"NYC\"\n";
        assert_eq!(
            format_source(src),
            "2024-01-15 event \"location\" \"NYC\"\n"
        );
    }

    #[test]
    fn query_canonical() {
        let src = "2024-01-15 query \"q1\" \"SELECT account\"\n";
        assert_eq!(
            format_source(src),
            "2024-01-15 query \"q1\" \"SELECT account\"\n"
        );
    }

    #[test]
    fn pad_canonical() {
        let src = "2024-01-15  pad   Assets:A   Equity:Opening\n";
        assert_eq!(
            format_source(src),
            "2024-01-15 pad Assets:A Equity:Opening\n"
        );
    }

    #[test]
    fn document_with_tags_and_links_canonical() {
        let src = "2024-06-01 document Assets:Bank \"stmt.pdf\" #q1 ^scan42 #urgent\n";
        assert_eq!(
            format_source(src),
            "2024-06-01 document Assets:Bank \"stmt.pdf\" #q1 ^scan42 #urgent\n"
        );
    }

    #[test]
    fn price_canonical_strips_thousands_separators() {
        let src = "2024-01-15 price USD  1,234.56 EUR\n";
        assert_eq!(format_source(src), "2024-01-15 price USD 1234.56 EUR\n");
    }

    #[test]
    fn price_arithmetic_canonicalizes_spacing() {
        let src = "2024-01-15 price USD 1/2 EUR\n";
        assert_eq!(format_source(src), "2024-01-15 price USD 1 / 2 EUR\n");
    }

    #[test]
    fn balance_canonical() {
        let src = "2024-01-15  balance  Assets:Cash   100.00  USD\n";
        assert_eq!(
            format_source(src),
            "2024-01-15 balance Assets:Cash 100.00 USD\n"
        );
    }

    #[test]
    fn balance_with_tolerance_canonical() {
        let src = "2024-01-15 balance Assets:Cash 100.00 USD ~ 0.01 USD\n";
        assert_eq!(
            format_source(src),
            "2024-01-15 balance Assets:Cash 100.00 USD ~ 0.01 USD\n"
        );
    }

    #[test]
    fn balance_arithmetic_canonical() {
        let src = "2024-01-15 balance Assets:Cash  0.25 + 0.75  USD\n";
        assert_eq!(
            format_source(src),
            "2024-01-15 balance Assets:Cash 0.25 + 0.75 USD\n"
        );
    }

    #[test]
    fn custom_canonical() {
        let src = "2024-01-01 custom \"budget\" Expenses:Food 500.00 USD\n";
        assert_eq!(
            format_source(src),
            "2024-01-01 custom \"budget\" Expenses:Food 500.00 USD\n"
        );
    }

    #[test]
    fn option_canonical() {
        let src = "option   \"title\"   \"My Ledger\"\n";
        assert_eq!(format_source(src), "option \"title\" \"My Ledger\"\n");
    }

    #[test]
    fn include_canonical() {
        let src = "include  \"other.beancount\"\n";
        assert_eq!(format_source(src), "include \"other.beancount\"\n");
    }

    #[test]
    fn plugin_canonical_with_config() {
        let src = "plugin  \"beancount.plugins.unrealized\"  \"Unrealized\"\n";
        assert_eq!(
            format_source(src),
            "plugin \"beancount.plugins.unrealized\" \"Unrealized\"\n"
        );
    }

    #[test]
    fn plugin_canonical_without_config() {
        let src = "plugin   \"my.plugin\"\n";
        assert_eq!(format_source(src), "plugin \"my.plugin\"\n");
    }

    #[test]
    fn pushtag_poptag_canonical() {
        let src = "pushtag  #active\npoptag  #active\n";
        assert_eq!(format_source(src), "pushtag #active\n\npoptag #active\n");
    }

    #[test]
    fn pushmeta_popmeta_canonical() {
        let src = "pushmeta location: \"NYC\"\npopmeta location:\n";
        assert_eq!(
            format_source(src),
            "pushmeta location: \"NYC\"\n\npopmeta location:\n"
        );
    }

    // ---- Transaction tests ------------------------------------

    #[test]
    fn transaction_minimal_two_postings_aligns_amounts() {
        let src = "\
2024-01-15 * \"Coffee\"
  Assets:Cash       -5.00 USD
  Expenses:Coffee    5.00 USD
";
        // max LHS = 15 (Expenses:Coffee); number_col = 17.
        // max number width = 6 (`-5.00`); number_width = 6.
        // Posting 1: account end at col 13, pad 4 → `-5.00` (width 6,
        //   no left-pad) → currency at col 24.
        // Posting 2: account end at col 17, pad 2 → ` 5.00` (width
        //   5 left-padded by 1) → currency at col 24.
        let expected = "\
2024-01-15 * \"Coffee\"
  Assets:Cash      -5.00 USD
  Expenses:Coffee   5.00 USD
";
        assert_eq!(format_source(src), expected);
    }

    #[test]
    fn transaction_payee_and_narration() {
        let src =
            "2024-01-15 * \"Starbucks\" \"Coffee\"\n  Assets:Cash -5.00 USD\n  Expenses:Coffee\n";
        let out = format_source(src);
        assert!(
            out.contains("2024-01-15 * \"Starbucks\" \"Coffee\"\n"),
            "got: {out}"
        );
    }

    #[test]
    fn transaction_pending_flag() {
        let src = "2024-01-15 ! \"Pending\"\n  Assets:Cash -5.00 USD\n  Expenses:Misc\n";
        let out = format_source(src);
        assert!(out.starts_with("2024-01-15 ! \"Pending\"\n"), "got: {out}");
    }

    #[test]
    fn transaction_txn_keyword_normalized_to_star() {
        // The `txn` keyword form is canonical-form equivalent to `*`.
        let src = "2024-01-15 txn \"x\"\n  Assets:Cash -1.00 USD\n  Expenses:Misc\n";
        let out = format_source(src);
        assert!(out.starts_with("2024-01-15 * \"x\"\n"), "got: {out}");
    }

    #[test]
    fn transaction_header_tags_and_links() {
        let src =
            "2024-01-15 * \"x\" #tag1 ^link1 #tag2\n  Assets:Cash -1.00 USD\n  Expenses:Misc\n";
        let out = format_source(src);
        assert!(
            out.starts_with("2024-01-15 * \"x\" #tag1 ^link1 #tag2\n"),
            "got: {out}"
        );
    }

    #[test]
    fn transaction_auto_balance_posting_no_amount() {
        let src = "2024-01-15 * \"x\"\n  Assets:Cash  -5.00 USD\n  Expenses:Misc\n";
        let out = format_source(src);
        // The auto-balance posting has no amount; should just be
        // the indented account name.
        assert!(out.contains("\n  Expenses:Misc\n"), "got: {out}");
    }

    #[test]
    fn transaction_posting_with_cost_spec() {
        let src = "2024-01-15 * \"buy\"\n  Assets:Brokerage  10 HOOL {500.00 USD}\n  Assets:Cash  -5000.00 USD\n";
        let out = format_source(src);
        assert!(out.contains("10 HOOL {500.00 USD}"), "got: {out}");
    }

    #[test]
    fn transaction_posting_with_total_cost_spec() {
        let src = "2024-01-15 * \"buy\"\n  Assets:Brokerage  10 HOOL {{5000.00 USD}}\n  Assets:Cash  -5000.00 USD\n";
        let out = format_source(src);
        assert!(out.contains("10 HOOL {{5000.00 USD}}"), "got: {out}");
    }

    #[test]
    fn transaction_posting_with_per_unit_price() {
        let src = "2024-01-15 * \"buy\"\n  Assets:Brokerage  10 HOOL @ 500.00 USD\n  Assets:Cash  -5000.00 USD\n";
        let out = format_source(src);
        assert!(out.contains("10 HOOL @ 500.00 USD"), "got: {out}");
    }

    #[test]
    fn transaction_posting_with_total_price() {
        let src = "2024-01-15 * \"buy\"\n  Assets:Brokerage  10 HOOL @@ 5000.00 USD\n  Assets:Cash  -5000.00 USD\n";
        let out = format_source(src);
        assert!(out.contains("10 HOOL @@ 5000.00 USD"), "got: {out}");
    }

    #[test]
    fn transaction_posting_with_flag() {
        let src = "2024-01-15 * \"x\"\n  ! Assets:Cash  -5.00 USD\n  Expenses:Misc  5.00 USD\n";
        let out = format_source(src);
        assert!(out.contains("\n  ! Assets:Cash"), "got: {out}");
    }

    #[test]
    fn transaction_negative_amount() {
        let src = "2024-01-15 * \"x\"\n  Assets:Cash -5.00 USD\n  Expenses:Misc 5.00 USD\n";
        let out = format_source(src);
        assert!(out.contains("-5.00 USD"), "got: {out}");
        assert!(out.contains(" 5.00 USD"), "got: {out}");
    }

    #[test]
    fn transaction_strips_thousands_separators_in_postings() {
        let src = "2024-01-15 * \"x\"\n  Assets:Cash -1,000.00 USD\n  Expenses:Misc 1,000.00 USD\n";
        let out = format_source(src);
        assert!(out.contains("-1000.00 USD"), "got: {out}");
        assert!(!out.contains("1,000"), "got: {out}");
    }

    #[test]
    fn transaction_arithmetic_amount() {
        let src =
            "2024-01-15 * \"x\"\n  Assets:Cash  -(1.00 + 2.00) USD\n  Expenses:Misc 3.00 USD\n";
        let out = format_source(src);
        // The arithmetic expression should render with single
        // spaces around binary ops and tight parens.
        assert!(
            out.contains("(1.00 + 2.00) USD") || out.contains("-(1.00 + 2.00) USD"),
            "got: {out}"
        );
    }

    #[test]
    fn transaction_idempotent() {
        let src = "\
2024-01-15 * \"Coffee\"
  Assets:Cash       -5.00 USD
  Expenses:Coffee    5.00 USD
";
        let once = format_source(src);
        let twice = format_source(&once);
        assert_eq!(once, twice);
    }

    #[test]
    fn transaction_file_wide_alignment_across_transactions() {
        let src = "\
2024-01-15 * \"x\"
  Assets:Cash -5.00 USD
  Expenses:Misc 5.00 USD

2024-01-16 * \"y\"
  Liabilities:CreditCard:Visa  -100.00 USD
  Expenses:Big  100.00 USD
";
        let out = format_source(src);
        // Cross-posting invariant: the currency column (USD here)
        // lands at the same column on every posting line, even when
        // individual numbers differ in width or sign. The number
        // field is right-justified so the currency column is uniform.
        let usd_cols: Vec<usize> = out
            .lines()
            .filter(|l| l.starts_with("  ") && l.contains(" USD"))
            .filter_map(|l| l.find("USD"))
            .collect();
        assert!(
            usd_cols.len() >= 4,
            "expected ≥4 posting lines, got {usd_cols:?} in {out}"
        );
        let first = usd_cols[0];
        assert!(
            usd_cols.iter().all(|&c| c == first),
            "expected USD column uniform at {first}, got {usd_cols:?} in:\n{out}"
        );
    }

    #[test]
    fn transaction_posting_metadata_indented_four() {
        let src =
            "2024-01-15 * \"x\"\n  Assets:Cash -5.00 USD\n    foo: \"bar\"\n  Expenses:Misc\n";
        let out = format_source(src);
        assert!(out.contains("\n    foo: \"bar\"\n"), "got: {out}");
    }

    // ---- Code-review regression tests -----------------------------
    //
    // Each test pins a bug surfaced by the high-effort code review of
    // PR #1284 and verified at runtime against the unfixed formatter.

    #[test]
    fn cost_spec_per_unit_plus_total_opener_preserved() {
        // Bug: format_cost_spec only branched on is_total() and emitted
        // `{` for the `{#` opener too, dropping the `#` marker and
        // changing semantics from per-unit-plus-total to plain
        // per-unit cost.
        let src = "2024-01-01 * \"buy\"\n  Assets:Brokerage 10 HOOL {# 500.00 USD}\n  Assets:Cash -5000.00 USD\n";
        let out = format_source(src);
        assert!(
            out.contains("{# 500.00 USD}"),
            "expected `{{#` opener preserved; got:\n{out}"
        );
        assert!(!out.contains("{500.00 USD}"), "got:\n{out}");
    }

    #[test]
    fn cost_spec_comma_stays_tight_to_prev_token() {
        // Bug: format_cost_spec's catch-all arm inserted a space
        // before every non-trivia token including COMMA, producing
        // `{500.00 USD , 2024-01-15}` instead of the canonical
        // `{500.00 USD, 2024-01-15}`.
        let src = "2024-01-01 * \"buy\"\n  Assets:Brokerage 10 HOOL {500.00 USD, 2024-01-15}\n  Assets:Cash -5000.00 USD\n";
        let out = format_source(src);
        assert!(
            out.contains("{500.00 USD, 2024-01-15}"),
            "comma must stay tight to USD; got:\n{out}"
        );
        assert!(
            !out.contains("USD ,"),
            "no space allowed before comma; got:\n{out}"
        );
    }

    #[test]
    fn custom_directive_preserves_date_value_arguments() {
        // Bug: emit_custom's post-seen_type match skipped every DATE
        // token, silently dropping legitimate date-typed value
        // arguments. The leading directive date is already skipped
        // via the seen_type=false phase.
        let src = "2024-01-01 custom \"budget\" \"name\" 2024-06-15 100.00 USD\n";
        let out = format_source(src);
        assert!(
            out.contains("2024-06-15"),
            "value-position DATE must survive; got: {out}"
        );
    }

    #[test]
    fn file_level_adjacent_comments_stay_tight() {
        // Bug: format_node's top-level walk inserted a blank `\n`
        // separator before every emitted item including comments,
        // breaking section-header blocks like `; ====\n; HEADER\n; ====`
        // by injecting blanks between every adjacent comment line.
        let src = "; ====\n; HEADER\n; ====\n2024-01-01 open Assets:A\n";
        let expected = "; ====\n; HEADER\n; ====\n2024-01-01 open Assets:A\n";
        assert_eq!(format_source(src), expected);
    }

    #[test]
    fn metadata_internal_whitespace_normalized() {
        // Bug: emit_meta_entries_of passed META_ENTRY source text
        // through verbatim, so `foo: "bar"` and `foo:    "bar"` —
        // identical typed ASTs — produced different formatter
        // output, violating the gofmt-style invariant the rustdoc
        // declares.
        let a = "2024-01-01 open Assets:Bank\n  starting: \"foo\"\n";
        let b = "2024-01-01 open Assets:Bank\n  starting:    \"foo\"\n";
        assert_eq!(format_source(a), format_source(b));
    }

    #[test]
    fn metadata_number_thousands_separator_stripped() {
        // Same invariant: numbers inside metadata values share the
        // canonical thousands-separator policy with posting numbers
        // (otherwise the same file would emit inconsistent numeric
        // forms in postings vs. metadata).
        let src = "2024-01-01 open Assets:Bank\n  starting_balance: 1,000.00 USD\n";
        let out = format_source(src);
        assert!(
            out.contains("1000.00 USD"),
            "thousands-sep should strip in metadata too; got: {out}"
        );
        assert!(!out.contains("1,000"), "got: {out}");
    }

    #[test]
    fn bare_cr_line_endings_normalized_to_lf_before_parse() {
        // Bug: the lexer doesn't treat bare CR as a line terminator,
        // so a classic-Mac-authored `directive\r…\rdirective\r`
        // parsed as one broken directive and the rest were silently
        // dropped. format_source normalizes line endings BEFORE
        // parsing so bare CR (and CRLF) are treated as LF.
        let src = "2024-01-01 open Assets:A\r2024-01-02 open Assets:B\r";
        let out = format_source(src);
        assert!(
            out.contains("2024-01-01 open Assets:A"),
            "first directive lost: {out:?}"
        );
        assert!(
            out.contains("2024-01-02 open Assets:B"),
            "second directive lost on bare-CR input: {out:?}"
        );
    }

    #[test]
    fn crlf_input_canonicalizes_to_lf() {
        // CRLF and bare CR both fold to LF on the way through the
        // canonical pass (the canonical form is LF-only).
        let src = "2024-01-01 open Assets:A\r\n2024-01-02 open Assets:B\r\n";
        let out = format_source(src);
        assert!(
            !out.contains('\r'),
            "canonical output must be LF-only: {out:?}"
        );
        assert!(out.contains("2024-01-01 open Assets:A\n"), "got: {out:?}");
        assert!(out.contains("2024-01-02 open Assets:B\n"), "got: {out:?}");
    }

    #[test]
    fn metadata_value_with_unary_minus_stays_tight() {
        // Bug: emit_meta_entry's tokenized walk inserted a space
        // after a unary `+`/`-`, breaking `key: -5.00 USD` →
        // `key: - 5.00 USD`. Routed through write_canonical_token_sequence
        // so unary detection matches the balance/price/posting paths.
        let src = "2024-01-01 open Assets:Bank\n  threshold: -5.00 USD\n";
        let out = format_source(src);
        assert!(
            out.contains("threshold: -5.00 USD"),
            "unary minus must stay tight in metadata; got: {out}"
        );
        assert!(
            !out.contains("- 5.00"),
            "no space after unary minus; got: {out}"
        );
    }

    #[test]
    fn metadata_value_with_unary_plus_stays_tight() {
        let src = "2024-01-01 open Assets:Bank\n  min: +1.00 USD\n";
        let out = format_source(src);
        assert!(out.contains("min: +1.00 USD"), "got: {out}");
        assert!(!out.contains("+ 1.00"), "got: {out}");
    }

    #[test]
    fn cost_spec_negative_cost_stays_tight() {
        // Bug: format_cost_spec catch-all had no unary-operator
        // handling. `{-500 USD}` formatted to `{- 500 USD}`. Now
        // routes through write_canonical_token_sequence.
        let src = "2024-01-01 * \"x\"\n  Assets:Brokerage 10 HOOL {-500 USD}\n  Assets:Cash -5000.00 USD\n";
        let out = format_source(src);
        assert!(
            out.contains("{-500 USD}"),
            "negative cost spec must stay tight; got:\n{out}"
        );
        assert!(!out.contains("{- "), "got:\n{out}");
    }

    #[test]
    fn cost_spec_arithmetic_with_unary_stays_tight() {
        // `{500 * -2 USD}` formerly emitted `{500 * - 2 USD}` because
        // the cost-spec catch-all didn't understand unary +/-.
        let src = "2024-01-01 * \"x\"\n  Assets:Brokerage 10 HOOL {500 * -2 USD}\n  Assets:Cash -1000.00 USD\n";
        let out = format_source(src);
        assert!(
            out.contains("{500 * -2 USD}"),
            "cost-spec arithmetic unary must stay tight; got:\n{out}"
        );
    }

    // ---- Property tests -------------------------------------------
    //
    // Two invariants the rustdoc's gofmt-style promise depends on,
    // pinned over a hand-curated input matrix:
    //
    // - **Idempotence:** `format_source(format_source(x)) == format_source(x)`.
    // - **Round-trip stability for canonicalize_directives:** the
    //   synthesize-then-canonicalize shim produces text that, when
    //   parsed back, yields the same Directive count and zero parse
    //   errors.
    //
    // The matrix covers every directive kind plus the high-risk
    // edge cases the prior reviews surfaced (unary +/- in metadata,
    // cost-spec arithmetic, CRLF, bare CR, multi-line strings,
    // comments containing quotes, non-Latin accounts). When the
    // upstream compatibility corpus is fetched into
    // `tests/compatibility/files/` the per-file sweep at the bottom
    // also runs; otherwise the file-based test is skipped.

    const IDEMPOTENCE_MATRIX: &[(&str, &str)] = &[
        ("empty", ""),
        ("only_comment", "; header comment\n"),
        ("only_directive", "2024-01-01 open Assets:Cash\n"),
        (
            "two_open_directives",
            "2024-01-01 open Assets:A\n2024-01-02 open Assets:B\n",
        ),
        (
            "transaction_with_cost_and_price",
            "2024-01-15 * \"buy\"\n  Assets:Brokerage 10 HOOL {500.00 USD} @ 510.00 USD\n  Assets:Cash -5000.00 USD\n",
        ),
        (
            "transaction_with_per_unit_plus_total_cost",
            "2024-01-15 * \"x\"\n  Assets:Brokerage 10 HOOL {# 500.00 USD}\n  Assets:Cash -5000.00 USD\n",
        ),
        (
            "transaction_with_arithmetic_amount",
            "2024-01-15 * \"x\"\n  Assets:Cash  -(1.00 + 2.00) USD\n  Expenses:Misc 3.00 USD\n",
        ),
        (
            "balance_with_arithmetic_and_tolerance",
            "2024-01-15 balance Assets:Cash 0.25 + 0.75 USD ~ 0.01 USD\n",
        ),
        // Regression for Copilot #2: a previous emit_amount_expression
        // skipped tokens until the first NUMBER, which dropped a
        // leading unary `-` and silently flipped the sign — a
        // balance assertion that asserted a debit would assert a
        // credit after a round-trip. These fixtures pin the
        // sign / paren preservation explicitly.
        (
            "balance_leading_unary_minus",
            "2024-01-15 balance Assets:A -1.00 USD\n",
        ),
        (
            "balance_leading_parenthesized_expression",
            "2024-01-15 balance Assets:A (1 + 2) USD\n",
        ),
        (
            "price_leading_unary_minus",
            "2024-01-15 price USD -1.00 EUR\n",
        ),
        (
            "price_with_thousands_separator",
            "2024-01-15 price USD 1,234.56 EUR\n",
        ),
        (
            "metadata_unary_minus",
            "2024-01-01 open Assets:Bank\n  threshold: -5.00 USD\n",
        ),
        (
            "metadata_arithmetic",
            "2024-01-01 open Assets:Bank\n  total: 1000 + 500 USD\n",
        ),
        (
            "cost_spec_with_comma_and_date",
            "2024-01-15 * \"x\"\n  Assets:Brokerage 10 HOOL {500.00 USD, 2024-01-15}\n  Assets:Cash -5000.00 USD\n",
        ),
        (
            "cost_spec_with_negative",
            "2024-01-15 * \"x\"\n  Assets:Brokerage 10 HOOL {-500 USD}\n  Assets:Cash 5000.00 USD\n",
        ),
        (
            "transaction_with_tags_and_links",
            "2024-01-15 * \"x\" #tag1 ^link1 #tag2\n  Assets:Cash -1.00 USD\n  Expenses:Misc 1.00 USD\n",
        ),
        (
            "custom_with_date_value",
            "2024-01-01 custom \"budget\" \"name\" 2024-06-15 100.00 USD\n",
        ),
        (
            "non_latin_account_name",
            "2024-01-15 * \"x\"\n  Активы:Банк -5.00 USD\n  Expenses:Misc 5.00 USD\n",
        ),
        (
            "section_header_comments",
            "; ====\n; HEADER\n; ====\n2024-01-01 open Assets:A\n",
        ),
        (
            "multiline_note_string",
            "2024-01-15 note Assets:Bank \"line 1\nline 2\"\n",
        ),
        (
            "comment_containing_quote",
            "; comment with \"a quote\n2024-01-01 open Assets:A\n",
        ),
        (
            "crlf_input",
            "2024-01-01 open Assets:A\r\n2024-01-02 open Assets:B\r\n",
        ),
        (
            "bare_cr_input",
            "2024-01-01 open Assets:A\r2024-01-02 open Assets:B\r",
        ),
        (
            "file_with_trailing_newlines",
            "2024-01-01 open Assets:A\n\n\n",
        ),
        ("file_without_trailing_newline", "2024-01-01 open Assets:A"),
        // Regression for Copilot #1: collect_trailing_comment
        // previously returned None for a directive with no
        // header-terminating NEWLINE token, which silently dropped
        // a same-line trailing comment at EOF when the file lacked
        // a trailing newline. The canonical formatter restores the
        // trailing newline, but the dropped comment was already
        // gone.
        (
            "trailing_comment_no_final_newline",
            "2024-01-15 open Assets:A ; trailing",
        ),
        (
            "posting_with_trailing_comment",
            "2024-01-15 * \"x\"\n  Assets:Cash -5.00 USD ; pocket\n  Expenses:Misc 5.00 USD\n",
        ),
        (
            "balance_assertion_with_meta",
            "2024-01-15 balance Assets:Cash 100.00 USD\n  source: \"bank\"\n",
        ),
        (
            "options_and_includes",
            "option \"title\" \"My Ledger\"\ninclude \"sub.beancount\"\nplugin \"my.plugin\" \"cfg\"\n",
        ),
        // ---- per-variant coverage ---------------------------------
        ("close_directive", "2024-12-31 close Assets:Cash\n"),
        ("commodity_directive", "2024-01-01 commodity HOOL\n"),
        ("note_directive", "2024-01-15 note Assets:Cash \"a note\"\n"),
        ("event_directive", "2024-01-15 event \"location\" \"NYC\"\n"),
        (
            "query_directive",
            "2024-01-15 query \"q1\" \"SELECT account\"\n",
        ),
        ("pad_directive", "2024-01-15 pad Assets:A Equity:Opening\n"),
        (
            "document_directive",
            "2024-06-01 document Assets:Bank \"stmt.pdf\" #q1\n",
        ),
        // Note: `#!` and `#+` anywhere on a line, not just at
        // line start, open the lexer's SHEBANG / EMACS_DIRECTIVE
        // tokens. The fixture places `#+` mid-line and tails it
        // with an unbalanced `"`: an incorrect state machine that
        // gated the opener on `at_line_start` would stay in Code
        // when it hit the `#+`, then flip to InString on the next
        // `"` and trap there for the remainder of the file. The
        // lexer-agreement property test catches that divergence,
        // and the round-trip body runs too because the parser
        // treats the mid-line EMACS_DIRECTIVE as same-line
        // trailing trivia under the directive-terminator rule.
        (
            "emacs_directive_mid_line_with_quote",
            "2024-01-15 open Assets:A #+stray \"q\n",
        ),
        ("pushtag_directive", "pushtag #active\n"),
        ("poptag_directive", "poptag #active\n"),
        ("pushmeta_directive", "pushmeta location: \"NYC\"\n"),
        ("popmeta_directive", "popmeta location:\n"),
    ];

    /// Number of fixtures in [`IDEMPOTENCE_MATRIX`] that legitimately
    /// produce zero typed directives — comment-only / empty /
    /// pragma-only inputs. The round-trip property test skips these
    /// (they have nothing to emit), but every OTHER fixture MUST
    /// exercise the body. Bumping this constant when adding such a
    /// fixture is the only manual maintenance the coverage floor
    /// needs; otherwise the floor (`IDEMPOTENCE_MATRIX.len() -
    /// ROUNDTRIP_KNOWN_ZERO_DIRECTIVE_FIXTURES`) tracks the matrix
    /// automatically.
    ///
    /// Today's zero-directive fixtures (skipped by the round-trip
    /// body), verified by an exhaustive probe against the live
    /// parser:
    ///
    /// - `empty`, `only_comment` — no directives at all.
    /// - `bare_cr_input` — the parser does not recognize bare CR
    ///   (without a following LF) as a directive terminator, so
    ///   the file's two would-be directives never surface as
    ///   structured tokens. The fixture's purpose is the
    ///   line-ending state-machine pass, not the round-trip body.
    /// - `pushtag_directive`, `poptag_directive`,
    ///   `pushmeta_directive`, `popmeta_directive` — pragma
    ///   directives don't surface as `Directive` variants on the
    ///   typed-AST side (the parser also rejects them today, so
    ///   they produce parse errors and the skip-on-errors guard
    ///   triggers).
    /// - `options_and_includes` — option / include / plugin lines
    ///   live on separate `ParseResult` collections, not on
    ///   `.directives`.
    ///
    /// Note: `comment_containing_quote` and
    /// `emacs_directive_mid_line_with_quote` BOTH exercise the
    /// body — each is paired with a parseable directive on the
    /// same line or an adjacent line, and the trivia token
    /// (comment / `EMACS_DIRECTIVE`) attaches as same-line or
    /// inter-directive trivia under the directive-terminator
    /// rule. Their purpose is the state-machine / lexer agreement
    /// property on a comment with an unbalanced `"`, not the
    /// zero-directive case.
    const ROUNDTRIP_KNOWN_ZERO_DIRECTIVE_FIXTURES: usize = 8;

    #[test]
    fn lf_to_crlf_outside_strings_preserves_string_interior() {
        // Bug: a flat in_string-only state machine would re-inject
        // CRLF inside multi-line strings, mutating the user's bytes.
        let s = "2024-01-15 note Assets:Bank \"line 1\nline 2\"\n";
        let out = lf_to_crlf_outside_strings(s);
        assert!(out.contains("line 1\nline 2"), "got: {out:?}");
        assert!(out.ends_with("\r\n"), "got: {out:?}");
    }

    #[test]
    fn lf_to_crlf_outside_strings_handles_comment_with_quote() {
        // Bug: an unbalanced `"` inside a `;` comment formerly flipped
        // in_string=true for the rest of the file, leaving every
        // subsequent newline as LF.
        let s = "; comment with \"a quote\n2024-01-01 open Assets:A\n";
        let out = lf_to_crlf_outside_strings(s);
        assert_eq!(
            out,
            "; comment with \"a quote\r\n2024-01-01 open Assets:A\r\n",
        );
    }

    #[test]
    fn lf_to_crlf_outside_strings_handles_percent_comment_with_quote() {
        let s = "% percent \"quote\n2024-01-01 open Assets:A\n";
        let out = lf_to_crlf_outside_strings(s);
        assert_eq!(out, "% percent \"quote\r\n2024-01-01 open Assets:A\r\n");
    }

    #[test]
    fn crlf_to_lf_preserves_crlf_inside_strings() {
        // Bug fix mirror: a Windows-authored multi-line string had
        // its CRLF folded to LF by the pre-parse normalizer too,
        // which silently mutated the user's bytes.
        let s = "2024-01-15 note Assets:Bank \"line1\r\nline2\"\r\n";
        let normalized = crlf_to_lf_outside_strings(s);
        // Outside the string, the trailing CRLF folds to LF; inside
        // the string, CRLF stays CRLF (user's bytes preserved).
        assert!(
            normalized.contains("\"line1\r\nline2\""),
            "got: {:?}",
            &*normalized
        );
        assert!(normalized.ends_with('\n') && !normalized.ends_with("\r\n"));
    }

    #[test]
    fn idempotence_matrix() {
        // The gofmt invariant in the file rustdoc: f(f(x)) == f(x)
        // on every accepted input. Each fixture below covers one
        // axis of the canonical-form spec; together they exercise
        // every directive kind and every spacing rule shared via
        // write_canonical_token_sequence.
        for (name, src) in IDEMPOTENCE_MATRIX {
            let once = format_source(src);
            let twice = format_source(&once);
            assert_eq!(
                once, twice,
                "idempotence broken on fixture `{name}`\n--- once ---\n{once}\n--- twice ---\n{twice}",
            );
        }
    }

    #[test]
    fn canonicalize_directives_roundtrips_every_synthesized_directive() {
        // For each canonical-form fixture: parse → take the typed
        // directives → run them through canonicalize_directives →
        // re-parse the canonical text → assert the parser reports
        // zero errors and the directive count is preserved.
        //
        // This is the proper end-to-end test of the two-pass shim
        // the FFI format.entry and rledger add/extract commands all
        // depend on. Without it, a future Directive variant added
        // to rustledger-core without matching coverage in
        // cst::format would silently round-trip to truncated text.
        //
        // Counter + assertion guards against silent-skip: if the
        // guard at the top of the loop ever filters too many
        // fixtures (e.g. a parser regression that drops directives
        // from previously-clean fixtures), the test fails instead
        // of silently passing with zero coverage.
        use rustledger_core::format::FormatConfig;
        let cfg = FormatConfig::default();
        let mut exercised = 0usize;
        for (name, src) in IDEMPOTENCE_MATRIX {
            let parsed = crate::parse(src);
            if parsed.errors.is_empty() && !parsed.directives.is_empty() {
                let dirs: Vec<&rustledger_core::Directive> =
                    parsed.directives.iter().map(|s| &s.value).collect();
                let formatted = super::canonicalize_directives(dirs.iter().copied(), &cfg)
                    .unwrap_or_else(|e| {
                        panic!("canonicalize_directives error on fixture `{name}`: {e}")
                    });
                let reparsed = crate::parse(&formatted);
                assert!(
                    reparsed.errors.is_empty(),
                    "round-trip parse errors on fixture `{name}`:\n--- formatted ---\n{formatted}\n--- errors ---\n{:?}",
                    reparsed.errors,
                );
                assert_eq!(
                    parsed.directives.len(),
                    reparsed.directives.len(),
                    "directive count drifted on fixture `{name}`\n--- formatted ---\n{formatted}",
                );
                exercised += 1;
            }
        }
        let expected = IDEMPOTENCE_MATRIX
            .len()
            .saturating_sub(ROUNDTRIP_KNOWN_ZERO_DIRECTIVE_FIXTURES);
        assert!(
            exercised >= expected,
            "only {exercised} fixtures exercised the round-trip body, \
             expected at least {expected} (= IDEMPOTENCE_MATRIX.len() - \
             {ROUNDTRIP_KNOWN_ZERO_DIRECTIVE_FIXTURES}). A parser \
             regression or a broken fixture is silently dropping coverage."
        );
    }

    /// `SHEBANG` / `EMACS_DIRECTIVE` lines (`#!…` / `#+…` at line
    /// start) also count as comments for the LSP-CRLF state
    /// machine. A stray quote inside such a line used to flip
    /// `in_string=true` for the rest of the file just like the
    /// `;` / `%` comment case the round-3 fix covered.
    #[test]
    fn lf_to_crlf_outside_strings_handles_emacs_directive_with_quote() {
        let s = "#+title: \"My Book\n2024-01-01 open Assets:A\n";
        let out = lf_to_crlf_outside_strings(s);
        assert_eq!(out, "#+title: \"My Book\r\n2024-01-01 open Assets:A\r\n");
    }

    #[test]
    fn lf_to_crlf_outside_strings_handles_shebang_with_quote() {
        let s = "#!shebang \"quote\n2024-01-01 open Assets:A\n";
        let out = lf_to_crlf_outside_strings(s);
        assert_eq!(out, "#!shebang \"quote\r\n2024-01-01 open Assets:A\r\n");
    }

    /// `#` NOT at line start is a TAG / HASH token; the state
    /// machine must NOT treat it as a comment opener.
    #[test]
    fn lf_to_crlf_outside_strings_hash_mid_line_is_not_comment() {
        let s = "2024-01-15 * \"x\" #tag1\n  Assets:A 1 USD\n";
        let out = lf_to_crlf_outside_strings(s);
        // Every LF outside strings becomes CRLF — including the
        // one ending the tag-bearing line.
        assert!(out.contains("#tag1\r\n"), "got: {out:?}");
        assert!(out.ends_with("\r\n"), "got: {out:?}");
    }

    /// Regression for Copilot #2 inline review on PR #1284: a
    /// previous `emit_amount_expression` dropped leading unary
    /// signs and parens, flipping the sign on
    /// `2024-01-15 balance Assets:A
    /// -1.00 USD` to `1.00 USD` — silent data corruption (a debit
    /// asserted as a credit). Byte-exact pins on every shape.
    #[test]
    fn balance_price_preserve_leading_unary_and_parens() {
        // Bare leading minus on balance.
        let src = "2024-01-15 balance Assets:A -1.00 USD\n";
        assert_eq!(
            format_source(src),
            "2024-01-15 balance Assets:A -1.00 USD\n"
        );

        // Bare leading minus on price (sign flip would change
        // every quote on the user's commodity).
        let src = "2024-01-15 price USD -1.00 EUR\n";
        assert_eq!(format_source(src), "2024-01-15 price USD -1.00 EUR\n");

        // Leading parenthesized expression. The previous code
        // dropped the `(`, which made the trailing `)` unbalanced
        // AND made the first-CURRENCY scan find the wrong token.
        let src = "2024-01-15 balance Assets:A (1 + 2) USD\n";
        assert_eq!(
            format_source(src),
            "2024-01-15 balance Assets:A (1 + 2) USD\n"
        );

        // Leading minus on a parenthesized arithmetic expression.
        let src = "2024-01-15 balance Assets:A -(1 + 2) USD\n";
        assert_eq!(
            format_source(src),
            "2024-01-15 balance Assets:A -(1 + 2) USD\n"
        );
    }

    /// Regression for Copilot #1 inline review on PR #1284:
    /// `collect_trailing_comment` used `?` on the header-terminating
    /// NEWLINE, silently dropping same-line trailing comments at
    /// EOF when the file had no final newline. The canonical
    /// formatter restores the trailing newline, but the dropped
    /// comment was already gone — a real-world case for editors
    /// that don't insert a trailing newline on save.
    #[test]
    fn trailing_comment_preserved_at_eof_without_newline() {
        let src = "2024-01-15 open Assets:A ; trailing";
        assert_eq!(format_source(src), "2024-01-15 open Assets:A ; trailing\n");
    }

    #[test]
    fn try_format_source_returns_ok_on_clean_input() {
        let src = "2024-01-15 open Assets:Cash\n";
        let out = super::try_format_source(src).expect("clean input should format");
        assert_eq!(out, super::format_source(src));
    }

    #[test]
    fn try_format_source_returns_err_on_parse_error() {
        // Bare `unparsable` text triggers parser errors. The
        // helper must surface them instead of silently emitting
        // canonical text around a broken file.
        let src = "this is not a directive at all\n";
        let err = super::try_format_source(src).expect_err("garbage should error");
        assert!(!err.is_empty(), "errors must not be empty");
    }

    #[test]
    fn cr_outside_strings_present_distinguishes_in_string_cr() {
        // CR inside a multi-line string literal must NOT count —
        // the formatter wouldn't fold it.
        let in_string_only = "2024-01-15 note Assets:Bank \"line1\r\nline2\"\n";
        assert!(!super::cr_outside_strings_present(in_string_only));

        // CR outside any string literal (CRLF line terminator)
        // counts — that's what crlf_to_lf_outside_strings would
        // fold.
        let crlf_terminator = "2024-01-01 open Assets:A\r\n";
        assert!(super::cr_outside_strings_present(crlf_terminator));

        // No `\r` at all — fast path.
        let lf_only = "2024-01-01 open Assets:A\n";
        assert!(!super::cr_outside_strings_present(lf_only));

        // CR inside a `;` comment is outside any string and counts.
        // (Beancount lexer's comment regex excludes the newline, so
        // the comment region ends at `\r`; either way, the predicate
        // says "yes, the formatter would fold this byte".)
        let comment_with_cr = "; comment with \"quote\rstuff\n";
        assert!(super::cr_outside_strings_present(comment_with_cr));
    }

    #[test]
    fn canonicalize_directives_directive_count_mismatch_is_reported() {
        // Drive the new DirectiveCountMismatch error variant.
        // Today's Directive variants all round-trip with matching
        // counts, so this test pins the Display rendering of the
        // variant (the user-facing message). The positive-count-
        // match path is exercised by
        // `canonicalize_directives_positive_count_check` below.
        let err = super::CanonicalizeError::DirectiveCountMismatch {
            input: 3,
            reparsed: 2,
        };
        let msg = format!("{err}");
        assert!(msg.contains("3 directive(s)"), "got: {msg}");
        assert!(msg.contains("2 survived"), "got: {msg}");
        assert!(msg.contains("rledger bug"), "got: {msg}");
    }

    /// Single source of truth for the variant → fixture mapping
    /// used by both the compile-time exhaustiveness check
    /// ([`_directive_variant_fixture_coverage`]) and the runtime
    /// semantic check
    /// ([`directive_variant_fixture_names_resolve_in_matrix`]).
    ///
    /// Each tuple is `(VariantName, fixture_name)`. The
    /// `VariantName` half is the string the runtime check uses to
    /// confirm the fixture parses to that variant; the
    /// `fixture_name` half is what the compile-time match returns
    /// for the same variant. A future `Directive::Hedge` variant
    /// only ships with canonical-form coverage if BOTH a new
    /// arm is added to the compile-time match AND a row here
    /// names a fixture that actually produces a `Hedge` on parse.
    const DIRECTIVE_VARIANT_FIXTURE_MAP: &[(&str, &str)] = &[
        ("Transaction", "transaction_with_cost_and_price"),
        ("Balance", "balance_with_arithmetic_and_tolerance"),
        ("Open", "only_directive"),
        ("Close", "close_directive"),
        ("Commodity", "commodity_directive"),
        ("Pad", "pad_directive"),
        ("Event", "event_directive"),
        ("Query", "query_directive"),
        ("Note", "note_directive"),
        ("Document", "document_directive"),
        ("Price", "price_with_thousands_separator"),
        ("Custom", "custom_with_date_value"),
    ];

    /// Lookup helper: variant tag string → fixture name. Used by
    /// the compile-time match below. Panics if the variant is not
    /// in the map (which would be an internal-consistency bug, not
    /// a user-facing case).
    const fn fixture_for_variant(tag: &str) -> &'static str {
        let mut i = 0;
        while i < DIRECTIVE_VARIANT_FIXTURE_MAP.len() {
            let (v, f) = DIRECTIVE_VARIANT_FIXTURE_MAP[i];
            // const_str equality: compare byte slices.
            let v_bytes = v.as_bytes();
            let t_bytes = tag.as_bytes();
            if v_bytes.len() == t_bytes.len() {
                let mut k = 0;
                let mut eq = true;
                while k < v_bytes.len() {
                    if v_bytes[k] != t_bytes[k] {
                        eq = false;
                        break;
                    }
                    k += 1;
                }
                if eq {
                    return f;
                }
            }
            i += 1;
        }
        panic!("DIRECTIVE_VARIANT_FIXTURE_MAP missing entry for variant tag");
    }

    /// Compile-time check that every `rustledger_core::Directive`
    /// variant has at least one source-text fixture in
    /// [`IDEMPOTENCE_MATRIX`] exercising its emit path. The
    /// function NEVER runs — its body is an exhaustive `match` over
    /// the `Directive` enum. Adding a new variant breaks
    /// compilation unless the author adds a match arm referencing
    /// `fixture_for_variant("NewVariantName")`, AND adds a row to
    /// [`DIRECTIVE_VARIANT_FIXTURE_MAP`] naming the fixture. The
    /// runtime test then confirms the fixture parses to a directive
    /// of that variant.
    ///
    /// The non-`Directive` pragma-style directives (Pushtag,
    /// Poptag, Pushmeta, Popmeta, options, includes, plugins)
    /// don't appear in the typed `Directive` enum; they're covered
    /// by separate fixtures whose names map directly into
    /// `IDEMPOTENCE_MATRIX`.
    #[allow(dead_code)]
    fn _directive_variant_fixture_coverage(d: &rustledger_core::Directive) -> &'static str {
        match d {
            rustledger_core::Directive::Transaction(_) => fixture_for_variant("Transaction"),
            rustledger_core::Directive::Balance(_) => fixture_for_variant("Balance"),
            rustledger_core::Directive::Open(_) => fixture_for_variant("Open"),
            rustledger_core::Directive::Close(_) => fixture_for_variant("Close"),
            rustledger_core::Directive::Commodity(_) => fixture_for_variant("Commodity"),
            rustledger_core::Directive::Pad(_) => fixture_for_variant("Pad"),
            rustledger_core::Directive::Event(_) => fixture_for_variant("Event"),
            rustledger_core::Directive::Query(_) => fixture_for_variant("Query"),
            rustledger_core::Directive::Note(_) => fixture_for_variant("Note"),
            rustledger_core::Directive::Document(_) => fixture_for_variant("Document"),
            rustledger_core::Directive::Price(_) => fixture_for_variant("Price"),
            rustledger_core::Directive::Custom(_) => fixture_for_variant("Custom"),
        }
    }

    #[test]
    fn directive_variant_fixture_names_resolve_in_matrix() {
        // Runtime mirror of the compile-time match above:
        //
        //   (1) every fixture name appears in IDEMPOTENCE_MATRIX;
        //   (2) parsing that fixture produces AT LEAST one
        //       directive of the variant the map row names.
        //
        // Without check (2) the compile-time match is satisfied by
        // any fixture-name string — a future contributor adding
        // a row `("Hedge", "only_comment")` would compile, the
        // lookup would resolve, and Hedge would ship with zero
        // canonical-form coverage. The semantic check rejects that
        // by parsing the named fixture and inspecting the
        // directive variant.
        use rustledger_core::Directive;
        fn matches_variant(d: &Directive, expected: &str) -> bool {
            matches!(
                (d, expected),
                (Directive::Transaction(_), "Transaction")
                    | (Directive::Balance(_), "Balance")
                    | (Directive::Open(_), "Open")
                    | (Directive::Close(_), "Close")
                    | (Directive::Commodity(_), "Commodity")
                    | (Directive::Pad(_), "Pad")
                    | (Directive::Event(_), "Event")
                    | (Directive::Query(_), "Query")
                    | (Directive::Note(_), "Note")
                    | (Directive::Document(_), "Document")
                    | (Directive::Price(_), "Price")
                    | (Directive::Custom(_), "Custom")
            )
        }
        for (variant, name) in DIRECTIVE_VARIANT_FIXTURE_MAP {
            let (_, src) = IDEMPOTENCE_MATRIX
                .iter()
                .find(|(n, _)| *n == *name)
                .unwrap_or_else(|| {
                    panic!(
                        "fixture `{name}` is named by \
                     DIRECTIVE_VARIANT_FIXTURE_MAP but missing from \
                     IDEMPOTENCE_MATRIX"
                    )
                });
            let parsed = crate::parse(src);
            let found = parsed
                .directives
                .iter()
                .any(|s| matches_variant(&s.value, variant));
            assert!(
                found,
                "fixture `{name}` is mapped to `Directive::{variant}` by \
                 DIRECTIVE_VARIANT_FIXTURE_MAP, but parsing it produced \
                 no directive of that variant (got {:?}). This silently \
                 leaves the variant without canonical-form coverage.",
                parsed
                    .directives
                    .iter()
                    .map(|s| std::mem::discriminant(&s.value))
                    .collect::<Vec<_>>()
            );
        }
    }

    /// Property test: the `SourceState` classification used by the
    /// line-ending helpers must agree with the lexer's
    /// classification on every byte of a corpus of fixtures.
    ///
    /// Concretely: for every byte offset in every fixture, the
    /// state machine's `InString` periods MUST line up with the
    /// lexer's STRING token spans, and its `InComment` periods MUST
    /// line up with the union of COMMENT / SHEBANG /
    /// `EMACS_DIRECTIVE` token spans. A divergence — e.g. the lexer
    /// gains a new comment lexeme that the state machine treats as
    /// code — fails this test instead of silently mutating user
    /// bytes inside the new lexeme on a line-ending round-trip.
    #[test]
    fn source_state_classification_agrees_with_lexer() {
        use crate::logos_lexer::{Token, tokenize_lossless};

        for (name, src) in IDEMPOTENCE_MATRIX {
            // Run the lexer to get authoritative classification of
            // each token. Build a per-byte map of expected state.
            let tokens = tokenize_lossless(src);
            let mut expected = vec![SourceState::Code; src.len()];
            for (token, span) in &tokens {
                let classify = match token {
                    Token::String(_) => Some(SourceState::InString),
                    Token::Comment(_) | Token::Shebang(_) | Token::EmacsDirective(_) => {
                        Some(SourceState::InComment)
                    }
                    _ => None,
                };
                if let Some(state) = classify {
                    for byte in &mut expected[span.start..span.end] {
                        *byte = state;
                    }
                }
            }

            // Run the state-machine classifier and compare per
            // byte. We skip ONLY the exact bytes where a
            // transition fires — the lexer includes those bytes
            // inside the resulting token while the state machine
            // tags them with the PRE-transition state (the
            // 'opener' is still Code, the closing LF is still
            // InComment). Tracking the transition indices
            // explicitly (rather than skipping every `"`/`;`/`%`
            // / newline byte) means a state-machine bug at any
            // non-transition `"`/`;`/`%` byte — e.g. inside a
            // comment or string — surfaces as a real failure
            // instead of being silently masked.
            let (actual, transitions) = classify_source_bytes_with_transitions(src);

            for (i, (&want, &got)) in expected.iter().zip(actual.iter()).enumerate() {
                if transitions.contains(&i) {
                    continue;
                }
                assert_eq!(
                    want,
                    got,
                    "state-machine / lexer disagreement on fixture `{name}` \
                     at byte {i} ({:?}): lexer said {want:?}, state machine said {got:?}",
                    src.as_bytes()[i] as char
                );
            }
        }
    }

    /// Walk `s` through the same state-machine logic the
    /// line-ending helpers use, returning a per-byte classification
    /// AND the set of byte indices where a state transition
    /// fired. The transition indices are the ONLY bytes where the
    /// state machine and the lexer can legitimately disagree (the
    /// off-by-one at opener / closer / terminator); callers
    /// comparing against the lexer should skip exactly those
    /// indices and assert agreement everywhere else.
    fn classify_source_bytes_with_transitions(
        s: &str,
    ) -> (Vec<SourceState>, std::collections::HashSet<usize>) {
        let (body, bom_len) = match s.strip_prefix('\u{FEFF}') {
            Some(rest) => (rest, '\u{FEFF}'.len_utf8()),
            None => (s, 0),
        };
        let mut out: Vec<SourceState> = vec![SourceState::Code; s.len()];
        let mut transitions = std::collections::HashSet::new();
        let mut chars = body.char_indices().peekable();
        let mut state = SourceState::Code;
        let mut prev_was_backslash = false;
        while let Some((rel_i, ch)) = chars.next() {
            let i = bom_len + rel_i;
            let peek = chars.peek().map(|&(_, c)| c);
            // Classify THIS byte under the state BEFORE advancing.
            for byte in &mut out[i..i + ch.len_utf8()] {
                *byte = state;
            }
            let prev_state = state;
            let next_state = advance_source_state(ch, peek, state, &mut prev_was_backslash);
            // Record only OPENING transitions and the comment-
            // closing newline, where the state machine and lexer
            // legitimately disagree on this single byte:
            //   - Code → InString : opening `"` is Code-side but
            //     the lexer puts it inside the STRING token.
            //   - Code → InComment: opening `;` / `%` / `#!` /
            //     `#+` is Code-side but the lexer puts it inside
            //     the COMMENT / SHEBANG / EMACS_DIRECTIVE token.
            //   - InComment → Code: the `\n` ending the comment is
            //     classified InComment by the state machine but
            //     sits OUTSIDE the comment token (the lexer's
            //     `[^\n\r]*` excludes it).
            // The InString → Code transition (closing `"`) is NOT
            // a disagreement: the state machine still tags that
            // byte as InString (pre-transition), and the lexer
            // includes the closing `"` inside the STRING token.
            // Skipping it would silently mask a real bug.
            if next_state != state {
                let opening = matches!(prev_state, SourceState::Code)
                    && matches!(next_state, SourceState::InString | SourceState::InComment);
                let comment_close = matches!(prev_state, SourceState::InComment)
                    && matches!(next_state, SourceState::Code);
                if opening || comment_close {
                    transitions.insert(i);
                    // For a `#!` or `#+` opener the lexer's token
                    // span begins at the `#`, so the second byte
                    // (`!` / `+`) is also a "before the lexer's
                    // token start" byte the state machine tags as
                    // Code. Record it too.
                    if matches!(ch, '#') && matches!(peek, Some('!' | '+')) {
                        transitions.insert(i + 1);
                    }
                }
            }
            state = next_state;
        }
        (out, transitions)
    }

    #[test]
    fn canonicalize_directives_positive_count_check() {
        // Pin the success path of the count check: pass a real
        // multi-directive input through canonicalize_directives and
        // assert that the output round-trips to the SAME directive
        // count. Without this test, a regression that always
        // returned CountMismatch (e.g. `==` instead of `!=` on the
        // count comparison) would be caught only on production
        // calls, not in CI. Together with the Display test above,
        // this gives coverage of both arms of the count guard.
        use rustledger_core::format::FormatConfig;
        let cfg = FormatConfig::default();
        let src = "2024-01-01 open Assets:Cash\n2024-01-02 open Assets:Bank\n2024-01-03 close Assets:Cash\n";
        let parsed = crate::parse(src);
        assert_eq!(
            parsed.directives.len(),
            3,
            "fixture must parse to 3 directives"
        );
        let dirs: Vec<&rustledger_core::Directive> =
            parsed.directives.iter().map(|s| &s.value).collect();
        let formatted = super::canonicalize_directives(dirs.iter().copied(), &cfg)
            .expect("canonicalize_directives should succeed on this input");
        let reparsed = crate::parse(&formatted);
        assert_eq!(
            reparsed.directives.len(),
            3,
            "count check accepted but round-trip dropped directives: {formatted}"
        );
    }
}
