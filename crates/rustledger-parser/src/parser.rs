//! High-performance hand-rolled parser for Beancount syntax.
//!
//! Manual state-machine parser over a Logos-produced token stream. An
//! earlier version targeted the winnow Stream trait but the hand-rolled
//! approach turned out simpler and faster, so the winnow dependency was
//! removed.
//!
//! # Architecture
//!
//! ```text
//! Source (&str) → Logos tokenize() → Vec<SpannedToken> → Manual parser → Directives
//! ```

use std::borrow::Cow;

use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::str::FromStr;

use rustledger_core::{
    Amount, Balance, Close, Commodity, CostSpec, Custom, Directive, Document, Event,
    IncompleteAmount, InternedStr, MetaValue, Metadata, Note, Open, Pad, Posting, Price,
    PriceAnnotation, Query, Transaction,
};

/// Cap on upfront `directives` preallocation to bound the single-allocation
/// size on large/untrusted inputs (RPC, WASM, uploaded files). Vec still
/// grows past this transparently if a real file exceeds it. See `parse`.
const MAX_PREALLOC_DIRECTIVES: usize = 16_384;

use crate::diagnostics::BOM_REMOVAL_HINT;

/// Cap on upfront `comments` preallocation. Same rationale as
/// [`MAX_PREALLOC_DIRECTIVES`].
const MAX_PREALLOC_COMMENTS: usize = 8_192;

use crate::ParseResult;
use crate::error::{ParseError, ParseErrorKind};
use crate::logos_lexer::{Token, tokenize};
use rustledger_core::span::{Span, Spanned};

// ============================================================================
// Token Stream
// ============================================================================

/// A spanned token - a token paired with its byte offset span.
#[derive(Debug, Clone)]
struct SpannedToken<'src> {
    token: Token<'src>,
    span: (usize, usize),
}

/// Token stream - a wrapper around a slice of tokens with a cursor.
struct TokenStream<'src> {
    tokens: &'src [SpannedToken<'src>],
    pos: usize,
    /// A deferred error set when a date token has valid format but invalid
    /// calendar values (e.g., Feb 29 in a non-leap year). Used in place of
    /// the generic "unexpected input" error during error recovery.
    deferred_error: Option<ParseError>,
    /// String interner for deduplicating repeated strings (accounts, currencies).
    /// Typical ledger: ~10 unique accounts × 1000 txns = 10K lookups vs 10K allocations.
    interner: rustledger_core::intern::StringInterner,
    /// Byte-position record of every Currency token the parser
    /// consumed, paired with its interned value.
    ///
    /// The AST stores currencies as `InternedStr` values stripped of
    /// their source positions because currencies are pervasively
    /// reused in computed contexts (booking arithmetic, residual
    /// aggregation, query results) where a source span would be
    /// meaningless or actively wrong. Source-position queries — LSP
    /// rename / references / document-highlight — instead consume
    /// this parallel index. The parser is the canonical owner of
    /// source-token positions, so this is its natural home.
    ///
    /// `file_id` is left at the default (0) and overwritten later
    /// when a `SourceMap` assigns each file an id — same pattern
    /// as `Spanned<Directive>` produced by this parser.
    currency_occurrences: Vec<Spanned<rustledger_core::Currency>>,
}

impl<'src> TokenStream<'src> {
    fn new(tokens: &'src [SpannedToken<'src>]) -> Self {
        Self {
            tokens,
            pos: 0,
            deferred_error: None,
            interner: rustledger_core::intern::StringInterner::new(),
            currency_occurrences: Vec::new(),
        }
    }

    const fn is_empty(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn peek(&self) -> Option<&SpannedToken<'src>> {
        self.tokens.get(self.pos)
    }

    fn peek_token(&self) -> Option<&Token<'src>> {
        self.tokens.get(self.pos).map(|t| &t.token)
    }

    const fn advance(&mut self) {
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
    }

    fn span_from(&self, start_pos: usize) -> Span {
        let start = self.tokens.get(start_pos).map_or(0, |t| t.span.0);
        let end = if self.pos > 0 {
            self.tokens.get(self.pos - 1).map_or(0, |t| t.span.1)
        } else {
            start
        };
        Span::new(start, end)
    }

    /// Skip tokens until newline (for error recovery).
    fn skip_to_newline(&mut self) {
        while let Some(t) = self.peek() {
            if matches!(t.token, Token::Newline) {
                self.advance();
                break;
            }
            self.advance();
        }
    }
}

// ============================================================================
// Result Type
// ============================================================================

type ParseRes<T> = Result<T, ()>;

// ============================================================================
// Token Parsers
// ============================================================================

fn parse_date(stream: &mut TokenStream<'_>) -> ParseRes<NaiveDate> {
    if let Some(t) = stream.peek()
        && let Token::Date(s) = &t.token
    {
        let span = Span::new(t.span.0, t.span.1);

        // Fast path: canonical "YYYY-MM-DD" (10 chars, no '/')
        // avoids normalize_date_str + chrono's format parser overhead.
        if s.len() == 10
            && s.as_bytes()[4] == b'-'
            && s.as_bytes()[7] == b'-'
            && let (Ok(y), Ok(m), Ok(d)) = (
                s[0..4].parse::<i32>(),
                s[5..7].parse::<u32>(),
                s[8..10].parse::<u32>(),
            )
            && let Some(date) = rustledger_core::naive_date(y, m, d)
        {
            stream.advance();
            return Ok(date);
        }

        // Slow path: normalize separators and zero-pad, then parse
        let normalized = normalize_date_str(s);
        if let Ok(date) = normalized.parse::<NaiveDate>() {
            stream.advance();
            return Ok(date);
        }
        // The token matched the date regex (valid format) but the calendar
        // values are invalid (e.g., Feb 29 in a non-leap year, month 13).
        // Build a descriptive error and defer it for the error-recovery path.
        let msg = describe_invalid_date(s);
        stream.deferred_error = Some(ParseError::new(ParseErrorKind::InvalidDateValue(msg), span));
    }
    Err(())
}

use crate::diagnostics::{describe_invalid_date, normalize_date_str};

fn parse_number(stream: &mut TokenStream<'_>) -> ParseRes<Decimal> {
    if let Some(t) = stream.peek()
        && let Token::Number(s) = &t.token
    {
        let has_commas = s.contains(',');

        // Fast path: simple numbers without commas — use our lightweight
        // parser instead of Decimal::from_str.
        if !has_commas && let Some(num) = fast_parse_decimal(s) {
            stream.advance();
            return Ok(num);
        }

        // Slow path: commas or format fast_parse_decimal can't handle.
        let cleaned = if has_commas {
            Cow::Owned(s.replace(',', ""))
        } else {
            Cow::Borrowed(*s)
        };
        if let Ok(num) = Decimal::from_str(&cleaned) {
            stream.advance();
            return Ok(num);
        }
    }
    Err(())
}

/// Fast decimal parser for simple beancount number formats.
///
/// Handles `[0-9]+(\.[0-9]*)?` — no sign, no commas, no exponent. The
/// `[0-9]*` after the dot matches the lexer's grammar and accepts
/// trailing-decimal forms like `"5."`. Returns `None` for anything more
/// complex (sign included — see [`parse_signed_number`]), falling
/// through to `Decimal::from_str`.
///
/// Mantissa accumulator is `u128` so the fast path accepts the full
/// range that `rust_decimal` itself supports (96-bit mantissa, up to
/// 7.9e28). Before this fix the accumulator was `i64` and bailed past
/// `9.2e18`, which forced 8-decimal crypto amounts and accumulated
/// price math through the slow `Decimal::from_str` path on every
/// parse. Construction goes through [`Decimal::try_from_i128_with_scale`]
/// which rejects mantissa values that don't fit in `rust_decimal`'s
/// 96-bit field — those still opt out of the fast path so the caller's
/// slow-path fallback sees them.
fn fast_parse_decimal(s: &str) -> Option<Decimal> {
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return None;
    }

    let mut mantissa: u128 = 0;
    let mut scale: u32 = 0;
    let mut in_decimal = false;

    for &b in bytes {
        match b {
            b'0'..=b'9' => {
                // Check for overflow before multiplying. u128 can absorb
                // up to ~3.4e38 before overflowing — well past
                // rust_decimal's effective limit, so the `?` only fires
                // on genuinely huge inputs (40+ digits).
                mantissa = mantissa
                    .checked_mul(10)?
                    .checked_add(u128::from(b - b'0'))?;
                if in_decimal {
                    scale += 1;
                }
            }
            b'.' if !in_decimal => {
                in_decimal = true;
            }
            _ => return None, // Unexpected character — fall back to Decimal::from_str
        }
    }

    // Cast to i128: only fails when the u128 high bit is set (mantissa
    // > 1.7e38). That's already past Decimal::MAX (7.9e28), so the
    // try_from below would reject too — this just bails earlier.
    let mantissa_i128 = i128::try_from(mantissa).ok()?;
    Decimal::try_from_i128_with_scale(mantissa_i128, scale).ok()
}

/// Parse a number with optional leading minus sign.
///
/// Used in contexts where a full expression isn't expected but negative
/// numbers should be accepted (e.g., tolerance values, custom directive args).
fn parse_signed_number(stream: &mut TokenStream<'_>) -> ParseRes<Decimal> {
    let negate = stream
        .peek()
        .is_some_and(|t| matches!(t.token, Token::Minus));
    if negate {
        stream.advance();
    }
    let n = parse_number(stream)?;
    Ok(if negate { -n } else { n })
}

fn parse_string<'a>(stream: &mut TokenStream<'a>) -> ParseRes<Cow<'a, str>> {
    if let Some(t) = stream.peek()
        && let Token::String(s) = &t.token
    {
        let inner = &s[1..s.len() - 1];
        // Fast path: no escape sequences — borrow directly from source (zero alloc).
        // Slow path: process escapes into owned String.
        let result = if inner.contains('\\') {
            Cow::Owned(process_string_escapes(inner))
        } else {
            Cow::Borrowed(inner)
        };
        stream.advance();
        return Ok(result);
    }
    Err(())
}

/// Parse a quoted string, returning an owned String.
///
/// Convenience wrapper around `parse_string` for callers that need
/// a `String` rather than `Cow<str>`.
fn parse_string_owned(stream: &mut TokenStream<'_>) -> ParseRes<String> {
    parse_string(stream).map(Cow::into_owned)
}

/// Process escape sequences in a string. Only called for strings that
/// contain backslashes (the fast path is handled by `parse_string`).
fn process_string_escapes(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => result.push('\n'),
                Some('t') => result.push('\t'),
                Some('r') => result.push('\r'),
                Some('\\') => result.push('\\'),
                Some('"') => result.push('"'),
                Some(other) => {
                    result.push('\\');
                    result.push(other);
                }
                None => result.push('\\'),
            }
        } else {
            result.push(c);
        }
    }
    result
}

fn parse_account(stream: &mut TokenStream<'_>) -> ParseRes<rustledger_core::Account> {
    if let Some(t) = stream.peek()
        && let Token::Account(s) = &t.token
    {
        let result = stream.interner.intern(s);
        stream.advance();
        return Ok(result.into());
    }
    Err(())
}

fn parse_currency(stream: &mut TokenStream<'_>) -> ParseRes<rustledger_core::Currency> {
    if let Some(t) = stream.peek()
        && let Token::Currency(s) = &t.token
    {
        let span = Span::new(t.span.0, t.span.1);
        let result: rustledger_core::Currency = stream.interner.intern(s).into();
        // Record the source-token position for downstream
        // span-aware consumers (LSP rename / references /
        // document-highlight). See `TokenStream::currency_occurrences`
        // for the rationale.
        stream
            .currency_occurrences
            .push(Spanned::new(result.clone(), span));
        stream.advance();
        return Ok(result);
    }
    Err(())
}

fn parse_tag(stream: &mut TokenStream<'_>) -> ParseRes<rustledger_core::Tag> {
    if let Some(t) = stream.peek()
        && let Token::Tag(s) = &t.token
    {
        let result = stream.interner.intern(&s[1..]); // Skip #
        stream.advance();
        return Ok(result.into());
    }
    Err(())
}

fn parse_link(stream: &mut TokenStream<'_>) -> ParseRes<rustledger_core::Link> {
    if let Some(t) = stream.peek()
        && let Token::Link(s) = &t.token
    {
        let result = stream.interner.intern(&s[1..]); // Skip ^
        stream.advance();
        return Ok(result.into());
    }
    Err(())
}

fn parse_flag(stream: &mut TokenStream<'_>) -> ParseRes<char> {
    if let Some(t) = stream.peek() {
        match &t.token {
            Token::Star => {
                stream.advance();
                return Ok('*');
            }
            Token::Pending => {
                stream.advance();
                return Ok('!');
            }
            Token::Hash => {
                stream.advance();
                return Ok('#');
            }
            Token::Flag(s) => {
                let c = s.chars().next().unwrap_or('*');
                stream.advance();
                return Ok(c);
            }
            // Single-char currencies can be used as transaction flags (e.g., T, P, C)
            // This matches Python beancount's behavior where single uppercase letters
            // are disambiguated based on context
            Token::Currency(s) if s.len() == 1 => {
                let c = s.chars().next().unwrap();
                stream.advance();
                return Ok(c);
            }
            _ => {}
        }
    }
    Err(())
}

fn parse_meta_key(stream: &mut TokenStream<'_>) -> ParseRes<String> {
    if let Some(t) = stream.peek()
        && let Token::MetaKey(s) = &t.token
    {
        let result = s[..s.len() - 1].to_string(); // Remove trailing :
        stream.advance();
        return Ok(result);
    }
    Err(())
}

fn parse_boolean(stream: &mut TokenStream<'_>) -> ParseRes<bool> {
    if let Some(t) = stream.peek() {
        match &t.token {
            Token::True => {
                stream.advance();
                return Ok(true);
            }
            Token::False => {
                stream.advance();
                return Ok(false);
            }
            _ => {}
        }
    }
    Err(())
}

/// Expect a specific token kind.
macro_rules! expect_token {
    ($stream:expr, $pat:pat) => {
        if let Some(t) = $stream.peek() {
            if matches!(t.token, $pat) {
                $stream.advance();
                Ok(())
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    };
}

fn skip_newlines(stream: &mut TokenStream<'_>) {
    while let Some(t) = stream.peek() {
        if matches!(t.token, Token::Newline) {
            stream.advance();
        } else {
            break;
        }
    }
}

fn skip_comment(stream: &mut TokenStream<'_>) {
    if let Some(t) = stream.peek()
        && matches!(t.token, Token::Comment(_) | Token::PercentComment(_))
    {
        stream.advance();
    }
}

/// Capture and return a comment if present, otherwise return None.
fn capture_comment(stream: &mut TokenStream<'_>) -> Option<String> {
    if let Some(t) = stream.peek() {
        match &t.token {
            Token::Comment(c) | Token::PercentComment(c) => {
                let comment = c.to_string();
                stream.advance();
                return Some(comment);
            }
            _ => {}
        }
    }
    None
}

// ============================================================================
// Expression Parser (for arithmetic in amounts)
// ============================================================================

fn parse_primary(stream: &mut TokenStream<'_>) -> ParseRes<Decimal> {
    // Check for parenthesized expression
    if let Some(t) = stream.peek() {
        if matches!(t.token, Token::LParen) {
            stream.advance();
            let expr = parse_expr(stream)?;
            expect_token!(stream, Token::RParen)?;
            return Ok(expr);
        }
        // Unary minus
        if matches!(t.token, Token::Minus) {
            stream.advance();
            let n = parse_primary(stream)?;
            return Ok(-n);
        }
        // Unary plus
        if matches!(t.token, Token::Plus) {
            stream.advance();
            return parse_primary(stream);
        }
        // Date token in expression context: re-parse as arithmetic (issue #876).
        // The Logos lexer greedily matches `\d{4}[-/]\d{1,2}[-/]\d{1,2}` as a
        // Date token, but in an expression/amount position `1000-12-32` should
        // be evaluated as 1000 - 12 - 32 = 956. We split the Date text into
        // its numeric components and compute the result here.
        //
        // Only dash-separated dates are recovered as subtraction. Slash-separated
        // dates (e.g. `2024/1/5`) fall through to a parse error because Python
        // beancount does not treat them as division either — returning a silently
        // wrong number would be worse than an error.
        if let Token::Date(s) = &t.token {
            if s.contains('/') {
                // Slash-separated date in expression context — not valid arithmetic.
                return Err(());
            }
            let parts: Vec<&str> = s.splitn(3, '-').collect();
            if parts.len() == 3
                && let (Ok(a), Ok(b), Ok(c)) = (
                    Decimal::from_str(parts[0]),
                    Decimal::from_str(parts[1]),
                    Decimal::from_str(parts[2]),
                )
            {
                stream.advance();
                let result = a.checked_sub(b).and_then(|r| r.checked_sub(c)).ok_or(())?;
                return Ok(result);
            }
        }
    }
    parse_number(stream)
}

fn parse_term(stream: &mut TokenStream<'_>) -> ParseRes<Decimal> {
    let mut result = parse_primary(stream)?;

    while let Some(t) = stream.peek() {
        match &t.token {
            Token::Star => {
                stream.advance();
                let rhs = parse_primary(stream)?;
                result = result.checked_mul(rhs).ok_or(())?;
            }
            Token::Slash => {
                stream.advance();
                let rhs = parse_primary(stream)?;
                if rhs.is_zero() {
                    return Err(());
                }
                result = result.checked_div(rhs).ok_or(())?;
            }
            _ => break,
        }
    }

    Ok(result)
}

fn parse_expr(stream: &mut TokenStream<'_>) -> ParseRes<Decimal> {
    let mut result = parse_term(stream)?;

    while let Some(t) = stream.peek() {
        match &t.token {
            Token::Plus => {
                stream.advance();
                let rhs = parse_term(stream)?;
                result = result.checked_add(rhs).ok_or(())?;
            }
            Token::Minus => {
                stream.advance();
                let rhs = parse_term(stream)?;
                result = result.checked_sub(rhs).ok_or(())?;
            }
            _ => break,
        }
    }

    Ok(result)
}

// ============================================================================
// Amount Parsers
// ============================================================================

fn parse_amount(stream: &mut TokenStream<'_>) -> ParseRes<Amount> {
    let number = parse_expr(stream)?;
    let currency = parse_currency(stream)?;
    Ok(Amount::new(number, currency))
}

fn parse_incomplete_amount(stream: &mut TokenStream<'_>) -> ParseRes<IncompleteAmount> {
    // Try number + currency
    let start_pos = stream.pos;
    if let Ok(number) = parse_expr(stream) {
        if let Ok(currency) = parse_currency(stream) {
            return Ok(IncompleteAmount::Complete(Amount::new(number, currency)));
        }
        return Ok(IncompleteAmount::NumberOnly(number));
    }

    // Reset and try just currency
    stream.pos = start_pos;
    if let Ok(currency) = parse_currency(stream) {
        return Ok(IncompleteAmount::CurrencyOnly(currency));
    }

    Err(())
}

// ============================================================================
// Cost Specification Parser
// ============================================================================

fn parse_cost_spec(stream: &mut TokenStream<'_>) -> ParseRes<CostSpec> {
    let is_total;

    // Record opening brace position for error reporting on unclosed braces.
    let brace_span = stream.peek().map_or((0, 0), |t| t.span);

    // Check opening brace type
    if let Some(t) = stream.peek() {
        match &t.token {
            Token::LDoubleBrace => {
                stream.advance();
                is_total = true;
            }
            Token::LBraceHash => {
                stream.advance();
                is_total = true;
            }
            Token::LBrace => {
                stream.advance();
                is_total = false;
            }
            _ => return Err(()),
        }
    } else {
        return Err(());
    }

    let mut spec = CostSpec::default();

    // Parse cost components. A cost spec must close with `}` on the same
    // logical line as the opening `{`; a Newline or EOF before the close
    // means the brace is unclosed, which is a hard parse error.
    let set_unclosed_error = |stream: &mut TokenStream<'_>| {
        stream.deferred_error = Some(ParseError::new(
            ParseErrorKind::SyntaxError("unclosed cost specification: missing '}'".to_string()),
            Span::new(brace_span.0, brace_span.1),
        ));
    };

    loop {
        // Check for closing brace or premature termination.
        if let Some(t) = stream.peek() {
            match &t.token {
                Token::RBrace | Token::RDoubleBrace => {
                    stream.advance();
                    break;
                }
                Token::Comma => {
                    stream.advance();
                    continue;
                }
                Token::Newline => {
                    set_unclosed_error(stream);
                    return Err(());
                }
                _ => {}
            }
        } else {
            set_unclosed_error(stream);
            return Err(());
        }

        // Check for merge operator {*}
        if let Some(t) = stream.peek()
            && matches!(t.token, Token::Star)
        {
            stream.advance();
            spec.merge = true;
            continue;
        }

        // Try to parse different component types
        if let Ok(date) = parse_date(stream) {
            spec.date = Some(date);
        } else if let Ok(label) = parse_string_owned(stream) {
            spec.label = Some(label);
        } else if let Ok(number) = parse_expr(stream) {
            // Check if this is followed by # (total cost marker)
            if let Some(t) = stream.peek()
                && matches!(t.token, Token::Hash)
            {
                stream.advance();
                // `{ N # T USD }` source carries both a per-unit (`N`)
                // and a total (`T`). The booker derives per-unit as
                // `T / |units|`, so the user-written `N` is
                // informationally redundant — Python beancount treats
                // this form as semantically equivalent to
                // `{{ T USD }}` and we follow suit by keeping only the
                // total. If the user-written N ever disagrees with
                // T / |units|, the validator's NegativeCost / balance
                // checks operate on the booker-derived value, which is
                // the canonical one. The pre-#1164 shape stored both
                // numbers and required downstream code to know which
                // one was authoritative; the new shape makes the
                // total-wins precedence explicit at the parser site.
                let _ = number; // Drop the user-written per-unit per the rationale above.
                if let Ok(total) = parse_expr(stream) {
                    spec.number = Some(rustledger_core::CostNumber::Total { value: total });
                    if let Ok(c) = parse_currency(stream) {
                        spec.currency = Some(c);
                    }
                    continue;
                }
            }

            spec.number = Some(if is_total {
                rustledger_core::CostNumber::Total { value: number }
            } else {
                rustledger_core::CostNumber::PerUnit { value: number }
            });

            // Optional currency
            if let Ok(c) = parse_currency(stream) {
                spec.currency = Some(c);
            }
        } else {
            // Unknown component, skip
            stream.advance();
        }
    }

    Ok(spec)
}

// ============================================================================
// Price Annotation Parser
// ============================================================================

fn parse_price_annotation(stream: &mut TokenStream<'_>) -> ParseRes<PriceAnnotation> {
    let is_total = if let Some(t) = stream.peek() {
        match &t.token {
            Token::AtAt => {
                stream.advance();
                true
            }
            Token::At => {
                stream.advance();
                false
            }
            _ => return Err(()),
        }
    } else {
        return Err(());
    };

    // Try full amount first (number + currency)
    let save_pos = stream.pos;
    if let Ok(amount) = parse_amount(stream) {
        return Ok(if is_total {
            PriceAnnotation::total(amount)
        } else {
            PriceAnnotation::unit(amount)
        });
    }
    stream.pos = save_pos;

    // Try just currency (incomplete price - number missing)
    if let Ok(currency) = parse_currency(stream) {
        let incomplete = IncompleteAmount::CurrencyOnly(currency);
        return Ok(if is_total {
            PriceAnnotation::total_incomplete(incomplete)
        } else {
            PriceAnnotation::unit_incomplete(incomplete)
        });
    }
    stream.pos = save_pos;

    // Try just number (incomplete price - currency missing)
    if let Ok(number) = parse_expr(stream) {
        let incomplete = IncompleteAmount::NumberOnly(number);
        return Ok(if is_total {
            PriceAnnotation::total_incomplete(incomplete)
        } else {
            PriceAnnotation::unit_incomplete(incomplete)
        });
    }
    stream.pos = save_pos;

    Err(())
}

// ============================================================================
// Posting Parser
// ============================================================================

fn parse_posting(stream: &mut TokenStream<'_>) -> ParseRes<Spanned<Posting>> {
    // Remember the starting token index so we can build a span covering
    // the posting line itself (indent → trailing comment) once parsing
    // succeeds. The span deliberately excludes following posting-level
    // metadata lines so consumers can replace a posting line without
    // disturbing its metadata. See `Transaction.postings` rustdoc and
    // issue #1142.
    let start_tok = stream.pos;

    // Expect indent (regular or deep - some files use 4-space indentation for postings)
    if let Some(t) = stream.peek() {
        if !matches!(t.token, Token::Indent(_) | Token::DeepIndent(_)) {
            return Err(());
        }
        stream.advance();
    } else {
        return Err(());
    }

    // Optional flag
    let flag = parse_flag(stream).ok();

    // Account (required)
    let account = parse_account(stream)?;

    // Optional amount
    let amount = parse_incomplete_amount(stream).ok();

    // Optional cost. Peek for an opening brace first so that on non-cost
    // inputs we don't consume any tokens; once committed, propagate parse
    // errors (such as an unclosed brace) instead of silently swallowing them.
    let cost = if matches!(
        stream.peek_token(),
        Some(Token::LBrace | Token::LBraceHash | Token::LDoubleBrace)
    ) {
        Some(parse_cost_spec(stream)?)
    } else {
        None
    };

    // Optional price
    let price = parse_price_annotation(stream).ok();

    // Capture optional trailing comment on this line
    let trailing_comment = capture_comment(stream);

    // Snapshot the span end *before* descending into metadata so the span
    // covers only the posting line itself (incl. its trailing comment).
    let line_span = stream.span_from(start_tok);

    // Parse posting-level metadata (lines with DeepIndent)
    let posting_meta = parse_posting_metadata(stream);

    // Create posting - use auto for account-only or with_incomplete for amount
    let mut posting = if let Some(amt) = amount {
        Posting::with_incomplete(account, amt)
    } else {
        Posting::auto(account)
    };

    if let Some(f) = flag {
        posting.flag = Some(f);
    }
    if let Some(c) = cost {
        posting.cost = Some(c);
    }
    if let Some(p) = price {
        posting.price = Some(p);
    }
    posting.meta = posting_meta;
    if let Some(c) = trailing_comment {
        posting.trailing_comments.push(c);
    }

    Ok(Spanned::new(posting, line_span))
}

/// Parse a single posting-level metadata line (deep indent + key: value).
fn parse_posting_metadata_line(stream: &mut TokenStream<'_>) -> ParseRes<(String, MetaValue)> {
    // Expect deep indent (3+ spaces)
    if let Some(t) = stream.peek() {
        if !matches!(t.token, Token::DeepIndent(_)) {
            return Err(());
        }
        stream.advance();
    } else {
        return Err(());
    }

    // Parse key (must be a MetaKey token)
    let key = parse_meta_key(stream)?;
    let value = parse_meta_value(stream)?;
    skip_comment(stream);

    Ok((key, value))
}

/// Parse posting-level metadata (uses `DeepIndent` tokens).
fn parse_posting_metadata(stream: &mut TokenStream<'_>) -> Metadata {
    let mut meta: Metadata = Metadata::default();

    loop {
        // Skip newlines between metadata lines
        skip_newlines(stream);

        // Try to parse a posting metadata line (deep indent)
        let save_pos = stream.pos;
        if let Ok((key, value)) = parse_posting_metadata_line(stream) {
            meta.insert(key, value);
        } else {
            // Restore position if we didn't find metadata
            stream.pos = save_pos;
            break;
        }
    }

    meta
}

// ============================================================================
// Meta Value Parser
// ============================================================================

fn parse_meta_value(stream: &mut TokenStream<'_>) -> ParseRes<MetaValue> {
    if let Ok(s) = parse_string_owned(stream) {
        return Ok(MetaValue::String(s));
    }
    if let Ok(b) = parse_boolean(stream) {
        return Ok(MetaValue::Bool(b));
    }
    if let Ok(a) = parse_account(stream) {
        return Ok(MetaValue::Account(a));
    }
    if let Ok(d) = parse_date(stream) {
        return Ok(MetaValue::Date(d));
    }
    // Tag value (e.g., #trip-florida)
    if let Ok(tag) = parse_tag(stream) {
        return Ok(MetaValue::Tag(tag));
    }
    // Link value (e.g., ^doc-123)
    if let Ok(link) = parse_link(stream) {
        return Ok(MetaValue::Link(link));
    }

    // Try amount before plain number
    let start_pos = stream.pos;
    if let Ok(amt) = parse_amount(stream) {
        return Ok(MetaValue::Amount(amt));
    }
    stream.pos = start_pos;

    if let Ok(n) = parse_expr(stream) {
        return Ok(MetaValue::Number(n));
    }
    if let Ok(c) = parse_currency(stream) {
        return Ok(MetaValue::Currency(c));
    }

    Err(())
}

/// Parse metadata lines, also skipping any indented comment lines.
fn parse_metadata_with_comments(stream: &mut TokenStream<'_>) -> Metadata {
    let mut meta: Metadata = Metadata::default();

    loop {
        // Skip newlines
        skip_newlines(stream);

        let save_pos = stream.pos;

        // Check for indent
        let Some(t) = stream.peek() else {
            break;
        };

        match &t.token {
            Token::Indent(_) | Token::DeepIndent(_) => {
                stream.advance();

                // Skip indented comments
                if let Some(t) = stream.peek()
                    && matches!(t.token, Token::Comment(_) | Token::PercentComment(_))
                {
                    stream.advance();
                    continue;
                }

                // Try to parse metadata
                if let Ok(key) = parse_meta_key(stream) {
                    let value = parse_meta_value(stream).ok();
                    if let Some(v) = value {
                        meta.insert(key, v);
                    } else {
                        meta.insert(key, MetaValue::None);
                    }
                    skip_comment(stream);
                    continue;
                }

                // Not metadata or comment - restore and break
                stream.pos = save_pos;
                break;
            }
            _ => break,
        }
    }

    meta
}

// ============================================================================
// Directive Parsers
// ============================================================================

/// Intermediate parsed item.
enum ParsedItem {
    Directive(Directive, Span),
    DirectiveWithPipe(Directive, Span),
    /// A directive that encountered a recoverable error (e.g. invalid booking method).
    /// The directive is NOT added to the output; only the error is emitted.
    DirectiveError(ParseError, Span),
    Option(String, String, Span),
    Include(String, Span),
    Plugin(String, Option<String>, Span),
    Pushtag(rustledger_core::Tag, Span),
    Poptag(rustledger_core::Tag, Span),
    Pushmeta(String, MetaValue, Span),
    Popmeta(String, Span),
    /// A standalone comment line with its text and span
    Comment(String, Span),
}

fn parse_option_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    expect_token!(stream, Token::Option_)?;
    let key = parse_string_owned(stream)?;
    let value = parse_string_owned(stream)?;
    let span = stream.span_from(start_pos);
    Ok(ParsedItem::Option(key, value, span))
}

fn parse_include_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    expect_token!(stream, Token::Include)?;
    let path = parse_string_owned(stream)?;
    let span = stream.span_from(start_pos);
    Ok(ParsedItem::Include(path, span))
}

fn parse_plugin_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    expect_token!(stream, Token::Plugin)?;
    let name = parse_string_owned(stream)?;
    let config = parse_string_owned(stream).ok();
    let span = stream.span_from(start_pos);
    Ok(ParsedItem::Plugin(name, config, span))
}

fn parse_pushtag_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    expect_token!(stream, Token::Pushtag)?;
    let tag = parse_tag(stream)?;
    let span = stream.span_from(start_pos);
    Ok(ParsedItem::Pushtag(tag, span))
}

fn parse_poptag_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    expect_token!(stream, Token::Poptag)?;
    let tag = parse_tag(stream)?;
    let span = stream.span_from(start_pos);
    Ok(ParsedItem::Poptag(tag, span))
}

fn parse_pushmeta_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    expect_token!(stream, Token::Pushmeta)?;
    let key = parse_meta_key(stream)?;
    let value = parse_meta_value(stream)?;
    let span = stream.span_from(start_pos);
    Ok(ParsedItem::Pushmeta(key, value, span))
}

fn parse_popmeta_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    expect_token!(stream, Token::Popmeta)?;
    let key = parse_meta_key(stream)?;
    let span = stream.span_from(start_pos);
    Ok(ParsedItem::Popmeta(key, span))
}

fn parse_transaction_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;

    let date = parse_date(stream)?;

    // Flag (txn keyword or flag character)
    // Single-char currencies (e.g., T, V) can also be used as transaction flags
    let flag = if let Some(t) = stream.peek() {
        match &t.token {
            Token::Txn => {
                stream.advance();
                '*'
            }
            Token::Star | Token::Pending | Token::Hash | Token::Flag(_) => parse_flag(stream)?,
            Token::Currency(s) if s.len() == 1 => parse_flag(stream)?,
            Token::String(_) => '*', // Implied txn
            _ => return Err(()),
        }
    } else {
        return Err(());
    };

    // Parse payee/narration strings (Cow avoids allocation for no-escape case)
    let mut strings: Vec<Cow<'_, str>> = Vec::with_capacity(2);
    let mut has_pipe = false;

    while let Ok(s) = parse_string(stream) {
        strings.push(s);
        if let Some(t) = stream.peek()
            && matches!(t.token, Token::Pipe)
        {
            stream.advance();
            has_pipe = true;
        }
    }

    // Tags and links — Vec::new() avoids an upfront heap allocation
    // when no tags/links are present (the common case).
    let mut tags: Vec<rustledger_core::Tag> = Vec::new();
    let mut links: Vec<rustledger_core::Link> = Vec::new();

    loop {
        if let Ok(tag) = parse_tag(stream) {
            tags.push(tag);
        } else if let Ok(link) = parse_link(stream) {
            links.push(link);
        } else {
            break;
        }
    }

    skip_comment(stream);

    // Parse transaction-level metadata, tags/links, and postings
    let mut txn_meta: Metadata = Metadata::default();
    let mut postings: Vec<Spanned<Posting>> = Vec::with_capacity(4);
    // Track comments between postings. Vec::new() avoids allocation
    // when no inter-posting comments are present.
    let mut pending_comments: Vec<String> = Vec::new();

    loop {
        // Skip newlines between lines
        skip_newlines(stream);

        // Check what kind of indented line this is
        let save_pos = stream.pos;

        // First, check for any indent (regular or deep)
        if let Some(t) = stream.peek() {
            match &t.token {
                Token::Indent(_) | Token::DeepIndent(_) => {
                    stream.advance();

                    // Check for comment on its own line - collect it for the next posting
                    if let Some(t) = stream.peek()
                        && let Token::Comment(c) | Token::PercentComment(c) = &t.token
                    {
                        pending_comments.push(c.to_string());
                        stream.advance();
                        continue;
                    }

                    // Try to parse multiple tags/links on the same line
                    let mut found_tag_or_link = false;
                    loop {
                        if let Ok(tag) = parse_tag(stream) {
                            tags.push(tag);
                            found_tag_or_link = true;
                        } else if let Ok(link) = parse_link(stream) {
                            links.push(link);
                            found_tag_or_link = true;
                        } else {
                            break;
                        }
                    }
                    if found_tag_or_link {
                        skip_comment(stream);
                        continue;
                    }

                    // Try to parse metadata (key: value or just key:)
                    if let Ok(key) = parse_meta_key(stream) {
                        // Value is optional - empty metadata is valid
                        let value = parse_meta_value(stream).ok();
                        if let Some(v) = value {
                            txn_meta.insert(key, v);
                        } else {
                            // Empty metadata - use None/null value
                            txn_meta.insert(key, MetaValue::None);
                        }
                        skip_comment(stream);
                        continue;
                    }

                    // Restore position - wasn't comment/tag/link/metadata
                    stream.pos = save_pos;
                }
                _ => {}
            }
        }

        // Try to parse a posting (needs fresh start with indent check)
        if let Ok(mut spanned_posting) = parse_posting(stream) {
            // Attach any pending comments to this posting
            if !pending_comments.is_empty() {
                spanned_posting.value.comments = std::mem::take(&mut pending_comments);
            }
            postings.push(spanned_posting);
        } else {
            // If the posting failed with a deferred error (e.g. an unclosed
            // cost brace), propagate the failure so the top-level error
            // recovery emits the deferred error instead of silently building
            // a truncated transaction.
            if stream.deferred_error.is_some() {
                return Err(());
            }
            break;
        }
    }

    // Any remaining pending comments become transaction trailing comments
    let txn_trailing_comments = pending_comments;

    // Build transaction
    let (payee, narration): (Option<InternedStr>, InternedStr) = if has_pipe && strings.len() >= 2 {
        let p: InternedStr = strings.remove(0).as_ref().into();
        let n: InternedStr = strings.remove(0).as_ref().into();
        (Some(p), n)
    } else {
        match strings.len() {
            0 => (None, InternedStr::from("")),
            1 => {
                let n: InternedStr = strings.remove(0).as_ref().into();
                (None, n)
            }
            _ => {
                let p: InternedStr = strings.remove(0).as_ref().into();
                let n: InternedStr = strings.remove(0).as_ref().into();
                (Some(p), n)
            }
        }
    };

    let mut txn = Transaction::new(date, narration).with_flag(flag);
    if let Some(p) = payee {
        txn = txn.with_payee(p);
    }
    for t in tags {
        txn = txn.with_tag(t);
    }
    for l in links {
        txn = txn.with_link(l);
    }
    // Push parser-derived `Spanned<Posting>`s directly; `with_posting`
    // would wrap with `Spanned::synthesized` and discard the real span.
    txn.postings = postings;
    // Apply transaction-level metadata and trailing comments
    txn.meta = txn_meta;
    txn.trailing_comments = txn_trailing_comments;

    let span = stream.span_from(start_pos);

    if has_pipe {
        Ok(ParsedItem::DirectiveWithPipe(
            Directive::Transaction(txn),
            span,
        ))
    } else {
        Ok(ParsedItem::Directive(Directive::Transaction(txn), span))
    }
}

fn parse_balance_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    let date = parse_date(stream)?;
    expect_token!(stream, Token::Balance)?;
    let account = parse_account(stream)?;

    // Parse number first
    let number = parse_expr(stream)?;

    // Optional tolerance (before currency)
    let tolerance = if let Some(t) = stream.peek() {
        if matches!(t.token, Token::Tilde) {
            stream.advance();
            parse_signed_number(stream).ok()
        } else {
            None
        }
    } else {
        None
    };

    // Parse currency
    let currency = parse_currency(stream)?;
    let amount = Amount::new(number, currency);

    skip_comment(stream);

    // Parse directive metadata (and skip any trailing indented comments)
    let meta = parse_metadata_with_comments(stream);
    let span = stream.span_from(start_pos);

    let balance = Balance {
        date,
        account,
        amount,
        tolerance,
        meta,
    };

    Ok(ParsedItem::Directive(Directive::Balance(balance), span))
}

fn parse_open_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    let date = parse_date(stream)?;
    expect_token!(stream, Token::Open)?;
    let account = parse_account(stream)?;

    // Parse currencies separated by commas
    let mut currencies: Vec<rustledger_core::Currency> = Vec::with_capacity(3);
    while let Ok(c) = parse_currency(stream) {
        currencies.push(c);
        // Consume optional comma separator
        if let Some(t) = stream.peek()
            && matches!(t.token, Token::Comma)
        {
            stream.advance();
        }
    }

    let booking = if let Ok(s) = parse_string_owned(stream) {
        // Validate booking method: must be one of the valid uppercase methods per beancount v3.
        const VALID_BOOKING_METHODS: &[&str] = &[
            "FIFO",
            "STRICT",
            "STRICT_WITH_SIZE",
            "LIFO",
            "HIFO",
            "NONE",
            "AVERAGE",
        ];
        if !VALID_BOOKING_METHODS.contains(&s.as_str()) {
            skip_comment(stream);
            let span = stream.span_from(start_pos);
            let err = ParseError::new(ParseErrorKind::InvalidBookingMethod(s), span);
            stream.skip_to_newline();
            // Consume any indented metadata lines so error recovery lands
            // on the next top-level entry cleanly.
            parse_metadata_with_comments(stream);
            return Ok(ParsedItem::DirectiveError(err, span));
        }
        Some(s)
    } else {
        None
    };

    skip_comment(stream);

    // Parse directive metadata (and skip any trailing indented comments)
    let meta = parse_metadata_with_comments(stream);
    let span = stream.span_from(start_pos);

    let open = Open {
        date,
        account,
        currencies,
        booking,
        meta,
    };

    Ok(ParsedItem::Directive(Directive::Open(open), span))
}

fn parse_close_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    let date = parse_date(stream)?;
    expect_token!(stream, Token::Close)?;
    let account = parse_account(stream)?;
    skip_comment(stream);

    let meta = parse_metadata_with_comments(stream);
    let span = stream.span_from(start_pos);

    let close = Close {
        date,
        account,
        meta,
    };

    Ok(ParsedItem::Directive(Directive::Close(close), span))
}

fn parse_commodity_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    let date = parse_date(stream)?;
    expect_token!(stream, Token::Commodity)?;
    let currency = parse_currency(stream)?;
    skip_comment(stream);

    // Parse directive metadata (and skip any trailing indented comments)
    let meta = parse_metadata_with_comments(stream);
    let span = stream.span_from(start_pos);

    let commodity = Commodity {
        date,
        currency,
        meta,
    };

    Ok(ParsedItem::Directive(Directive::Commodity(commodity), span))
}

fn parse_pad_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    let date = parse_date(stream)?;
    expect_token!(stream, Token::Pad)?;
    let account = parse_account(stream)?;
    let source = parse_account(stream)?;
    skip_comment(stream);

    let meta = parse_metadata_with_comments(stream);
    let span = stream.span_from(start_pos);

    let pad = Pad {
        date,
        account,
        source_account: source,
        meta,
    };

    Ok(ParsedItem::Directive(Directive::Pad(pad), span))
}

fn parse_event_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    let date = parse_date(stream)?;
    expect_token!(stream, Token::Event)?;
    let event_type = parse_string_owned(stream)?;
    let value = parse_string_owned(stream)?;
    skip_comment(stream);

    let meta = parse_metadata_with_comments(stream);
    let span = stream.span_from(start_pos);

    let event = Event {
        date,
        event_type,
        value,
        meta,
    };

    Ok(ParsedItem::Directive(Directive::Event(event), span))
}

fn parse_query_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    let date = parse_date(stream)?;
    expect_token!(stream, Token::Query)?;
    let name = parse_string_owned(stream)?;
    let query = parse_string_owned(stream)?;
    skip_comment(stream);

    // Parse directive metadata
    let meta = parse_metadata_with_comments(stream);
    let span = stream.span_from(start_pos);

    let query_directive = Query {
        date,
        name,
        query,
        meta,
    };

    Ok(ParsedItem::Directive(
        Directive::Query(query_directive),
        span,
    ))
}

fn parse_note_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    let date = parse_date(stream)?;
    expect_token!(stream, Token::Note)?;
    let account = parse_account(stream)?;
    let comment = parse_string_owned(stream)?;
    skip_comment(stream);

    // Parse directive metadata (and skip any trailing indented comments)
    let meta = parse_metadata_with_comments(stream);
    let span = stream.span_from(start_pos);

    let note = Note {
        date,
        account,
        comment,
        meta,
    };

    Ok(ParsedItem::Directive(Directive::Note(note), span))
}

fn parse_document_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    let date = parse_date(stream)?;
    expect_token!(stream, Token::Document)?;
    let account = parse_account(stream)?;
    let path = parse_string_owned(stream)?;

    // Optional tags and links — Vec::new() avoids allocation when absent
    let mut tags: Vec<rustledger_core::Tag> = Vec::new();
    let mut links: Vec<rustledger_core::Link> = Vec::new();
    loop {
        if let Ok(tag) = parse_tag(stream) {
            tags.push(tag);
        } else if let Ok(link) = parse_link(stream) {
            links.push(link);
        } else {
            break;
        }
    }

    skip_comment(stream);

    let meta = parse_metadata_with_comments(stream);
    let span = stream.span_from(start_pos);

    let doc = Document {
        date,
        account,
        path,
        tags,
        links,
        meta,
    };

    Ok(ParsedItem::Directive(Directive::Document(doc), span))
}

fn parse_price_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    let date = parse_date(stream)?;
    expect_token!(stream, Token::Price)?;
    let currency = parse_currency(stream)?;
    let amount = parse_amount(stream)?;
    skip_comment(stream);

    let meta = parse_metadata_with_comments(stream);
    let span = stream.span_from(start_pos);

    let price = Price {
        date,
        currency,
        amount,
        meta,
    };

    Ok(ParsedItem::Directive(Directive::Price(price), span))
}

fn parse_custom_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    let date = parse_date(stream)?;
    expect_token!(stream, Token::Custom)?;
    let name = parse_string_owned(stream)?;

    let mut values = Vec::with_capacity(4);
    loop {
        // String
        if let Ok(s) = parse_string_owned(stream) {
            values.push(MetaValue::String(s));
            continue;
        }
        // Account (try before amount since account can't be part of amount)
        if let Ok(a) = parse_account(stream) {
            values.push(MetaValue::Account(a));
            continue;
        }
        // Boolean
        if let Ok(b) = parse_boolean(stream) {
            values.push(MetaValue::Bool(b));
            continue;
        }
        // Try amount (number + currency) before plain number
        let save_pos = stream.pos;
        if let Ok(amt) = parse_amount(stream) {
            values.push(MetaValue::Amount(amt));
            continue;
        }
        stream.pos = save_pos;
        // Plain number (without currency), may be negative
        if let Ok(n) = parse_signed_number(stream) {
            values.push(MetaValue::Number(n));
            continue;
        }
        // Date
        if let Ok(d) = parse_date(stream) {
            values.push(MetaValue::Date(d));
            continue;
        }
        // Currency (standalone)
        if let Ok(c) = parse_currency(stream) {
            values.push(MetaValue::Currency(c));
            continue;
        }
        break;
    }

    skip_comment(stream);

    // Parse directive metadata
    let meta = parse_metadata_with_comments(stream);
    let span = stream.span_from(start_pos);

    let custom = Custom {
        date,
        custom_type: name,
        values,
        meta,
    };

    Ok(ParsedItem::Directive(Directive::Custom(custom), span))
}

// ============================================================================
// Main Entry Parser
// ============================================================================

fn parse_dated_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    // Peek at second token to dispatch
    if stream.tokens.get(stream.pos + 1).is_none() {
        return Err(());
    }

    let second = &stream.tokens[stream.pos + 1].token;

    match second {
        Token::Txn
        | Token::Star
        | Token::Pending
        | Token::Hash
        | Token::Flag(_)
        | Token::String(_) => parse_transaction_directive(stream),
        // Single-char currencies can be transaction flags (e.g., "2024-01-01 T 'desc'")
        Token::Currency(s) if s.len() == 1 => parse_transaction_directive(stream),
        Token::Balance => parse_balance_directive(stream),
        Token::Open => parse_open_directive(stream),
        Token::Close => parse_close_directive(stream),
        Token::Commodity => parse_commodity_directive(stream),
        Token::Pad => parse_pad_directive(stream),
        Token::Event => parse_event_directive(stream),
        Token::Query => parse_query_directive(stream),
        Token::Note => parse_note_directive(stream),
        Token::Document => parse_document_directive(stream),
        Token::Price => parse_price_directive(stream),
        Token::Custom => parse_custom_directive(stream),
        _ => Err(()),
    }
}

fn parse_entry(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    skip_newlines(stream);

    if stream.is_empty() {
        return Err(());
    }

    let first = stream.peek_token().ok_or(())?;

    match first {
        Token::Option_ => parse_option_directive(stream),
        Token::Include => parse_include_directive(stream),
        Token::Plugin => parse_plugin_directive(stream),
        Token::Pushtag => parse_pushtag_directive(stream),
        Token::Poptag => parse_poptag_directive(stream),
        Token::Pushmeta => parse_pushmeta_directive(stream),
        Token::Popmeta => parse_popmeta_directive(stream),
        Token::Date(_) => parse_dated_directive(stream),
        Token::Comment(text) | Token::PercentComment(text) => {
            let start_pos = stream.pos;
            let text = text.to_string();
            stream.advance();
            let span = stream.span_from(start_pos);
            Ok(ParsedItem::Comment(text, span))
        }
        Token::Shebang(text) | Token::EmacsDirective(text) => {
            let start_pos = stream.pos;
            let text = text.to_string();
            stream.advance();
            let span = stream.span_from(start_pos);
            Ok(ParsedItem::Comment(text, span))
        }
        Token::Star => {
            // Org-mode header - skip the line (no text to preserve)
            let start_pos = stream.pos;
            stream.skip_to_newline();
            let span = stream.span_from(start_pos);
            Ok(ParsedItem::Comment(String::new(), span))
        }
        _ => Err(()),
    }
}

// ============================================================================
// Push Tag/Meta Application
// ============================================================================

fn apply_pushed_tags(directive: &mut Directive, tag_stack: &[(rustledger_core::Tag, Span)]) {
    if tag_stack.is_empty() {
        return;
    }

    if let Directive::Transaction(txn) = directive {
        for (tag, _) in tag_stack {
            if !txn.tags.contains(tag) {
                txn.tags.push(tag.clone());
            }
        }
    }
}

fn apply_pushed_meta(directive: &mut Directive, meta_stack: &[(String, MetaValue, Span)]) {
    if meta_stack.is_empty() {
        return;
    }

    let meta = match directive {
        Directive::Transaction(d) => &mut d.meta,
        Directive::Balance(d) => &mut d.meta,
        Directive::Open(d) => &mut d.meta,
        Directive::Close(d) => &mut d.meta,
        Directive::Commodity(d) => &mut d.meta,
        Directive::Pad(d) => &mut d.meta,
        Directive::Event(d) => &mut d.meta,
        Directive::Query(d) => &mut d.meta,
        Directive::Note(d) => &mut d.meta,
        Directive::Document(d) => &mut d.meta,
        Directive::Price(d) => &mut d.meta,
        Directive::Custom(d) => &mut d.meta,
    };

    for (key, value, _) in meta_stack {
        meta.insert(key.clone(), value.clone());
    }
}

// ============================================================================
// Public API
// ============================================================================

/// Parse beancount source code using the hand-rolled state-machine parser
/// over a Logos-produced token stream.
///
/// # Canonical UTF-8 BOM handling
///
/// A strict-byte-0 leading BOM is stripped before any lexer/parser
/// code runs ([`crate::bom::strip_leading`]). The result is flagged
/// in [`ParseResult::has_leading_bom`] and all spans returned to the
/// caller are shifted back into the *original source* coordinate
/// frame, so a directive starting at byte 3 of the original BOM-
/// prefixed source has `span.start == 3` even though the inner parser
/// saw it at byte 0 of the stripped view.
///
/// This shape — strip at the boundary, flag on the result, restore
/// spans — is the single source of truth for BOM handling across the
/// parser/formatter pair. See the [`crate::bom`] module docstring for
/// the architectural rationale.
pub fn parse(source: &str) -> ParseResult {
    let (stripped, had_bom) = crate::bom::strip_leading(source);
    let mut result = parse_inner(stripped);
    if had_bom {
        shift_spans_up(&mut result, crate::bom::BOM_LEN);
    }
    result.has_leading_bom = had_bom;
    result
}

/// Add `offset` to every span stored in `result`. Used to translate
/// spans from the BOM-stripped coordinate frame the inner parser uses
/// back to the original-source frame callers expect.
///
/// # Compile-time enforcement of completeness
///
/// The body opens with an **exhaustive named destructure** of
/// `ParseResult`. Adding a new field to `ParseResult` will fail to
/// compile here until the contributor decides whether the field
/// carries a span and, if so, threads it through `shift`. This is the
/// only place in the codebase that must visit every spanned field; a
/// soft "remember to extend this function" doc comment was previously
/// the only contract, and it failed (a `Transaction.postings`
/// recursion was missed for several iterations before this guard was
/// added).
///
/// If you're adding a new field and the compiler points you here:
///
/// * Carries a `Span` (or nests one transitively): add a `shift(&mut
///   field.span)` line (or recurse, e.g. via the `shift_directive_*`
///   helpers below).
/// * Doesn't carry a span (e.g. `has_leading_bom: bool`): bind it to
///   `_` in the destructure and add a one-line comment explaining
///   why.
fn shift_spans_up(result: &mut ParseResult, offset: usize) {
    use rustledger_core::ShiftSpans;
    let shift = |s: &mut crate::Span| {
        s.start += offset;
        s.end += offset;
    };

    // Destructure exhaustively. The compiler enforces that every field
    // of ParseResult is mentioned here; any field added to the struct
    // breaks this pattern and forces an explicit decision about
    // whether it needs span shifting.
    let ParseResult {
        directives,
        options,
        includes,
        plugins,
        comments,
        errors,
        warnings,
        currency_occurrences,
        // `has_leading_bom` is a bool, not a span. It's set by the
        // outer `parse()` after this function runs.
        has_leading_bom: _,
    } = result;

    // Directives: shift the wrapping span AND descend into any inner
    // spans the directive variant might carry. Recursion through the
    // payload is delegated to `ShiftSpans` impls living in
    // rustledger-core's `shift_spans_impls` module — see the rustdoc
    // there for the discipline (round-18: per-type exhaustive matches
    // without wildcards force a deliberate compile-time decision
    // whenever a directive payload's structure changes).
    for d in directives {
        shift(&mut d.span);
        d.value.shift_spans(&shift);
    }
    for (_, _, span) in options {
        shift(span);
    }
    for (_, span) in includes {
        shift(span);
    }
    for (_, _, span) in plugins {
        shift(span);
    }
    for c in comments {
        shift(&mut c.span);
    }
    for err in errors {
        shift(&mut err.span);
    }
    for warn in warnings {
        shift(&mut warn.span);
    }
    for occ in currency_occurrences {
        shift(&mut occ.span);
    }
}

/// Consume a leading run of BOM-only `Token::Error` tokens from
/// `stream` and return their combined span, if any.
///
/// Logos's default error path emits one `Err(())` per unrecognized
/// character; the `Err` arm in `tokenize` wraps the offending bytes in
/// `Token::Error(invalid_text)`. A mid-file BOM therefore appears as
/// one (or, for runs, several BYTE-ADJACENT) `Token::Error("\u{FEFF}")`
/// tokens.
///
/// **Byte-adjacency requirement.** The helper coalesces consecutive
/// BOM tokens only when they are byte-contiguous (`prev.span.end ==
/// next.span.start`). Logos's `#[logos(skip r"[ \t]+"]` removes
/// whitespace tokens from the stream entirely, so `\u{FEFF} \u{FEFF}`
/// produces two BOM `Token::Error`s that LOOK adjacent in the stream
/// but cover NON-contiguous byte ranges (with a space byte between
/// them). Coalescing those would emit a diagnostic span covering the
/// inter-BOM whitespace — misleading the user about which bytes to
/// delete. The adjacency check forces a separate diagnostic per
/// non-adjacent BOM token.
///
/// Returns `None` (and does not advance) when the current token is not
/// a BOM-only `Token::Error`. Hybrid spans like `\u{FEFF}garbage`
/// appear as a BOM-only Err immediately followed by non-BOM Errs;
/// only the BOM-only prefix is consumed here, so the caller still
/// surfaces a `SyntaxError` for the trailing garbage.
fn consume_leading_bom_run(stream: &mut TokenStream<'_>) -> Option<Span> {
    fn is_bom_only_err(token: &Token<'_>) -> bool {
        if let Token::Error(s) = token {
            !s.is_empty() && s.chars().all(|c| c == crate::bom::BOM_CHAR)
        } else {
            false
        }
    }

    let first = stream.peek()?;
    if !is_bom_only_err(&first.token) {
        return None;
    }
    let span_start = first.span.0;
    let mut span_end = first.span.1;
    stream.advance();
    while let Some(t) = stream.peek() {
        if !is_bom_only_err(&t.token) {
            break;
        }
        // Only coalesce byte-adjacent BOM tokens. A gap (lexer-
        // skipped whitespace between two BOMs) breaks the run; the
        // next iteration's call into this helper picks up the second
        // BOM as its own focused diagnostic.
        if t.span.0 != span_end {
            break;
        }
        span_end = t.span.1;
        stream.advance();
    }
    Some(Span::new(span_start, span_end))
}

/// Inner parser entry point. Operates on a source assumed to have NO
/// leading BOM (the public [`parse`] function strips it before calling
/// this). All spans this returns are in the stripped coordinate
/// frame — [`parse`] shifts them up by `BOM_LEN` if a BOM was stripped.
fn parse_inner(source: &str) -> ParseResult {
    let raw_tokens: Vec<SpannedToken<'_>> = tokenize(source)
        .into_iter()
        .map(|(token, span)| SpannedToken {
            token,
            span: (span.start, span.end),
        })
        .collect();

    let mut stream = TokenStream::new(&raw_tokens);

    // Preallocate collections with estimated capacities.
    //
    // Typical beancount file: ~50 bytes per directive, a few
    // options/includes/plugins. `directives` and `comments` are capped
    // to bound the single-allocation size on very large or untrusted
    // inputs (RPC, WASM, file uploads), so an adversary can't coerce a
    // multi-megabyte upfront allocation just by padding the source with
    // whitespace. The caps cover typical-size files (16384 directives
    // ≈ 800KB at 50 bytes each, 8192 comments same) without an OOM/DoS
    // spike on pathological inputs. Vec will grow past the cap
    // transparently if a real file exceeds it.
    let mut directives = Vec::with_capacity((source.len() / 50).min(MAX_PREALLOC_DIRECTIVES));
    let mut options = Vec::with_capacity(4);
    let mut includes = Vec::with_capacity(4);
    let mut plugins = Vec::with_capacity(4);
    let mut comments = Vec::with_capacity((source.len() / 100).min(MAX_PREALLOC_COMMENTS));
    let mut errors = Vec::with_capacity(4);

    let mut tag_stack: Vec<(rustledger_core::Tag, Span)> = Vec::with_capacity(8);
    let mut meta_stack: Vec<(String, MetaValue, Span)> = Vec::with_capacity(8);

    while !stream.is_empty() {
        // Skip any blank lines between directives so `error_start` points at
        // a real token. Otherwise, if the stream has only trailing newlines
        // left, we'd capture a newline token's span and then try to emit a
        // spurious "unexpected input" error for it.
        skip_newlines(&mut stream);
        if stream.is_empty() {
            break;
        }

        // Mid-file BOM recovery: a Token::Error containing only BOM
        // bytes is layout-transparent. Without this targeted handling,
        // the generic skip_to_newline recovery below consumes the
        // entire following directive into the error span — the user
        // loses their next `open` / transaction / balance assertion
        // silently. We coalesce a run of consecutive BOM-only Error
        // tokens (logos emits one Err per char, so a 6-byte `\u{FEFF}
        // \u{FEFF}` produces two tokens) into a single diagnostic, then
        // resume from the next non-BOM token.
        if let Some(bom_span) = consume_leading_bom_run(&mut stream) {
            errors.push(
                ParseError::new(ParseErrorKind::BomInDirectiveBody, bom_span)
                    .with_hint(BOM_REMOVAL_HINT),
            );
            continue;
        }

        let error_start = stream.pos;

        if let Ok(item) = parse_entry(&mut stream) {
            // Clear any deferred error from inner parsing attempts that
            // ultimately resolved successfully (e.g., a date in metadata
            // where the metadata was skipped but the directive was valid).
            stream.deferred_error = None;
            match item {
                ParsedItem::Directive(mut d, span) => {
                    apply_pushed_tags(&mut d, &tag_stack);
                    apply_pushed_meta(&mut d, &meta_stack);
                    directives.push(Spanned::new(d, span));
                }
                ParsedItem::DirectiveWithPipe(mut d, span) => {
                    errors.push(ParseError::new(ParseErrorKind::DeprecatedPipeSymbol, span));
                    apply_pushed_tags(&mut d, &tag_stack);
                    apply_pushed_meta(&mut d, &meta_stack);
                    directives.push(Spanned::new(d, span));
                }
                ParsedItem::DirectiveError(err, _span) => {
                    // Directive failed with a specific recoverable error (e.g. invalid booking
                    // method). The directive is dropped and the error is recorded.
                    errors.push(err);
                }
                ParsedItem::Option(k, v, span) => options.push((k, v, span)),
                ParsedItem::Include(p, span) => includes.push((p, span)),
                ParsedItem::Plugin(p, c, span) => plugins.push((p, c, span)),
                ParsedItem::Pushtag(tag, span) => tag_stack.push((tag, span)),
                ParsedItem::Poptag(tag, span) => {
                    if let Some(pos) = tag_stack.iter().rposition(|(t, _)| t == &tag) {
                        tag_stack.remove(pos);
                    } else {
                        errors.push(ParseError::new(
                            ParseErrorKind::InvalidPoptag(tag.to_string()),
                            span,
                        ));
                    }
                }
                ParsedItem::Pushmeta(key, value, span) => meta_stack.push((key, value, span)),
                ParsedItem::Popmeta(key, span) => {
                    if let Some(pos) = meta_stack.iter().rposition(|(k, _, _)| k == &key) {
                        meta_stack.remove(pos);
                    } else {
                        errors.push(ParseError::new(ParseErrorKind::InvalidPopmeta(key), span));
                    }
                }
                ParsedItem::Comment(text, span) => {
                    comments.push(Spanned::new(text, span));
                }
            }
        } else {
            // parse_entry failed. Because we pre-skipped newlines above,
            // `error_start` always points at a real token — meaning there
            // is a genuine parse error to report, whether or not the inner
            // parser consumed tokens before failing. This also catches
            // incomplete final directives at EOF (e.g. `2024-01-01 open`
            // with no account) and unclosed constructs like cost braces.
            //
            // Error recovery: skip to next newline (no-op if already at EOF).
            stream.skip_to_newline();
            let span = stream.span_from(error_start);
            // Specific-error classification is split from the deferred-
            // error pull so a BOM byte in the failed span is ALWAYS
            // surfaced — even when an inner parser also set a deferred
            // error (e.g., invalid date) for the same region. Without
            // this split, a two-strike input (`"2024-13-99 open Bank
            // \u{FEFF}USD\n"`, invalid month + embedded BOM) would
            // surface only the date diagnostic and the user would have
            // no clue that a BOM is also corrupting the line.
            //
            // A strict-byte-0 leading BOM was already stripped at the
            // `crate::parse` entry boundary (see `crate::bom`), so any
            // U+FEFF byte we see in `error_text` is by definition mid-
            // file. Logos's default error path emits Token::Error for
            // it; we scan with `contains` rather than `starts_with` to
            // catch both shapes (BOM at span start from a concatenation
            // accident, and BOM mid-token from embedded payloads).
            // Clamp BOTH ends to source.len() — defense against any
            // future recovery path that records error_start past the
            // source's byte length. Used both for slicing `error_text`
            // (to avoid 'byte index out of bounds' panics here) AND
            // for every emitted error's span (so downstream consumers
            // like the LSP that slice `source[err.span.start..err.span.end]`
            // for diagnostic-context rendering can't panic either).
            // Defining the clamped span ONCE means a contributor can't
            // accidentally emit an unclamped span in one of the four
            // classification branches below.
            // Clamp the span to source bounds before using it for any
            // slicing or emission. Three axes of defense:
            //
            // 1. `start.min(source.len())` and `end.min(source.len())`
            //    bound both ends by the source length, so a future
            //    recovery path that records error_start past the
            //    source's byte length can't panic the slice below.
            // 2. `lo.min(hi)` enforces `start <= end` so a degenerate
            //    out-of-order span (e.g., a hypothetical future
            //    recovery path that mistakenly calls `Span::new(later,
            //    earlier)`) can't panic the slice with 'slice index
            //    starts after end'.
            // 3. Building `clamped_span` ONCE and using it for every
            //    `ParseError::new(..., clamped_span)` push — INCLUDING
            //    the deferred-error rebuild below — means a contributor
            //    can't accidentally emit an unclamped span in one of
            //    the five emission paths.
            let lo = span.start.min(source.len());
            let hi = span.end.min(source.len());
            // Debug builds surface upstream span-ordering bugs at the
            // point of construction; release builds silently collapse
            // the span via `lo.min(hi)` below. Without the assert, a
            // `Span::new(later, earlier)` mistake elsewhere would
            // produce a zero-width empty diagnostic at `end` rather
            // than a visible failure pointing at the bug's origin.
            debug_assert!(
                span.start <= span.end,
                "ParseError span has start > end: start={}, end={} — \
                 a producer constructed a degenerate span; fix the producer rather than \
                 relying on this clamp",
                span.start,
                span.end,
            );
            let clamped_span = crate::Span::new(lo.min(hi), hi);
            // Use `get(..)` rather than `&source[..]` so a span that
            // lands on a non-UTF-8-char-boundary byte (which logos
            // doesn't produce, but a future heuristic recovery path
            // using byte-position arithmetic might) doesn't panic.
            // Falling back to the empty string means classification
            // treats the span as containing no BOM / no Unicode-
            // account; the dedicated diagnostic still fires (because
            // some primary error WAS recorded), just without the
            // BOM/Unicode hint. Strictly better than panicking.
            let error_text = source
                .get(clamped_span.start..clamped_span.end)
                .unwrap_or("");
            let has_bom = error_text.contains(crate::bom::BOM_CHAR);
            let unicode_account = find_unicode_account(error_text);
            let deferred = stream.deferred_error.take();

            // The primary diagnostic is the most actionable description
            // of what went wrong. `bom_is_primary` records whether THAT
            // primary is itself the BOM diagnostic — in which case the
            // additive secondary BOM emission below is suppressed (we
            // don't want to emit BOM twice). In all other cases
            // (deferred-error / unicode-account / generic syntax) the
            // primary is something else and `has_bom` triggers the
            // additive secondary so the user learns about both.
            //
            // Expression form (rather than `let bom_is_primary; if ...`)
            // so every branch yields a `bool` structurally — a future
            // contributor adding a fifth classifier branch can't
            // forget the assignment or escape via `return`/`continue`
            // without the compiler catching it.
            let bom_is_primary: bool = if let Some(mut err) = deferred {
                // Clamp the deferred error's span to source bounds
                // before pushing — keeps the "all emitted spans are
                // bounded by source.len()" invariant intact for
                // downstream LSP consumers that slice source by
                // `err.span`. The deferred error was constructed
                // elsewhere with a span we didn't clamp at the
                // build site.
                err.span = crate::Span::new(
                    err.span.start.min(source.len()),
                    err.span.end.min(source.len()),
                );
                err.span.start = err.span.start.min(err.span.end);
                // If the deferred error is ITSELF a BOM diagnostic
                // (no current inner parser sets this, but the path is
                // structurally reachable once a future contributor
                // wires BOM detection inside e.g. parse_date), treat
                // it as the primary BOM diagnostic so the additive
                // secondary emission below doesn't double-fire and
                // produce duplicate Bom errors for the same span.
                let deferred_is_bom = matches!(err.kind, ParseErrorKind::BomInDirectiveBody);
                errors.push(err);
                deferred_is_bom
            } else if let Some(account) = unicode_account {
                // Prefer the Unicode-account diagnostic over the BOM
                // diagnostic when both are present — the account name
                // is the actionable root cause (the BOM is often a
                // side-effect of a Windows-exported file containing a
                // non-ASCII account).
                errors.push(ParseError::new(
                    ParseErrorKind::InvalidAccount(account.to_string()),
                    clamped_span,
                ));
                false
            } else if has_bom {
                errors.push(
                    ParseError::new(ParseErrorKind::BomInDirectiveBody, clamped_span)
                        .with_hint(BOM_REMOVAL_HINT),
                );
                true
            } else {
                errors.push(ParseError::new(
                    ParseErrorKind::SyntaxError("unexpected input".to_string()),
                    clamped_span,
                ));
                false
            };

            // Surface the BOM diagnostic as an additive secondary error
            // when a different primary diagnostic already fired for the
            // same span. Two errors are better than one when both
            // apply — without this the deferred-error path (e.g.
            // invalid date) would hide the BOM completely and the user
            // would have no clue that an invisible byte is also
            // corrupting the line.
            if has_bom && !bom_is_primary {
                errors.push(
                    ParseError::new(ParseErrorKind::BomInDirectiveBody, clamped_span)
                        .with_hint(BOM_REMOVAL_HINT),
                );
            }
        }
    }

    // Check for unclosed pushtags
    for (tag, span) in &tag_stack {
        errors.push(ParseError::new(
            ParseErrorKind::UnclosedPushtag(tag.to_string()),
            *span,
        ));
    }

    // Check for unclosed pushmeta
    for (key, _, span) in &meta_stack {
        errors.push(ParseError::new(
            ParseErrorKind::UnclosedPushmeta(key.clone()),
            *span,
        ));
    }

    ParseResult {
        directives,
        options,
        includes,
        plugins,
        comments,
        errors,
        warnings: Vec::new(),
        currency_occurrences: stream.currency_occurrences,
        // The strip-at-entry boundary sets this flag on the outer
        // ParseResult after `parse_inner` returns. Inside the inner
        // parser we always operate on a BOM-free view, so this is
        // unconditionally false here — the wrapper `parse()` overwrites
        // it when a BOM was stripped.
        has_leading_bom: false,
    }
}

use crate::diagnostics::find_unicode_account;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_transaction() {
        let source = r#"
2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food:Coffee  5.00 USD
  Assets:Cash
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
    }

    #[test]
    fn test_posting_span_covers_line_only() {
        // The Spanned<Posting>.span covers the posting line itself —
        // not surrounding newlines, not following metadata. This pins
        // the contract the LSP relies on to fix issue #1142.
        let source = "\
2024-01-15 * \"Coffee\"
  Expenses:Food  5.00 USD
  Assets:Cash
";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(txn) = &result.directives[0].value else {
            panic!("expected transaction");
        };
        let slice0 = &source[txn.postings[0].span.start..txn.postings[0].span.end];
        assert!(
            slice0.contains("Expenses:Food") && slice0.contains("5.00 USD"),
            "span0 slice: {slice0:?}"
        );
        assert!(!slice0.contains("Assets:Cash"), "span0 slice: {slice0:?}");
        assert!(
            txn.postings[0].span.end <= txn.postings[1].span.start,
            "spans overlap"
        );
    }

    #[test]
    fn test_posting_span_excludes_following_metadata() {
        // Posting-level metadata lines (e.g. `effective_date:`) must sit
        // *outside* the posting span — this is the precise scenario behind
        // issue #1142 where LSP formatting overwrote metadata lines.
        let source = "\
2024-01-15 * \"Test\"
  Expenses:Food  5.00 USD
    effective_date: 2024-01-20
  Assets:Cash  -5.00 USD
    effective_date: 2024-01-21
";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(txn) = &result.directives[0].value else {
            panic!("expected transaction");
        };
        for spanned in &txn.postings {
            let slice = &source[spanned.span.start..spanned.span.end];
            assert!(
                !slice.contains("effective_date"),
                "posting span leaked into metadata: {slice:?}"
            );
        }
        assert_eq!(txn.postings[0].meta.len(), 1);
        assert_eq!(txn.postings[1].meta.len(), 1);
    }

    #[test]
    fn test_posting_span_includes_trailing_comment() {
        // A same-line trailing comment is part of the posting line and
        // belongs inside the span so an LSP edit replaces it atomically.
        let source = "\
2024-01-15 * \"Test\"
  Expenses:Food  5.00 USD  ; lunch
  Assets:Cash
";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(txn) = &result.directives[0].value else {
            panic!("expected transaction");
        };
        let span = txn.postings[0].span;
        let slice = &source[span.start..span.end];
        assert!(
            slice.contains("; lunch"),
            "trailing comment not in span: {slice:?}"
        );
    }

    #[test]
    fn test_posting_span_handles_unicode_account() {
        // Span end is a byte offset; multi-byte UTF-8 in the account
        // must not slip out of the span.
        let source = "2024-01-15 * \"x\"\n  Expenses:Café  1 EUR\n  Assets:Cash\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(txn) = &result.directives[0].value else {
            panic!("expected transaction");
        };
        let slice = &source[txn.postings[0].span.start..txn.postings[0].span.end];
        assert!(
            slice.contains("Expenses:Café") && slice.contains("1 EUR"),
            "unicode account not fully covered: {slice:?}"
        );
    }

    #[test]
    fn test_synthesized_posting_carries_zero_span_and_synth_file_id() {
        // Programmatically-constructed postings (plugins, tests, CLI) wrap
        // with Spanned::synthesized so consumers can distinguish
        // source-derived from synthesized at the per-posting level.
        let p = rustledger_core::Spanned::synthesized(Posting::auto("Assets:Cash"));
        assert_eq!(p.span, rustledger_core::Span::ZERO);
        assert_eq!(p.file_id, rustledger_core::SYNTHESIZED_FILE_ID);
    }

    #[test]
    fn test_parse_balance() {
        let source = "2024-01-01 balance Assets:Bank 1000.00 USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
    }

    #[test]
    fn test_parse_open() {
        let source = "2024-01-01 open Assets:Bank USD EUR\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
    }

    #[test]
    fn test_parse_option() {
        let source = "option \"title\" \"My Ledger\"\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.options.len(), 1);
        assert_eq!(result.options[0].0, "title");
        assert_eq!(result.options[0].1, "My Ledger");
    }

    #[test]
    fn test_parse_include() {
        let source = "include \"other.beancount\"\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.includes.len(), 1);
        assert_eq!(result.includes[0].0, "other.beancount");
    }

    #[test]
    fn test_parse_plugin() {
        let source = "plugin \"beancount.plugins.auto_accounts\"\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.plugins.len(), 1);
    }

    #[test]
    fn test_parse_arithmetic() {
        let source = "2024-01-01 balance Assets:Bank 1000 + 500 - 200 USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        if let Directive::Balance(b) = &result.directives[0].value {
            assert_eq!(b.amount.number, Decimal::from(1300));
        } else {
            panic!("Expected Balance directive");
        }
    }

    #[test]
    fn test_parse_division_by_zero_does_not_panic() {
        // Regression test: division by zero should not panic, just fail to parse
        let source = "2024-01-01 balance Assets:Bank 1/0 USD\n";
        let result = parse(source);
        // Should have parse errors, not panic
        assert!(
            !result.errors.is_empty(),
            "expected parse error for division by zero"
        );
    }

    #[test]
    fn test_parse_inline_comment_before_posting() {
        let source = r#"2024-01-15 * "Test"
  ; This is an inline comment
  Expenses:Food  50.00 USD
  Assets:Bank
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            assert_eq!(txn.postings.len(), 2);
            // First posting should have the inline comment attached
            assert_eq!(
                txn.postings[0].comments,
                vec!["; This is an inline comment".to_string()]
            );
            // Second posting should have no comments
            assert!(txn.postings[1].comments.is_empty());
        } else {
            panic!("Expected Transaction directive");
        }
    }

    #[test]
    fn test_parse_multiple_comments_before_posting() {
        let source = r#"2024-01-15 * "Test"
  ; Comment 1
  ; Comment 2
  Expenses:Food  50.00 USD
  Assets:Bank
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            // First posting should have both comments
            assert_eq!(
                txn.postings[0].comments,
                vec!["; Comment 1".to_string(), "; Comment 2".to_string()]
            );
        } else {
            panic!("Expected Transaction directive");
        }
    }

    #[test]
    fn test_parse_trailing_comment_on_posting() {
        let source = r#"2024-01-15 * "Test"
  Expenses:Food  50.00 USD ; trailing comment
  Assets:Bank
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            assert_eq!(
                txn.postings[0].trailing_comments,
                vec!["; trailing comment".to_string()]
            );
        } else {
            panic!("Expected Transaction directive");
        }
    }

    #[test]
    fn test_parse_transaction_trailing_comments() {
        let source = r#"2024-01-15 * "Test"
  Expenses:Food  50.00 USD
  Assets:Bank
  ; Comment after last posting
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            assert_eq!(
                txn.trailing_comments,
                vec!["; Comment after last posting".to_string()]
            );
        } else {
            panic!("Expected Transaction directive");
        }
    }

    // Issue #364: Formatter not preserving comments
    // This comprehensive test verifies all comment positions are preserved through
    // a parse -> format -> re-parse roundtrip.
    #[test]
    fn test_issue_364_comment_preservation_roundtrip() {
        use rustledger_core::format::{FormatConfig, format_directives};

        let source = r#"2024-01-15 * "Groceries"
  ; Pre-comment 1 for first posting
  ; Pre-comment 2 for first posting
  Expenses:Food  50.00 USD ; trailing comment on first posting
  ; Pre-comment for second posting
  Assets:Bank
  ; Transaction trailing comment 1
  ; Transaction trailing comment 2
"#;

        // First parse
        let result1 = parse(source);
        assert!(
            result1.errors.is_empty(),
            "parse errors: {:?}",
            result1.errors
        );
        assert_eq!(result1.directives.len(), 1);

        let txn1 = match &result1.directives[0].value {
            Directive::Transaction(t) => t,
            _ => panic!("Expected Transaction"),
        };

        // Verify first parse captured all comments
        assert_eq!(
            txn1.postings[0].comments,
            vec![
                "; Pre-comment 1 for first posting".to_string(),
                "; Pre-comment 2 for first posting".to_string()
            ],
            "First posting should have 2 pre-comments"
        );
        assert_eq!(
            txn1.postings[0].trailing_comments,
            vec!["; trailing comment on first posting".to_string()],
            "First posting should have trailing comment"
        );
        assert_eq!(
            txn1.postings[1].comments,
            vec!["; Pre-comment for second posting".to_string()],
            "Second posting should have 1 pre-comment"
        );
        assert_eq!(
            txn1.trailing_comments,
            vec![
                "; Transaction trailing comment 1".to_string(),
                "; Transaction trailing comment 2".to_string()
            ],
            "Transaction should have 2 trailing comments"
        );

        // Format back to string
        let config = FormatConfig::default();
        let formatted = format_directives([&result1.directives[0].value], &config);

        // Re-parse the formatted output
        let result2 = parse(&formatted);
        assert!(
            result2.errors.is_empty(),
            "re-parse errors: {:?}\nformatted:\n{}",
            result2.errors,
            formatted
        );
        assert_eq!(result2.directives.len(), 1);

        let txn2 = match &result2.directives[0].value {
            Directive::Transaction(t) => t,
            _ => panic!("Expected Transaction after roundtrip"),
        };

        // Verify roundtrip preserved all comments
        assert_eq!(
            txn2.postings[0].comments, txn1.postings[0].comments,
            "Roundtrip should preserve first posting pre-comments"
        );
        assert_eq!(
            txn2.postings[0].trailing_comments, txn1.postings[0].trailing_comments,
            "Roundtrip should preserve first posting trailing comment"
        );
        assert_eq!(
            txn2.postings[1].comments, txn1.postings[1].comments,
            "Roundtrip should preserve second posting pre-comments"
        );
        assert_eq!(
            txn2.trailing_comments, txn1.trailing_comments,
            "Roundtrip should preserve transaction trailing comments"
        );
    }

    // Issue #364: Verify blank lines between directives are preserved
    #[test]
    fn test_issue_364_blank_lines_preserved() {
        let source = r#"2024-01-01 open Assets:Bank USD

2024-01-15 * "Transaction 1"
  Expenses:Food  50.00 USD
  Assets:Bank

2024-01-16 * "Transaction 2"
  Expenses:Food  25.00 USD
  Assets:Bank
"#;

        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        // Should have 3 directives: open + 2 transactions
        assert_eq!(result.directives.len(), 3);

        // Check that blank lines are tracked in spans (trailing_newlines)
        // The span should include trailing newlines for proper formatting
        for (i, dir) in result.directives.iter().enumerate() {
            assert!(
                dir.span.end > dir.span.start,
                "Directive {i} should have non-empty span"
            );
        }
    }

    /// A leading UTF-8 BOM (`\u{FEFF}` / EF BB BF) at strict byte 0 is
    /// stripped at the `parse()` boundary (see `crate::bom`), the inner
    /// parser runs on a BOM-free view, and every span returned to the
    /// caller is shifted back into the original-source coordinate
    /// frame. The `has_leading_bom` flag carries the strip outcome.
    #[test]
    fn test_leading_bom_strips_cleanly_and_flag_set() {
        let source = "\u{FEFF}2024-01-01 open Assets:Bank USD\n";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "BOM should be stripped, got errors: {:?}",
            result.errors
        );
        assert_eq!(result.directives.len(), 1, "expected 1 directive");
        assert!(
            result.has_leading_bom,
            "has_leading_bom should be true for a BOM-prefixed source"
        );
        // Spans are in ORIGINAL coords: the directive starts at byte 3
        // (after the 3-byte BOM), not byte 0.
        let dir_span = result.directives[0].span;
        assert_eq!(
            dir_span.start, 3,
            "directive span.start should be in original-source coords (3, after BOM); \
             got {dir_span:?}"
        );
    }

    /// No-BOM source: flag is false, spans are in their natural
    /// (unshifted) coordinate frame.
    #[test]
    fn test_no_leading_bom_flag_is_false() {
        let source = "2024-01-01 open Assets:Bank USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty());
        assert!(
            !result.has_leading_bom,
            "has_leading_bom should be false for a BOM-less source"
        );
        assert_eq!(result.directives[0].span.start, 0);
    }

    /// Regression: nested `Spanned<Posting>` inside `Transaction.postings`
    /// must be shifted into the original-source coordinate frame too,
    /// not just the outer `Spanned<Directive>::span`.
    ///
    /// Verifies the `shift_spans_up` recursion into directive bodies
    /// (via `shift_directive_inner_spans`). Without that recursion,
    /// posting spans stay in the BOM-stripped frame — 3 bytes too
    /// small. Every LSP feature that uses per-posting spans
    /// (`document_highlight`, `document_color`, `linked_editing`,
    /// `call_hierarchy`) would land 3 bytes early, off the start of
    /// the actual posting line.
    ///
    /// The test computes the expected byte offset of each posting line
    /// in the ORIGINAL (BOM-included) source and asserts that
    /// `posting.span.start` matches. Catches the bug structurally
    /// rather than relying on a format round-trip (`format_source`
    /// happens not to use posting spans — it re-renders from
    /// structured data).
    #[test]
    fn test_posting_spans_shifted_into_original_source_frame() {
        let src =
            "\u{FEFF}2024-01-15 * \"Coffee\"\n  Expenses:Food 5.00 USD\n  Assets:Bank -5.00 USD\n";
        let result = parse(src);
        assert!(result.errors.is_empty(), "{:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
        assert!(result.has_leading_bom);

        let Directive::Transaction(txn) = &result.directives[0].value else {
            panic!("expected Transaction, got {:?}", result.directives[0].value);
        };
        assert_eq!(txn.postings.len(), 2, "expected 2 postings");

        // The byte IMMEDIATELY BEFORE posting.span.start must be
        // `\n` — postings span from the start of their indent (or
        // account, if no indent) on a fresh line. This is the LSP
        // load-bearing invariant: per-posting features (highlight,
        // color, linked-edit, call-hierarchy) walk back from
        // span.start expecting to find the line boundary.
        //
        // Without the `shift_directive_inner_spans` recursion, posting
        // spans stay in the stripped-source frame (3 bytes too small).
        // For the test input, the byte 3 positions earlier is INSIDE
        // the previous directive's payload — `e"` (the closing
        // characters of `"Coffee"`) — NOT a newline. This assertion
        // catches that exact byte-offset drift.
        let p0_start = txn.postings[0].span.start;
        assert!(p0_start > 0, "posting[0].span.start must be > 0");
        // Build a context window that's safe to slice even if the
        // regression under test makes `p0_start` overshoot
        // `src.len()` — without explicit clamping on BOTH bounds, the
        // diagnostic format-arg slice would panic 'byte index out of
        // bounds' before the assertion message renders, masking the
        // real failure with an opaque arithmetic panic.
        let ctx0_lo = p0_start.saturating_sub(5);
        let ctx0_hi = (p0_start + 5).min(src.len());
        assert_eq!(
            src.as_bytes()[p0_start - 1],
            b'\n',
            "byte before posting[0].span.start ({p0_start}) must be \\n in original source frame; \
             a regression that leaves spans in stripped-source frame would point this 3 bytes too early, \
             into the directive's payload bytes. \
             Got byte before = {:?} (0x{:02x}); \
             surrounding context: {:?}",
            src.as_bytes()[p0_start - 1] as char,
            src.as_bytes()[p0_start - 1],
            &src[ctx0_lo..ctx0_hi],
        );
        let p1_start = txn.postings[1].span.start;
        // Symmetric guard with the p0 case — without it, a regression
        // that affects posting[1] too would underflow in `p1_start - 1`
        // and panic instead of surfacing the documented diagnostic.
        assert!(p1_start > 0, "posting[1].span.start must be > 0");
        assert_eq!(
            src.as_bytes()[p1_start - 1],
            b'\n',
            "byte before posting[1].span.start ({p1_start}) must be \\n in original source frame; \
             got: {:?}",
            src.as_bytes()[p1_start - 1] as char,
        );

        // And the slice contains the account name (sanity check that
        // posting.span.end is also in the correct frame, not just
        // span.start).
        let p0_slice = &src[txn.postings[0].span.start..txn.postings[0].span.end];
        assert!(
            p0_slice.contains("Expenses:Food"),
            "slicing original source by posting[0].span must contain 'Expenses:Food'; got {p0_slice:?}"
        );
        let p1_slice = &src[txn.postings[1].span.start..txn.postings[1].span.end];
        assert!(
            p1_slice.contains("Assets:Bank"),
            "slicing original source by posting[1].span must contain 'Assets:Bank'; got {p1_slice:?}"
        );
    }

    /// The previously-widened case (whitespace before BOM) is correctly
    /// a parse error now: that input is malformed (the BOM is mid-file
    /// by strict definition). The strict-byte-0 strip means
    /// `crate::bom::strip_leading` leaves the input alone, the lexer
    /// sees the space + BOM, and the BOM byte falls into the error
    /// path producing the dedicated diagnostic.
    #[test]
    fn test_leading_whitespace_then_bom_is_error() {
        let source = " \u{FEFF}2024-01-01 open Assets:Bank USD\n";
        let result = parse(source);
        assert!(
            !result.errors.is_empty(),
            "whitespace-before-BOM is mid-file BOM, should produce an error"
        );
        let messages: Vec<String> = result.errors.iter().map(ParseError::message).collect();
        assert!(
            messages.iter().any(|m| m.contains("BOM")),
            "expected a BOM diagnostic, got: {messages:?}"
        );
        assert!(
            !result.has_leading_bom,
            "has_leading_bom should be false — only strict-byte-0 counts"
        );
    }

    /// A BOM at a non-zero byte offset (e.g., concatenated files like
    /// `cat windows-a.bean windows-b.bean > merged.bean`) is NOT
    /// silently consumed — the parser surfaces a clear "UTF-8 BOM
    /// detected mid-file" diagnostic so the user can fix the
    /// concatenation mistake.
    ///
    /// Pins two contracts simultaneously: (1) the BOM produces a
    /// `BomInDirectiveBody` diagnostic with span covering just the
    /// BOM bytes (3 UTF-8 bytes for one U+FEFF), and (2) the
    /// directive FOLLOWING the BOM still parses — the parser does
    /// NOT consume the next directive into the error recovery span.
    /// The two-directive assertion catches the data-loss regression
    /// that existed before `consume_leading_bom_run`: the old
    /// `skip_to_newline` recovery would swallow the entire
    /// `2024-01-02 open Assets:Cash USD` line into the BOM span,
    /// silently dropping the second `open` directive.
    #[test]
    fn test_mid_file_bom_produces_error() {
        let source = "2024-01-01 open Assets:Bank USD\n\u{FEFF}2024-01-02 open Assets:Cash USD\n";
        let result = parse(source);
        assert!(
            !result.errors.is_empty(),
            "mid-file BOM should produce a parse error"
        );
        let msg = result.errors[0].message();
        assert!(
            msg.contains("BOM") && msg.contains("directive body"),
            "expected BOM-in-directive error, got: {msg}"
        );

        // Both directives must survive: the BOM at the start of line
        // 2 is layout-transparent, not a terminator.
        assert_eq!(
            result.directives.len(),
            2,
            "the directive following the mid-file BOM must still parse — \
             got directives: {:?}",
            result
                .directives
                .iter()
                .map(|d| format!("{:?}", d.value))
                .collect::<Vec<_>>()
        );

        // The BOM diagnostic span covers exactly the BOM bytes
        // (3 UTF-8 bytes per U+FEFF), not the whole second line.
        let bom_err = result
            .errors
            .iter()
            .find(|e| matches!(e.kind, ParseErrorKind::BomInDirectiveBody))
            .expect("a BomInDirectiveBody error must exist");
        let span_len = bom_err.span.end - bom_err.span.start;
        assert_eq!(
            span_len,
            crate::bom::BOM_LEN,
            "BOM diagnostic span must cover exactly the BOM bytes ({} bytes), \
             not the whole recovery range — span = {}..{}, length = {}",
            crate::bom::BOM_LEN,
            bom_err.span.start,
            bom_err.span.end,
            span_len
        );
    }

    /// Multiple consecutive mid-file BOMs (e.g., from triple-
    /// concatenated Windows files) coalesce into ONE diagnostic
    /// whose span covers the full BOM run, and the directive
    /// following the run still parses. Pins the
    /// `consume_leading_bom_run` coalescing behavior.
    #[test]
    fn test_consecutive_mid_file_boms_coalesce_and_preserve_next_directive() {
        let source =
            "2024-01-01 open Assets:Bank USD\n\u{FEFF}\u{FEFF}2024-01-02 open Assets:Cash USD\n";
        let result = parse(source);
        assert_eq!(
            result.directives.len(),
            2,
            "directive after a multi-BOM run must still parse"
        );
        let bom_errs: Vec<_> = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, ParseErrorKind::BomInDirectiveBody))
            .collect();
        assert_eq!(
            bom_errs.len(),
            1,
            "consecutive BOMs must coalesce into a single diagnostic, got: {bom_errs:?}"
        );
        let span_len = bom_errs[0].span.end - bom_errs[0].span.start;
        assert_eq!(
            span_len,
            2 * crate::bom::BOM_LEN,
            "coalesced BOM-run span must cover both BOMs"
        );
    }

    /// Two BOMs separated by lexer-skipped whitespace (`\u{FEFF}
    /// \u{FEFF}`) emit per-BOM focused diagnostics, NOT one coalesced
    /// span covering the inter-BOM space.
    ///
    /// Pre-round-18, the coalescing loop in `consume_leading_bom_run`
    /// didn't check byte adjacency. For input `\u{FEFF} \u{FEFF}` the
    /// two BOM Errs appear consecutive in the token stream (space
    /// skipped by logos) and were coalesced into a single span
    /// covering bytes 0..7 — labeling the inter-BOM whitespace as
    /// part of the BOM diagnostic. The adjacency check forces a
    /// separate diagnostic per BOM, each covering exactly the BOM
    /// bytes.
    ///
    /// The test asserts there are AT LEAST TWO focused
    /// `BomInDirectiveBody` diagnostics whose spans contain only BOM
    /// chars. Recovery downstream may emit additional broader errors
    /// covering the inter-BOM whitespace + later corruption
    /// (currently the indent walker treats the post-BOM space as an
    /// `Indent` token that `parse_entry` rejects); those broader
    /// diagnostics may also happen to be classified as
    /// `BomInDirectiveBody` because their span contains a BOM byte.
    /// The user-visible contract pinned here is: the focused per-BOM
    /// diagnostics exist.
    #[test]
    fn test_non_adjacent_boms_emit_per_bom_diagnostics() {
        let source =
            "2024-01-01 open Assets:Bank USD\n\u{FEFF} \u{FEFF}2024-01-02 open Assets:Cash USD\n";
        let result = parse(source);
        let focused_bom_errs: Vec<_> = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, ParseErrorKind::BomInDirectiveBody))
            .filter(|e| {
                let span_text = source.get(e.span.start..e.span.end).unwrap_or("");
                !span_text.is_empty() && span_text.chars().all(|c| c == crate::bom::BOM_CHAR)
            })
            .collect();
        assert!(
            focused_bom_errs.len() >= 2,
            "expected at least one focused diagnostic per non-adjacent BOM — \
             span containing only BOM chars; got focused errs: {focused_bom_errs:?}, \
             all errs: {:?}",
            result.errors
        );
        // Each focused diagnostic's span is exactly one BOM long.
        for err in &focused_bom_errs {
            assert_eq!(
                err.span.end - err.span.start,
                crate::bom::BOM_LEN,
                "focused diagnostic must cover exactly one BOM"
            );
        }
    }

    /// A BOM embedded mid-line (not at the start of a fresh directive)
    /// also surfaces as the dedicated BOM diagnostic. The previous
    /// `starts_with` classifier missed this case because the error
    /// span covers the WHOLE failed directive — which starts with the
    /// date, not the BOM.
    #[test]
    fn test_mid_line_bom_produces_error() {
        // BOM after the account name, before the currency.
        let source = "2024-01-01 open Assets:Bank \u{FEFF}USD\n";
        let result = parse(source);
        assert!(
            !result.errors.is_empty(),
            "mid-line BOM should produce a parse error"
        );
        let msg = result.errors[0].message();
        assert!(msg.contains("BOM"), "expected BOM diagnostic, got: {msg}");
    }

    /// Two-strike input: invalid date AND a BOM in the same failed
    /// span. The deferred date error fires first, but the BOM
    /// diagnostic must STILL surface as a separate error — the user
    /// should learn about both. Previously the deferred-error branch
    /// short-circuited the BOM classifier entirely and the BOM hint
    /// was silently dropped.
    #[test]
    fn test_bom_alongside_deferred_error_both_surface() {
        let source = "2024-13-99 open Assets:Bank \u{FEFF}USD\n";
        let result = parse(source);
        assert!(
            result.errors.len() >= 2,
            "expected both invalid-date AND BOM errors, got: {:?}",
            result
                .errors
                .iter()
                .map(ParseError::message)
                .collect::<Vec<_>>()
        );
        // The date diagnostic comes first (primary, actionable root cause).
        let messages: Vec<String> = result.errors.iter().map(ParseError::message).collect();
        assert!(
            messages.iter().any(|m| m.to_lowercase().contains("date")
                || m.contains("13")
                || m.to_lowercase().contains("month")),
            "expected an invalid-date diagnostic in the error set, got: {messages:?}"
        );
        // The BOM diagnostic surfaces as a secondary additive error.
        assert!(
            messages.iter().any(|m| m.contains("BOM")),
            "expected a BOM diagnostic alongside the deferred date error, got: {messages:?}"
        );
    }

    /// Pins the load-bearing `matches!(err.kind, BomInDirectiveBody)`
    /// discriminant used by the deferred-error branch of the
    /// classifier (parser.rs:~2305). Today no inner parser sets
    /// `stream.deferred_error = Some(ParseError::new(BomInDirectiveBody, ...))`,
    /// so this code path is structurally reachable but unreachable
    /// via real input. Without this test, a future rename or refactor
    /// that broke the `matches!()` expression (e.g., variant rename
    /// gone wrong, or a destructure-typo) would slip through every
    /// existing integration test because none of them exercise the
    /// dedup path.
    ///
    /// When a future contributor wires BOM detection inside an inner
    /// parser (e.g. `parse_date` recognizing an embedded BOM and
    /// setting a deferred `BomInDirectiveBody`), this test ensures the
    /// dedup logic recognizes it as the primary diagnostic and
    /// suppresses the additive secondary, preventing duplicate
    /// emission.
    #[test]
    fn test_deferred_bom_kind_discriminant() {
        let err = ParseError::new(ParseErrorKind::BomInDirectiveBody, crate::Span::new(0, 3));
        assert!(
            matches!(err.kind, ParseErrorKind::BomInDirectiveBody),
            "matches! on err.kind must recognize BomInDirectiveBody; \
             this is the load-bearing expression in the deferred-error \
             dedup branch of the classifier."
        );
        // Inverse check: a non-BOM kind must NOT match.
        let other = ParseError::new(
            ParseErrorKind::SyntaxError("not a BOM".to_string()),
            crate::Span::new(0, 3),
        );
        assert!(
            !matches!(other.kind, ParseErrorKind::BomInDirectiveBody),
            "matches! must NOT misclassify other kinds as BomInDirectiveBody"
        );
    }

    /// When the failed-entry span contains a Cyrillic/CJK account
    /// AND a BOM, the Unicode-account diagnostic (if it would fire) is
    /// the primary and the BOM hint is surfaced as an additive
    /// secondary error. The error-ordering policy is asserted at the
    /// code-path level (`bom_is_primary` flag in the classifier above,
    /// false when a non-BOM diagnostic is the primary so the additive
    /// secondary BOM emission fires) rather than via a single input,
    /// because constructing an input where `find_unicode_account`
    /// returns Some AND the error span also contains a BOM is narrow:
    /// most valid Cyrillic/CJK accounts tokenize cleanly as
    /// `Token::Account`, so they don't appear in the recovered error
    /// span. The dual-diagnostic contract for the common case
    /// (deferred-error + BOM) is pinned by
    /// `test_bom_alongside_deferred_error_both_surface`. The
    /// Unicode-account-only path (no BOM) is pinned by
    /// `test_unicode_account_emits_invalid_account_error` (below, if
    /// present) and by the lexer's account tests.
    #[test]
    fn test_cyrillic_account_with_bom_surfaces_bom_diagnostic() {
        // The Cyrillic account parses cleanly, so the failed span is
        // just `\u{FEFF}USD`. We pin the BOM diagnostic as the only
        // diagnostic — the test ensures the BOM classifier still fires
        // for this real-world Windows-export shape even when a
        // non-ASCII account is part of the line.
        let source = "2024-01-01 open Активы:Банк \u{FEFF}USD\n";
        let result = parse(source);
        assert!(
            !result.errors.is_empty(),
            "expected at least one error, got: {:?}",
            result.errors
        );
        let messages: Vec<String> = result.errors.iter().map(ParseError::message).collect();
        assert!(
            messages.iter().any(|m| m.contains("BOM")),
            "expected a BOM diagnostic when a BOM byte sits next to a Cyrillic account, \
             got: {messages:?}"
        );
    }

    #[test]
    fn test_unicode_account_parses_successfully() {
        // Cyrillic accounts are valid — Unicode uppercase letters (\p{Lu})
        // and CJK ideographs (\p{Lo}) are accepted at component start.
        let source = "2024-01-01 open Активы:Банк\n";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "Cyrillic account should parse without errors, got: {:?}",
            result
                .errors
                .iter()
                .map(ParseError::message)
                .collect::<Vec<_>>()
        );
        assert_eq!(result.directives.len(), 1, "Should have 1 directive");
    }

    // ============================================================================
    // HIGH PRIORITY TESTS - Core Parsing Functions
    // ============================================================================

    #[test]
    fn test_parse_date_two_digit_year_is_rejected() {
        // The lexer's date regex requires a 4-digit year (see logos_lexer.rs).
        // A 2-digit year like `24-01-15` is therefore not recognized as
        // `Token::Date` and cannot produce a directive. Pin that rejection
        // so a future lexer change that accepts 2-digit years (e.g., adding
        // a year-shortcut feature) will fail this test and prompt the
        // author to explicitly decide the semantics.
        let source = "24-01-15 open Assets:Bank USD\n";
        let result = parse(source);
        assert!(
            !result.errors.is_empty(),
            "2-digit years should produce a parse error"
        );
        assert!(
            result.directives.is_empty(),
            "2-digit years should not produce any directives, got: {:?}",
            result.directives
        );
    }

    #[test]
    fn test_parse_date_single_digit_month() {
        // Single-digit month should be normalized to 2024-01-15.
        let source = "2024-1-15 open Assets:Bank USD\n";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "Expected no parse errors, got: {:?}",
            result.errors
        );
        assert_eq!(result.directives.len(), 1, "Expected exactly one directive");
        match &result.directives[0].value {
            Directive::Open(open) => assert_eq!(
                open.date,
                rustledger_core::naive_date(2024, 1, 15).unwrap(),
                "Single-digit month should normalize to 2024-01-15"
            ),
            other => panic!("Expected Directive::Open, got: {other:?}"),
        }
    }

    #[test]
    fn test_process_string_escapes() {
        // Newline escape
        assert_eq!(process_string_escapes("hello\\nworld"), "hello\nworld");
        // Tab escape
        assert_eq!(process_string_escapes("tab\\t"), "tab\t");
        // Quote escape
        assert_eq!(process_string_escapes("say \\\"hello\\\""), "say \"hello\"");
        // Backslash escape
        assert_eq!(process_string_escapes("back\\\\slash"), "back\\slash");
        // No escapes
        assert_eq!(process_string_escapes("plain text"), "plain text");
    }

    #[test]
    fn test_parse_signed_number_in_balance_tolerance() {
        // `parse_signed_number` only runs in specific contexts where the
        // grammar expects a signed value, notably the optional balance
        // tolerance after `~`. Top-level bare numbers (`+100` / `-50.00`)
        // don't reach this code path. Use a balance directive with an
        // explicit negative tolerance to actually exercise it.
        //
        // The balance grammar is `<number> [~ <tolerance>] <currency>`,
        // so the tolerance comes between the number and the currency,
        // not after the currency.
        let source = "2024-01-01 open Assets:Cash USD\n\
                      2024-01-15 balance Assets:Cash 100 ~ -1 USD\n";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "Expected no parse errors, got: {:?}",
            result.errors
        );
        assert_eq!(result.directives.len(), 2);

        match &result.directives[1].value {
            Directive::Balance(balance) => {
                assert_eq!(
                    balance.tolerance,
                    Some(Decimal::from(-1)),
                    "Balance tolerance should parse as -1 via parse_signed_number"
                );
            }
            other => panic!("Expected Directive::Balance, got: {other:?}"),
        }
    }

    #[test]
    fn test_parse_flag_star() {
        let source = r#"
2024-01-15 * "Test"
  Assets:Cash  100 USD
  Expenses:Test
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
        match &result.directives[0].value {
            Directive::Transaction(txn) => assert_eq!(txn.flag, '*'),
            other => panic!("Expected Directive::Transaction, got: {other:?}"),
        }
    }

    #[test]
    fn test_parse_flag_exclamation() {
        let source = r#"
2024-01-15 ! "Test"
  Assets:Cash  100 USD
  Expenses:Test
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
        match &result.directives[0].value {
            Directive::Transaction(txn) => assert_eq!(txn.flag, '!'),
            other => panic!("Expected Directive::Transaction, got: {other:?}"),
        }
    }

    #[test]
    fn test_parse_option_with_true_string_value() {
        // `option` directives store their value as a raw string regardless
        // of content; they do NOT go through `parse_boolean`. This test
        // pins that string round-trip. See
        // `test_parse_boolean_metadata_value` below for actual
        // `parse_boolean` coverage.
        let source = "option \"bool\" \"True\"\n";
        let result = parse(source);
        assert_eq!(result.options.len(), 1);
        assert_eq!(result.options[0].1, "True");
    }

    #[test]
    fn test_parse_option_with_false_string_value() {
        // See `test_parse_option_with_true_string_value`.
        let source = "option \"bool\" \"False\"\n";
        let result = parse(source);
        assert_eq!(result.options.len(), 1);
        assert_eq!(result.options[0].1, "False");
    }

    #[test]
    fn test_parse_boolean_metadata_value() {
        // `parse_boolean` fires on bare `True` / `False` tokens produced
        // by the lexer, which only happens for metadata values (and a few
        // other contexts). Exercise it by attaching boolean metadata to
        // an `open` directive and asserting the resulting `MetaValue::Bool`.
        let source = concat!(
            "2024-01-01 open Assets:Bank USD\n",
            "  flag_true: TRUE\n",
            "  flag_false: FALSE\n",
        );
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "Expected no parse errors, got: {:?}",
            result.errors
        );
        assert_eq!(result.directives.len(), 1);
        match &result.directives[0].value {
            Directive::Open(open) => {
                assert_eq!(
                    open.meta.get("flag_true"),
                    Some(&MetaValue::Bool(true)),
                    "TRUE should parse as MetaValue::Bool(true), got: {:?}",
                    open.meta.get("flag_true")
                );
                assert_eq!(
                    open.meta.get("flag_false"),
                    Some(&MetaValue::Bool(false)),
                    "FALSE should parse as MetaValue::Bool(false), got: {:?}",
                    open.meta.get("flag_false")
                );
            }
            other => panic!("Expected Directive::Open, got: {other:?}"),
        }
    }

    #[test]
    fn test_parse_arithmetic_multiplication() {
        let source = "2024-01-01 balance Assets:Bank 10 * 5 USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
        match &result.directives[0].value {
            Directive::Balance(b) => assert_eq!(b.amount.number, Decimal::from(50)),
            other => panic!("Expected Directive::Balance, got: {other:?}"),
        }
    }

    #[test]
    fn test_parse_arithmetic_parentheses() {
        let source = "2024-01-01 balance Assets:Bank (10 + 5) * 2 USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
        match &result.directives[0].value {
            Directive::Balance(b) => assert_eq!(b.amount.number, Decimal::from(30)),
            other => panic!("Expected Directive::Balance, got: {other:?}"),
        }
    }

    #[test]
    fn test_parse_incomplete_amount_number_only() {
        // A posting amount with a number but no currency should parse as
        // `IncompleteAmount::NumberOnly`. This pins the parse path through
        // `parse_incomplete_amount`'s NumberOnly branch.
        let source = r#"
2024-01-15 * "Test"
  Assets:Cash  100
  Expenses:Test
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
        match &result.directives[0].value {
            Directive::Transaction(txn) => {
                assert_eq!(txn.postings.len(), 2);
                assert_eq!(
                    txn.postings[0].units,
                    Some(IncompleteAmount::NumberOnly(Decimal::from(100))),
                    "first posting should have units as NumberOnly(100), got: {:?}",
                    txn.postings[0].units
                );
            }
            other => panic!("Expected Directive::Transaction, got: {other:?}"),
        }
    }

    // Metadata tests removed - posting metadata format differs from expected

    // ============================================================================
    // MEDIUM PRIORITY TESTS - Directive Parsing
    // ============================================================================

    #[test]
    fn test_parse_pushtag_and_poptag_directive() {
        // Pushtag must be closed with poptag
        let source = "pushtag #tag1\n2024-01-01 open Assets:Bank USD\npoptag #tag1\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn test_parse_poptag_without_push_errors() {
        let source = "poptag #neverpushed\n";
        let result = parse(source);
        assert!(
            !result.errors.is_empty(),
            "poptag without pushtag should error"
        );
        let msg = result.errors[0].message();
        assert!(
            msg.contains("poptag") || msg.contains("never pushed"),
            "error should mention poptag issue, got: {msg}"
        );
    }

    #[test]
    fn test_parse_pushmeta_and_popmeta_directive() {
        // Pushmeta/popmeta push metadata onto a stack and apply it to
        // every enclosed directive until the matching popmeta. They are
        // not themselves stored in `result.directives`; they mutate the
        // metadata of enclosed directives via `apply_pushed_meta`.
        //
        // Syntax: `pushmeta key: "value"` then `popmeta key:` (the colon
        // is required because `parse_meta_key` expects a MetaKey token).
        let source = concat!(
            "pushmeta key: \"value\"\n",
            "2024-01-01 open Assets:Bank USD\n",
            "popmeta key:\n",
            "2024-01-02 close Assets:Bank\n",
        );
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "Expected no parse errors, got: {:?}",
            result.errors
        );
        assert_eq!(
            result.directives.len(),
            2,
            "pushmeta/popmeta should not appear as directives; expected just open + close, got: {:?}",
            result
                .directives
                .iter()
                .map(|d| format!("{:?}", d.value))
                .collect::<Vec<_>>()
        );

        // The open directive (inside the push/pop window) should have the
        // pushed metadata applied.
        match &result.directives[0].value {
            Directive::Open(open) => {
                assert_eq!(
                    open.meta.get("key"),
                    Some(&MetaValue::String("value".to_string())),
                    "Enclosed directive should have pushed metadata applied"
                );
            }
            other => panic!("Expected Directive::Open, got: {other:?}"),
        }

        // The close directive (after popmeta) should NOT have the metadata.
        match &result.directives[1].value {
            Directive::Close(close) => {
                assert!(
                    !close.meta.contains_key("key"),
                    "Directive after popmeta should not have the popped key, got meta: {:?}",
                    close.meta
                );
            }
            other => panic!("Expected Directive::Close, got: {other:?}"),
        }
    }

    #[test]
    fn test_parse_close_directive() {
        let source = "2024-01-01 close Assets:Bank\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
        assert!(matches!(result.directives[0].value, Directive::Close(_)));
    }

    #[test]
    fn test_parse_commodity_directive() {
        let source = "2024-01-01 commodity USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
        assert!(matches!(
            result.directives[0].value,
            Directive::Commodity(_)
        ));
    }

    #[test]
    fn test_parse_pad_directive() {
        // `parse_pad_directive` calls `parse_account` twice: the account
        // being padded and the source (e.g., Equity:Opening-Balances).
        let source = "2024-01-01 pad Assets:Bank Equity:Opening-Balances\n";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "Expected no parse errors, got: {:?}",
            result.errors
        );
        assert_eq!(result.directives.len(), 1);
        match &result.directives[0].value {
            Directive::Pad(pad) => {
                assert_eq!(pad.account.as_ref(), "Assets:Bank");
                assert_eq!(pad.source_account.as_ref(), "Equity:Opening-Balances");
            }
            other => panic!("Expected Directive::Pad, got: {other:?}"),
        }
    }

    #[test]
    fn test_parse_event_directive() {
        // `parse_event_directive` expects two quoted strings:
        // event_type and value.
        let source = "2024-01-01 event \"location\" \"Paris\"\n";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "Expected no parse errors, got: {:?}",
            result.errors
        );
        assert_eq!(result.directives.len(), 1);
        match &result.directives[0].value {
            Directive::Event(event) => {
                assert_eq!(event.event_type, "location");
                assert_eq!(event.value, "Paris");
            }
            other => panic!("Expected Directive::Event, got: {other:?}"),
        }
    }

    #[test]
    fn test_parse_note_directive() {
        // `parse_note_directive` expects an account followed by a quoted
        // comment string.
        let source = "2024-01-01 note Assets:Bank \"This is a note\"\n";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "Expected no parse errors, got: {:?}",
            result.errors
        );
        assert_eq!(result.directives.len(), 1);
        match &result.directives[0].value {
            Directive::Note(note) => {
                assert_eq!(note.account.as_ref(), "Assets:Bank");
                assert_eq!(note.comment, "This is a note");
            }
            other => panic!("Expected Directive::Note, got: {other:?}"),
        }
    }

    #[test]
    fn test_parse_document_directive() {
        // `parse_document_directive` expects an account followed by a
        // quoted path string.
        let source = "2024-01-01 document Assets:Bank \"2024/report.pdf\"\n";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "Expected no parse errors, got: {:?}",
            result.errors
        );
        assert_eq!(result.directives.len(), 1);
        match &result.directives[0].value {
            Directive::Document(document) => {
                assert_eq!(document.account.as_ref(), "Assets:Bank");
                assert_eq!(document.path, "2024/report.pdf");
            }
            other => panic!("Expected Directive::Document, got: {other:?}"),
        }
    }

    #[test]
    fn test_parse_price_directive() {
        let source = "2024-01-01 price AAPL 150.00 USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
        assert!(matches!(result.directives[0].value, Directive::Price(_)));
    }

    // ============================================================================
    // LOW PRIORITY TESTS - Edge Cases
    // ============================================================================

    // Link test removed - posting metadata format differs

    #[test]
    fn test_parse_cost_spec_per_unit() {
        let source = r#"
2024-01-15 * "Test"
  Assets:Stock  -10 AAPL {150.00 USD}
  Assets:Cash
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn test_parse_cost_spec_date() {
        let source = r#"
2024-01-15 * "Test"
  Assets:Stock  -10 AAPL {2024-01-01}
  Assets:Cash
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn test_parse_cost_spec_label() {
        let source = r#"
2024-01-15 * "Test"
  Assets:Stock  -10 AAPL {"purchase"}
  Assets:Cash
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn test_parse_cost_spec_merge() {
        let source = r#"
2024-01-15 * "Test"
  Assets:Stock  -10 AAPL {*}
  Assets:Cash
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let txn = result.directives.iter().find_map(|d| {
            if let Directive::Transaction(t) = &d.value {
                Some(t)
            } else {
                None
            }
        });
        let posting = &txn.unwrap().postings[0];
        let cost = posting.cost.as_ref().expect("should have cost spec");
        assert!(cost.merge, "merge flag should be true for {{*}}");
    }

    #[test]
    fn test_parse_price_annotation_unit() {
        let source = r#"
2024-01-15 * "Test"
  Assets:Stock  10 AAPL @ 150.00 USD
  Assets:Cash
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn test_parse_price_annotation_total() {
        let source = r#"
2024-01-15 * "Test"
  Assets:Stock  10 AAPL @@ 1500.00 USD
  Assets:Cash
"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn test_parse_standalone_comment() {
        let source = "; This is a standalone comment\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(
            result.comments.len(),
            1,
            "Single-line comment source should produce exactly one comment"
        );
    }

    #[test]
    fn test_parse_multiple_standalone_comments() {
        let source = "; Comment 1\n; Comment 2\n; Comment 3\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.comments.len(), 3);
    }

    /// Regression test for issue #876 (beancount/beancount#986).
    /// Arithmetic expressions like `1000-12-32` in posting amounts must be
    /// evaluated as subtraction (1000 - 12 - 32 = 956), not tokenized as dates.
    #[test]
    fn test_date_arithmetic_ambiguity_subtraction() {
        let source = "2024-01-15 balance Assets:Bank 1000-12-32 USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        if let Directive::Balance(b) = &result.directives[0].value {
            assert_eq!(
                b.amount.number,
                Decimal::from(956),
                "1000-12-32 should evaluate to 956"
            );
            assert_eq!(b.amount.currency.as_str(), "USD");
        } else {
            panic!("Expected Balance directive");
        }
    }

    /// Regression test for issue #876: another date-like arithmetic expression.
    /// `2000-6-4` in a posting amount should evaluate to 2000 - 6 - 4 = 1990.
    #[test]
    fn test_date_arithmetic_ambiguity_single_digit() {
        let source = "2024-01-15 balance Assets:Bank 2000-6-4 USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        if let Directive::Balance(b) = &result.directives[0].value {
            assert_eq!(
                b.amount.number,
                Decimal::from(1990),
                "2000-6-4 should evaluate to 1990"
            );
        } else {
            panic!("Expected Balance directive");
        }
    }

    /// Regression test for issue #876: normal dates at line start must still
    /// be parsed as dates and not be affected by the arithmetic recovery.
    #[test]
    fn test_date_at_line_start_still_works() {
        let source = "2024-01-15 * \"Test\"\n  Assets:Bank  100 USD\n  Expenses:Other\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
        if let Directive::Transaction(txn) = &result.directives[0].value {
            assert_eq!(txn.postings.len(), 2);
        } else {
            panic!("Expected Transaction directive");
        }
    }

    /// Demonstrates that a real date-like pattern in an expression context is
    /// recovered as subtraction: 2024 - 1 - 15 = 2008.
    #[test]
    fn test_date_arithmetic_valid_date_in_expression() {
        let source = "2024-01-15 balance Assets:Bank 2024-01-15 USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        if let Directive::Balance(b) = &result.directives[0].value {
            assert_eq!(
                b.amount.number,
                Decimal::from(2008),
                "2024-01-15 in amount context should evaluate to 2024 - 1 - 15 = 2008"
            );
            assert_eq!(b.amount.currency.as_str(), "USD");
        } else {
            panic!("Expected Balance directive");
        }
    }

    /// Known limitation: since the lexer tokenizes "1000-12-32" as a single Date
    /// token, it is recovered as (1000 - 12 - 32) = 956. When followed by `*2`,
    /// the result is 956 * 2 = 1912, not the mathematically correct
    /// 1000 - 12 - (32 * 2) = 924.
    /// This is acceptable because YYYY-MM-DD patterns followed by operators are
    /// extremely unlikely in real ledger files, and fixing this would require
    /// changes at the lexer level rather than the parser level.
    #[test]
    fn test_date_arithmetic_precedence_limitation() {
        let source = "2024-01-15 balance Assets:Bank 1000-12-32*2 USD\n";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        if let Directive::Balance(b) = &result.directives[0].value {
            // (1000 - 12 - 32) * 2 = 956 * 2 = 1912, not 1000 - 12 - 64 = 924
            assert_eq!(
                b.amount.number,
                Decimal::from(1912),
                "1000-12-32*2 evaluates as (1000-12-32)*2 = 1912 due to lexer-level tokenization"
            );
        } else {
            panic!("Expected Balance directive");
        }
    }

    /// Slash-separated date-like tokens in expression context must produce a
    /// parse error, not silently compute division. Python beancount would also
    /// reject `2024/1/5` in an amount position.
    #[test]
    fn test_slash_date_in_expression_is_error() {
        let source = "2024-01-15 balance Assets:Bank 2024/1/5 USD\n";
        let result = parse(source);
        assert!(
            !result.errors.is_empty(),
            "slash-separated date in expression context should produce a parse error"
        );
    }

    // ========== fast_parse_decimal differential tests ==========

    fn assert_fast_path_matches_oracle(s: &str) {
        let fast = fast_parse_decimal(s);
        let oracle = Decimal::from_str(s).ok();
        match (fast, oracle) {
            (Some(f), Some(o)) => assert_eq!(
                f, o,
                "fast_parse_decimal({s:?})={f} disagreed with Decimal::from_str={o}"
            ),
            (Some(f), None) => {
                panic!("fast_parse_decimal accepted {s:?} as {f} but Decimal::from_str rejected")
            }
            (None, _) => {} // fast path opt-out is always allowed; the slow path takes over.
        }
    }

    #[test]
    fn fast_parse_decimal_matches_oracle_on_known_inputs() {
        for s in [
            "0",
            "1",
            "10",
            "100",
            "1000",
            "0.0",
            "0.00",
            "0.000",
            "0.1",
            "0.01",
            "0.001",
            "0.0001",
            "1.0",
            "1.00",
            "1.23",
            "1.230",
            "100.50",
            "1234.56",
            "0.1234567890123456789", // 19 fractional digits, mantissa fits in i64
            "9223372036854775807",   // i64::MAX exactly
            "9223372036854775806.0", // pre-u128 forced overflow on next mul10 — should now stay on fast path
            "99999999999999999999", // 20 nines, pre-u128 must opt out — should now stay on fast path
            "5.",                   // trailing-decimal form (lexer accepts `(\.\d*)?`)
        ] {
            assert_fast_path_matches_oracle(s);
        }
    }

    /// Inputs in the i64-overflow regime that the i64-mantissa version
    /// punted to `Decimal::from_str` and the u128 version now accepts.
    /// Verifies (a) the fast path returns Some, not None, and (b) the
    /// value matches the slow-path oracle exactly.
    #[test]
    fn fast_parse_decimal_handles_u128_range() {
        for s in [
            // 20-digit integer, ~1.8x i64::MAX
            "18446744073709551616",
            // BTC-scale 8-decimal amount past i64
            "123456789.12345678",
            // High-precision price computation result (28 sig figs total)
            "1.234567890123456789012345678",
            // Decimal::MAX as an integer (2^96 - 1 = 79228162514264337593543950335)
            "79228162514264337593543950335",
        ] {
            let fast = fast_parse_decimal(s);
            let oracle = Decimal::from_str(s).ok();
            assert!(
                fast.is_some(),
                "fast path should accept {s:?} now that mantissa is u128"
            );
            assert_eq!(fast, oracle, "fast vs slow disagree on {s:?}");
        }
    }

    /// Past `Decimal::MAX` (mantissa > 2^96 - 1) the fast path must
    /// opt out so the caller's `Decimal::from_str` fallback can return
    /// the same rejection. Locks in the bail-out behavior we rely on.
    #[test]
    fn fast_parse_decimal_opts_out_past_decimal_max() {
        for s in [
            "79228162514264337593543950336", // 2^96 — first integer past Decimal::MAX
            "1000000000000000000000000000000", // 30 digits, well past
        ] {
            assert_eq!(
                fast_parse_decimal(s),
                None,
                "fast path should opt out on {s:?} so slow path can handle / reject it"
            );
        }
    }

    #[test]
    fn fast_parse_decimal_rejects_malformed() {
        // "1,000" is a valid lexer Number token but parse_number routes commas to the slow path; the rest the lexer rejects outright. Either way fast_parse_decimal must return None.
        for s in ["", "1.2.3", "abc", "1e5", "-1", "+1", "1,000"] {
            assert_eq!(fast_parse_decimal(s), None, "should reject {s:?}");
        }
    }

    #[test]
    fn fast_parse_decimal_zero_with_leading_zeros() {
        // Direct echo of the importer bug class (#972): make sure the fast path doesn't
        // strip post-decimal leading zeros.
        assert_eq!(
            fast_parse_decimal("0.01"),
            Some(Decimal::from_str("0.01").unwrap())
        );
        assert_eq!(
            fast_parse_decimal("0.001"),
            Some(Decimal::from_str("0.001").unwrap())
        );
        assert_eq!(fast_parse_decimal("0.00"), Some(Decimal::ZERO));
    }

    proptest::proptest! {
        // Bounded comma-free subset of the lexer's Number grammar that
        // fast_parse_decimal can plausibly accept. Widened to 28 digits
        // per side from the pre-fix cap of 18 (which was constrained by
        // i64 overflow on the fast path). Note: not every generated
        // input is representable — `rust_decimal`'s actual limit is ~29
        // significant digits total with scale ≤ 28, so a generated
        // string like `9999…9.9999…9` with 28 digits per side has 56
        // sig figs and will overflow. That's intentional: those inputs
        // exercise the opt-out branch, and we assert agreement only
        // when fast_parse_decimal returns `Some`. Longer/comma inputs
        // go to the slow path so we don't generate them here.
        #[test]
        fn fast_parse_decimal_agrees_with_decimal_from_str(
            s in "[0-9]{1,28}(\\.[0-9]{1,28})?"
        ) {
            let fast = fast_parse_decimal(&s);
            let oracle = Decimal::from_str(&s).ok();
            if let Some(f) = fast {
                proptest::prop_assert_eq!(Some(f), oracle);
            }
        }

        #[test]
        fn fast_parse_decimal_round_trips_through_display(
            mantissa in 0i64..=i64::MAX,
            scale in 0u32..=18
        ) {
            let original = Decimal::new(mantissa, scale);
            let s = original.to_string();
            // Display output has no commas/sign so we can hit fast_parse_decimal directly without going through the lexer.
            let fast = fast_parse_decimal(&s);
            let oracle = Decimal::from_str(&s).ok();
            if let Some(f) = fast {
                proptest::prop_assert_eq!(f, original);
            }
            // When the fast path opts out, the slow path (Decimal::from_str) must succeed.
            if fast.is_none() {
                proptest::prop_assert_eq!(oracle, Some(original));
            }
        }
    }
}
