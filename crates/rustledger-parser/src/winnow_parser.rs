//! Winnow-based parser for Beancount syntax.
//!
//! This module provides a high-performance parser using winnow combinators,
//! designed as a faster alternative to the chumsky-based parser.
//!
//! # Architecture
//!
//! ```text
//! Source (&str) → Logos tokenize() → Vec<SpannedToken> → Manual parser → Directives
//! ```
//!
//! We use a manual token stream approach rather than implementing winnow's Stream
//! trait, as it provides simpler code and good performance.

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

/// Cap on upfront `comments` preallocation. Same rationale as
/// [`MAX_PREALLOC_DIRECTIVES`].
const MAX_PREALLOC_COMMENTS: usize = 8_192;

use crate::ParseResult;
use crate::error::{ParseError, ParseErrorKind};
use crate::logos_lexer::{Token, tokenize};
use crate::span::{Span, Spanned};

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
}

impl<'src> TokenStream<'src> {
    fn new(tokens: &'src [SpannedToken<'src>]) -> Self {
        Self {
            tokens,
            pos: 0,
            deferred_error: None,
            interner: rustledger_core::intern::StringInterner::new(),
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

/// Zero-pad single-digit month/day and normalize '/' separators to '-'.
/// Returns the original string as-is when already in canonical `YYYY-MM-DD` form
/// to avoid unnecessary allocation on the hot path.
fn normalize_date_str(s: &str) -> Cow<'_, str> {
    // Fast path: already canonical (no '/', month+day are 2 digits → length is 10).
    if !s.contains('/') && s.len() == 10 {
        return Cow::Borrowed(s);
    }
    // Separator can be '-' or '/'; the regex guarantees three parts.
    let s = s.replace('/', "-");
    if let Some((year, rest)) = s.split_once('-')
        && let Some((month, day)) = rest.split_once('-')
    {
        return Cow::Owned(format!("{year}-{month:0>2}-{day:0>2}"));
    }
    Cow::Owned(s)
}

/// Build a human-readable reason why a date string is invalid.
fn describe_invalid_date(s: &str) -> String {
    let parts: Vec<&str> = s.split(['-', '/']).collect();
    if parts.len() == 3
        && let (Ok(year), Ok(month), Ok(day)) = (
            parts[0].parse::<i32>(),
            parts[1].parse::<u32>(),
            parts[2].parse::<u32>(),
        )
    {
        if !(1..=12).contains(&month) {
            return format!("month {month} out of range");
        }
        let year_month = format!("{year}-{month:02}");
        return format!("day {day} out of range for {year_month}");
    }
    format!("invalid date '{s}'")
}

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
/// Handles `[0-9]+(\.[0-9]+)?` — no sign, no commas, no exponent.
/// Returns `None` for anything more complex, falling through to
/// `Decimal::from_str`.
fn fast_parse_decimal(s: &str) -> Option<Decimal> {
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return None;
    }

    let mut mantissa: i64 = 0;
    let mut scale: u32 = 0;
    let mut in_decimal = false;

    for &b in bytes {
        match b {
            b'0'..=b'9' => {
                // Check for overflow before multiplying
                mantissa = mantissa.checked_mul(10)?.checked_add(i64::from(b - b'0'))?;
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

    Some(Decimal::new(mantissa, scale))
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

fn parse_account(stream: &mut TokenStream<'_>) -> ParseRes<InternedStr> {
    if let Some(t) = stream.peek()
        && let Token::Account(s) = &t.token
    {
        let result = stream.interner.intern(s);
        stream.advance();
        return Ok(result);
    }
    Err(())
}

fn parse_currency(stream: &mut TokenStream<'_>) -> ParseRes<InternedStr> {
    if let Some(t) = stream.peek()
        && let Token::Currency(s) = &t.token
    {
        let result = stream.interner.intern(s);
        stream.advance();
        return Ok(result);
    }
    Err(())
}

fn parse_tag(stream: &mut TokenStream<'_>) -> ParseRes<InternedStr> {
    if let Some(t) = stream.peek()
        && let Token::Tag(s) = &t.token
    {
        let result = stream.interner.intern(&s[1..]); // Skip #
        stream.advance();
        return Ok(result);
    }
    Err(())
}

fn parse_link(stream: &mut TokenStream<'_>) -> ParseRes<InternedStr> {
    if let Some(t) = stream.peek()
        && let Token::Link(s) = &t.token
    {
        let result = stream.interner.intern(&s[1..]); // Skip ^
        stream.advance();
        return Ok(result);
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
                // The number after # is the total
                if let Ok(total) = parse_expr(stream) {
                    spec.number_total = Some(total);
                    if let Ok(c) = parse_currency(stream) {
                        spec.currency = Some(c);
                    }
                    continue;
                }
            }

            if is_total {
                spec.number_total = Some(number);
            } else {
                spec.number_per = Some(number);
            }

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
            PriceAnnotation::Total(amount)
        } else {
            PriceAnnotation::Unit(amount)
        });
    }
    stream.pos = save_pos;

    // Try just currency (incomplete price - number missing)
    if let Ok(currency) = parse_currency(stream) {
        let incomplete = IncompleteAmount::CurrencyOnly(currency);
        return Ok(if is_total {
            PriceAnnotation::TotalIncomplete(incomplete)
        } else {
            PriceAnnotation::UnitIncomplete(incomplete)
        });
    }
    stream.pos = save_pos;

    // Try just number (incomplete price - currency missing)
    if let Ok(number) = parse_expr(stream) {
        let incomplete = IncompleteAmount::NumberOnly(number);
        return Ok(if is_total {
            PriceAnnotation::TotalIncomplete(incomplete)
        } else {
            PriceAnnotation::UnitIncomplete(incomplete)
        });
    }
    stream.pos = save_pos;

    Err(())
}

// ============================================================================
// Posting Parser
// ============================================================================

fn parse_posting(stream: &mut TokenStream<'_>) -> ParseRes<Posting> {
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

    Ok(posting)
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
        return Ok(MetaValue::Account(a.to_string()));
    }
    if let Ok(d) = parse_date(stream) {
        return Ok(MetaValue::Date(d));
    }
    // Tag value (e.g., #trip-florida)
    if let Ok(tag) = parse_tag(stream) {
        return Ok(MetaValue::Tag(tag.to_string()));
    }
    // Link value (e.g., ^doc-123)
    if let Ok(link) = parse_link(stream) {
        return Ok(MetaValue::Link(link.to_string()));
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
        return Ok(MetaValue::Currency(c.to_string()));
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
    Pushtag(InternedStr, Span),
    Poptag(InternedStr, Span),
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
    let mut tags: Vec<InternedStr> = Vec::new();
    let mut links: Vec<InternedStr> = Vec::new();

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
    let mut postings = Vec::with_capacity(4);
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
        if let Ok(mut posting) = parse_posting(stream) {
            // Attach any pending comments to this posting
            if !pending_comments.is_empty() {
                posting.comments = std::mem::take(&mut pending_comments);
            }
            postings.push(posting);
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
    for p in postings {
        txn = txn.with_posting(p);
    }
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
    let mut currencies: Vec<InternedStr> = Vec::with_capacity(3);
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
    let mut tags: Vec<InternedStr> = Vec::new();
    let mut links: Vec<InternedStr> = Vec::new();
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
            values.push(MetaValue::Account(a.to_string()));
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
            values.push(MetaValue::Currency(c.to_string()));
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

fn apply_pushed_tags(directive: &mut Directive, tag_stack: &[(InternedStr, Span)]) {
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

/// Parse beancount source code using winnow-based parser.
pub fn parse(source: &str) -> ParseResult {
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

    let mut tag_stack: Vec<(InternedStr, Span)> = Vec::with_capacity(8);
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
            // Prefer a deferred error set by an inner parser (e.g., invalid
            // date value or unclosed cost spec) over the generic "unexpected
            // input" fallback.
            if let Some(err) = stream.deferred_error.take() {
                errors.push(err);
            } else {
                // Produce specific error messages for known patterns
                let error_text = &source[span.start..span.end.min(source.len())];
                let kind = if error_text.starts_with('\u{FEFF}') {
                    // UTF-8 BOM (byte order mark)
                    ParseErrorKind::SyntaxError("Invalid token: UTF-8 BOM detected; remove the BOM from the beginning of the file".to_string())
                } else if let Some(account) = find_unicode_account(error_text) {
                    // Non-ASCII characters in what looks like an account name
                    ParseErrorKind::InvalidAccount(account.to_string())
                } else {
                    ParseErrorKind::SyntaxError("unexpected input".to_string())
                };
                errors.push(ParseError::new(kind, span));
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
    }
}

/// Find a Unicode account name in the error text, if any.
///
/// Scans all whitespace-delimited tokens in the text for a pattern that looks
/// like an account name (uppercase start + colon) but contains non-ASCII.
/// Returns the matching token, or `None`.
fn find_unicode_account(text: &str) -> Option<&str> {
    for token in text.split_whitespace() {
        if !token.contains(':') {
            continue;
        }
        let first_char = token.chars().next().unwrap_or(' ');
        if !first_char.is_uppercase() {
            continue;
        }
        if !token.is_ascii() {
            return Some(token);
        }
    }
    None
}

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
        use rustledger_core::format::{FormatConfig, format_directive};

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
        let formatted = format_directive(&result1.directives[0].value, &config);

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

    #[test]
    fn test_bom_produces_invalid_token_error() {
        let source = "\u{FEFF}2024-01-01 open Assets:Bank USD\n";
        let result = parse(source);
        assert!(
            !result.errors.is_empty(),
            "BOM should produce a parse error"
        );
        let msg = result.errors[0].message();
        assert!(
            msg.contains("Invalid token"),
            "BOM error should contain 'Invalid token', got: {msg}"
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
            "9223372036854775806.0", // forces overflow on next mul10 → opt-out OK
            "99999999999999999999",  // 20 nines, must opt out (overflow)
            "5.",                    // trailing-decimal form (lexer accepts `(\.\d*)?`)
        ] {
            assert_fast_path_matches_oracle(s);
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
        // Bounded comma-free subset of the lexer's Number grammar that fast_parse_decimal can plausibly accept; longer/comma inputs go to the slow path so we don't generate them here.
        #[test]
        fn fast_parse_decimal_agrees_with_decimal_from_str(
            s in "[0-9]{1,18}(\\.[0-9]{1,18})?"
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
