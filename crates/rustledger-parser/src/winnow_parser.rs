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

use chrono::NaiveDate;
use rust_decimal::Decimal;
use std::str::FromStr;

use rustledger_core::{
    Amount, Balance, Close, Commodity, CostSpec, Custom, Directive, Document, Event,
    IncompleteAmount, InternedStr, MetaValue, Metadata, Note, Open, Pad, Posting, Price,
    PriceAnnotation, Query, Transaction,
};

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
}

impl<'src> TokenStream<'src> {
    const fn new(tokens: &'src [SpannedToken<'src>]) -> Self {
        Self { tokens, pos: 0 }
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
        let normalized = s.replace('/', "-");
        if let Ok(date) = NaiveDate::parse_from_str(&normalized, "%Y-%m-%d") {
            stream.advance();
            return Ok(date);
        }
    }
    Err(())
}

fn parse_number(stream: &mut TokenStream<'_>) -> ParseRes<Decimal> {
    if let Some(t) = stream.peek()
        && let Token::Number(s) = &t.token
    {
        let cleaned = s.replace(',', "");
        if let Ok(num) = Decimal::from_str(&cleaned) {
            stream.advance();
            return Ok(num);
        }
    }
    Err(())
}

fn parse_string(stream: &mut TokenStream<'_>) -> ParseRes<String> {
    if let Some(t) = stream.peek()
        && let Token::String(s) = &t.token
    {
        let inner = &s[1..s.len() - 1];
        let result = process_string_escapes(inner);
        stream.advance();
        return Ok(result);
    }
    Err(())
}

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
        let result: InternedStr = (*s).into();
        stream.advance();
        return Ok(result);
    }
    Err(())
}

fn parse_currency(stream: &mut TokenStream<'_>) -> ParseRes<InternedStr> {
    if let Some(t) = stream.peek()
        && let Token::Currency(s) = &t.token
    {
        let result: InternedStr = (*s).into();
        stream.advance();
        return Ok(result);
    }
    Err(())
}

fn parse_tag(stream: &mut TokenStream<'_>) -> ParseRes<InternedStr> {
    if let Some(t) = stream.peek()
        && let Token::Tag(s) = &t.token
    {
        let result: InternedStr = s[1..].into(); // Skip #
        stream.advance();
        return Ok(result);
    }
    Err(())
}

fn parse_link(stream: &mut TokenStream<'_>) -> ParseRes<InternedStr> {
    if let Some(t) = stream.peek()
        && let Token::Link(s) = &t.token
    {
        let result: InternedStr = s[1..].into(); // Skip ^
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
                result *= rhs;
            }
            Token::Slash => {
                stream.advance();
                let rhs = parse_primary(stream)?;
                result /= rhs;
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
                result += rhs;
            }
            Token::Minus => {
                stream.advance();
                let rhs = parse_term(stream)?;
                result -= rhs;
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

    // Parse cost components
    loop {
        // Check for closing brace
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
                _ => {}
            }
        } else {
            return Err(());
        }

        // Try to parse different component types
        if let Ok(date) = parse_date(stream) {
            spec.date = Some(date);
        } else if let Ok(label) = parse_string(stream) {
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

    // Optional cost
    let cost = parse_cost_spec(stream).ok();

    // Optional price
    let price = parse_price_annotation(stream).ok();

    // Skip optional comment
    skip_comment(stream);

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
    if let Ok(s) = parse_string(stream) {
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
    let key = parse_string(stream)?;
    let value = parse_string(stream)?;
    let span = stream.span_from(start_pos);
    Ok(ParsedItem::Option(key, value, span))
}

fn parse_include_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    expect_token!(stream, Token::Include)?;
    let path = parse_string(stream)?;
    let span = stream.span_from(start_pos);
    Ok(ParsedItem::Include(path, span))
}

fn parse_plugin_directive(stream: &mut TokenStream<'_>) -> ParseRes<ParsedItem> {
    let start_pos = stream.pos;
    expect_token!(stream, Token::Plugin)?;
    let name = parse_string(stream)?;
    let config = parse_string(stream).ok();
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
    let flag = if let Some(t) = stream.peek() {
        match &t.token {
            Token::Txn => {
                stream.advance();
                '*'
            }
            Token::Star | Token::Pending | Token::Hash | Token::Flag(_) => parse_flag(stream)?,
            Token::String(_) => '*', // Implied txn
            _ => return Err(()),
        }
    } else {
        return Err(());
    };

    // Parse payee/narration strings
    let mut strings = Vec::new();
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

    // Tags and links
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
    let mut postings = Vec::new();

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

                    // Check for comment on its own line
                    if let Some(t) = stream.peek()
                        && matches!(t.token, Token::Comment(_) | Token::PercentComment(_))
                    {
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
        if let Ok(posting) = parse_posting(stream) {
            postings.push(posting);
        } else {
            break;
        }
    }

    // Build transaction
    let (payee, narration) = if has_pipe && strings.len() >= 2 {
        (Some(strings.remove(0)), strings.remove(0))
    } else {
        match strings.len() {
            0 => (None, String::new()),
            1 => (None, strings.remove(0)),
            _ => (Some(strings.remove(0)), strings.remove(0)),
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
    // Apply transaction-level metadata
    txn.meta = txn_meta;

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
            parse_number(stream).ok()
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
    let mut currencies: Vec<InternedStr> = Vec::new();
    while let Ok(c) = parse_currency(stream) {
        currencies.push(c);
        // Consume optional comma separator
        if let Some(t) = stream.peek()
            && matches!(t.token, Token::Comma)
        {
            stream.advance();
        }
    }

    let booking = parse_string(stream).ok().and_then(|s| s.parse().ok());

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
    let event_type = parse_string(stream)?;
    let value = parse_string(stream)?;
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
    let name = parse_string(stream)?;
    let query = parse_string(stream)?;
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
    let comment = parse_string(stream)?;
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
    let path = parse_string(stream)?;

    // Optional tags and links
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
    let name = parse_string(stream)?;

    let mut values = Vec::new();
    loop {
        // String
        if let Ok(s) = parse_string(stream) {
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
        // Plain number (without currency)
        if let Ok(n) = parse_number(stream) {
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

    let mut directives = Vec::new();
    let mut options = Vec::new();
    let mut includes = Vec::new();
    let mut plugins = Vec::new();
    let mut comments = Vec::new();
    let mut errors = Vec::new();

    let mut tag_stack: Vec<(InternedStr, Span)> = Vec::new();
    let mut meta_stack: Vec<(String, MetaValue, Span)> = Vec::new();

    while !stream.is_empty() {
        let error_start = stream.pos;

        if let Ok(item) = parse_entry(&mut stream) {
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
            // If stream is now empty, we just consumed trailing newlines - not an error
            if stream.is_empty() {
                break;
            }
            // Error recovery: skip to next newline
            stream.skip_to_newline();
            let span = stream.span_from(error_start);
            errors.push(ParseError::new(
                ParseErrorKind::SyntaxError("unexpected input".to_string()),
                span,
            ));
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
}
