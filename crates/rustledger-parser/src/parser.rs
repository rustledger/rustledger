//! Parser implementation for beancount files.
//!
//! Uses chumsky for parser combinators with error recovery.
//!
//! # Organization
//!
//! This module is organized into the following sections:
//!
//! 1. **Main API** (lines ~30-95) - `parse()` function and result handling
//! 2. **Tag/Meta Helpers** (lines ~98-235) - pushtag/pushmeta application
//! 3. **File Structure** (lines ~238-320) - file, entry, whitespace parsers
//! 4. **Special Directives** (lines ~321-400) - option, include, plugin, push/pop
//! 5. **Primitives** (lines ~400-600) - strings, dates, numbers, expressions
//! 6. **Amounts & Costs** (lines ~600-850) - amount, cost spec, price annotation
//! 7. **Metadata & Accounts** (lines ~850-940) - account, flag, tag, link, metadata
//! 8. **Transactions** (lines ~940-1180) - transaction body, postings
//! 9. **Directive Bodies** (lines ~1180-2054) - balance, open, close, etc.

use chumsky::prelude::*;
use rust_decimal::Decimal;
use std::str::FromStr;

use chrono::NaiveDate;
use rustledger_core::{
    Amount, Balance, Close, Commodity, CostSpec, Custom, Directive, Document, Event,
    IncompleteAmount, MetaValue, Metadata, Note, Open, Pad, Posting, Price, PriceAnnotation, Query,
    Transaction,
};

use crate::ParseResult;
use crate::error::{ParseError, ParseErrorKind};
use crate::span::{Span, Spanned};

type ParserInput<'a> = &'a str;
type ParserExtra<'a> = extra::Err<Rich<'a, char>>;

/// Convert a `SimpleSpan` to our Span type.
const fn to_span(s: SimpleSpan) -> Span {
    Span::new(s.start, s.end)
}

/// Parse beancount source code.
pub fn parse(source: &str) -> ParseResult {
    let (items, errs) = file_parser().parse(source).into_output_errors();

    let items = items.unwrap_or_default();

    let mut directives = Vec::new();
    let mut options = Vec::new();
    let mut includes = Vec::new();
    let mut plugins = Vec::new();

    // Tag stack for pushtag/poptag
    let mut tag_stack: Vec<String> = Vec::new();
    // Meta stack for pushmeta/popmeta
    let mut meta_stack: Vec<(String, MetaValue)> = Vec::new();

    for (item, simple_span) in items {
        let span = to_span(simple_span);
        match item {
            ParsedItem::Directive(d) => {
                // Apply pushed tags to transactions
                let d = apply_pushed_tags(d, &tag_stack);
                // Apply pushed meta to all directives
                let d = apply_pushed_meta(d, &meta_stack);
                directives.push(Spanned::new(d, span));
            }
            ParsedItem::Option(k, v) => options.push((k, v, span)),
            ParsedItem::Include(p) => includes.push((p, span)),
            ParsedItem::Plugin(p, c) => plugins.push((p, c, span)),
            ParsedItem::Pushtag(tag) => tag_stack.push(tag),
            ParsedItem::Poptag(tag) => {
                // Remove the tag from the stack (should match)
                if let Some(pos) = tag_stack.iter().rposition(|t| t == &tag) {
                    tag_stack.remove(pos);
                }
            }
            ParsedItem::Pushmeta(key, value) => meta_stack.push((key, value)),
            ParsedItem::Popmeta(key) => {
                // Remove the meta from the stack (should match)
                if let Some(pos) = meta_stack.iter().rposition(|(k, _)| k == &key) {
                    meta_stack.remove(pos);
                }
            }
            ParsedItem::Comment => {}
        }
    }

    let errors: Vec<ParseError> = errs
        .into_iter()
        .map(|e| {
            let span = to_span(*e.span());
            let kind = if e.found().is_none() {
                ParseErrorKind::UnexpectedEof
            } else {
                ParseErrorKind::SyntaxError(e.to_string())
            };
            ParseError::new(kind, span)
        })
        .collect();

    ParseResult {
        directives,
        options,
        includes,
        plugins,
        errors,
    }
}

/// Apply pushed tags to a directive (only affects transactions).
fn apply_pushed_tags(directive: Directive, tag_stack: &[String]) -> Directive {
    if tag_stack.is_empty() {
        return directive;
    }

    match directive {
        Directive::Transaction(mut txn) => {
            // Add pushed tags that aren't already present
            for tag in tag_stack {
                if !txn.tags.contains(tag) {
                    txn.tags.push(tag.clone());
                }
            }
            Directive::Transaction(txn)
        }
        other => other,
    }
}

/// Apply pushed metadata to a directive (affects all directive types).
fn apply_pushed_meta(directive: Directive, meta_stack: &[(String, MetaValue)]) -> Directive {
    if meta_stack.is_empty() {
        return directive;
    }

    match directive {
        Directive::Transaction(mut txn) => {
            for (key, value) in meta_stack {
                if !txn.meta.contains_key(key) {
                    txn.meta.insert(key.clone(), value.clone());
                }
            }
            Directive::Transaction(txn)
        }
        Directive::Balance(mut bal) => {
            for (key, value) in meta_stack {
                if !bal.meta.contains_key(key) {
                    bal.meta.insert(key.clone(), value.clone());
                }
            }
            Directive::Balance(bal)
        }
        Directive::Open(mut open) => {
            for (key, value) in meta_stack {
                if !open.meta.contains_key(key) {
                    open.meta.insert(key.clone(), value.clone());
                }
            }
            Directive::Open(open)
        }
        Directive::Close(mut close) => {
            for (key, value) in meta_stack {
                if !close.meta.contains_key(key) {
                    close.meta.insert(key.clone(), value.clone());
                }
            }
            Directive::Close(close)
        }
        Directive::Commodity(mut comm) => {
            for (key, value) in meta_stack {
                if !comm.meta.contains_key(key) {
                    comm.meta.insert(key.clone(), value.clone());
                }
            }
            Directive::Commodity(comm)
        }
        Directive::Pad(mut pad) => {
            for (key, value) in meta_stack {
                if !pad.meta.contains_key(key) {
                    pad.meta.insert(key.clone(), value.clone());
                }
            }
            Directive::Pad(pad)
        }
        Directive::Event(mut event) => {
            for (key, value) in meta_stack {
                if !event.meta.contains_key(key) {
                    event.meta.insert(key.clone(), value.clone());
                }
            }
            Directive::Event(event)
        }
        Directive::Query(mut query) => {
            for (key, value) in meta_stack {
                if !query.meta.contains_key(key) {
                    query.meta.insert(key.clone(), value.clone());
                }
            }
            Directive::Query(query)
        }
        Directive::Note(mut note) => {
            for (key, value) in meta_stack {
                if !note.meta.contains_key(key) {
                    note.meta.insert(key.clone(), value.clone());
                }
            }
            Directive::Note(note)
        }
        Directive::Document(mut doc) => {
            for (key, value) in meta_stack {
                if !doc.meta.contains_key(key) {
                    doc.meta.insert(key.clone(), value.clone());
                }
            }
            Directive::Document(doc)
        }
        Directive::Price(mut price) => {
            for (key, value) in meta_stack {
                if !price.meta.contains_key(key) {
                    price.meta.insert(key.clone(), value.clone());
                }
            }
            Directive::Price(price)
        }
        Directive::Custom(mut custom) => {
            for (key, value) in meta_stack {
                if !custom.meta.contains_key(key) {
                    custom.meta.insert(key.clone(), value.clone());
                }
            }
            Directive::Custom(custom)
        }
    }
}

/// Items that can appear in a beancount file.
#[derive(Debug, Clone)]
enum ParsedItem {
    Directive(Directive),
    Option(String, String),
    Include(String),
    Plugin(String, Option<String>),
    Pushtag(String),
    Poptag(String),
    Pushmeta(String, MetaValue),
    Popmeta(String),
    Comment,
}

/// Main file parser.
fn file_parser<'a>()
-> impl Parser<'a, ParserInput<'a>, Vec<(ParsedItem, SimpleSpan)>, ParserExtra<'a>> {
    // Skip leading whitespace/newlines, then parse entries with error recovery
    skip_blank_lines().ignore_then(
        // Try to parse an entry, or skip a bad line on failure
        entry_parser()
            .map_with(|item, e| Some((item, e.span())))
            .recover_with(via_parser(
                // On error, skip at least one char then rest of line, emit None
                any()
                    .then(none_of("\r\n").repeated())
                    .then_ignore(newline().or_not())
                    .to(None),
            ))
            .then_ignore(skip_blank_lines())
            .repeated()
            .collect::<Vec<_>>()
            .map(|items| items.into_iter().flatten().collect()),
    )
}

/// Skip blank lines and comments.
fn skip_blank_lines<'a>() -> impl Parser<'a, ParserInput<'a>, (), ParserExtra<'a>> + Clone {
    choice((
        // Empty line: optional whitespace followed by newline
        ws().then_ignore(newline()),
        // Comment line: ; followed by anything until newline
        ws().then_ignore(just(';'))
            .then_ignore(none_of("\r\n").repeated())
            .then_ignore(newline()),
        // Org-mode style headers (* at start of line, not a directive)
        // These are used for organization but ignored by beancount
        just('*')
            .then(none_of("\r\n").repeated())
            .then_ignore(newline())
            .ignored(),
    ))
    .repeated()
    .ignored()
}

/// Parse a single entry (directive, option, etc.) NOT including trailing newlines.
fn entry_parser<'a>() -> impl Parser<'a, ParserInput<'a>, ParsedItem, ParserExtra<'a>> {
    choice((
        dated_directive().map(ParsedItem::Directive),
        option_directive(),
        include_directive(),
        plugin_directive(),
        pushtag_directive(),
        poptag_directive(),
        pushmeta_directive(),
        popmeta_directive(),
        // Standalone comment at end of file (no trailing newline)
        ws().ignore_then(just(';'))
            .then(none_of("\r\n").repeated())
            .to(ParsedItem::Comment),
    ))
}

/// Parse whitespace (spaces and tabs, not newlines).
fn ws<'a>() -> impl Parser<'a, ParserInput<'a>, (), ParserExtra<'a>> + Clone {
    one_of(" \t").repeated().ignored()
}

/// Parse required whitespace.
fn ws1<'a>() -> impl Parser<'a, ParserInput<'a>, (), ParserExtra<'a>> + Clone {
    one_of(" \t").repeated().at_least(1).ignored()
}

/// Parse a newline.
fn newline<'a>() -> impl Parser<'a, ParserInput<'a>, (), ParserExtra<'a>> + Clone {
    just('\n')
        .ignored()
        .or(just('\r').ignore_then(just('\n')).ignored())
}

/// Parse a comment line.
fn comment_line<'a>() -> impl Parser<'a, ParserInput<'a>, (), ParserExtra<'a>> {
    ws().then(just(';').then(none_of("\r\n").repeated()))
        .ignored()
}

/// Parse an option directive.
fn option_directive<'a>() -> impl Parser<'a, ParserInput<'a>, ParsedItem, ParserExtra<'a>> {
    just("option")
        .ignore_then(ws1())
        .ignore_then(string_literal())
        .then_ignore(ws1())
        .then(string_literal())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .map(|(k, v)| ParsedItem::Option(k, v))
}

/// Parse an include directive.
fn include_directive<'a>() -> impl Parser<'a, ParserInput<'a>, ParsedItem, ParserExtra<'a>> {
    just("include")
        .ignore_then(ws1())
        .ignore_then(string_literal())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .map(ParsedItem::Include)
}

/// Parse a plugin directive.
fn plugin_directive<'a>() -> impl Parser<'a, ParserInput<'a>, ParsedItem, ParserExtra<'a>> {
    just("plugin")
        .ignore_then(ws1())
        .ignore_then(string_literal())
        .then(ws1().ignore_then(string_literal()).or_not())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .map(|(name, config)| ParsedItem::Plugin(name, config))
}

/// Parse a pushtag directive.
fn pushtag_directive<'a>() -> impl Parser<'a, ParserInput<'a>, ParsedItem, ParserExtra<'a>> {
    just("pushtag")
        .ignore_then(ws1())
        .ignore_then(just('#'))
        .ignore_then(tag_name())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .map(ParsedItem::Pushtag)
}

/// Parse a poptag directive.
fn poptag_directive<'a>() -> impl Parser<'a, ParserInput<'a>, ParsedItem, ParserExtra<'a>> {
    just("poptag")
        .ignore_then(ws1())
        .ignore_then(just('#'))
        .ignore_then(tag_name())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .map(ParsedItem::Poptag)
}

/// Parse a pushmeta directive: pushmeta key: value
fn pushmeta_directive<'a>() -> impl Parser<'a, ParserInput<'a>, ParsedItem, ParserExtra<'a>> {
    just("pushmeta")
        .ignore_then(ws1())
        .ignore_then(metadata_key())
        .then_ignore(just(':'))
        .then_ignore(ws())
        .then(metadata_value())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .map(|(key, value)| ParsedItem::Pushmeta(key, value))
}

/// Parse a popmeta directive: popmeta key:
fn popmeta_directive<'a>() -> impl Parser<'a, ParserInput<'a>, ParsedItem, ParserExtra<'a>> {
    just("popmeta")
        .ignore_then(ws1())
        .ignore_then(metadata_key())
        .then_ignore(just(':'))
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .map(ParsedItem::Popmeta)
}

/// Parse a tag name (alphanumeric and dashes).
fn tag_name<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    one_of("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_")
        .repeated()
        .at_least(1)
        .collect()
}

/// Parse a string literal.
/// Parse a multi-line string (triple-quoted).
fn multiline_string<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    just("\"\"\"")
        .ignore_then(
            // Match any character except """ (greedy until we see """)
            any()
                .and_is(just("\"\"\"").not())
                .repeated()
                .collect::<String>(),
        )
        .then_ignore(just("\"\"\""))
}

/// Parse a single-line string.
fn single_line_string<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    just('"')
        .ignore_then(
            none_of("\"\\")
                .or(just('\\').ignore_then(any()))
                .repeated()
                .collect::<String>(),
        )
        .then_ignore(just('"'))
}

/// Parse a string literal (single or multi-line).
fn string_literal<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    // Try multi-line first (more specific pattern)
    multiline_string().or(single_line_string())
}

/// Parse digits (for dates).
fn date_digits<'a>() -> impl Parser<'a, ParserInput<'a>, &'a str, ParserExtra<'a>> + Clone {
    one_of("0123456789").repeated().at_least(1).to_slice()
}

/// Parse a date (YYYY-MM-DD).
fn date<'a>() -> impl Parser<'a, ParserInput<'a>, NaiveDate, ParserExtra<'a>> + Clone {
    date_digits()
        .then_ignore(just('-').or(just('/')))
        .then(date_digits())
        .then_ignore(just('-').or(just('/')))
        .then(date_digits())
        .try_map(|((year, month), day): ((&str, &str), &str), span| {
            let y: i32 = year
                .parse()
                .map_err(|_| Rich::custom(span, "invalid year"))?;
            let m: u32 = month
                .parse()
                .map_err(|_| Rich::custom(span, "invalid month"))?;
            let d: u32 = day.parse().map_err(|_| Rich::custom(span, "invalid day"))?;
            NaiveDate::from_ymd_opt(y, m, d).ok_or_else(|| Rich::custom(span, "invalid date"))
        })
}

/// Parse digits.
fn digits<'a>() -> impl Parser<'a, ParserInput<'a>, &'a str, ParserExtra<'a>> + Clone {
    one_of("0123456789").repeated().at_least(1).to_slice()
}

/// Parse a number literal (supports comma separators: 1,234,567.89 and leading decimals: .50).
fn number_literal<'a>() -> impl Parser<'a, ParserInput<'a>, Decimal, ParserExtra<'a>> + Clone {
    // Integer part: digits optionally separated by commas
    let int_part = digits()
        .then(just(',').then(digits()).repeated().collect::<Vec<_>>())
        .to_slice();

    // Fractional part: dot followed by digits
    let frac_part = just('.').then(digits());

    // Number can be:
    // - int_part only (e.g., "123")
    // - int_part followed by frac_part (e.g., "123.45")
    // - frac_part only (e.g., ".50")
    let number_body = choice((
        // Integer with optional fraction: 123 or 123.45
        int_part
            .then(frac_part.clone().or_not())
            .map(|(int, frac)| (Some(int), frac)),
        // Leading decimal: .50
        frac_part.map(|frac| (None, Some(frac))),
    ));

    number_body.try_map(
        |(int_part, frac_part): (Option<&str>, Option<(char, &str)>), span| {
            let mut s = String::new();
            // Remove commas from integer part
            if let Some(int) = int_part {
                for c in int.chars() {
                    if c != ',' {
                        s.push(c);
                    }
                }
            } else {
                // Leading decimal needs a 0 for parsing
                s.push('0');
            }
            if let Some((_, frac)) = frac_part {
                s.push('.');
                s.push_str(frac);
            }
            Decimal::from_str(&s).map_err(|_| Rich::custom(span, "invalid number"))
        },
    )
}

/// Parse an arithmetic expression with standard precedence.
/// Supports: +, -, *, /, parentheses, unary minus.
fn expr<'a>() -> impl Parser<'a, ParserInput<'a>, Decimal, ParserExtra<'a>> + Clone {
    recursive(|expr| {
        // Atom: number literal or parenthesized expression
        let atom = choice((
            // Parenthesized expression
            just('(')
                .ignore_then(ws())
                .ignore_then(expr.clone())
                .then_ignore(ws())
                .then_ignore(just(')')),
            // Plain number
            number_literal(),
        ));

        // Unary: optional +/- signs with optional whitespace, followed by atom
        let unary = choice((just('-'), just('+')))
            .then_ignore(ws())
            .repeated()
            .collect::<Vec<_>>()
            .then(atom)
            .map(|(signs, n): (Vec<char>, Decimal)| {
                // Count minus signs - each flips the sign, plus is a no-op
                let neg_count = signs.iter().filter(|&&c| c == '-').count();
                if neg_count % 2 == 1 { -n } else { n }
            });

        // mul_op: * or /
        let mul_op = just('*').or(just('/'));

        // Term: unary expressions combined with * and /
        let term = unary.clone().foldl(
            ws().ignore_then(mul_op)
                .then_ignore(ws())
                .then(unary)
                .repeated(),
            |left, (op, right)| {
                if op == '*' {
                    left * right
                } else {
                    left / right
                }
            },
        );

        // add_op: + or -
        let add_op = just('+').or(just('-'));

        // Expression: terms combined with + and -
        term.clone().foldl(
            ws().ignore_then(add_op)
                .then_ignore(ws())
                .then(term)
                .repeated(),
            |left, (op, right)| {
                if op == '+' {
                    left + right
                } else {
                    left - right
                }
            },
        )
    })
}

/// Parse a number (for backward compatibility, now delegates to expr).
fn number<'a>() -> impl Parser<'a, ParserInput<'a>, Decimal, ParserExtra<'a>> + Clone {
    expr()
}

/// Parse a currency code.
/// Supports extended syntax: can start with / or uppercase letter
/// Can contain uppercase letters, digits, ', ., _, -, /
fn currency<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    one_of("/ABCDEFGHIJKLMNOPQRSTUVWXYZ")
        .then(one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789'._-/").repeated())
        .to_slice()
        .map(|s: &str| s.to_string())
}

/// Parse an amount (number + currency).
fn amount<'a>() -> impl Parser<'a, ParserInput<'a>, Amount, ParserExtra<'a>> + Clone {
    number()
        .then_ignore(ws())
        .then(currency())
        .map(|(n, c)| Amount::new(n, c))
}

/// Parse an incomplete amount for postings.
///
/// Supports:
/// - `100.00 USD` - Complete amount
/// - `100.00` - Number only (currency to be inferred)
/// - `USD` - Currency only (number to be interpolated)
fn incomplete_amount<'a>()
-> impl Parser<'a, ParserInput<'a>, IncompleteAmount, ParserExtra<'a>> + Clone {
    // Complete amount: number + currency
    let complete = number()
        .then_ignore(ws())
        .then(currency())
        .map(|(n, c)| IncompleteAmount::Complete(Amount::new(n, c)));

    // Number only: just a number, no currency
    let number_only = number().map(IncompleteAmount::NumberOnly);

    // Currency only: just a currency, no number
    let currency_only = currency().map(|c| IncompleteAmount::CurrencyOnly(c.into()));

    // Try complete first, then number-only, then currency-only
    choice((complete, number_only, currency_only))
}

/// A single cost component: amount, date, string label, or "*" (merge).
#[derive(Debug, Clone)]
enum CostComponent {
    /// Full amount: number + currency
    Amount(Decimal, String),
    /// Number only (currency inferred)
    NumberOnly(Decimal),
    /// Currency only (number to be interpolated)
    CurrencyOnly(String),
    /// Date
    Date(NaiveDate),
    /// String label
    Label(String),
    /// Merge marker
    Merge,
    /// Hash separator for per-unit # total syntax
    Hash,
}

/// Parse a cost component.
fn cost_component<'a>() -> impl Parser<'a, ParserInput<'a>, CostComponent, ParserExtra<'a>> + Clone
{
    choice((
        // Date (must come before number to avoid 2024 matching from 2024-01-15)
        date().map(CostComponent::Date),
        // Amount (number + currency)
        number()
            .then_ignore(ws())
            .then(currency())
            .map(|(n, c)| CostComponent::Amount(n, c)),
        // Number only
        number().map(CostComponent::NumberOnly),
        // Currency only (must come after number to avoid conflicts)
        currency().map(CostComponent::CurrencyOnly),
        // String label
        string_literal().map(CostComponent::Label),
        // Merge marker
        just('*').to(CostComponent::Merge),
        // Hash for per-unit # total syntax
        just('#').to(CostComponent::Hash),
    ))
}

/// Parse a cost specification: {`cost_comp_list`} or {{`cost_comp_list`}}.
fn cost_spec<'a>() -> impl Parser<'a, ParserInput<'a>, CostSpec, ParserExtra<'a>> + Clone {
    // Cost spec allows:
    // - Empty components between commas: {, 100.0 USD, , }
    // - Whitespace-only separation: {100 USD 2024-01-01}
    // - Slash separation: {100 USD / 2024-01-01 / "label"}
    //
    // Approach: parse a sequence of either cost_components or delimiters (comma/slash)
    // then filter to keep only the actual components

    // A cost item: either a real component or a delimiter (to be ignored)
    let delimiter = just(',').or(just('/')).to(None);
    let component_item = cost_component().map(Some);
    let cost_item = component_item.or(delimiter);

    // Parse items separated by whitespace (whitespace is the universal separator)
    let cost_components = cost_item
        .padded()
        .repeated()
        .collect::<Vec<_>>()
        .map(|v| v.into_iter().flatten().collect::<Vec<_>>());

    // Single braces: per-unit cost (or combined with # for total)
    let single_brace = just('{')
        .ignore_then(cost_components.clone())
        .then_ignore(just('}'))
        .map(|components| build_cost_spec(components, false));

    // Double braces: total cost
    let double_brace = just("{{")
        .ignore_then(cost_components)
        .then_ignore(just("}}"))
        .map(|components| build_cost_spec(components, true));

    // Try double brace first to avoid partial match
    double_brace.or(single_brace)
}

/// Build a `CostSpec` from parsed components.
///
/// Handles the `#` syntax for combining per-unit and total costs:
/// - `{150 USD}` - per-unit cost
/// - `{{150 USD}}` - total cost
/// - `{150 # 5 USD}` - per-unit=150, total=5, currency=USD
/// - `{# 5 USD}` - total only
/// - `{150 # USD}` - per-unit=150, currency=USD
fn build_cost_spec(components: Vec<CostComponent>, is_total_brace: bool) -> CostSpec {
    let mut spec = CostSpec::default();

    // Find if there's a hash separator
    let hash_pos = components
        .iter()
        .position(|c| matches!(c, CostComponent::Hash));

    // If hash present, components before # are per-unit, after # are total
    // If no hash, all components go to per-unit (or total if double-brace)
    let (per_unit_comps, total_comps): (Vec<_>, Vec<_>) = if let Some(pos) = hash_pos {
        let (before, after) = components.split_at(pos);
        (before.to_vec(), after[1..].to_vec()) // Skip the hash itself
    } else if is_total_brace {
        (vec![], components)
    } else {
        (components, vec![])
    };

    // Process per-unit components
    for comp in per_unit_comps {
        match comp {
            CostComponent::Amount(num, curr) => {
                spec.number_per = Some(num);
                spec.currency = Some(curr.into());
            }
            CostComponent::NumberOnly(num) => {
                spec.number_per = Some(num);
            }
            CostComponent::CurrencyOnly(curr) => {
                if spec.currency.is_none() {
                    spec.currency = Some(curr.into());
                }
            }
            CostComponent::Date(d) => {
                spec.date = Some(d);
            }
            CostComponent::Label(l) => {
                spec.label = Some(l);
            }
            CostComponent::Merge => {
                spec.merge = true;
            }
            CostComponent::Hash => {}
        }
    }

    // Process total components
    for comp in total_comps {
        match comp {
            CostComponent::Amount(num, curr) => {
                spec.number_total = Some(num);
                spec.currency = Some(curr.into());
            }
            CostComponent::NumberOnly(num) => {
                spec.number_total = Some(num);
            }
            CostComponent::CurrencyOnly(curr) => {
                if spec.currency.is_none() {
                    spec.currency = Some(curr.into());
                }
            }
            CostComponent::Date(d) => {
                if spec.date.is_none() {
                    spec.date = Some(d);
                }
            }
            CostComponent::Label(l) => {
                if spec.label.is_none() {
                    spec.label = Some(l);
                }
            }
            CostComponent::Merge => {
                spec.merge = true;
            }
            CostComponent::Hash => {}
        }
    }

    spec
}

/// Parse a price annotation: @ amount or @@ amount.
///
/// Supports incomplete prices:
/// - `@ 1.2 CAD` - complete unit price
/// - `@@ 100 CAD` - complete total price
/// - `@ 1.2` - number only
/// - `@ CAD` - currency only
/// - `@` - empty (to be interpolated)
fn price_annotation<'a>()
-> impl Parser<'a, ParserInput<'a>, PriceAnnotation, ParserExtra<'a>> + Clone {
    // Parse the optional amount after @ or @@
    let price_amount = choice((
        // Complete amount
        amount().map(|a| Some(IncompleteAmount::Complete(a))),
        // Incomplete amount (number or currency only)
        incomplete_amount().map(Some),
        // Empty (nothing after @)
        empty().to(None),
    ));

    // Try @@ first (total), then @ (unit)
    choice((
        just("@@")
            .ignore_then(ws())
            .ignore_then(price_amount.clone())
            .map(|opt_amount| match opt_amount {
                Some(IncompleteAmount::Complete(a)) => PriceAnnotation::Total(a),
                Some(ia) => PriceAnnotation::TotalIncomplete(ia),
                None => PriceAnnotation::TotalEmpty,
            }),
        just('@')
            .ignore_then(ws())
            .ignore_then(price_amount)
            .map(|opt_amount| match opt_amount {
                Some(IncompleteAmount::Complete(a)) => PriceAnnotation::Unit(a),
                Some(ia) => PriceAnnotation::UnitIncomplete(ia),
                None => PriceAnnotation::UnitEmpty,
            }),
    ))
}

/// Parse an account name.
fn account<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    let account_type = choice((
        just("Assets"),
        just("Liabilities"),
        just("Equity"),
        just("Income"),
        just("Expenses"),
    ));

    let component = one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789")
        .then(one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-").repeated())
        .to_slice();

    account_type
        .then(just(':').then(component).repeated().at_least(1))
        .to_slice()
        .map(|s: &str| s.to_string())
}

/// Parse a flag (* or ! or txn keyword).
fn flag<'a>() -> impl Parser<'a, ParserInput<'a>, char, ParserExtra<'a>> + Clone {
    choice((
        one_of("*!"),
        just("txn").to('*'), // 'txn' is equivalent to '*'
    ))
}

/// Parse a tag (#tag).
fn tag<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    just('#')
        .ignore_then(
            one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_/.")
                .repeated()
                .at_least(1)
                .to_slice(),
        )
        .map(|s: &str| s.to_string())
}

/// Parse a link (^link).
fn link<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    just('^')
        .ignore_then(
            one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_/.")
                .repeated()
                .at_least(1)
                .to_slice(),
        )
        .map(|s: &str| s.to_string())
}

/// Parse a metadata key (lowercase letter followed by alphanumeric, dash, or underscore).
fn metadata_key<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    one_of("abcdefghijklmnopqrstuvwxyz")
        .then(one_of("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_").repeated())
        .to_slice()
        .map(|s: &str| s.to_string())
}

/// Parse a metadata value.
fn metadata_value<'a>() -> impl Parser<'a, ParserInput<'a>, MetaValue, ParserExtra<'a>> + Clone {
    choice((
        // String
        string_literal().map(MetaValue::String),
        // Account (must be before currency since currency is a prefix match)
        account().map(MetaValue::Account),
        // Tag
        tag().map(MetaValue::Tag),
        // Link
        link().map(MetaValue::Link),
        // Date (try before number to avoid partial match)
        date().map(MetaValue::Date),
        // Amount (number + currency) - try before plain number
        amount().map(MetaValue::Amount),
        // Plain number
        number().map(MetaValue::Number),
        // Currency (standalone)
        currency().map(MetaValue::Currency),
    ))
}

/// Parse a metadata line (indented key: value).
/// Value is optional - `key:` without a value produces `MetaValue::None`
fn metadata_line<'a>() -> impl Parser<'a, ParserInput<'a>, (String, MetaValue), ParserExtra<'a>> {
    newline()
        .ignore_then(ws1())
        .ignore_then(metadata_key())
        .then_ignore(just(':'))
        .then_ignore(ws())
        .then(metadata_value().or_not())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .map(|(key, value)| (key, value.unwrap_or(MetaValue::None)))
}

/// Parse a dated directive.
fn dated_directive<'a>() -> impl Parser<'a, ParserInput<'a>, Directive, ParserExtra<'a>> {
    date()
        .then_ignore(ws1())
        .then(choice((
            transaction_body(),
            balance_body(),
            open_body(),
            close_body(),
            commodity_body(),
            pad_body(),
            event_body(),
            query_body(),
            note_body(),
            document_body(),
            price_body(),
            custom_body(),
        )))
        .map(|(d, dir_fn)| dir_fn(d))
}

/// Either a posting, metadata entry, or tag/link continuation in a transaction.
#[derive(Debug, Clone)]
enum PostingOrMeta {
    Posting(Posting),
    Meta(String, MetaValue),
    TagsLinks(Vec<String>, Vec<String>),
}

/// Element that can appear in transaction header: string, tag, or link.
#[derive(Debug, Clone)]
enum TxnHeaderItem {
    String(String),
    Tag(String),
    Link(String),
}

/// Parse a transaction body.
fn transaction_body<'a>()
-> impl Parser<'a, ParserInput<'a>, Box<dyn Fn(NaiveDate) -> Directive + 'a>, ParserExtra<'a>> {
    // Header items: strings, tags, and links can be interleaved in any order
    let header_item = choice((
        string_literal().map(TxnHeaderItem::String),
        tag().map(TxnHeaderItem::Tag),
        link().map(TxnHeaderItem::Link),
    ));

    flag()
        .then_ignore(ws())
        .then(header_item.separated_by(ws()).collect::<Vec<_>>())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .then(posting_or_meta().repeated().collect::<Vec<_>>())
        .map(move |((f, header_items), items)| {
            Box::new(move |date: NaiveDate| {
                // Extract strings (first two are payee/narration), tags, and links
                let mut strings = Vec::new();
                let mut tags = Vec::new();
                let mut links = Vec::new();

                for item in header_items.clone() {
                    match item {
                        TxnHeaderItem::String(s) => strings.push(s),
                        TxnHeaderItem::Tag(t) => tags.push(t),
                        TxnHeaderItem::Link(l) => links.push(l),
                    }
                }

                // Determine payee and narration from strings
                let (payee, narration) = match strings.len() {
                    0 => (None, String::new()),
                    1 => (None, strings[0].clone()),
                    _ => (Some(strings[0].clone()), strings[1].clone()),
                };

                let mut txn = Transaction::new(date, narration).with_flag(f);
                if let Some(p) = payee {
                    txn = txn.with_payee(p);
                }
                for t in tags {
                    txn = txn.with_tag(t);
                }
                for l in links {
                    txn = txn.with_link(l);
                }
                for item in items.clone().into_iter().flatten() {
                    match item {
                        PostingOrMeta::Posting(p) => {
                            txn = txn.with_posting(p);
                        }
                        PostingOrMeta::Meta(k, v) => {
                            txn.meta.insert(k, v);
                        }
                        PostingOrMeta::TagsLinks(t, l) => {
                            for tag in t {
                                txn = txn.with_tag(tag);
                            }
                            for link in l {
                                txn = txn.with_link(link);
                            }
                        }
                    }
                }
                Directive::Transaction(txn)
            }) as Box<dyn Fn(NaiveDate) -> Directive + 'a>
        })
}

/// Parse either a posting, a metadata line, tag/link continuation, or a comment-only line.
fn posting_or_meta<'a>() -> impl Parser<'a, ParserInput<'a>, Option<PostingOrMeta>, ParserExtra<'a>>
{
    // Both start with newline + indent
    // Metadata: lowercase key followed by ':'
    // Posting: flag or account (uppercase first letter)
    // TagsLinks: line with only tags and/or links
    // Comment: just a semicolon line (returns None)
    let meta_entry = newline()
        .ignore_then(ws1())
        .ignore_then(metadata_key())
        .then_ignore(just(':'))
        .then_ignore(ws())
        .then(metadata_value().or_not())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .map(|(k, v)| Some(PostingOrMeta::Meta(k, v.unwrap_or(MetaValue::None))));

    // Tag/link continuation line (only tags and links, no posting)
    let tag_or_link = choice((
        tag().map(|t| (Some(t), None)),
        link().map(|l| (None, Some(l))),
    ));
    let tags_links_line = newline()
        .ignore_then(ws1())
        .ignore_then(
            tag_or_link
                .separated_by(ws())
                .at_least(1)
                .collect::<Vec<_>>(),
        )
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .map(|items| {
            let mut tags = Vec::new();
            let mut links = Vec::new();
            for (t, l) in items {
                if let Some(tag) = t {
                    tags.push(tag);
                }
                if let Some(link) = l {
                    links.push(link);
                }
            }
            Some(PostingOrMeta::TagsLinks(tags, links))
        });

    // Comment-only line between postings
    let comment_only = newline()
        .ignore_then(ws())
        .ignore_then(just(';'))
        .ignore_then(none_of("\n\r").repeated())
        .map(|()| None);

    // Use choice with metadata first (more specific pattern - requires ':')
    // Then tags/links, then posting, then comment
    choice((
        meta_entry,
        tags_links_line,
        posting().map(|p| Some(PostingOrMeta::Posting(p))),
        comment_only,
    ))
}

/// Parse a posting-level metadata line (indented more than the posting).
fn posting_metadata<'a>() -> impl Parser<'a, ParserInput<'a>, (String, MetaValue), ParserExtra<'a>>
{
    // Posting metadata is indented more than postings (typically 4+ spaces)
    newline()
        .ignore_then(just("    ").or(just("\t\t"))) // Extra indentation
        .ignore_then(ws())
        .ignore_then(metadata_key())
        .then_ignore(just(':'))
        .then_ignore(ws())
        .then(metadata_value().or_not())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .map(|(k, v)| (k, v.unwrap_or(MetaValue::None)))
}

/// Parse a posting with optional metadata.
fn posting<'a>() -> impl Parser<'a, ParserInput<'a>, Posting, ParserExtra<'a>> {
    // Amount with optional cost and price
    let amount_with_cost_price = incomplete_amount()
        .then(ws().ignore_then(cost_spec()).or_not())
        .then(ws().ignore_then(price_annotation()).or_not())
        .map(|((units, cost), price)| (Some(units), cost, price));

    // Just cost spec (no units) - starts with {
    let just_cost = cost_spec()
        .then(ws().ignore_then(price_annotation()).or_not())
        .map(|(cost, price)| (None, Some(cost), price));

    // Just price annotation (no units) - starts with @
    let just_price = price_annotation().map(|price| (None, None, Some(price)));

    newline()
        .ignore_then(ws1())
        .ignore_then(flag().then_ignore(ws()).or_not())
        .then(account())
        .then_ignore(ws())
        .then(
            // Try amount first, then just cost, then just price, then nothing
            amount_with_cost_price.or(just_cost).or(just_price).or_not(),
        )
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .then(posting_metadata().repeated().collect::<Vec<_>>())
        .map(|(((flag, acct), amount_cost_price), metadata)| {
            let mut p = if let Some((units, cost, price)) = amount_cost_price {
                let mut posting = if let Some(u) = units {
                    Posting::with_incomplete(&acct, u)
                } else {
                    Posting::auto(&acct)
                };
                posting.cost = cost;
                posting.price = price;
                posting
            } else {
                Posting::auto(&acct)
            };
            if let Some(f) = flag {
                p.flag = Some(f);
            }
            // Add posting metadata
            for (key, value) in metadata {
                p.meta.insert(key, value);
            }
            p
        })
}

/// Parse a balance directive body.
fn balance_body<'a>()
-> impl Parser<'a, ParserInput<'a>, Box<dyn Fn(NaiveDate) -> Directive + 'a>, ParserExtra<'a>> {
    // Amount with optional tolerance: NUMBER [~ TOLERANCE] CURRENCY [{COST}]
    // e.g., "200 USD", "200 ~ 0.002 USD", or "10 MSFT {45.30 USD}"
    let tolerance = ws()
        .ignore_then(just('~'))
        .ignore_then(ws())
        .ignore_then(number());

    let amount_with_tolerance_and_cost = number()
        .then(tolerance.or_not())
        .then_ignore(ws())
        .then(currency())
        .then(ws().ignore_then(cost_spec()).or_not())
        .map(|(((num, tol), curr), _cost)| (Amount::new(num, &curr), tol));

    just("balance")
        .ignore_then(ws1())
        .ignore_then(account())
        .then_ignore(ws1())
        .then(amount_with_tolerance_and_cost)
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .then(metadata_line().repeated().collect::<Vec<_>>())
        .map(move |((acct, (amt, tol)), meta_items)| {
            let mut meta = Metadata::default();
            for (k, v) in meta_items {
                meta.insert(k, v);
            }
            Box::new(move |date: NaiveDate| {
                Directive::Balance(Balance {
                    date,
                    account: acct.clone().into(),
                    amount: amt.clone(),
                    tolerance: tol,
                    meta: meta.clone(),
                })
            }) as Box<dyn Fn(NaiveDate) -> Directive + 'a>
        })
}

/// Parse an open directive body.
fn open_body<'a>()
-> impl Parser<'a, ParserInput<'a>, Box<dyn Fn(NaiveDate) -> Directive + 'a>, ParserExtra<'a>> {
    just("open")
        .ignore_then(ws1())
        .ignore_then(account())
        .then_ignore(ws())
        .then(
            currency()
                .separated_by(just(',').then(ws()))
                .collect::<Vec<_>>(),
        )
        .then_ignore(ws())
        .then(string_literal().or_not())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .then(metadata_line().repeated().collect::<Vec<_>>())
        .map(move |(((acct, currencies), booking), meta_items)| {
            let mut meta = Metadata::default();
            for (k, v) in meta_items {
                meta.insert(k, v);
            }
            Box::new(move |date: NaiveDate| {
                Directive::Open(Open {
                    date,
                    account: acct.clone().into(),
                    currencies: currencies.iter().map(|c| c.clone().into()).collect(),
                    booking: booking.clone(),
                    meta: meta.clone(),
                })
            }) as Box<dyn Fn(NaiveDate) -> Directive + 'a>
        })
}

/// Parse a close directive body.
fn close_body<'a>()
-> impl Parser<'a, ParserInput<'a>, Box<dyn Fn(NaiveDate) -> Directive + 'a>, ParserExtra<'a>> {
    just("close")
        .ignore_then(ws1())
        .ignore_then(account())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .then(metadata_line().repeated().collect::<Vec<_>>())
        .map(move |(acct, meta_items)| {
            let mut meta = Metadata::default();
            for (k, v) in meta_items {
                meta.insert(k, v);
            }
            Box::new(move |date: NaiveDate| {
                Directive::Close(Close {
                    date,
                    account: acct.clone().into(),
                    meta: meta.clone(),
                })
            }) as Box<dyn Fn(NaiveDate) -> Directive + 'a>
        })
}

/// Parse a commodity directive body.
fn commodity_body<'a>()
-> impl Parser<'a, ParserInput<'a>, Box<dyn Fn(NaiveDate) -> Directive + 'a>, ParserExtra<'a>> {
    just("commodity")
        .ignore_then(ws1())
        .ignore_then(currency())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .then(metadata_line().repeated().collect::<Vec<_>>())
        .map(move |(curr, metadata)| {
            Box::new(move |date: NaiveDate| {
                let mut meta = Metadata::default();
                for (k, v) in metadata.clone() {
                    meta.insert(k, v);
                }
                Directive::Commodity(Commodity {
                    date,
                    currency: curr.clone().into(),
                    meta,
                })
            }) as Box<dyn Fn(NaiveDate) -> Directive + 'a>
        })
}

/// Parse a pad directive body.
fn pad_body<'a>()
-> impl Parser<'a, ParserInput<'a>, Box<dyn Fn(NaiveDate) -> Directive + 'a>, ParserExtra<'a>> {
    just("pad")
        .ignore_then(ws1())
        .ignore_then(account())
        .then_ignore(ws1())
        .then(account())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .then(metadata_line().repeated().collect::<Vec<_>>())
        .map(move |((acct, source), meta_items)| {
            let mut meta = Metadata::default();
            for (k, v) in meta_items {
                meta.insert(k, v);
            }
            Box::new(move |date: NaiveDate| {
                Directive::Pad(Pad {
                    date,
                    account: acct.clone().into(),
                    source_account: source.clone().into(),
                    meta: meta.clone(),
                })
            }) as Box<dyn Fn(NaiveDate) -> Directive + 'a>
        })
}

/// Parse an event directive body.
fn event_body<'a>()
-> impl Parser<'a, ParserInput<'a>, Box<dyn Fn(NaiveDate) -> Directive + 'a>, ParserExtra<'a>> {
    just("event")
        .ignore_then(ws1())
        .ignore_then(string_literal())
        .then_ignore(ws1())
        .then(string_literal())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .then(metadata_line().repeated().collect::<Vec<_>>())
        .map(move |((name, value), meta_items)| {
            let mut meta = Metadata::default();
            for (k, v) in meta_items {
                meta.insert(k, v);
            }
            Box::new(move |date: NaiveDate| {
                Directive::Event(Event {
                    date,
                    event_type: name.clone(),
                    value: value.clone(),
                    meta: meta.clone(),
                })
            }) as Box<dyn Fn(NaiveDate) -> Directive + 'a>
        })
}

/// Parse a query directive body.
fn query_body<'a>()
-> impl Parser<'a, ParserInput<'a>, Box<dyn Fn(NaiveDate) -> Directive + 'a>, ParserExtra<'a>> {
    just("query")
        .ignore_then(ws1())
        .ignore_then(string_literal())
        .then_ignore(ws1())
        .then(string_literal())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .map(move |(name, query_string)| {
            Box::new(move |date: NaiveDate| {
                Directive::Query(Query {
                    date,
                    name: name.clone(),
                    query: query_string.clone(),
                    meta: Metadata::default(),
                })
            }) as Box<dyn Fn(NaiveDate) -> Directive + 'a>
        })
}

/// Parse a note directive body.
fn note_body<'a>()
-> impl Parser<'a, ParserInput<'a>, Box<dyn Fn(NaiveDate) -> Directive + 'a>, ParserExtra<'a>> {
    just("note")
        .ignore_then(ws1())
        .ignore_then(account())
        .then_ignore(ws1())
        .then(string_literal())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .then(metadata_line().repeated().collect::<Vec<_>>())
        .map(move |((acct, comment), meta_items)| {
            let mut meta = Metadata::default();
            for (k, v) in meta_items {
                meta.insert(k, v);
            }
            Box::new(move |date: NaiveDate| {
                Directive::Note(Note {
                    date,
                    account: acct.clone().into(),
                    comment: comment.clone(),
                    meta: meta.clone(),
                })
            }) as Box<dyn Fn(NaiveDate) -> Directive + 'a>
        })
}

/// Parse a document directive body.
fn document_body<'a>()
-> impl Parser<'a, ParserInput<'a>, Box<dyn Fn(NaiveDate) -> Directive + 'a>, ParserExtra<'a>> {
    // Tags and links after the path
    let tag_or_link = choice((
        tag().map(|t| (Some(t), None)),
        link().map(|l| (None, Some(l))),
    ));

    just("document")
        .ignore_then(ws1())
        .ignore_then(account())
        .then_ignore(ws1())
        .then(string_literal())
        .then_ignore(ws())
        .then(tag_or_link.separated_by(ws()).collect::<Vec<_>>())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .then(metadata_line().repeated().collect::<Vec<_>>())
        .map(move |(((acct, filename), tags_links), meta_items)| {
            let (tags, links): (Vec<_>, Vec<_>) = tags_links
                .into_iter()
                .map(|(t, l)| {
                    (
                        t.into_iter().collect::<Vec<_>>(),
                        l.into_iter().collect::<Vec<_>>(),
                    )
                })
                .fold((vec![], vec![]), |(mut ts, mut ls), (t, l)| {
                    ts.extend(t);
                    ls.extend(l);
                    (ts, ls)
                });
            let mut meta = Metadata::default();
            for (k, v) in meta_items {
                meta.insert(k, v);
            }

            Box::new(move |date: NaiveDate| {
                Directive::Document(Document {
                    date,
                    account: acct.clone().into(),
                    path: filename.clone(),
                    tags: tags.clone(),
                    links: links.clone(),
                    meta: meta.clone(),
                })
            }) as Box<dyn Fn(NaiveDate) -> Directive + 'a>
        })
}

/// Parse a price directive body.
fn price_body<'a>()
-> impl Parser<'a, ParserInput<'a>, Box<dyn Fn(NaiveDate) -> Directive + 'a>, ParserExtra<'a>> {
    just("price")
        .ignore_then(ws1())
        .ignore_then(currency())
        .then_ignore(ws1())
        .then(amount())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .then(metadata_line().repeated().collect::<Vec<_>>())
        .map(move |((curr, amt), meta_items)| {
            let mut meta = Metadata::default();
            for (k, v) in meta_items {
                meta.insert(k, v);
            }
            Box::new(move |date: NaiveDate| {
                Directive::Price(Price {
                    date,
                    currency: curr.clone().into(),
                    amount: amt.clone(),
                    meta: meta.clone(),
                })
            }) as Box<dyn Fn(NaiveDate) -> Directive + 'a>
        })
}

/// Parse a custom directive body.
fn custom_body<'a>()
-> impl Parser<'a, ParserInput<'a>, Box<dyn Fn(NaiveDate) -> Directive + 'a>, ParserExtra<'a>> {
    // Custom values can be strings, accounts, amounts, dates, booleans, etc.
    let custom_value = metadata_value();

    just("custom")
        .ignore_then(ws1())
        .ignore_then(string_literal())
        .then_ignore(ws())
        .then(custom_value.separated_by(ws1()).collect::<Vec<_>>())
        .then_ignore(ws())
        .then_ignore(comment_line().or_not())
        .map(move |(name, values)| {
            Box::new(move |date: NaiveDate| {
                Directive::Custom(Custom {
                    date,
                    custom_type: name.clone(),
                    values: values.clone(),
                    meta: Metadata::default(),
                })
            }) as Box<dyn Fn(NaiveDate) -> Directive + 'a>
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    #[test]
    fn test_parse_empty() {
        let result = parse("");
        assert!(result.errors.is_empty());
        assert!(result.directives.is_empty());
    }

    #[test]
    fn test_parse_comment() {
        let result = parse("; This is a comment");
        assert!(result.errors.is_empty());
        assert!(result.directives.is_empty());
    }

    #[test]
    fn test_parse_option() {
        let result = parse(r#"option "title" "My Ledger""#);
        assert!(result.errors.is_empty());
        assert_eq!(result.options.len(), 1);
        assert_eq!(result.options[0].0, "title");
        assert_eq!(result.options[0].1, "My Ledger");
    }

    #[test]
    fn test_parse_include() {
        let result = parse(r#"include "other.beancount""#);
        assert!(result.errors.is_empty());
        assert_eq!(result.includes.len(), 1);
        assert_eq!(result.includes[0].0, "other.beancount");
    }

    #[test]
    fn test_parse_open() {
        let result = parse("2024-01-01 open Assets:Bank:Checking USD");
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
    }

    #[test]
    fn test_parse_transaction() {
        let source = r#"2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food:Coffee  5.00 USD
  Assets:Cash"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);
    }

    #[test]
    fn test_parse_posting_with_cost() {
        let source = r#"2024-01-15 * "Buy stock"
  Assets:Brokerage  10 AAPL {150.00 USD}
  Assets:Cash  -1500.00 USD"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            assert_eq!(txn.postings.len(), 2);
            let cost = txn.postings[0].cost.as_ref().expect("should have cost");
            assert_eq!(cost.number_per, Some(dec!(150.00)));
            assert_eq!(cost.currency, Some("USD".into()));
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_posting_with_cost_date_label() {
        let source = r#"2024-01-15 * "Buy stock"
  Assets:Brokerage  10 AAPL {150.00 USD, 2024-01-15, "lot1"}
  Assets:Cash"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            let cost = txn.postings[0].cost.as_ref().expect("should have cost");
            assert_eq!(cost.number_per, Some(dec!(150.00)));
            assert_eq!(cost.currency, Some("USD".into()));
            assert_eq!(
                cost.date,
                Some(NaiveDate::from_ymd_opt(2024, 1, 15).unwrap())
            );
            assert_eq!(cost.label, Some("lot1".to_string()));
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_posting_with_total_cost() {
        let source = r#"2024-01-15 * "Buy stock"
  Assets:Brokerage  10 AAPL {{1500.00 USD}}
  Assets:Cash"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            let cost = txn.postings[0].cost.as_ref().expect("should have cost");
            assert_eq!(cost.number_total, Some(dec!(1500.00)));
            assert_eq!(cost.currency, Some("USD".into()));
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_posting_with_price_per_unit() {
        let source = r#"2024-01-15 * "Currency exchange"
  Assets:EUR  100 EUR @ 1.10 USD
  Assets:USD"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            let price = txn.postings[0].price.as_ref().expect("should have price");
            if let PriceAnnotation::Unit(amt) = price {
                assert_eq!(amt.number, dec!(1.10));
                assert_eq!(amt.currency, "USD");
            } else {
                panic!("expected unit price");
            }
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_posting_with_total_price() {
        let source = r#"2024-01-15 * "Currency exchange"
  Assets:EUR  100 EUR @@ 110.00 USD
  Assets:USD"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            let price = txn.postings[0].price.as_ref().expect("should have price");
            if let PriceAnnotation::Total(amt) = price {
                assert_eq!(amt.number, dec!(110.00));
                assert_eq!(amt.currency, "USD");
            } else {
                panic!("expected total price");
            }
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_transaction_with_metadata() {
        let source = r#"2024-01-15 * "Coffee Shop" "Morning coffee"
  category: "food"
  source: "bank-statement"
  Expenses:Food:Coffee  5.00 USD
  Assets:Cash"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            // Check metadata was parsed
            assert!(txn.meta.contains_key("category"), "missing category meta");
            assert!(txn.meta.contains_key("source"), "missing source meta");

            // Verify values
            if let Some(MetaValue::String(s)) = txn.meta.get("category") {
                assert_eq!(s, "food");
            } else {
                panic!("category should be a string");
            }

            // Should still have 2 postings
            assert_eq!(txn.postings.len(), 2);
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_metadata_with_various_types() {
        let source = r#"2024-01-15 * "Test"
  string-value: "hello"
  number-value: 42.5
  date-value: 2024-01-20
  tag-value: #mytag
  Expenses:Test  100 USD
  Assets:Cash"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            // Check string
            if let Some(MetaValue::String(s)) = txn.meta.get("string-value") {
                assert_eq!(s, "hello");
            } else {
                panic!("string-value should be a string");
            }

            // Check number
            if let Some(MetaValue::Number(n)) = txn.meta.get("number-value") {
                assert_eq!(*n, dec!(42.5));
            } else {
                panic!(
                    "number-value should be a number, got {:?}",
                    txn.meta.get("number-value")
                );
            }

            // Check date
            if let Some(MetaValue::Date(d)) = txn.meta.get("date-value") {
                assert_eq!(*d, NaiveDate::from_ymd_opt(2024, 1, 20).unwrap());
            } else {
                panic!("date-value should be a date");
            }

            // Check tag
            if let Some(MetaValue::Tag(t)) = txn.meta.get("tag-value") {
                assert_eq!(t, "mytag");
            } else {
                panic!("tag-value should be a tag");
            }
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_comma_separated_numbers() {
        let source = r#"2024-01-15 * "Large purchase"
  Expenses:Large  1,234,567.89 USD
  Assets:Cash  -1,234,567.89 USD"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            let units = txn.postings[0].units.as_ref().expect("should have units");
            assert_eq!(units.number(), Some(dec!(1234567.89)));
            assert_eq!(units.currency(), Some("USD"));
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_posting_with_metadata() {
        let source = r#"2024-01-15 * "Coffee" "With receipt"
  Expenses:Food:Coffee  5.00 USD
    document: "receipt.pdf"
    vendor: "Starbucks"
  Assets:Cash"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            assert_eq!(txn.postings.len(), 2);

            // Check that the first posting has metadata
            let posting = &txn.postings[0];
            assert!(
                posting.meta.contains_key("document"),
                "missing document meta"
            );
            assert!(posting.meta.contains_key("vendor"), "missing vendor meta");

            if let Some(MetaValue::String(s)) = posting.meta.get("document") {
                assert_eq!(s, "receipt.pdf");
            } else {
                panic!("document should be a string");
            }

            if let Some(MetaValue::String(s)) = posting.meta.get("vendor") {
                assert_eq!(s, "Starbucks");
            } else {
                panic!("vendor should be a string");
            }

            // Second posting should have no metadata
            assert!(txn.postings[1].meta.is_empty());
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_multiline_string() {
        let source = r#"2024-01-15 * "Payee" """This is a
multi-line
narration"""
  Expenses:Test  100 USD
  Assets:Cash"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            assert!(txn.narration.contains("multi-line"));
            assert!(txn.narration.contains('\n'));
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_pushtag_poptag() {
        let source = r#"pushtag #trip

2024-01-15 * "Taxi" "Airport transfer"
  Expenses:Travel  50 USD
  Assets:Cash

2024-01-16 * "Hotel" "Night stay"
  Expenses:Lodging  150 USD
  Assets:Cash

poptag #trip

2024-01-17 * "Coffee" "Morning coffee"
  Expenses:Food  5 USD
  Assets:Cash"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 3);

        // First two transactions should have the #trip tag
        if let Directive::Transaction(txn) = &result.directives[0].value {
            assert!(
                txn.tags.contains(&"trip".to_string()),
                "first txn should have #trip tag"
            );
        } else {
            panic!("expected transaction");
        }

        if let Directive::Transaction(txn) = &result.directives[1].value {
            assert!(
                txn.tags.contains(&"trip".to_string()),
                "second txn should have #trip tag"
            );
        } else {
            panic!("expected transaction");
        }

        // Third transaction should NOT have the #trip tag
        if let Directive::Transaction(txn) = &result.directives[2].value {
            assert!(
                !txn.tags.contains(&"trip".to_string()),
                "third txn should NOT have #trip tag"
            );
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_nested_pushtag() {
        let source = r#"pushtag #project
pushtag #urgent

2024-01-15 * "Task" "Urgent project task"
  Expenses:Work  100 USD
  Assets:Cash

poptag #urgent

2024-01-16 * "Task" "Normal project task"
  Expenses:Work  50 USD
  Assets:Cash

poptag #project"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        // First transaction should have both tags
        if let Directive::Transaction(txn) = &result.directives[0].value {
            assert!(txn.tags.contains(&"project".to_string()));
            assert!(txn.tags.contains(&"urgent".to_string()));
        } else {
            panic!("expected transaction");
        }

        // Second transaction should only have #project
        if let Directive::Transaction(txn) = &result.directives[1].value {
            assert!(txn.tags.contains(&"project".to_string()));
            assert!(!txn.tags.contains(&"urgent".to_string()));
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_pushtag_with_existing_tags() {
        let source = r#"pushtag #auto

2024-01-15 * "Test" "Transaction with own tags" #manual
  Expenses:Test  100 USD
  Assets:Cash"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            // Should have both the pushed tag and the explicit tag
            assert!(txn.tags.contains(&"auto".to_string()));
            assert!(txn.tags.contains(&"manual".to_string()));
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_leading_decimal() {
        // Test numbers with leading decimal point (no integer part)
        let source = r#"2024-01-15 * "Leading decimal"
  Assets:Cash  .50 USD
  Expenses:Small  -.50 USD"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            let units = txn.postings[0].units.as_ref().expect("should have units");
            assert_eq!(units.number(), Some(dec!(0.50)));

            let units2 = txn.postings[1].units.as_ref().expect("should have units");
            assert_eq!(units2.number(), Some(dec!(-0.50)));
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_open_with_booking_method() {
        let source = "2024-01-01 open Assets:Stock:FIFO \"FIFO\"";
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);

        if let Directive::Open(open) = &result.directives[0].value {
            assert_eq!(open.account, "Assets:Stock:FIFO");
            assert_eq!(open.booking, Some("FIFO".to_string()));
        } else {
            panic!("expected open directive");
        }
    }

    #[test]
    fn test_parse_commodity_with_metadata() {
        let source = r#"2024-01-01 commodity CAD
  name: "Canadian Dollar"
  asset-class: "cash""#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        assert_eq!(result.directives.len(), 1);

        if let Directive::Commodity(comm) = &result.directives[0].value {
            assert_eq!(comm.currency, "CAD");
            assert!(comm.meta.contains_key("name"));
            assert!(comm.meta.contains_key("asset-class"));
        } else {
            panic!("expected commodity directive");
        }
    }

    #[test]
    fn test_parse_arithmetic_addition() {
        let source = r#"2024-01-15 * "Test"
  Expenses:Food  10 + 5 USD
  Assets:Cash  -15 USD"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            let units = txn.postings[0].units.as_ref().expect("should have units");
            assert_eq!(units.number(), Some(dec!(15)));
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_arithmetic_multiplication() {
        let source = r#"2024-01-15 * "Test"
  Expenses:Food  10 * 5 USD
  Assets:Cash  -50 USD"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            let units = txn.postings[0].units.as_ref().expect("should have units");
            assert_eq!(units.number(), Some(dec!(50)));
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_arithmetic_complex() {
        let source = r#"2024-01-15 * "Test"
  Expenses:Food  (10 + 5) * 2 USD
  Assets:Cash  -30 USD"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            let units = txn.postings[0].units.as_ref().expect("should have units");
            assert_eq!(units.number(), Some(dec!(30)));
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_arithmetic_division() {
        let source = r#"2024-01-15 * "Test"
  Expenses:Food  100 / 4 USD
  Assets:Cash  -25 USD"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            let units = txn.postings[0].units.as_ref().expect("should have units");
            assert_eq!(units.number(), Some(dec!(25)));
        } else {
            panic!("expected transaction");
        }
    }

    #[test]
    fn test_parse_arithmetic_precedence() {
        // Test that * has higher precedence than +
        let source = r#"2024-01-15 * "Test"
  Expenses:Food  10 + 5 * 2 USD
  Assets:Cash  -20 USD"#;
        let result = parse(source);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);

        if let Directive::Transaction(txn) = &result.directives[0].value {
            let units = txn.postings[0].units.as_ref().expect("should have units");
            // 10 + (5 * 2) = 10 + 10 = 20
            assert_eq!(units.number(), Some(dec!(20)));
        } else {
            panic!("expected transaction");
        }
    }
}
