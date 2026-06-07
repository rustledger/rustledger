//! CST -> `ParseResult` converter (phase 3.2-3.4 of #1262).
//!
//! [`parse_via_cst`] is a parallel implementation of the public
//! [`crate::parse`] entry point that delegates to the CST
//! ([`crate::parse_structured`]) and rebuilds the existing AST-shaped
//! [`ParseResult`] by walking the typed-AST surface from
//! [`crate::cst::ast`]. The current default code path remains the
//! hand-rolled state-machine parser in `crate::parser`; this
//! function is gated behind its own public export so the corpus
//! baseline differential test can compare both paths file-by-file.
//!
//! ## Migration scaffolding
//!
//! Phase 3.2-3.4 builds out converters for each directive type
//! incrementally. Coverage is tracked by the differential test:
//! each converted directive type drops a corresponding file class
//! from the test's allow-list. Once every directive type is
//! covered and the corpus passes byte-identically, a follow-up PR
//! flips [`crate::parse`] to call this function and a later phase
//! deletes `crate::parser`.
//!
//! ## Coverage status
//!
//! Implemented directive converters:
//! - Open, Close, Commodity (single-line, simple shape)
//! - Note, Document, Event, Query, Price (single-line)
//! - Balance (single-line + amount + optional tolerance)
//! - Pad (single-line, two accounts)
//!
//! Pending directive converters:
//! - Pushtag, Poptag, Pushmeta, Popmeta (state-only side effects)
//! - Option, Include, Plugin (`ParseResult` fields, not directives)
//! - Custom (heterogeneous value list)
//! - Transaction (header + postings + metadata, most complex)
//!
//! Pending lossless features (deferred):
//! - Document tags + links (need raw-token walk; field on
//!   `Document` struct currently filled empty)
//! - `currency_occurrences` field on `ParseResult` (downstream
//!   LSP rename/references depends on this — filled empty until
//!   Transaction lands)
//! - Standalone `comments` field

use rust_decimal::Decimal;
use rustledger_core::{
    Account, Amount, Currency, Directive, Link, MetaValue, Metadata, NaiveDate, Span, Spanned, Tag,
    naive_date,
};

use crate::ParseResult;
use crate::cst::ast::{
    self, AstNode, AstToken, BalanceDirective, CloseDirective, CommodityDirective,
    DocumentDirective, EventDirective, MetaEntry, NoteDirective, OpenDirective, PadDirective,
    PriceDirective, QueryDirective, SourceFile,
};

/// Parse Beancount source via the CST and produce the legacy
/// [`ParseResult`] shape. Parallel implementation of
/// [`crate::parse`]; not yet wired as the default code path.
///
/// See the module-level rustdoc for migration status.
#[must_use]
pub fn parse_via_cst(source: &str) -> ParseResult {
    // BOM detection mirrors the legacy parser's behavior: strip a
    // leading 3-byte BOM from the source before tokenizing and
    // record its presence in the result. Spans index the original
    // source frame INCLUDING the BOM offset.
    let (stripped, has_leading_bom) = crate::bom::strip_leading(source);
    let bom_offset: u32 = if has_leading_bom { 3 } else { 0 };

    let source_file = SourceFile::parse(stripped);

    let mut directives: Vec<Spanned<Directive>> = Vec::new();
    let options: Vec<(String, String, Span)> = Vec::new();
    let includes: Vec<(String, Span)> = Vec::new();
    let plugins: Vec<(String, Option<String>, Span)> = Vec::new();
    let comments: Vec<Spanned<String>> = Vec::new();
    let errors = Vec::new();
    let warnings = Vec::new();
    let currency_occurrences = Vec::new();

    for directive in source_file.directives() {
        match directive {
            ast::Directive::Open(node) => {
                if let Some(spanned) = convert_open(&node, bom_offset) {
                    directives.push(spanned);
                }
            }
            ast::Directive::Close(node) => {
                if let Some(spanned) = convert_close(&node, bom_offset) {
                    directives.push(spanned);
                }
            }
            ast::Directive::Commodity(node) => {
                if let Some(spanned) = convert_commodity(&node, bom_offset) {
                    directives.push(spanned);
                }
            }
            ast::Directive::Note(node) => {
                if let Some(spanned) = convert_note(&node, bom_offset) {
                    directives.push(spanned);
                }
            }
            ast::Directive::Document(node) => {
                if let Some(spanned) = convert_document(&node, bom_offset) {
                    directives.push(spanned);
                }
            }
            ast::Directive::Event(node) => {
                if let Some(spanned) = convert_event(&node, bom_offset) {
                    directives.push(spanned);
                }
            }
            ast::Directive::Query(node) => {
                if let Some(spanned) = convert_query(&node, bom_offset) {
                    directives.push(spanned);
                }
            }
            ast::Directive::Price(node) => {
                if let Some(spanned) = convert_price(&node, bom_offset) {
                    directives.push(spanned);
                }
            }
            ast::Directive::Balance(node) => {
                if let Some(spanned) = convert_balance(&node, bom_offset) {
                    directives.push(spanned);
                }
            }
            ast::Directive::Pad(node) => {
                if let Some(spanned) = convert_pad(&node, bom_offset) {
                    directives.push(spanned);
                }
            }
            // Remaining directive types fall through unconverted —
            // they're added in subsequent commits. The differential
            // test's allow-list pins which file classes still
            // legitimately produce an empty result.
            _ => {}
        }
    }

    ParseResult {
        directives,
        options,
        includes,
        plugins,
        comments,
        errors,
        warnings,
        currency_occurrences,
        has_leading_bom,
    }
}

// ---- Directive converters --------------------------------------

fn convert_open(node: &OpenDirective, bom_offset: u32) -> Option<Spanned<Directive>> {
    let date = parse_date_token(node.date()?.text())?;
    let account = Account::new(node.account()?.text());
    let currencies: Vec<Currency> = node.currencies().map(|c| Currency::new(c.text())).collect();
    let booking = node
        .booking_method()
        .and_then(|s| s.text_unquoted().map(String::from));
    let meta = convert_meta_entries(node.syntax());

    let open = rustledger_core::directive::Open {
        date,
        account,
        currencies,
        booking,
        meta,
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Open(open), span))
}

fn convert_close(node: &CloseDirective, bom_offset: u32) -> Option<Spanned<Directive>> {
    let date = parse_date_token(node.date()?.text())?;
    let account = Account::new(node.account()?.text());
    let meta = convert_meta_entries(node.syntax());

    let close = rustledger_core::directive::Close {
        date,
        account,
        meta,
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Close(close), span))
}

fn convert_commodity(node: &CommodityDirective, bom_offset: u32) -> Option<Spanned<Directive>> {
    let date = parse_date_token(node.date()?.text())?;
    let currency = Currency::new(node.currency()?.text());
    let meta = convert_meta_entries(node.syntax());

    let commodity = rustledger_core::directive::Commodity {
        date,
        currency,
        meta,
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Commodity(commodity), span))
}

fn convert_note(node: &NoteDirective, bom_offset: u32) -> Option<Spanned<Directive>> {
    let date = parse_date_token(node.date()?.text())?;
    let account = Account::new(node.account()?.text());
    let comment = node.text()?.text_unquoted()?.to_string();
    let meta = convert_meta_entries(node.syntax());

    let note = rustledger_core::directive::Note {
        date,
        account,
        comment,
        meta,
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Note(note), span))
}

fn convert_document(node: &DocumentDirective, bom_offset: u32) -> Option<Spanned<Directive>> {
    let date = parse_date_token(node.date()?.text())?;
    let account = Account::new(node.account()?.text());
    let path = node.path()?.text_unquoted()?.to_string();
    // TODO: extract tags/links from raw header tokens (the
    // typed-AST surface doesn't yet expose accessors for these
    // on DocumentDirective). Currently filled empty — matches
    // the documents-without-trailing-tags-or-links case but
    // drops information for documents that have them.
    let tags = Vec::new();
    let links = Vec::new();
    let meta = convert_meta_entries(node.syntax());

    let document = rustledger_core::directive::Document {
        date,
        account,
        path,
        tags,
        links,
        meta,
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Document(document), span))
}

fn convert_event(node: &EventDirective, bom_offset: u32) -> Option<Spanned<Directive>> {
    let date = parse_date_token(node.date()?.text())?;
    let event_type = node.event_type()?.text_unquoted()?.to_string();
    let value = node.value()?.text_unquoted()?.to_string();
    let meta = convert_meta_entries(node.syntax());

    let event = rustledger_core::directive::Event {
        date,
        event_type,
        value,
        meta,
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Event(event), span))
}

fn convert_query(node: &QueryDirective, bom_offset: u32) -> Option<Spanned<Directive>> {
    let date = parse_date_token(node.date()?.text())?;
    let name = node.name()?.text_unquoted()?.to_string();
    let query = node.query()?.text_unquoted()?.to_string();
    let meta = convert_meta_entries(node.syntax());

    let q = rustledger_core::directive::Query {
        date,
        name,
        query,
        meta,
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Query(q), span))
}

fn convert_price(node: &PriceDirective, bom_offset: u32) -> Option<Spanned<Directive>> {
    let date = parse_date_token(node.date()?.text())?;
    let base_currency = Currency::new(node.base_currency()?.text());
    let number = parse_decimal_token(node.number()?.text())?;
    let quote_currency = Currency::new(node.quote_currency()?.text());
    let amount = Amount::new(number, quote_currency);
    let meta = convert_meta_entries(node.syntax());

    let price = rustledger_core::directive::Price {
        date,
        currency: base_currency,
        amount,
        meta,
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Price(price), span))
}

fn convert_balance(node: &BalanceDirective, bom_offset: u32) -> Option<Spanned<Directive>> {
    let date = parse_date_token(node.date()?.text())?;
    let account = Account::new(node.account()?.text());
    let number = parse_decimal_token(node.number()?.text())?;
    let currency = Currency::new(node.currency()?.text());
    let amount = Amount::new(number, currency);
    let tolerance = extract_balance_tolerance(node.syntax());
    let meta = convert_meta_entries(node.syntax());

    let balance = rustledger_core::directive::Balance {
        date,
        account,
        amount,
        tolerance,
        meta,
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Balance(balance), span))
}

/// Balance directives may include an explicit tolerance via a
/// `~` (TILDE) token followed by a NUMBER. The typed-AST surface
/// surfaces NUMBER via `number()` (which returns the FIRST one,
/// the asserted balance); the tolerance NUMBER comes second.
/// Walk raw tokens until TILDE, then collect the next NUMBER.
fn extract_balance_tolerance(node: &crate::SyntaxNode) -> Option<Decimal> {
    let mut past_tilde = false;
    for el in node.children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        if past_tilde && t.kind() == crate::SyntaxKind::NUMBER {
            return parse_decimal_token(t.text());
        }
        if t.kind() == crate::SyntaxKind::TILDE {
            past_tilde = true;
        }
    }
    None
}

fn convert_pad(node: &PadDirective, bom_offset: u32) -> Option<Spanned<Directive>> {
    let date = parse_date_token(node.date()?.text())?;
    let account = Account::new(node.target_account()?.text());
    let source_account = Account::new(node.source_account()?.text());
    let meta = convert_meta_entries(node.syntax());

    let pad = rustledger_core::directive::Pad {
        date,
        account,
        source_account,
        meta,
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Pad(pad), span))
}

// ---- Metadata extraction ---------------------------------------

/// Extract the [`Metadata`] map from the directive node's
/// `META_ENTRY` sub-line children. Matches the legacy parser's
/// behavior: each entry's key (with trailing `:` stripped) maps
/// to a typed [`MetaValue`] derived from the value tokens.
fn convert_meta_entries(node: &crate::SyntaxNode) -> Metadata {
    let mut meta = Metadata::default();
    for entry in node.children().filter_map(MetaEntry::cast) {
        let Some(key_token) = entry.key() else {
            continue;
        };
        let key = key_token.text_without_colon().to_string();
        let value = meta_value_from_entry(&entry);
        meta.insert(key, value);
    }
    meta
}

/// Discriminate the value tokens under a `META_ENTRY` into a
/// typed [`MetaValue`]. Matches the legacy parser's preference
/// order: string > number > date > account > currency > tag >
/// link > bool > none.
fn meta_value_from_entry(entry: &MetaEntry) -> MetaValue {
    if let Some(s) = entry.value_string()
        && let Some(text) = s.text_unquoted()
    {
        return MetaValue::String(text.to_string());
    }
    if let Some(n) = entry.value_number()
        && let Some(decimal) = parse_decimal_token(n.text())
    {
        return MetaValue::Number(decimal);
    }
    if let Some(d) = entry.value_date()
        && let Some(date) = parse_date_token(d.text())
    {
        return MetaValue::Date(date);
    }
    if let Some(a) = entry.value_account() {
        return MetaValue::Account(Account::new(a.text()));
    }
    if let Some(c) = entry.value_currency() {
        return MetaValue::Currency(Currency::new(c.text()));
    }
    if let Some(b) = entry.value_bool() {
        return MetaValue::Bool(b);
    }
    // Tags and Links inside meta entries: walk raw tokens. The
    // typed-AST surface doesn't (yet) expose dedicated accessors,
    // so we scan direct token children.
    for tok in entry.syntax().children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = tok else {
            continue;
        };
        match t.kind() {
            crate::SyntaxKind::TAG => {
                let stripped = t.text().trim_start_matches('#');
                return MetaValue::Tag(Tag::new(stripped));
            }
            crate::SyntaxKind::LINK => {
                let stripped = t.text().trim_start_matches('^');
                return MetaValue::Link(Link::new(stripped));
            }
            _ => {}
        }
    }
    MetaValue::None
}

// ---- Token parsing helpers -------------------------------------

/// Parse a canonical `YYYY-MM-DD` date token. The CST lexer
/// produces normalized date tokens, so the slow-path
/// (slash-separator, single-digit month) doesn't apply here —
/// the lossless lexer keeps the original text but the typed-AST
/// `Date` accessor surfaces the same canonical-form requirement.
/// Returns `None` for tokens that don't parse as a valid date.
fn parse_date_token(text: &str) -> Option<NaiveDate> {
    // Fast path: canonical "YYYY-MM-DD".
    if text.len() == 10
        && text.as_bytes()[4] == b'-'
        && text.as_bytes()[7] == b'-'
        && let (Ok(y), Ok(m), Ok(d)) = (
            text[0..4].parse::<i32>(),
            text[5..7].parse::<u32>(),
            text[8..10].parse::<u32>(),
        )
    {
        return naive_date(y, m, d);
    }
    // Slow path: normalize and try the chrono parser.
    let normalized = if text.contains('/') {
        text.replace('/', "-")
    } else {
        text.to_string()
    };
    normalized.parse::<NaiveDate>().ok()
}

/// Parse a numeric token. Tolerates leading sign and thousands-
/// separator commas (legacy parser drops them).
fn parse_decimal_token(text: &str) -> Option<Decimal> {
    use std::str::FromStr;
    let cleaned: String;
    let s = if text.contains(',') {
        cleaned = text.replace(',', "");
        cleaned.as_str()
    } else {
        text
    };
    Decimal::from_str(s).ok()
}

// ---- Span helpers ----------------------------------------------

/// Convert a CST node's [`rowan::TextRange`] (relative to the
/// post-BOM source frame) into a [`Span`] in the original-source
/// frame.
fn node_span(node: &crate::SyntaxNode, bom_offset: u32) -> Span {
    let range = node.text_range();
    let start: u32 = range.start().into();
    let end: u32 = range.end().into();
    Span::new((start + bom_offset) as usize, (end + bom_offset) as usize)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_directive_count(result: &ParseResult, expected: usize) {
        assert_eq!(
            result.directives.len(),
            expected,
            "directive count mismatch: {:#?}",
            result.directives
        );
    }

    #[test]
    fn open_directive_basic() {
        let src = "2024-01-15 open Assets:Cash\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("expected Open, got {:?}", result.directives[0].value);
        };
        assert_eq!(open.date, naive_date(2024, 1, 15).unwrap());
        assert_eq!(open.account.as_str(), "Assets:Cash");
        assert!(open.currencies.is_empty());
        assert!(open.booking.is_none());
        assert!(open.meta.is_empty());
    }

    #[test]
    fn open_directive_with_currencies_and_booking() {
        let src = "2024-01-15 open Assets:Brokerage USD,EUR \"STRICT\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("expected Open");
        };
        let currencies: Vec<&str> = open.currencies.iter().map(Currency::as_str).collect();
        assert_eq!(currencies, vec!["USD", "EUR"]);
        assert_eq!(open.booking.as_deref(), Some("STRICT"));
    }

    #[test]
    fn open_directive_with_metadata() {
        let src = "2024-01-15 open Assets:Cash\n  note: \"main checking\"\n  number: 42\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("expected Open");
        };
        assert_eq!(
            open.meta.get("note"),
            Some(&MetaValue::String("main checking".to_string()))
        );
        assert_eq!(
            open.meta.get("number"),
            Some(&MetaValue::Number(Decimal::from(42)))
        );
    }

    #[test]
    fn close_directive_basic() {
        let src = "2024-12-31 close Assets:Cash\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Close(close) = &result.directives[0].value else {
            panic!("expected Close, got {:?}", result.directives[0].value);
        };
        assert_eq!(close.date, naive_date(2024, 12, 31).unwrap());
        assert_eq!(close.account.as_str(), "Assets:Cash");
    }

    #[test]
    fn commodity_directive_basic() {
        let src = "2024-01-01 commodity HOOL\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Commodity(c) = &result.directives[0].value else {
            panic!("expected Commodity");
        };
        assert_eq!(c.currency.as_str(), "HOOL");
    }

    #[test]
    fn bom_offset_is_included_in_spans() {
        let src = "\u{FEFF}2024-01-15 open Assets:Cash\n";
        let result = parse_via_cst(src);
        assert!(result.has_leading_bom);
        let span = result.directives[0].span;
        assert_eq!(span.start, 3, "span should include BOM offset");
    }

    #[test]
    fn unrecognized_directives_currently_drop_silently() {
        // Phase 3.2 scaffolding: Transaction etc. aren't converted
        // yet, so they're silently absent. Pin this so we notice
        // when each converter lands.
        let src = "2024-01-15 * \"x\"\n  Assets:Cash  -5 USD\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 0);
    }

    #[test]
    fn note_directive_basic() {
        let src = "2024-01-15 note Assets:Cash \"deposit received\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Note(note) = &result.directives[0].value else {
            panic!("expected Note");
        };
        assert_eq!(note.date, naive_date(2024, 1, 15).unwrap());
        assert_eq!(note.account.as_str(), "Assets:Cash");
        assert_eq!(note.comment, "deposit received");
    }

    #[test]
    fn document_directive_basic() {
        let src = "2024-01-15 document Assets:Cash \"/path/to/file.pdf\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Document(d) = &result.directives[0].value else {
            panic!("expected Document");
        };
        assert_eq!(d.account.as_str(), "Assets:Cash");
        assert_eq!(d.path, "/path/to/file.pdf");
        // tags/links currently unimplemented — pin as empty.
        assert!(d.tags.is_empty());
        assert!(d.links.is_empty());
    }

    #[test]
    fn event_directive_basic() {
        let src = "2024-01-15 event \"location\" \"Berlin\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Event(e) = &result.directives[0].value else {
            panic!("expected Event");
        };
        assert_eq!(e.event_type, "location");
        assert_eq!(e.value, "Berlin");
    }

    #[test]
    fn query_directive_basic() {
        let src = "2024-01-15 query \"income\" \"SELECT account, sum(position)\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Query(q) = &result.directives[0].value else {
            panic!("expected Query");
        };
        assert_eq!(q.name, "income");
        assert_eq!(q.query, "SELECT account, sum(position)");
    }

    #[test]
    fn price_directive_basic() {
        let src = "2024-01-15 price USD 1.10 EUR\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Price(p) = &result.directives[0].value else {
            panic!("expected Price");
        };
        assert_eq!(p.currency.as_str(), "USD");
        assert_eq!(p.amount.number, Decimal::new(110, 2));
        assert_eq!(p.amount.currency.as_str(), "EUR");
    }

    #[test]
    fn balance_directive_basic() {
        let src = "2024-06-30 balance Assets:Cash 100.00 USD\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Balance(b) = &result.directives[0].value else {
            panic!("expected Balance");
        };
        assert_eq!(b.account.as_str(), "Assets:Cash");
        assert_eq!(b.amount.number, Decimal::new(10000, 2));
        assert_eq!(b.amount.currency.as_str(), "USD");
        assert!(b.tolerance.is_none());
    }

    #[test]
    fn balance_directive_with_explicit_tolerance() {
        let src = "2024-06-30 balance Assets:Cash 100.00 ~ 0.05 USD\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Balance(b) = &result.directives[0].value else {
            panic!("expected Balance");
        };
        assert_eq!(b.amount.number, Decimal::new(10000, 2));
        assert_eq!(b.tolerance, Some(Decimal::new(5, 2)));
    }

    #[test]
    fn pad_directive_basic() {
        let src = "2024-01-01 pad Assets:Cash Equity:Opening-Balances\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Pad(p) = &result.directives[0].value else {
            panic!("expected Pad");
        };
        assert_eq!(p.account.as_str(), "Assets:Cash");
        assert_eq!(p.source_account.as_str(), "Equity:Opening-Balances");
    }
}
