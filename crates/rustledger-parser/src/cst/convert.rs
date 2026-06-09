//! CST -> `ParseResult` converter.
//!
//! [`parse_via_cst`] is the implementation behind the public
//! [`crate::parse`] entry point. It walks the structured CST from
//! [`crate::parse_structured`] via the typed-AST surface in
//! [`crate::cst::ast`] and produces the legacy AST-shaped
//! [`ParseResult`] that downstream consumers (loader, booking,
//! validate, query, LSP) consume.
//!
//! ## Conversion scope
//!
//! Per-directive converters: Open, Close, Commodity, Note,
//! Document, Event, Query, Price, Balance, Pad, Custom, and
//! Transaction (with its full posting / cost-spec / price-
//! annotation / metadata / trailing-comments machinery).
//!
//! State-only directives (Pushtag / Poptag / Pushmeta / Popmeta)
//! mutate `tag_stack` / `meta_stack` inherited by subsequent
//! directives; mismatched-pop and unclosed-at-EOF emit specific
//! `ParseErrorKind` variants. Arithmetic AMOUNT expressions
//! (`120 / 3 USD` ≡ `40 USD`) are evaluated; the same logic
//! powers numeric values in BALANCE and PRICE directives.
//!
//! Field-level extractors populate `ParseResult.options`,
//! `.includes`, `.plugins`, `.comments`, `.currency_occurrences`.
//!
//! ## Error surfacing
//!
//! A single [`walk_descendants_once`] pass collects standalone
//! comments, currency occurrences, and inline `ERROR_TOKEN` /
//! mid-file-BOM errors. Specialized extractors run alongside for
//! `ERROR_NODE` classification, transaction body errors, unclosed
//! cost braces, indented top-level directives, and bare-currency
//! values in custom directives.

use rust_decimal::Decimal;
use rustledger_core::cost::{CostNumber, CostSpec};
use rustledger_core::directive::{PriceAnnotation, PriceKind};
use rustledger_core::{
    Account, Amount, Currency, Directive, IncompleteAmount, InternedStr, Link, MetaValue, Metadata,
    NaiveDate, Posting, Span, Spanned, Tag, naive_date,
};

use crate::ParseResult;
use crate::cst::ast::{
    self, AstNode, AstToken, BalanceDirective, CloseDirective, CommodityDirective, CustomDirective,
    DocumentDirective, EventDirective, IncludeDirective, MetaEntry, NoteDirective, OpenDirective,
    OptionDirective, PadDirective, PluginDirective, PostingFlagKind, PriceDirective,
    QueryDirective, SourceFile, Transaction as AstTransaction, TransactionFlagKind,
};

/// Parse Beancount source via the CST and produce the AST-shaped
/// [`ParseResult`]. This is the implementation behind
/// [`crate::parse`]; the public entry delegates here unconditionally.
///
/// See the module-level rustdoc for the conversion scope.
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
    let mut directive_nodes: Vec<crate::SyntaxNode> = Vec::new();
    let mut options: Vec<(String, String, Span)> = Vec::new();
    let mut includes: Vec<(String, Span)> = Vec::new();
    let mut plugins: Vec<(String, Option<String>, Span)> = Vec::new();
    // Single-pass descendants walk that yields inline errors,
    // top-level comments, and currency occurrences (replaces three
    // separate `descendants_with_tokens` walks at 3·O(N) → 1·O(N)).
    let DescendantsWalkResult {
        inline_errors,
        top_level_comments,
        currency_occurrences,
        account_occurrences,
    } = walk_descendants_once(&source_file, bom_offset);

    let mut comments: Vec<Spanned<String>> = top_level_comments;
    comments.extend(extract_section_marker_comments(&source_file, bom_offset));
    // Merge in source order; the two helpers' classifiers are
    // disjoint today (STAR-first vs COMMENT-kind-first) but
    // dedup-by-start keeps the invariant local.
    comments.sort_by_key(|s| s.span.start);
    comments.dedup_by_key(|s| s.span.start);
    let mut errors = extract_error_node_errors(&source_file, stripped, bom_offset);
    errors.extend(extract_transaction_body_errors(&source_file, bom_offset));
    errors.extend(extract_unclosed_cost_brace_errors(&source_file, bom_offset));
    errors.extend(extract_indented_directive_errors(
        &source_file,
        stripped,
        bom_offset,
    ));
    errors.extend(extract_custom_value_errors(&source_file, bom_offset));
    errors.extend(inline_errors);
    let warnings = Vec::new();

    // pushtag/poptag/pushmeta/popmeta state. The legacy parser
    // maintains a stack across directives; each Transaction
    // inherits the active pushed-tag set, and EVERY directive
    // inherits the active pushed-meta set. We pair each entry
    // with the originating directive's span so unclosed-at-EOF
    // diagnostics can point at the offending push.
    let mut tag_stack: Vec<(Tag, Span)> = Vec::new();
    // Vec-of-tuples (NOT a `Metadata` map) so legacy semantics
    // are preserved: `pushmeta x: 1` then `pushmeta x: 2` should
    // shadow (peek returns 2) and `popmeta x` should pop the
    // most recent, leaving x=1 active. A HashMap would have lost
    // the shadowed entry on the second push.
    let mut meta_stack: Vec<(String, MetaValue, Span)> = Vec::new();

    for directive in source_file.directives() {
        // Helper to push a successfully-converted directive
        // alongside its CST node so the post-pass span fixup
        // can index them in parallel.
        let cst_node = directive.syntax().clone();
        // `is_directive_producing` tracks whether THIS arm is
        // expected to emit a `Spanned<Directive>` (the 12
        // directive types). The catch-all below uses it to
        // surface a `SyntaxError` when a producing converter
        // returned `None` without emitting a more specific
        // diagnostic - the silent-drop class of bug the integ
        // tests caught for `2024-01-01 open` (no account),
        // `balance Assets:X` (no amount), etc.
        let is_directive_producing = matches!(
            directive,
            ast::Directive::Open(_)
                | ast::Directive::Close(_)
                | ast::Directive::Commodity(_)
                | ast::Directive::Note(_)
                | ast::Directive::Document(_)
                | ast::Directive::Event(_)
                | ast::Directive::Query(_)
                | ast::Directive::Price(_)
                | ast::Directive::Balance(_)
                | ast::Directive::Pad(_)
                | ast::Directive::Custom(_)
                | ast::Directive::Transaction(_)
        );
        let errors_before = errors.len();
        let pushed_directive = match directive {
            ast::Directive::Open(node) => convert_open(&node, bom_offset, &mut errors),
            ast::Directive::Close(node) => convert_close(&node, bom_offset, &mut errors),
            ast::Directive::Commodity(node) => convert_commodity(&node, bom_offset, &mut errors),
            ast::Directive::Note(node) => convert_note(&node, bom_offset, &mut errors),
            ast::Directive::Document(node) => convert_document(&node, bom_offset, &mut errors),
            ast::Directive::Event(node) => convert_event(&node, bom_offset, &mut errors),
            ast::Directive::Query(node) => convert_query(&node, bom_offset, &mut errors),
            ast::Directive::Price(node) => convert_price(&node, bom_offset, &mut errors),
            ast::Directive::Balance(node) => convert_balance(&node, bom_offset, &mut errors),
            ast::Directive::Pad(node) => convert_pad(&node, bom_offset, &mut errors),
            ast::Directive::Custom(node) => convert_custom(&node, bom_offset, &mut errors),
            ast::Directive::Transaction(node) => {
                convert_transaction(&node, bom_offset, &mut errors)
            }
            ast::Directive::Option(node) => {
                if let Some(triple) = convert_option(&node, bom_offset) {
                    options.push(triple);
                }
                None
            }
            ast::Directive::Include(node) => {
                if let Some(pair) = convert_include(&node, bom_offset) {
                    includes.push(pair);
                }
                None
            }
            ast::Directive::Plugin(node) => {
                if let Some(triple) = convert_plugin(&node, bom_offset) {
                    plugins.push(triple);
                }
                None
            }
            // State-only side effects: mutate the inherited
            // tag/meta sets that apply to subsequent directives.
            ast::Directive::Pushtag(node) => {
                if let Some(tag_token) = node.tag() {
                    let span = node_span(node.syntax(), bom_offset);
                    tag_stack.push((Tag::new(tag_token.text().trim_start_matches('#')), span));
                }
                None
            }
            ast::Directive::Poptag(node) => {
                if let Some(tag_token) = node.tag() {
                    let name = tag_token.text().trim_start_matches('#');
                    if let Some(pos) = tag_stack.iter().rposition(|(t, _)| t.as_str() == name) {
                        tag_stack.remove(pos);
                    } else {
                        errors.push(crate::ParseError::new(
                            crate::ParseErrorKind::InvalidPoptag(name.to_string()),
                            node_span(node.syntax(), bom_offset),
                        ));
                    }
                }
                None
            }
            ast::Directive::Pushmeta(node) => {
                if let Some(key_token) = node.key() {
                    let key = key_token.text_without_colon().to_string();
                    let value = pushmeta_value(node.syntax());
                    let span = node_span(node.syntax(), bom_offset);
                    meta_stack.push((key, value, span));
                }
                None
            }
            ast::Directive::Popmeta(node) => {
                if let Some(key_token) = node.key() {
                    let key = key_token.text_without_colon().to_string();
                    if let Some(pos) = meta_stack.iter().rposition(|(k, _, _)| k == &key) {
                        meta_stack.remove(pos);
                    } else {
                        errors.push(crate::ParseError::new(
                            crate::ParseErrorKind::InvalidPopmeta(key),
                            node_span(node.syntax(), bom_offset),
                        ));
                    }
                }
                None
            }
        };
        if let Some(mut spanned) = pushed_directive {
            apply_inherited_state(&mut spanned.value, &tag_stack, &meta_stack);
            directives.push(spanned);
            directive_nodes.push(cst_node);
        } else if is_directive_producing && errors.len() == errors_before {
            // Producing converter silently dropped the directive
            // (typically: a required field like an account on
            // `open`, an amount on `balance`, or a source account
            // on `pad` was missing). Mirror the legacy parser's
            // top-level error-recovery path which emits a
            // `SyntaxError("unexpected input")` for the failed
            // span so downstream tooling sees the same shape.
            errors.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError("unexpected input".to_string()),
                node_span(&cst_node, bom_offset),
            ));
        }
    }

    // Unclosed pushtag/pushmeta at EOF - legacy emits one error
    // per leftover stack entry, pointing at the originating push
    // directive's span.
    for (tag, span) in &tag_stack {
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::UnclosedPushtag(tag.as_str().to_string()),
            *span,
        ));
    }
    for (key, _, span) in &meta_stack {
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::UnclosedPushmeta(key.clone()),
            *span,
        ));
    }
    errors.sort_by_key(|e| e.span.start);

    // Post-pass: align directive spans with the legacy parser's
    // convention (skip leading trivia, extend through inter-
    // directive trivia to the next directive's start).
    fixup_directive_spans(&source_file, bom_offset, &directive_nodes, &mut directives);

    ParseResult {
        directives,
        options,
        includes,
        plugins,
        comments,
        errors,
        warnings,
        currency_occurrences,
        account_occurrences,
        has_leading_bom,
    }
}

// ---- Directive converters --------------------------------------

/// Valid booking methods per beancount v3 - must match the
/// whitelist legacy `parser::parse_open_directive` enforces. An
/// `open` directive whose explicit booking string isn't on this
/// list is rejected (directive dropped, `InvalidBookingMethod`
/// error emitted) by both the legacy parser and `convert_open`.
const VALID_BOOKING_METHODS: &[&str] = &[
    "FIFO",
    "STRICT",
    "STRICT_WITH_SIZE",
    "LIFO",
    "HIFO",
    "NONE",
    "AVERAGE",
];

fn convert_open(
    node: &OpenDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    let account = Account::new(node.account()?.text());
    let currencies: Vec<Currency> = node.currencies().map(|c| Currency::new(c.text())).collect();
    let booking = node
        .booking_method()
        .and_then(|s| s.text_unquoted().map(String::from));
    let span = node_span(node.syntax(), bom_offset);
    if let Some(b) = &booking
        && !VALID_BOOKING_METHODS.contains(&b.as_str())
    {
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::InvalidBookingMethod(b.clone()),
            span,
        ));
        return None;
    }
    let meta = convert_meta_entries(node.syntax());

    let open = rustledger_core::directive::Open {
        date,
        account,
        currencies,
        booking,
        meta,
    };
    Some(Spanned::new(Directive::Open(open), span))
}

fn convert_close(
    node: &CloseDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
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

fn convert_commodity(
    node: &CommodityDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
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

fn convert_note(
    node: &NoteDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
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

fn convert_document(
    node: &DocumentDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    let account = Account::new(node.account()?.text());
    let path = node.path()?.text_unquoted()?.to_string();
    // Trailing tags/links on the document header (legacy
    // `parse_document_directive` collects them in a loop after
    // the path STRING). TAG / LINK tokens only appear in the
    // header (not in META_ENTRY children, which are walked
    // separately below), so a direct-child token walk that
    // stops at the first NEWLINE captures them in source order.
    let mut tags: Vec<Tag> = Vec::new();
    let mut links: Vec<Link> = Vec::new();
    for el in node.syntax().children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        match t.kind() {
            crate::SyntaxKind::NEWLINE => break,
            crate::SyntaxKind::TAG => {
                tags.push(Tag::new(t.text().trim_start_matches('#')));
            }
            crate::SyntaxKind::LINK => {
                links.push(Link::new(t.text().trim_start_matches('^')));
            }
            _ => {}
        }
    }
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

fn convert_event(
    node: &EventDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
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

fn convert_query(
    node: &QueryDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
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

fn convert_price(
    node: &PriceDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    let base_currency = Currency::new(node.base_currency()?.text());
    // Same arithmetic support as `convert_balance`: a price
    // directive's value can use `+`, `-`, `*`, `/`, and parens.
    let number = directive_arithmetic_value(node.syntax()).or_else(|| {
        let mut n = parse_decimal_token(node.number()?.text())?;
        if node_has_minus_before_number(node.syntax()) {
            n = -n;
        }
        Some(n)
    })?;
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

fn convert_balance(
    node: &BalanceDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    let account = Account::new(node.account()?.text());
    // Beancount accepts arithmetic in the balance assertion's
    // value (`balance Assets:X 0.25 + 0.75 GBP` ≡ 1.00 GBP).
    // Falls back to the first NUMBER token if the expression
    // can't be evaluated, with the legacy sign-flip behavior.
    let number = directive_arithmetic_value(node.syntax()).or_else(|| {
        let mut n = parse_decimal_token(node.number()?.text())?;
        if node_has_minus_before_number(node.syntax()) {
            n = -n;
        }
        Some(n)
    })?;
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

fn convert_pad(
    node: &PadDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
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

fn convert_custom(
    node: &CustomDirective,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;
    let custom_type = node.custom_type()?.text_unquoted()?.to_string();
    let values = extract_custom_values(node.syntax());
    let meta = convert_meta_entries(node.syntax());

    let custom = rustledger_core::directive::Custom {
        date,
        custom_type,
        values,
        meta,
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Custom(custom), span))
}

/// Walk the heterogeneous value tokens after the `custom "type"`
/// header. The legacy parser tries each value type in this order:
/// string > account > bool > amount (NUMBER+CURRENCY) > number >
/// date > currency. We replicate that priority on the flat token
/// stream, with one structural pass that pairs an immediately-
/// adjacent NUMBER+CURRENCY into an [`Amount`].
fn extract_custom_values(node: &crate::SyntaxNode) -> Vec<MetaValue> {
    let mut values = Vec::new();
    let mut seen_type_string = false;
    // Collect tokens by kind, skipping trivia. We do a two-pass:
    // first form Amount pairs (NUMBER + CURRENCY adjacent, ignoring
    // whitespace), then emit remaining tokens individually.
    let raw: Vec<rowan::SyntaxToken<crate::BeancountLanguage>> = node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| {
            !matches!(
                t.kind(),
                crate::SyntaxKind::WHITESPACE
                    | crate::SyntaxKind::NEWLINE
                    | crate::SyntaxKind::COMMENT
            )
        })
        .collect();

    let mut i = 0;
    while i < raw.len() {
        let t = &raw[i];
        // Skip the directive's header tokens (DATE, CUSTOM_KW, and
        // the first STRING which is the custom-type name).
        if !seen_type_string {
            if t.kind() == crate::SyntaxKind::STRING {
                seen_type_string = true;
            }
            i += 1;
            continue;
        }
        match t.kind() {
            crate::SyntaxKind::STRING => {
                if let Some(s) = strip_string_quotes(t.text()) {
                    values.push(MetaValue::String(s.to_string()));
                }
            }
            crate::SyntaxKind::ACCOUNT => {
                values.push(MetaValue::Account(Account::new(t.text())));
            }
            crate::SyntaxKind::BOOL_TRUE => values.push(MetaValue::Bool(true)),
            crate::SyntaxKind::BOOL_FALSE => values.push(MetaValue::Bool(false)),
            crate::SyntaxKind::NUMBER => {
                // Look ahead for an adjacent CURRENCY -> Amount.
                if let Some(next) = raw.get(i + 1)
                    && next.kind() == crate::SyntaxKind::CURRENCY
                    && let Some(num) = parse_decimal_token(t.text())
                {
                    let curr = Currency::new(next.text());
                    values.push(MetaValue::Amount(Amount::new(num, curr)));
                    i += 2;
                    continue;
                }
                if let Some(num) = parse_decimal_token(t.text()) {
                    values.push(MetaValue::Number(num));
                }
            }
            crate::SyntaxKind::DATE => {
                if let Some(date) = parse_date_token(t.text()) {
                    values.push(MetaValue::Date(date));
                }
            }
            crate::SyntaxKind::CURRENCY => {
                values.push(MetaValue::Currency(Currency::new(t.text())));
            }
            _ => {}
        }
        i += 1;
    }
    values
}

fn strip_string_quotes(raw: &str) -> Option<&str> {
    let bytes = raw.as_bytes();
    if bytes.len() < 2 || bytes[0] != b'"' || bytes[bytes.len() - 1] != b'"' {
        return None;
    }
    Some(&raw[1..raw.len() - 1])
}

fn convert_option(node: &OptionDirective, bom_offset: u32) -> Option<(String, String, Span)> {
    let key = node.key()?.text_unquoted()?.to_string();
    let value = node.value()?.text_unquoted()?.to_string();
    Some((
        key,
        value,
        single_line_directive_span(node.syntax(), bom_offset),
    ))
}

fn convert_include(node: &IncludeDirective, bom_offset: u32) -> Option<(String, Span)> {
    let path = node.path()?.text_unquoted()?.to_string();
    Some((path, single_line_directive_span(node.syntax(), bom_offset)))
}

fn convert_plugin(
    node: &PluginDirective,
    bom_offset: u32,
) -> Option<(String, Option<String>, Span)> {
    let module = node.module()?.text_unquoted()?.to_string();
    let config = node
        .config()
        .and_then(|c| c.text_unquoted().map(String::from));
    Some((
        module,
        config,
        single_line_directive_span(node.syntax(), bom_offset),
    ))
}

// ---- Transaction + Posting + sub-nodes -------------------------

fn convert_transaction(
    node: &AstTransaction,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Directive>> {
    let date = parse_directive_date(&node.date()?, errors, bom_offset)?;

    // Flag: explicit (TransactionFlag) or implied (leading STRING
    // with no flag token; defaults to '*').
    let flag = node.flag().map_or('*', |f| flag_char_from_transaction(&f));

    // Header strings: with 2 -> payee + narration; with 1 ->
    // narration-only; with 3+ -> ambiguous (typed-AST surface
    // returns None for both, matching the round-2 review fix).
    let strings: Vec<String> = node
        .strings()
        .filter_map(|s| s.text_unquoted().map(String::from))
        .collect();
    let (payee_str, narration_str) = match strings.len() {
        0 => (None, String::new()),
        1 => (None, strings.into_iter().next().unwrap()),
        2 => {
            let mut it = strings.into_iter();
            let p = it.next().unwrap();
            let n = it.next().unwrap();
            (Some(p), n)
        }
        // 3+ strings: surface only the last as narration; the
        // middle ones are unreachable through this typed shape
        // (matches the round-2 docstring).
        _ => (None, strings.last().cloned().unwrap_or_default()),
    };

    let payee = payee_str.map(InternedStr::from);
    let narration = InternedStr::from(narration_str);

    // Tags / links from the TRANSACTION node: the typed AST
    // accessor `tags()`/`links()` is scoped to the header region.
    // Trailing TAG / LINK tokens appearing on body lines (after
    // the header NEWLINE, OUTSIDE any POSTING / META_ENTRY child
    // node) are also part of the transaction's tag/link set per
    // Beancount semantics - `extract_transaction_body_errors`
    // already exempts them from the malformed-body diagnostic for
    // this reason. Aggregate them here so they don't silently
    // disappear.
    let mut tags: Vec<Tag> = node
        .tags()
        .map(|t| Tag::new(t.text().trim_start_matches('#')))
        .collect();
    let mut links: Vec<Link> = node
        .links()
        .map(|l| Link::new(l.text().trim_start_matches('^')))
        .collect();
    for el in node.syntax().children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            // Nodes (POSTING / META_ENTRY) own their own internal
            // tokens; we don't recurse into them.
            continue;
        };
        match t.kind() {
            crate::SyntaxKind::TAG => {
                let stripped = t.text().trim_start_matches('#');
                let new_tag = Tag::new(stripped);
                if !tags.contains(&new_tag) {
                    tags.push(new_tag);
                }
            }
            crate::SyntaxKind::LINK => {
                let stripped = t.text().trim_start_matches('^');
                let new_link = Link::new(stripped);
                if !links.contains(&new_link) {
                    links.push(new_link);
                }
            }
            _ => {}
        }
    }

    // Transaction-level metadata (META_ENTRY children directly on
    // the TRANSACTION node, NOT on POSTING children).
    let meta = convert_meta_entries(node.syntax());

    // Postings + pre-posting comments. The CST puts inter-
    // posting trivia (including `; comment` lines) as flat
    // tokens DIRECT under TRANSACTION between two POSTING
    // nodes. Walk in source order: COMMENT tokens accumulate
    // into `pending`, then attach to the next POSTING node's
    // `comments` field when we reach it. Tokens before the
    // header NEWLINE are skipped (they're transaction-header
    // content). Comments that remain in `pending` after the
    // final posting belong to the transaction itself
    // (legacy: `txn.trailing_comments = pending_comments`).
    let (postings, trailing_comments) = collect_postings_with_comments(node, bom_offset, errors);

    // Deprecated `|` separator between payee and narration: a
    // PIPE token in the header region. Legacy treats this as a
    // recoverable warning-shaped error (`DeprecatedPipeSymbol`)
    // and keeps the directive, so we do the same here.
    if header_has_pipe(node) {
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::DeprecatedPipeSymbol,
            node_span(node.syntax(), bom_offset),
        ));
    }

    let txn = rustledger_core::directive::Transaction {
        date,
        flag,
        payee,
        narration,
        tags,
        links,
        meta,
        postings,
        trailing_comments,
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Transaction(txn), span))
}

/// Returns true if the TRANSACTION header (direct-child tokens
/// up to the first NEWLINE) contains a `PIPE` token. The legacy
/// parser surfaces a `DeprecatedPipeSymbol` diagnostic for this
/// shape; the CST lexer classifies `|` as `PIPE`, so we just
/// scan the header directly.
fn header_has_pipe(node: &AstTransaction) -> bool {
    for el in node.syntax().children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        if t.kind() == crate::SyntaxKind::NEWLINE {
            return false;
        }
        if t.kind() == crate::SyntaxKind::PIPE {
            return true;
        }
    }
    false
}

/// Walk a `TRANSACTION`'s children in source order, attaching any
/// inter-posting `; comment` lines that appear as flat tokens
/// between `POSTING` nodes to the NEXT posting's `comments`
/// field. Matches the legacy parser, which collects
/// `pending_comments` while reading the body and applies them to
/// the next posting it parses.
///
/// Tokens before the header-terminator NEWLINE belong to the
/// transaction header (date/flag/strings/tags/links) and are
/// skipped.
///
/// Returns `(postings, trailing_comments)`: the second element is
/// any pending comments left over AFTER the final posting, which
/// legacy assigns to `Transaction::trailing_comments`.
fn collect_postings_with_comments(
    node: &AstTransaction,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> (Vec<Spanned<Posting>>, Vec<String>) {
    let mut out = Vec::new();
    let mut pending: Vec<String> = Vec::new();
    let mut past_header = false;
    for el in node.syntax().children_with_tokens() {
        match el {
            rowan::NodeOrToken::Token(t) => {
                if !past_header {
                    if t.kind() == crate::SyntaxKind::NEWLINE {
                        past_header = true;
                    }
                    continue;
                }
                if is_comment_kind(t.kind()) {
                    pending.push(t.text().to_string());
                } else if !is_trivia_kind(t.kind())
                    && !matches!(t.kind(), crate::SyntaxKind::TAG | crate::SyntaxKind::LINK)
                {
                    // Non-trivia, non-comment token in the
                    // transaction body that's NOT inside a
                    // POSTING / META_ENTRY child node = malformed
                    // body line (caught separately by
                    // `extract_transaction_body_errors`). Treat
                    // the same as a failed POSTING: clear pending
                    // so the malformed line's preceding comments
                    // don't migrate onto the next valid posting.
                    //
                    // EXEMPT TAG / LINK: trailing tags/links on
                    // transaction body lines (after the header)
                    // are valid Beancount - they extend the
                    // transaction's tag/link set without being
                    // a new posting. Treating them as malformed
                    // would drop legitimate preceding comments
                    // that belong to the NEXT posting. The same
                    // exemption appears in
                    // `extract_transaction_body_errors`, which
                    // does the parallel "is this a malformed
                    // body line?" classification.
                    pending.clear();
                }
            }
            rowan::NodeOrToken::Node(n) => {
                if !past_header {
                    // META_ENTRY or POSTING before the header
                    // NEWLINE shouldn't happen in well-formed
                    // input; treat any child node as "past the
                    // header" if we somehow encounter one.
                    past_header = true;
                }
                if let Some(p) = ast::Posting::cast(n) {
                    if let Some(mut spanned) = convert_posting(&p, bom_offset, errors) {
                        if !pending.is_empty() {
                            spanned.value.comments = std::mem::take(&mut pending);
                        }
                        out.push(spanned);
                    } else {
                        // Failed posting consumes any pending
                        // inter-posting comments - they belonged
                        // to it. Without this clear, a malformed
                        // posting's preceding comments would
                        // migrate forward and attach to the NEXT
                        // successful posting, misattributing them
                        // visibly to the wrong account line.
                        pending.clear();
                    }
                }
                // META_ENTRY child nodes: comments collected so
                // far don't apply to them (they're transaction
                // metadata). Drop them.
            }
        }
    }
    (out, pending)
}

fn flag_char_from_transaction(flag: &ast::TransactionFlag) -> char {
    match flag.classify() {
        TransactionFlagKind::Star | TransactionFlagKind::Txn => '*',
        TransactionFlagKind::Pending => '!',
        TransactionFlagKind::Hash => '#',
        TransactionFlagKind::Letter | TransactionFlagKind::CurrencyLetter => {
            flag.text().chars().next().unwrap_or('*')
        }
    }
}

fn convert_posting(
    node: &ast::Posting,
    bom_offset: u32,
    errors: &mut Vec<crate::ParseError>,
) -> Option<Spanned<Posting>> {
    let account = Account::new(node.account()?.text());

    let flag = node.flag().map(|f| flag_char_from_posting(&f));

    // A well-formed posting has AT MOST one `AMOUNT` child node
    // (the units). The CST builder will accept input like
    // `Expenses:Food  5 USD + 3 USD` and produce TWO sibling
    // `AMOUNT` nodes joined by a flat PLUS token, because the
    // grammar doesn't enforce that PLUS between two complete
    // amounts is invalid. `Posting::amount()` returns only the
    // first via `first_child`, so without this guard the second
    // amount (and the joining `+`) would be silently dropped and
    // the user's transaction would balance against the wrong
    // number. Emit a `SyntaxError` pointing at the trailing
    // siblings and keep the first amount.
    let mut amount_children = node
        .syntax()
        .children()
        .filter(|n| ast::Amount::can_cast(n.kind()));
    let first_amount = amount_children.next();
    let first_amount_end: Option<u32> = first_amount.as_ref().map(|n| n.text_range().end().into());
    let mut sibling_start: Option<u32> = None;
    let mut sibling_end: u32 = 0;
    for extra in amount_children {
        let range = extra.text_range();
        let start_u32: u32 = range.start().into();
        let end_u32: u32 = range.end().into();
        if sibling_start.is_none() {
            sibling_start = Some(start_u32);
        }
        sibling_end = end_u32;
    }
    if let Some(start_u32) = sibling_start {
        // Extend the span back to the end of the FIRST AMOUNT so
        // the diagnostic underline covers any joining operator
        // (`+`, `*`, whitespace) between the kept amount and the
        // orphans. Without this, a user sees only `3 USD` in
        // `5 USD + 3 USD` highlighted - and may not realize the
        // `+ 3 USD` together is what needs to be removed.
        let underline_start = first_amount_end.unwrap_or(start_u32);
        let span = Span::new(
            (underline_start + bom_offset) as usize,
            (sibling_end + bom_offset) as usize,
        );
        errors.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(
                "unexpected trailing tokens after posting amount".to_string(),
            ),
            span,
        ));
    }
    let units = first_amount
        .and_then(ast::Amount::cast)
        .and_then(|amt| convert_amount_to_incomplete(&amt, errors, bom_offset));
    let cost = node.cost_spec().map(|cs| convert_cost_spec(&cs));
    let price = node
        .price_annotation()
        .map(|pa| convert_price_annotation(&pa, errors, bom_offset));
    let meta = convert_meta_entries(node.syntax());

    // Trailing comments on the posting line: COMMENT direct-
    // child tokens BEFORE the terminator NEWLINE. The legacy
    // parser collects same-line `;` content into
    // `posting.trailing_comments`.
    let trailing_comments: Vec<String> = node
        .syntax()
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .take_while(|t| t.kind() != crate::SyntaxKind::NEWLINE)
        .filter(|t| is_comment_kind(t.kind()))
        .map(|t| t.text().to_string())
        .collect();

    let posting = Posting {
        account,
        units,
        cost,
        price,
        flag,
        meta,
        comments: Vec::new(),
        trailing_comments,
    };
    let span = posting_span(node.syntax(), bom_offset);
    Some(Spanned::new(posting, span))
}

fn flag_char_from_posting(flag: &ast::PostingFlag) -> char {
    match flag.classify() {
        PostingFlagKind::Star => '*',
        PostingFlagKind::Pending => '!',
        PostingFlagKind::Hash => '#',
        PostingFlagKind::Letter | PostingFlagKind::CurrencyLetter => {
            flag.text().chars().next().unwrap_or('*')
        }
    }
}

/// Convert an AMOUNT node into an [`IncompleteAmount`]. Returns
/// `None` if neither a number nor a currency is present (which
/// shouldn't happen for a well-formed AMOUNT, but matches the
/// lossless CST contract). Sign is folded into the number.
///
/// **Arithmetic limitation**: when the AMOUNT contains an
/// arithmetic expression (`100+5 USD`), only the FIRST `NUMBER`
/// is used. A proper expression evaluator is deferred - none of
/// the directive types we currently handle outside of postings
/// use AMOUNT shapes that the legacy parser would have evaluated
/// differently.
fn convert_amount_to_incomplete(
    amt: &ast::Amount,
    errors: &mut Vec<crate::ParseError>,
    bom_offset: u32,
) -> Option<IncompleteAmount> {
    // Arithmetic AMOUNT expressions (`120 / 3 USD`, `(1+2) USD`):
    // run the recursive-descent evaluator on the flat token
    // stream. Fast-path plain `NUMBER CURRENCY` shapes to keep
    // the common case allocation-free.
    let number = if amt.is_arithmetic() {
        let evaluated = evaluate_amount_expression(amt);
        if evaluated.is_none() {
            // `is_arithmetic` was true but the evaluator gave up
            // (decimal overflow, division by zero, malformed
            // expression, unbalanced parens). Without this
            // emission the amount silently degrades to
            // `CurrencyOnly` and the user only sees a downstream
            // "transaction doesn't balance" - masking the actual
            // root cause. Pin the span to the AMOUNT node so the
            // diagnostic underlines the offending expression.
            let range = amt.syntax().text_range();
            let start: u32 = range.start().into();
            let end: u32 = range.end().into();
            let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
            errors.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError(
                    "invalid arithmetic expression in amount (overflow, division by zero, or malformed)"
                        .to_string(),
                ),
                span,
            ));
        }
        evaluated
    } else {
        amt.number().and_then(|n| {
            let parsed = parse_decimal_token(n.text());
            if parsed.is_none() {
                // Symmetry with the arithmetic-failure path: when
                // a plain NUMBER token in an AMOUNT can't be
                // turned into a Decimal (e.g., 30+ digits - the
                // lexer's NUMBER regex has no max length but
                // `rust_decimal`'s 28-digit ceiling rejects it),
                // surface a diagnostic instead of silently
                // degrading to `CurrencyOnly`. Without this the
                // user only sees "transaction doesn't balance"
                // and never learns the parser dropped a number.
                let range = n.syntax().text_range();
                let start: u32 = range.start().into();
                let end: u32 = range.end().into();
                let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
                errors.push(crate::ParseError::new(
                    crate::ParseErrorKind::SyntaxError(
                        "invalid number in amount (likely exceeds 28-digit Decimal precision)"
                            .to_string(),
                    ),
                    span,
                ));
            }
            let mut value = parsed?;
            if let Some(sign) = amt.sign()
                && sign.is_minus()
            {
                value = -value;
            }
            Some(value)
        })
    };
    let currency = amt.currency().map(|c| Currency::new(c.text()));
    match (number, currency) {
        (Some(n), Some(c)) => Some(IncompleteAmount::Complete(Amount::new(n, c))),
        (Some(n), None) => Some(IncompleteAmount::NumberOnly(n)),
        (None, Some(c)) => Some(IncompleteAmount::CurrencyOnly(c)),
        (None, None) => None,
    }
}

/// Evaluate the arithmetic expression inside an `AMOUNT` node and
/// return the resulting decimal. Returns `None` when evaluation
/// fails (division by zero, decimal overflow, malformed parens,
/// missing operand).
///
/// AMOUNT children are flat tokens (no expression sub-tree): a
/// sequence of `NUMBER`, `PLUS`, `MINUS`, `STAR`, `SLASH`,
/// `L_PAREN`, `R_PAREN`, and a trailing `CURRENCY` at depth 0
/// that's the amount's currency rather than part of the
/// expression. The currency is stripped first; the rest goes
/// through recursive descent mirroring legacy
/// `parser::parse_expr` / `parse_term` / `parse_primary`.
///
/// Operator precedence and unary handling match Python beancount:
/// `*` and `/` bind tighter than `+` and `-`; a leading or post-
/// operator `-` is unary negation.
fn evaluate_amount_expression(amt: &ast::Amount) -> Option<Decimal> {
    let tokens = amount_expression_tokens(amt);
    let mut cursor = 0usize;
    let value = parse_arith_expr(&tokens, &mut cursor)?;
    // Trailing tokens after a successful parse mean the expression
    // is malformed (`1+2 3 USD`); refuse rather than silently
    // dropping them.
    if cursor != tokens.len() {
        return None;
    }
    Some(value)
}

/// Evaluate the arithmetic expression that appears as the
/// numeric value of a `BALANCE` / `PRICE` directive, returning
/// the resulting decimal or `None` if not arithmetic (single
/// NUMBER, callers fall back to `parse_decimal_token`).
///
/// Unlike `AMOUNT`, these directives don't wrap their value in
/// a dedicated node - the tokens are flat under the directive
/// node. The relevant region is from the FIRST `NUMBER` token up
/// to (but not including) the FIRST `CURRENCY` token at paren-
/// depth 0 (the amount currency). For BALANCE, this correctly
/// stops before any trailing `~ NUMBER [CURRENCY]` tolerance
/// region too.
///
/// Returns `Some` only when the slice contains at least one
/// arithmetic operator (`+`, `-`, `*`, `/`) or parens - for a
/// bare single `NUMBER`, returns `None` so the caller can use
/// the existing fast path (which preserves the legacy sign-flip
/// behavior).
fn directive_arithmetic_value(node: &crate::SyntaxNode) -> Option<Decimal> {
    let raw: Vec<crate::SyntaxToken> = node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| !is_trivia_kind(t.kind()))
        .skip_while(|t| t.kind() != crate::SyntaxKind::NUMBER)
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
    let tokens: Vec<crate::SyntaxToken> = raw.into_iter().take(end).collect();
    // Fast-path: zero or one token = no arithmetic.
    let has_op = tokens.iter().any(|t| {
        matches!(
            t.kind(),
            crate::SyntaxKind::PLUS
                | crate::SyntaxKind::MINUS
                | crate::SyntaxKind::STAR
                | crate::SyntaxKind::SLASH
                | crate::SyntaxKind::L_PAREN
        )
    });
    if !has_op {
        return None;
    }
    let mut cursor = 0usize;
    let value = parse_arith_expr(&tokens, &mut cursor)?;
    if cursor != tokens.len() {
        return None;
    }
    Some(value)
}

/// Collect AMOUNT's expression tokens - every non-trivia direct-
/// child token EXCEPT the trailing `CURRENCY` at paren-depth 0
/// (which is the amount's currency, not part of the expression).
/// Parens at any depth are preserved so `parse_arith_primary` can
/// recurse through them.
fn amount_expression_tokens(amt: &ast::Amount) -> Vec<crate::SyntaxToken> {
    let raw: Vec<crate::SyntaxToken> = amt
        .syntax()
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| !is_trivia_kind(t.kind()))
        .collect();
    // Find the index of the LAST `CURRENCY` at depth 0 - same
    // disambiguator as `Amount::currency()`. Tokens before that
    // index form the arithmetic expression.
    let mut depth: i32 = 0;
    let mut trailing_currency_idx: Option<usize> = None;
    for (i, t) in raw.iter().enumerate() {
        match t.kind() {
            crate::SyntaxKind::L_PAREN => depth += 1,
            crate::SyntaxKind::R_PAREN => depth -= 1,
            crate::SyntaxKind::CURRENCY if depth == 0 => trailing_currency_idx = Some(i),
            _ => {}
        }
    }
    let end = trailing_currency_idx.unwrap_or(raw.len());
    raw.into_iter().take(end).collect()
}

/// `expr := term (('+' | '-') term)*` - left-associative.
fn parse_arith_expr(tokens: &[crate::SyntaxToken], cursor: &mut usize) -> Option<Decimal> {
    let mut result = parse_arith_term(tokens, cursor)?;
    while let Some(op) = tokens.get(*cursor).map(crate::SyntaxToken::kind) {
        match op {
            crate::SyntaxKind::PLUS => {
                *cursor += 1;
                let rhs = parse_arith_term(tokens, cursor)?;
                result = result.checked_add(rhs)?;
            }
            crate::SyntaxKind::MINUS => {
                *cursor += 1;
                let rhs = parse_arith_term(tokens, cursor)?;
                result = result.checked_sub(rhs)?;
            }
            _ => break,
        }
    }
    Some(result)
}

/// `term := primary (('*' | '/') primary)*` - left-associative.
fn parse_arith_term(tokens: &[crate::SyntaxToken], cursor: &mut usize) -> Option<Decimal> {
    let mut result = parse_arith_primary(tokens, cursor)?;
    while let Some(op) = tokens.get(*cursor).map(crate::SyntaxToken::kind) {
        match op {
            crate::SyntaxKind::STAR => {
                *cursor += 1;
                let rhs = parse_arith_primary(tokens, cursor)?;
                result = result.checked_mul(rhs)?;
            }
            crate::SyntaxKind::SLASH => {
                *cursor += 1;
                let rhs = parse_arith_primary(tokens, cursor)?;
                if rhs.is_zero() {
                    return None;
                }
                result = result.checked_div(rhs)?;
            }
            _ => break,
        }
    }
    Some(result)
}

/// `primary := '(' expr ')' | '-' primary | '+' primary | NUMBER`.
fn parse_arith_primary(tokens: &[crate::SyntaxToken], cursor: &mut usize) -> Option<Decimal> {
    let t = tokens.get(*cursor)?;
    match t.kind() {
        crate::SyntaxKind::L_PAREN => {
            *cursor += 1;
            let inner = parse_arith_expr(tokens, cursor)?;
            // Mandatory closer; bail (returning None) on unbalance
            // - `Amount::currency()` already refuses to surface a
            // currency for unbalanced parens, so the amount as a
            // whole degrades cleanly to `NumberOnly`/`None`.
            let close = tokens.get(*cursor)?;
            if close.kind() != crate::SyntaxKind::R_PAREN {
                return None;
            }
            *cursor += 1;
            Some(inner)
        }
        crate::SyntaxKind::MINUS => {
            *cursor += 1;
            let inner = parse_arith_primary(tokens, cursor)?;
            Some(-inner)
        }
        crate::SyntaxKind::PLUS => {
            *cursor += 1;
            parse_arith_primary(tokens, cursor)
        }
        crate::SyntaxKind::NUMBER => {
            let value = parse_decimal_token(t.text())?;
            *cursor += 1;
            Some(value)
        }
        _ => None,
    }
}

fn convert_cost_spec(cs: &ast::CostSpec) -> CostSpec {
    let merge = cs.is_merge();
    let is_total = cs.is_total();

    // `{N # T CCY}` form: the value AFTER the `#` is the total
    // (per-unit `N` is informationally redundant and the booker
    // derives it from `T / |units|`). Pin this here so the form
    // is semantically equivalent to `{{T CCY}}` (matching Python
    // beancount). Without this, the FIRST `NUMBER` would be
    // surfaced as `PerUnit{N}` and the post-`#` total would be
    // silently dropped - inverting the post-booking value of
    // every cost-basis read of this spec form.
    let post_hash_total = cost_total_after_hash(cs);

    let cost_number = if let Some(total) = post_hash_total {
        Some(CostNumber::Total { value: total })
    } else {
        let number = cs.number().and_then(|n| parse_decimal_token(n.text()));
        match (number, is_total) {
            (Some(v), true) => Some(CostNumber::Total { value: v }),
            (Some(v), false) => Some(CostNumber::PerUnit { value: v }),
            (None, _) => None,
        }
    };

    let currency = cs.currency().map(|c| Currency::new(c.text()));
    let date = cs.date().and_then(|d| parse_date_token(d.text()));
    let label = cs.label().and_then(|s| s.text_unquoted().map(String::from));

    CostSpec {
        number: cost_number,
        currency,
        date,
        label,
        merge,
    }
}

/// Detect the `{N # T CCY}` cost-spec shape (a `HASH` token
/// between two `NUMBER` tokens at the cost-spec's depth) and
/// return `T` as a `Decimal`. Returns `None` for every other
/// shape - `{N CCY}`, `{{T CCY}}`, `{#}`, etc.
fn cost_total_after_hash(cs: &ast::CostSpec) -> Option<Decimal> {
    let mut seen_number = false;
    let mut past_hash = false;
    for el in cs.syntax().children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        match t.kind() {
            crate::SyntaxKind::NUMBER if !seen_number => {
                seen_number = true;
            }
            crate::SyntaxKind::HASH if seen_number => {
                past_hash = true;
            }
            crate::SyntaxKind::NUMBER if past_hash => {
                return parse_decimal_token(t.text());
            }
            _ => {}
        }
    }
    None
}

fn convert_price_annotation(
    pa: &ast::PriceAnnotation,
    errors: &mut Vec<crate::ParseError>,
    bom_offset: u32,
) -> PriceAnnotation {
    let kind = if pa.is_total() {
        PriceKind::Total
    } else {
        PriceKind::Unit
    };
    let amount = pa
        .amount()
        .and_then(|a| convert_amount_to_incomplete(&a, errors, bom_offset));
    PriceAnnotation { kind, amount }
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

/// Returns true if a node's flat direct-child tokens contain a
/// `MINUS` BEFORE the first `NUMBER`. Used to detect signed
/// numeric values in directives like Balance / Price whose typed-
/// AST accessors return the unsigned NUMBER token only.
fn node_has_minus_before_number(node: &crate::SyntaxNode) -> bool {
    for el in node.children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        match t.kind() {
            crate::SyntaxKind::MINUS => return true,
            crate::SyntaxKind::NUMBER => return false,
            _ => {}
        }
    }
    false
}

/// Returns true if a `META_ENTRY`'s value tokens contain a `MINUS`
/// before the first `NUMBER`. Used by `meta_value_from_entry` to
/// detect signed-number values like `precision: -1` which the
/// legacy parser handles via `parse_signed_number`.
fn meta_entry_has_minus_sign(entry: &MetaEntry) -> bool {
    let mut past_key = false;
    for el in entry.syntax().children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        if !past_key {
            if t.kind() == crate::SyntaxKind::META_KEY {
                past_key = true;
            }
            continue;
        }
        match t.kind() {
            crate::SyntaxKind::MINUS => return true,
            crate::SyntaxKind::NUMBER => return false,
            _ => {}
        }
    }
    false
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
        && let Some(mut decimal) = parse_decimal_token(n.text())
    {
        // A MINUS direct-child token (signed value) negates the
        // number. Legacy parses `precision: -1` as Number(-1);
        // we need the same.
        if meta_entry_has_minus_sign(entry) {
            decimal = -decimal;
        }
        // `0.50 USD` style: NUMBER + CURRENCY together → Amount.
        // Plain NUMBER without CURRENCY → Number. Matches legacy
        // parser priority where parse_amount runs before
        // parse_signed_number.
        if let Some(c) = entry.value_currency() {
            return MetaValue::Amount(Amount::new(decimal, Currency::new(c.text())));
        }
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

// ---- Inherited state (pushtag/poptag/pushmeta/popmeta) ---------

/// Merge active pushed-tag and pushed-meta state into a freshly
/// converted directive's value. Mirrors the legacy parser's
/// `apply_pushed_tags` + `apply_pushed_meta`: tags apply ONLY to
/// `Transaction`; meta applies to every directive's `meta` field.
///
/// The meta stack is a `Vec` (not a map) to preserve shadow/pop
/// semantics - `pushmeta x: 1; pushmeta x: 2; popmeta x` should
/// leave `x = 1` active, which a map-replacing-on-insert can't
/// express. Iterating in push order and inserting into the
/// directive's meta means later entries naturally win, matching
/// "topmost-shadow wins" behavior.
fn apply_inherited_state(
    value: &mut Directive,
    tag_stack: &[(Tag, Span)],
    meta_stack: &[(String, MetaValue, Span)],
) {
    if let Directive::Transaction(txn) = value {
        for (tag, _) in tag_stack {
            if !txn.tags.contains(tag) {
                txn.tags.push(tag.clone());
            }
        }
    }
    if meta_stack.is_empty() {
        return;
    }
    let meta = match value {
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
    for (k, v, _) in meta_stack {
        meta.insert(k.clone(), v.clone());
    }
}

/// Extract the value tokens after the `META_KEY` of a Pushmeta
/// directive into a typed [`MetaValue`]. Walks the directive's
/// direct-child tokens (the directive isn't a `META_ENTRY` so the
/// typed-AST accessors aren't reusable).
fn pushmeta_value(node: &crate::SyntaxNode) -> MetaValue {
    for el in node.children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        match t.kind() {
            crate::SyntaxKind::STRING => {
                if let Some(s) = strip_string_quotes(t.text()) {
                    return MetaValue::String(s.to_string());
                }
            }
            crate::SyntaxKind::NUMBER => {
                if let Some(n) = parse_decimal_token(t.text()) {
                    return MetaValue::Number(n);
                }
            }
            crate::SyntaxKind::DATE => {
                if let Some(d) = parse_date_token(t.text()) {
                    return MetaValue::Date(d);
                }
            }
            crate::SyntaxKind::ACCOUNT => return MetaValue::Account(Account::new(t.text())),
            crate::SyntaxKind::CURRENCY => return MetaValue::Currency(Currency::new(t.text())),
            crate::SyntaxKind::BOOL_TRUE => return MetaValue::Bool(true),
            crate::SyntaxKind::BOOL_FALSE => return MetaValue::Bool(false),
            crate::SyntaxKind::TAG => {
                return MetaValue::Tag(Tag::new(t.text().trim_start_matches('#')));
            }
            crate::SyntaxKind::LINK => {
                return MetaValue::Link(Link::new(t.text().trim_start_matches('^')));
            }
            _ => {}
        }
    }
    MetaValue::None
}

// ---- ParseResult.comments --------------------------------------

/// Comment-like syntax kinds that the legacy parser surfaces as
/// `ParseResult.comments` entries when they appear at the top
/// level (outside any directive's content).
const fn is_comment_kind(kind: crate::SyntaxKind) -> bool {
    matches!(
        kind,
        crate::SyntaxKind::COMMENT
            | crate::SyntaxKind::PERCENT_COMMENT
            | crate::SyntaxKind::SHEBANG
            | crate::SyntaxKind::EMACS_DIRECTIVE
    )
}

/// Walk every `COST_SPEC` node in the tree and emit a
/// `SyntaxError("unclosed cost specification: missing '}'")` for
/// any spec whose opener (`{`, `{{`, or `{#`) doesn't have a
/// matching closer at the spec's depth-0. Mirrors the legacy
/// parser's deferred-error emission at `parser.rs:705-707` so a
/// `10 AAPL {150 USD\n` posting or an EOF-truncated cost block
/// surfaces a diagnostic instead of silently producing a half-
/// built cost spec.
fn extract_unclosed_cost_brace_errors(
    source_file: &SourceFile,
    bom_offset: u32,
) -> Vec<crate::ParseError> {
    let mut out = Vec::new();
    for cs in source_file.syntax().descendants() {
        if cs.kind() != crate::SyntaxKind::COST_SPEC {
            continue;
        }
        let mut has_opener = false;
        let mut has_closer = false;
        for el in cs.children_with_tokens() {
            let rowan::NodeOrToken::Token(t) = el else {
                continue;
            };
            match t.kind() {
                crate::SyntaxKind::L_BRACE
                | crate::SyntaxKind::L_DOUBLE_BRACE
                | crate::SyntaxKind::L_BRACE_HASH => has_opener = true,
                crate::SyntaxKind::R_BRACE | crate::SyntaxKind::R_DOUBLE_BRACE => has_closer = true,
                _ => {}
            }
        }
        if has_opener && !has_closer {
            out.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError(
                    "unclosed cost specification: missing '}'".to_string(),
                ),
                node_span(&cs, bom_offset),
            ));
        }
    }
    out
}

/// Walk every top-level directive in `source_file` and emit a
/// `SyntaxError("top-level directive must start at column 0")`
/// for any whose content (first non-trivia token) starts at a
/// non-zero column. Per the Beancount language spec, top-level
/// directives are required to begin at column 0; indentation is
/// reserved for postings and metadata inside a transaction body.
///
/// The CST grammar happily accepts an indented `open` / `balance`
/// / etc., which is why this surfaces at converter level instead
/// of as a lex/parse error.
fn extract_indented_directive_errors(
    source_file: &SourceFile,
    stripped: &str,
    bom_offset: u32,
) -> Vec<crate::ParseError> {
    let mut out = Vec::new();
    for child in source_file.syntax().children() {
        if !ast::Directive::can_cast(child.kind()) {
            continue;
        }
        // Find the directive's content start - the first non-
        // trivia token. Leading WHITESPACE / NEWLINE / COMMENT
        // can land inside the directive node per the Directive-
        // Terminator Rule's inter-directive trivia attachment.
        let Some(content) = child
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .find(|t| !is_trivia_kind(t.kind()))
        else {
            continue;
        };
        let content_start: usize = u32::from(content.text_range().start()) as usize;
        // Column = offset since the last NEWLINE in the source,
        // or since byte 0 if this is the first line. >0 means
        // the directive's first content token has leading WS on
        // its own line - that's the indent error.
        let line_start = stripped[..content_start].rfind('\n').map_or(0, |nl| nl + 1);
        if content_start > line_start {
            let end: u32 = content.text_range().end().into();
            let span = Span::new(
                (line_start as u32 + bom_offset) as usize,
                (end + bom_offset) as usize,
            );
            out.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError(
                    "top-level directive must start at column 0".to_string(),
                ),
                span,
            ));
        }
    }
    out
}

/// Walk each `CUSTOM` directive and emit a `SyntaxError` for
/// every bare `CURRENCY` token in the value position (a CURRENCY
/// not paired with a preceding NUMBER as an Amount).
///
/// Per the Beancount language spec, custom-directive values are
/// limited to string / date / decimal / amount / boolean -
/// `bean-check` rejects a bare currency literal with a syntax
/// error. Rustledger's `extract_custom_values` has historically
/// been more lenient, accepting ACCOUNT / TAG / LINK in value
/// position too; we keep that extension (it's covered by the
/// existing `test_parse_custom_directive` integration test) but
/// surface a diagnostic for the bare-CURRENCY case so the
/// compat metric reflects bean-check's exit-code rejection on
/// shapes like `custom "x" 10 USD "y" NZD …`.
fn extract_custom_value_errors(
    source_file: &SourceFile,
    bom_offset: u32,
) -> Vec<crate::ParseError> {
    let mut out = Vec::new();
    for child in source_file.syntax().children() {
        if child.kind() != crate::SyntaxKind::CUSTOM_DIRECTIVE {
            continue;
        }
        // Collect non-trivia tokens, then skip past the
        // directive's header: DATE, CUSTOM_KW, and the first
        // STRING (the custom-type name). Everything after that
        // is values.
        let raw: Vec<crate::SyntaxToken> = child
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .filter(|t| !is_trivia_kind(t.kind()))
            .collect();
        let mut seen_type_string = false;
        let mut i = 0;
        while i < raw.len() {
            let t = &raw[i];
            if !seen_type_string {
                if t.kind() == crate::SyntaxKind::STRING {
                    seen_type_string = true;
                }
                i += 1;
                continue;
            }
            if t.kind() == crate::SyntaxKind::CURRENCY {
                // Only flag BARE CURRENCY - one that doesn't
                // follow a NUMBER (Amount-pairing). The Amount
                // pairing is handled by `extract_custom_values`
                // via i+1 lookahead, so a CURRENCY that's NOT
                // preceded by a NUMBER at i-1 is bare.
                let preceded_by_number = i > 0 && raw[i - 1].kind() == crate::SyntaxKind::NUMBER;
                if !preceded_by_number {
                    let range = t.text_range();
                    let start: u32 = range.start().into();
                    let end: u32 = range.end().into();
                    let span =
                        Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
                    out.push(crate::ParseError::new(
                        crate::ParseErrorKind::SyntaxError(
                            "bare currency literal is not a valid custom directive value"
                                .to_string(),
                        ),
                        span,
                    ));
                }
            }
            i += 1;
        }
    }
    out
}

/// Walk each `TRANSACTION` and emit a `SyntaxError` for any body
/// line that contains flat catch-all tokens (e.g., an
/// unrecognized identifier where a posting was expected).
/// Matches the legacy parser, which fails its inner posting
/// parser on such lines and recovers by skipping to the next
/// NEWLINE while emitting a `SyntaxError`.
fn extract_transaction_body_errors(
    source_file: &SourceFile,
    bom_offset: u32,
) -> Vec<crate::ParseError> {
    let mut out = Vec::new();
    for child in source_file.syntax().children() {
        if child.kind() != crate::SyntaxKind::TRANSACTION {
            continue;
        }
        // Skip past the header NEWLINE, then look for catch-all
        // tokens (non-trivia, non-comment) appearing on lines
        // OUTSIDE POSTING / META_ENTRY child nodes.
        // Track whether we've SEEN at least one non-trivia
        // header token (DATE / flag / STRING / etc.); only AFTER
        // that does the next NEWLINE count as the header
        // terminator. Otherwise leading-trivia NEWLINEs from the
        // Directive-Terminator Rule would falsely trip
        // past_header on the very first iteration.
        let mut past_header = false;
        let mut saw_header_content = false;
        let mut line_start: Option<u32> = None;
        let mut line_has_content = false;
        for el in child.children_with_tokens() {
            match el {
                rowan::NodeOrToken::Token(t) => {
                    if !past_header {
                        if t.kind() == crate::SyntaxKind::NEWLINE {
                            if saw_header_content {
                                past_header = true;
                            }
                        } else if !is_trivia_kind(t.kind()) {
                            saw_header_content = true;
                        }
                        continue;
                    }
                    let range = t.text_range();
                    let start: u32 = range.start().into();
                    let end: u32 = range.end().into();
                    if line_start.is_none() {
                        line_start = Some(start);
                    }
                    if t.kind() == crate::SyntaxKind::NEWLINE {
                        if line_has_content && let Some(ls) = line_start {
                            // Skip leading WHITESPACE in the span.
                            let span =
                                Span::new((ls + bom_offset) as usize, (end + bom_offset) as usize);
                            // Find first non-whitespace position
                            // for a tighter span matching legacy.
                            out.push(crate::ParseError::new(
                                crate::ParseErrorKind::SyntaxError("unexpected input".to_string()),
                                span,
                            ));
                        }
                        line_start = None;
                        line_has_content = false;
                    } else if !is_trivia_kind(t.kind())
                        && !is_comment_kind(t.kind())
                        && !matches!(t.kind(), crate::SyntaxKind::TAG | crate::SyntaxKind::LINK)
                    {
                        // TAG / LINK on body lines is valid
                        // Beancount syntax (tags/links after the
                        // first line continue the transaction's
                        // tag/link list). Don't flag as
                        // unexpected-input.
                        line_has_content = true;
                    }
                }
                rowan::NodeOrToken::Node(_) => {
                    // POSTING / META_ENTRY: not catch-all. Reset.
                    line_start = None;
                    line_has_content = false;
                    if !past_header {
                        past_header = true;
                    }
                }
            }
        }
    }
    out
}

/// Walk `ERROR_NODE` children of `SOURCE_FILE` and emit a
/// `ParseError` for each line that is NEITHER a section marker
/// (`*`-starting) NOR a column-0 comment. The variant emitted
/// mirrors the legacy parser's error-recovery classifier
/// (`parser.rs:2186-2249`): BOM-in-line → `BomInDirectiveBody`
/// (with `BOM_REMOVAL_HINT`); Unicode-character account →
/// `InvalidAccount`; otherwise → `SyntaxError("unexpected
/// input")`. `stripped` is the post-BOM-strip source so token
/// `text_range` indices into it correctly.
fn extract_error_node_errors(
    source_file: &SourceFile,
    stripped: &str,
    bom_offset: u32,
) -> Vec<crate::ParseError> {
    let mut out = Vec::new();
    for child in source_file.syntax().children() {
        if child.kind() != crate::SyntaxKind::ERROR_NODE {
            continue;
        }
        let mut line_start: Option<u32> = None;
        let mut first_non_trivia: Option<crate::SyntaxKind> = None;
        for el in child.children_with_tokens() {
            let rowan::NodeOrToken::Token(t) = el else {
                continue;
            };
            let range = t.text_range();
            let start: u32 = range.start().into();
            let end: u32 = range.end().into();
            if line_start.is_none() {
                line_start = Some(start);
            }
            if t.kind() == crate::SyntaxKind::NEWLINE {
                // Decide the line's classification.
                let is_section = matches!(first_non_trivia, Some(crate::SyntaxKind::STAR));
                let is_comment = matches!(first_non_trivia, Some(k) if is_comment_kind(k));
                if !is_section
                    && !is_comment
                    && first_non_trivia.is_some()
                    && let Some(ls) = line_start
                {
                    // Legacy span INCLUDES the terminator NEWLINE
                    // (skip_to_newline consumes it before
                    // span_from is called).
                    let span = Span::new((ls + bom_offset) as usize, (end + bom_offset) as usize);
                    let line_text = stripped.get(ls as usize..end as usize).unwrap_or("");
                    let primary = classify_recovery_error(line_text, span);
                    let primary_is_bom =
                        matches!(primary.kind, crate::ParseErrorKind::BomInDirectiveBody);
                    out.push(primary);
                    // Additive secondary `BomInDirectiveBody` when
                    // a different primary diagnostic (Unicode
                    // account / generic syntax) already fired AND
                    // the line ALSO contains a BOM byte. Matches
                    // legacy `parser.rs:2258-2263`: without this,
                    // a Windows-exported line with both problems
                    // surfaces only the actionable root cause and
                    // the user has no clue the invisible BOM byte
                    // is also corrupting the line.
                    if !primary_is_bom && line_text.contains(crate::bom::BOM_CHAR) {
                        out.push(
                            crate::ParseError::new(crate::ParseErrorKind::BomInDirectiveBody, span)
                                .with_hint(crate::diagnostics::BOM_REMOVAL_HINT),
                        );
                    }
                }
                line_start = None;
                first_non_trivia = None;
                continue;
            }
            if first_non_trivia.is_none() && !is_trivia_kind(t.kind()) {
                first_non_trivia = Some(t.kind());
            }
        }
    }
    out
}

/// Pick the most specific `ParseError` variant for an
/// error-recovery line, mirroring the legacy parser's classifier
/// at `parser.rs:2186-2249`:
/// 1. A Unicode-character account (`Assets:Café:…`) → primary
///    `InvalidAccount` - it's the actionable root cause.
/// 2. A mid-file BOM byte (`U+FEFF`) → `BomInDirectiveBody` with
///    `BOM_REMOVAL_HINT` so miette surfaces the remediation step.
/// 3. Anything else → `SyntaxError("unexpected input")`.
///
/// Order matters: a Windows-exported file with a Unicode account
/// AND an internal BOM gets the Unicode-account diagnostic
/// (the BOM is usually a side effect, not the root cause).
fn classify_recovery_error(line_text: &str, span: Span) -> crate::ParseError {
    if let Some(account) = crate::diagnostics::find_unicode_account(line_text) {
        return crate::ParseError::new(
            crate::ParseErrorKind::InvalidAccount(account.to_string()),
            span,
        );
    }
    if line_text.contains(crate::bom::BOM_CHAR) {
        return crate::ParseError::new(crate::ParseErrorKind::BomInDirectiveBody, span)
            .with_hint(crate::diagnostics::BOM_REMOVAL_HINT);
    }
    crate::ParseError::new(
        crate::ParseErrorKind::SyntaxError("unexpected input".to_string()),
        span,
    )
}

/// Walk every descendant token and emit a `ParseError` for each
/// `ERROR_TOKEN` (or BOM-containing token) that lands inside an
/// otherwise-valid directive node - i.e., NOT inside an
/// `ERROR_NODE` ancestor. Catches lexer-reject bytes the
/// outer recovery path misses:
/// - `.` in `.50 USD` (leading-decimal in posting amount) →
///   `SyntaxError`.
/// - Mid-file U+FEFF byte inside a recognized directive (e.g.,
///   `open Assets:Bank \u{FEFF}USD`) → `BomInDirectiveBody` with
///   `BOM_REMOVAL_HINT`.
///
/// The leading `SyntaxKind::BOM` token is skipped (the
/// legitimate strict-byte-0 BOM is already tracked by
/// `has_leading_bom`). `ERROR_NODE` descendants are skipped -
/// `extract_error_node_errors` / `classify_recovery_error`
/// already cover those.
/// Result of the fused descendants-walk visitor that powers
/// `walk_descendants_once`.
struct DescendantsWalkResult {
    inline_errors: Vec<crate::ParseError>,
    top_level_comments: Vec<Spanned<String>>,
    currency_occurrences: Vec<Spanned<Currency>>,
    account_occurrences: Vec<Spanned<rustledger_core::Account>>,
}

/// Fused single-pass visitor over `source_file`'s descendants -
/// replaces three separate walks (`extract_inline_token_errors`,
/// `extract_top_level_comments`, `extract_currency_occurrences`)
/// with one traversal. Each walk had its own per-token cost; the
/// LSP runs them on every keystroke, so collapsing 3·O(N) → 1·O(N)
/// matters at editor-edge latencies. The state of each former
/// walk is maintained inline below.
fn walk_descendants_once(source_file: &SourceFile, bom_offset: u32) -> DescendantsWalkResult {
    let mut inline_errors: Vec<crate::ParseError> = Vec::new();
    let mut top_level_comments: Vec<Spanned<String>> = Vec::new();
    let mut currency_occurrences: Vec<Spanned<Currency>> = Vec::new();
    let mut account_occurrences: Vec<Spanned<rustledger_core::Account>> = Vec::new();

    // `extract_top_level_comments` state: column-0 tracking.
    let mut preceded_by_ws = false;

    for el in source_file.syntax().descendants_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            // `extract_top_level_comments` used the Node arm to
            // reset preceded_by_ws when entering a recognized
            // directive. Keep that behavior - directive leading
            // trivia still gets column-0-classified correctly.
            if let rowan::NodeOrToken::Node(n) = el
                && ast::Directive::can_cast(n.kind())
            {
                preceded_by_ws = false;
            }
            continue;
        };

        // ---- `extract_top_level_comments` state machine -------
        match t.kind() {
            crate::SyntaxKind::NEWLINE => preceded_by_ws = false,
            crate::SyntaxKind::WHITESPACE => preceded_by_ws = true,
            k if is_comment_kind(k) => {
                if !preceded_by_ws {
                    let range = t.text_range();
                    let start: u32 = range.start().into();
                    let end: u32 = range.end().into();
                    let span =
                        Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
                    top_level_comments.push(Spanned::new(t.text().to_string(), span));
                }
            }
            _ => {
                preceded_by_ws = false;
            }
        }

        // ---- `extract_inline_token_errors` + currency walks ---
        if t.kind() == crate::SyntaxKind::BOM {
            continue;
        }
        // ERROR_NODE-ancestor check is only consulted for tokens
        // whose downstream emission depends on it (CURRENCY, BOM-
        // text-containing, ERROR_TOKEN). For well-formed source
        // most tokens fall into none of those buckets - gating
        // the per-token `parent_ancestors` walk on relevance
        // saves an O(depth) probe per WHITESPACE/NEWLINE/comment
        // token, which dominates token counts in real ledgers.
        let kind = t.kind();
        let has_bom = t.text().contains(crate::bom::BOM_CHAR);
        let is_error_token = kind == crate::SyntaxKind::ERROR_TOKEN;
        let needs_in_error_check = matches!(
            kind,
            crate::SyntaxKind::CURRENCY | crate::SyntaxKind::ACCOUNT
        ) || has_bom
            || is_error_token;
        if !needs_in_error_check {
            continue;
        }
        let in_error_node = t
            .parent_ancestors()
            .any(|a| a.kind() == crate::SyntaxKind::ERROR_NODE);

        // CURRENCY occurrences: only outside ERROR_NODE.
        if kind == crate::SyntaxKind::CURRENCY && !in_error_node {
            let range = t.text_range();
            let start: u32 = range.start().into();
            let end: u32 = range.end().into();
            let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
            currency_occurrences.push(Spanned::new(Currency::new(t.text()), span));
        }

        // ACCOUNT occurrences: only outside ERROR_NODE. The same
        // rationale as CURRENCY applies - the lexer classifies an
        // `ACCOUNT` token by its character shape independent of
        // whether the surrounding directive parses cleanly, and
        // source-position-aware tooling (LSP rename / references /
        // document-highlight) wants the token as the user typed it
        // even during a mid-edit broken state.
        if kind == crate::SyntaxKind::ACCOUNT && !in_error_node {
            let range = t.text_range();
            let start: u32 = range.start().into();
            let end: u32 = range.end().into();
            let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
            account_occurrences.push(Spanned::new(rustledger_core::Account::new(t.text()), span));
        }

        // Inline errors: BOM byte in a recognized directive
        // (-> BomInDirectiveBody + hint) or ERROR_TOKEN inside a
        // recognized directive (-> SyntaxError). Both skip when
        // already inside an ERROR_NODE (handled by the recovery
        // classifier).
        if (!has_bom && !is_error_token) || in_error_node {
            continue;
        }
        let range = t.text_range();
        let start: u32 = range.start().into();
        let end: u32 = range.end().into();
        let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
        if has_bom {
            inline_errors.push(
                crate::ParseError::new(crate::ParseErrorKind::BomInDirectiveBody, span)
                    .with_hint(crate::diagnostics::BOM_REMOVAL_HINT),
            );
        } else {
            inline_errors.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError("unexpected input".to_string()),
                span,
            ));
        }
    }

    DescendantsWalkResult {
        inline_errors,
        top_level_comments,
        currency_occurrences,
        account_occurrences,
    }
}

/// Emit empty-string comments for org-mode section-marker
/// lines (`* Heading`, `** Subheading`) inside `ERROR_NODE`
/// children. The legacy parser's `parse_entry` matches
/// `Token::Star` and emits `Comment(String::new(), line_span)`;
/// the structured CST wraps these lines in `ERROR_NODE`s so we
/// have to walk them and synthesize the same shape.
fn extract_section_marker_comments(
    source_file: &SourceFile,
    bom_offset: u32,
) -> Vec<Spanned<String>> {
    let mut out = Vec::new();
    for child in source_file.syntax().children() {
        if child.kind() != crate::SyntaxKind::ERROR_NODE {
            continue;
        }
        // Walk tokens line-by-line. A line starts at the start
        // of the first token after a NEWLINE (or at the node's
        // start) and ends at the next NEWLINE (inclusive).
        let mut line_start: Option<u32> = None;
        let mut first_non_trivia: Option<crate::SyntaxKind> = None;
        for el in child.children_with_tokens() {
            let rowan::NodeOrToken::Token(t) = el else {
                continue;
            };
            let range = t.text_range();
            let start: u32 = range.start().into();
            let end: u32 = range.end().into();
            if line_start.is_none() {
                line_start = Some(start);
            }
            if t.kind() == crate::SyntaxKind::NEWLINE {
                if first_non_trivia == Some(crate::SyntaxKind::STAR)
                    && let Some(ls) = line_start
                {
                    let span = Span::new((ls + bom_offset) as usize, (end + bom_offset) as usize);
                    out.push(Spanned::new(String::new(), span));
                }
                line_start = None;
                first_non_trivia = None;
                continue;
            }
            if first_non_trivia.is_none() && !is_trivia_kind(t.kind()) {
                first_non_trivia = Some(t.kind());
            }
        }
    }
    out
}

// `extract_top_level_comments` and `extract_currency_occurrences`
// are folded into `walk_descendants_once` above - see the
// comments there for the column-0 / ERROR_NODE-exclusion rules.

// ---- Token parsing helpers -------------------------------------

/// Parse a date token, accepting the same shapes as the legacy
/// parser: canonical `YYYY-MM-DD`, slash-separated `YYYY/M/D`,
/// and single-digit month/day. Returns `None` when the token
/// can't be turned into a real calendar date (invalid month,
/// invalid day for the given month, etc.).
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
    // Slow path: share legacy's normalizer so single-digit
    // month/day (`2024-1-15`, `2024-01-5`) and slash separators
    // are accepted everywhere the legacy parser accepts them.
    crate::diagnostics::normalize_date_str(text)
        .parse::<NaiveDate>()
        .ok()
}

/// Parse a directive's `DATE` token. On success returns the
/// `NaiveDate`; on a token whose calendar values don't form a
/// real date (`2024-13-01`, Feb 29 in a non-leap year) emits
/// `InvalidDateValue` with the legacy parser's human-readable
/// message and returns `None`. This mirrors
/// `parser.rs:181-182` so the CST and legacy parsers surface the
/// same diagnostics for malformed dates in directive position.
fn parse_directive_date(
    date_tok: &ast::Date,
    errors: &mut Vec<crate::ParseError>,
    bom_offset: u32,
) -> Option<NaiveDate> {
    let text = date_tok.text();
    if let Some(d) = parse_date_token(text) {
        return Some(d);
    }
    let range = date_tok.syntax().text_range();
    let start: u32 = range.start().into();
    let end: u32 = range.end().into();
    let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
    errors.push(crate::ParseError::new(
        crate::ParseErrorKind::InvalidDateValue(crate::diagnostics::describe_invalid_date(text)),
        span,
    ));
    None
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

/// Trivia kinds that don't count toward a span's start/end when
/// matching the legacy parser's span convention.
///
/// Covers WHITESPACE / NEWLINE plus EVERY comment-trivia kind
/// (`COMMENT`, `PERCENT_COMMENT`, `SHEBANG`, `EMACS_DIRECTIVE`)
/// so files with ledger-style `%` comments or org-mode
/// `#!`/`#+` lines have the same span/header-tracking behavior
/// as files with only `;` comments. Mirrors
/// `SyntaxKind::is_trivia()` minus `BOM` - a mid-file BOM byte
/// is an error to surface (`extract_inline_token_errors` /
/// `classify_recovery_error`), not trivia to silently skip.
const fn is_trivia_kind(kind: crate::SyntaxKind) -> bool {
    matches!(
        kind,
        crate::SyntaxKind::WHITESPACE
            | crate::SyntaxKind::NEWLINE
            | crate::SyntaxKind::COMMENT
            | crate::SyntaxKind::PERCENT_COMMENT
            | crate::SyntaxKind::SHEBANG
            | crate::SyntaxKind::EMACS_DIRECTIVE
    )
}

/// Span policy for `Posting`: the legacy parser ends the posting
/// span at the position just before the line's terminating
/// NEWLINE. The CST node's range INCLUDES the terminator
/// NEWLINE; trim it by using the NEWLINE token's start position.
/// We look at the FIRST direct-child NEWLINE token because
/// posting-attached metadata sub-lines (which have their own
/// inner NEWLINEs) come after the line terminator and shouldn't
/// extend the posting-line span.
fn posting_span(node: &crate::SyntaxNode, bom_offset: u32) -> Span {
    let range = node.text_range();
    let start: u32 = range.start().into();
    let end_raw: u32 = range.end().into();
    // Postings have no inter-directive leading trivia: their
    // first direct-child NEWLINE IS the terminator.
    let end = node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .find(|t| t.kind() == crate::SyntaxKind::NEWLINE)
        .map_or(end_raw, |t| u32::from(t.text_range().start()));
    Span::new((start + bom_offset) as usize, (end + bom_offset) as usize)
}

/// Span policy for non-Directive single-line constructs that
/// participate in inter-directive trivia attachment (Option,
/// Include, Plugin). Unlike Posting these may have leading
/// trivia (blank-line NEWLINEs, comments) inside the node from
/// the Directive-Terminator Rule. Start at the first non-trivia
/// content token; end at the first NEWLINE after that.
fn single_line_directive_span(node: &crate::SyntaxNode, bom_offset: u32) -> Span {
    let range = node.text_range();
    let start_raw: u32 = range.start().into();
    let end_raw: u32 = range.end().into();
    let mut content_start: Option<u32> = None;
    let mut terminator: Option<u32> = None;
    for t in node
        .children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
    {
        if content_start.is_none() {
            if !is_trivia_kind(t.kind()) {
                content_start = Some(u32::from(t.text_range().start()));
            }
        } else if t.kind() == crate::SyntaxKind::NEWLINE {
            terminator = Some(u32::from(t.text_range().start()));
            break;
        }
    }
    let start = content_start.unwrap_or(start_raw);
    let end = terminator.unwrap_or(end_raw);
    Span::new((start + bom_offset) as usize, (end + bom_offset) as usize)
}

/// Span policy for top-level directives: legacy directives start
/// at the first content character (skipping leading trivia from
/// the Directive-Terminator Rule) and extend through any
/// inter-directive trivia up to where the NEXT directive begins.
/// Computed in a post-pass since each directive's end depends on
/// the next one's start.
fn fixup_directive_spans(
    source_file: &SourceFile,
    bom_offset: u32,
    converted_nodes: &[crate::SyntaxNode],
    directives: &mut [Spanned<Directive>],
) {
    debug_assert_eq!(
        converted_nodes.len(),
        directives.len(),
        "converted_nodes and directives must be parallel arrays"
    );

    // Walk EVERY top-level Directive-castable child (including
    // pushtag/poptag/pushmeta/popmeta that we filter out of the
    // ParseResult) so the "next directive's start" boundary used
    // for span end-fixup matches the legacy parser: there, each
    // visible directive's span ends at the next /input/
    // directive's start, regardless of whether that next
    // directive is preserved.
    let all_starts: Vec<(usize, usize)> = source_file
        .syntax()
        .children()
        .filter(|n| ast::Directive::can_cast(n.kind()))
        .map(|n| {
            let raw_start: u32 = n.text_range().start().into();
            let content_start = n
                .descendants_with_tokens()
                .filter_map(rowan::NodeOrToken::into_token)
                .find(|t| !is_trivia_kind(t.kind()))
                .map_or_else(
                    || (raw_start + bom_offset) as usize,
                    |t| (u32::from(t.text_range().start()) + bom_offset) as usize,
                );
            ((raw_start + bom_offset) as usize, content_start)
        })
        .collect();

    let source_end: usize =
        (u32::from(source_file.syntax().text_range().end()) + bom_offset) as usize;

    // For each converted directive, find its position in the all
    // list by raw_start (which is unique per CST node), then use
    // the NEXT all_starts content_start as its span end.
    //
    // INVARIANT: every node in `converted_nodes` was yielded by
    // `source_file.directives()`, which is the same iteration
    // `all_starts` filters from. So `position` always succeeds in
    // well-formed input. Falling back to the node's own
    // `text_range` rather than panicking keeps the parser usable
    // when a future change to the typed-AST surface ever de-syncs
    // those two enumerations - a `panic!()` reachable from user
    // input is a `#![forbid(unsafe_code)]`-class regression for an
    // LSP/WASM consumer.
    for (i, spanned) in directives.iter_mut().enumerate() {
        let node = &converted_nodes[i];
        let raw_start: usize = (u32::from(node.text_range().start()) + bom_offset) as usize;
        let node_end: usize = (u32::from(node.text_range().end()) + bom_offset) as usize;
        if let Some(pos) = all_starts.iter().position(|(rs, _)| *rs == raw_start) {
            let start = all_starts[pos].1;
            let end = all_starts
                .get(pos + 1)
                .map_or(source_end, |(_, content)| *content);
            spanned.span = Span::new(start, end);
        } else {
            // Defensive fallback: match the success-path
            // convention by also trimming leading trivia. Without
            // this trim the fallback span would underline blank
            // lines / column-0 comments above the directive when
            // LSP/miette renders the diagnostic, even though the
            // directive itself starts further down.
            let content_start = node
                .descendants_with_tokens()
                .filter_map(rowan::NodeOrToken::into_token)
                .find(|t| !is_trivia_kind(t.kind()))
                .map_or(raw_start, |t| {
                    (u32::from(t.text_range().start()) + bom_offset) as usize
                });
            spanned.span = Span::new(content_start, node_end);
        }
    }
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
        // tags/links currently unimplemented - pin as empty.
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

    #[test]
    fn custom_directive_basic() {
        let src = "2024-01-01 custom \"budget\" \"food\" 500 USD\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Custom(c) = &result.directives[0].value else {
            panic!("expected Custom");
        };
        assert_eq!(c.custom_type, "budget");
        assert_eq!(c.values.len(), 2);
        assert_eq!(c.values[0], MetaValue::String("food".to_string()));
        // 500 USD becomes an Amount (NUMBER + CURRENCY adjacent).
        let MetaValue::Amount(amt) = &c.values[1] else {
            panic!("expected Amount, got {:?}", c.values[1]);
        };
        assert_eq!(amt.number, Decimal::from(500));
        assert_eq!(amt.currency.as_str(), "USD");
    }

    #[test]
    fn custom_directive_heterogeneous_values() {
        let src = "2024-01-01 custom \"test\" Assets:Cash TRUE 42 2024-06-15\n";
        let result = parse_via_cst(src);
        let Directive::Custom(c) = &result.directives[0].value else {
            panic!("expected Custom");
        };
        assert_eq!(c.values.len(), 4);
        assert!(matches!(c.values[0], MetaValue::Account(_)));
        assert_eq!(c.values[1], MetaValue::Bool(true));
        assert_eq!(c.values[2], MetaValue::Number(Decimal::from(42)));
        assert!(matches!(c.values[3], MetaValue::Date(_)));
    }

    #[test]
    fn option_directive_populates_options_field() {
        let src = "option \"title\" \"My Ledger\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 0);
        assert_eq!(result.options.len(), 1);
        assert_eq!(result.options[0].0, "title");
        assert_eq!(result.options[0].1, "My Ledger");
    }

    #[test]
    fn include_directive_populates_includes_field() {
        let src = "include \"shared.beancount\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 0);
        assert_eq!(result.includes.len(), 1);
        assert_eq!(result.includes[0].0, "shared.beancount");
    }

    #[test]
    fn plugin_directive_with_config() {
        let src = "plugin \"my.plugin\" \"cfg\"\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 0);
        assert_eq!(result.plugins.len(), 1);
        assert_eq!(result.plugins[0].0, "my.plugin");
        assert_eq!(result.plugins[0].1.as_deref(), Some("cfg"));
    }

    #[test]
    fn plugin_directive_without_config() {
        let src = "plugin \"my.plugin\"\n";
        let result = parse_via_cst(src);
        assert_eq!(result.plugins.len(), 1);
        assert_eq!(result.plugins[0].0, "my.plugin");
        assert!(result.plugins[0].1.is_none());
    }

    // ---- Transaction converter tests ------------------------------

    #[test]
    fn transaction_basic_two_postings() {
        let src = "2024-01-15 * \"Coffee Shop\" \"Morning coffee\"\n  \
                   Expenses:Food:Coffee  5.00 USD\n  \
                   Assets:Cash\n";
        let result = parse_via_cst(src);
        assert_directive_count(&result, 1);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(t.date, naive_date(2024, 1, 15).unwrap());
        assert_eq!(t.flag, '*');
        assert_eq!(
            t.payee.as_ref().map(InternedStr::as_str),
            Some("Coffee Shop")
        );
        assert_eq!(t.narration.as_str(), "Morning coffee");
        assert_eq!(t.postings.len(), 2);

        let p0 = &t.postings[0].value;
        assert_eq!(p0.account.as_str(), "Expenses:Food:Coffee");
        let Some(IncompleteAmount::Complete(amt)) = &p0.units else {
            panic!("expected complete units, got {:?}", p0.units);
        };
        assert_eq!(amt.number, Decimal::new(500, 2));
        assert_eq!(amt.currency.as_str(), "USD");

        let p1 = &t.postings[1].value;
        assert_eq!(p1.account.as_str(), "Assets:Cash");
        assert!(p1.units.is_none(), "auto-posting has no units");
    }

    #[test]
    fn transaction_narration_only_no_payee() {
        let src = "2024-01-15 ! \"Pending\"\n  Assets:Cash  -5 USD\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(t.flag, '!');
        assert!(t.payee.is_none());
        assert_eq!(t.narration.as_str(), "Pending");
    }

    #[test]
    fn transaction_implied_flag_via_leading_string() {
        let src = "2024-01-15 \"Implied\"\n  Assets:Cash  -5 USD\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(t.flag, '*', "implied flag defaults to *");
    }

    #[test]
    fn transaction_with_tags_and_links() {
        let src = "2024-01-15 * \"Coffee\" #daily ^trip1\n  Assets:Cash  -5 USD\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(t.tags.len(), 1);
        assert_eq!(t.tags[0].as_str(), "daily");
        assert_eq!(t.links.len(), 1);
        assert_eq!(t.links[0].as_str(), "trip1");
    }

    #[test]
    fn transaction_with_signed_amount() {
        let src = "2024-01-15 * \"x\"\n  Assets:Cash  -5.00 USD\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let Some(IncompleteAmount::Complete(amt)) = &t.postings[0].value.units else {
            panic!("expected complete units");
        };
        assert_eq!(amt.number, Decimal::new(-500, 2));
    }

    #[test]
    fn transaction_with_posting_flag() {
        let src = "2024-01-15 * \"x\"\n  ! Assets:Cash  -5 USD\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(t.postings[0].value.flag, Some('!'));
    }

    #[test]
    fn transaction_with_cost_spec_per_unit() {
        let src = "2024-01-15 * \"buy\"\n  \
                   Assets:Inv  10 HOOL {500.00 USD}\n  \
                   Assets:Cash\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let cost = t.postings[0].value.cost.as_ref().expect("cost spec");
        assert!(!cost.merge);
        let Some(CostNumber::PerUnit { value }) = &cost.number else {
            panic!("expected PerUnit");
        };
        assert_eq!(*value, Decimal::new(50000, 2));
        assert_eq!(cost.currency.as_ref().unwrap().as_str(), "USD");
    }

    #[test]
    fn transaction_with_cost_spec_total() {
        let src = "2024-01-15 * \"buy\"\n  \
                   Assets:Inv  10 HOOL {{5000 USD}}\n  \
                   Assets:Cash\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let cost = t.postings[0].value.cost.as_ref().expect("cost spec");
        let Some(CostNumber::Total { value }) = &cost.number else {
            panic!("expected Total");
        };
        assert_eq!(*value, Decimal::from(5000));
    }

    #[test]
    fn transaction_with_price_annotation_unit() {
        let src = "2024-01-15 * \"buy\"\n  \
                   Assets:Inv  10 HOOL @ 510 USD\n  \
                   Assets:Cash\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let price = t.postings[0]
            .value
            .price
            .as_ref()
            .expect("price annotation");
        assert!(price.is_unit());
        let Some(IncompleteAmount::Complete(amt)) = &price.amount else {
            panic!("expected complete price amount");
        };
        assert_eq!(amt.number, Decimal::from(510));
        assert_eq!(amt.currency.as_str(), "USD");
    }

    #[test]
    fn transaction_with_price_annotation_total() {
        let src = "2024-01-15 * \"buy\"\n  \
                   Assets:Inv  10 HOOL @@ 5100 USD\n  \
                   Assets:Cash\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let price = t.postings[0]
            .value
            .price
            .as_ref()
            .expect("price annotation");
        assert!(!price.is_unit(), "@@ is total form");
    }

    // ---- regression tests for review findings (#1281) ----------

    #[test]
    fn document_directive_preserves_tags_and_links() {
        // Finding 1: convert_document was filling tags/links empty
        // unconditionally. Legacy parse_document_directive collects
        // trailing `#tag` / `^link` tokens after the path STRING.
        let src = "2024-06-01 document Assets:Bank \"stmt.pdf\" #quarter1 ^scan42 #urgent\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Document(doc) = &result.directives[0].value else {
            panic!("expected Document");
        };
        let tags: Vec<&str> = doc.tags.iter().map(Tag::as_str).collect();
        let links: Vec<&str> = doc.links.iter().map(Link::as_str).collect();
        assert_eq!(tags, vec!["quarter1", "urgent"]);
        assert_eq!(links, vec!["scan42"]);
    }

    #[test]
    fn open_directive_rejects_invalid_booking_method() {
        // Finding 2: convert_open accepted any booking string; legacy
        // validates against [FIFO, STRICT, STRICT_WITH_SIZE, LIFO,
        // HIFO, NONE, AVERAGE] and on mismatch drops the directive
        // AND emits InvalidBookingMethod.
        let src = "2024-01-01 open Assets:Bank USD \"GARBAGE\"\n";
        let result = parse_via_cst(src);
        assert_eq!(result.directives.len(), 0, "directive should be dropped");
        assert_eq!(result.errors.len(), 1);
        let err = &result.errors[0];
        assert!(
            matches!(
                &err.kind,
                crate::ParseErrorKind::InvalidBookingMethod(s) if s == "GARBAGE"
            ),
            "expected InvalidBookingMethod, got {:?}",
            err.kind,
        );
    }

    #[test]
    fn open_directive_accepts_all_valid_booking_methods() {
        for method in VALID_BOOKING_METHODS {
            let src = format!("2024-01-01 open Assets:Bank USD \"{method}\"\n");
            let result = parse_via_cst(&src);
            assert!(
                result.errors.is_empty(),
                "{method} rejected: {:?}",
                result.errors
            );
            let Directive::Open(open) = &result.directives[0].value else {
                panic!("{method}: expected Open");
            };
            assert_eq!(open.booking.as_deref(), Some(*method));
        }
    }

    #[test]
    fn unclosed_pushtag_at_eof_emits_diagnostic() {
        // Finding 3: legacy emits one UnclosedPushtag per leftover
        // tag at EOF, pointing at the originating push directive.
        let src = "pushtag #active\n2024-01-01 open Assets:Bank USD\n";
        let result = parse_via_cst(src);
        let unclosed: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::UnclosedPushtag(t) => Some(t.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(unclosed, vec!["active".to_string()]);
    }

    #[test]
    fn unclosed_pushmeta_at_eof_emits_diagnostic() {
        // Finding 4: same as pushtag, for pushmeta.
        let src = "pushmeta location: \"NYC\"\n2024-01-01 open Assets:Bank USD\n";
        let result = parse_via_cst(src);
        let unclosed: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::UnclosedPushmeta(k) => Some(k.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(unclosed, vec!["location".to_string()]);
    }

    #[test]
    fn invalid_poptag_on_mismatch_emits_diagnostic() {
        // Finding 5: poptag for a tag never pushed should error,
        // not silently no-op.
        let src = "pushtag #foo\npoptag #bar\npoptag #foo\n";
        let result = parse_via_cst(src);
        let mismatches: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::InvalidPoptag(t) => Some(t.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(mismatches, vec!["bar".to_string()]);
        // and the matching #foo poptag should leave NO unclosed
        // diagnostic - i.e. the stack is empty after the matched pop.
        let leftover: Vec<_> = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, crate::ParseErrorKind::UnclosedPushtag(_)))
            .collect();
        assert!(leftover.is_empty(), "unexpected leftover: {leftover:?}");
    }

    #[test]
    fn invalid_popmeta_on_mismatch_emits_diagnostic() {
        // Finding 6: popmeta for a key never pushed should error,
        // not silently no-op. Also checks Vec-stack shadow semantics:
        // pushmeta x: 1; pushmeta x: 2; popmeta x leaves x=1 active.
        let src = "pushmeta location: \"NYC\"\npopmeta nope:\npopmeta location:\n";
        let result = parse_via_cst(src);
        let mismatches: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::InvalidPopmeta(k) => Some(k.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(mismatches, vec!["nope".to_string()]);
        let leftover: Vec<_> = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, crate::ParseErrorKind::UnclosedPushmeta(_)))
            .collect();
        assert!(leftover.is_empty(), "unexpected leftover: {leftover:?}");
    }

    #[test]
    fn pushmeta_shadow_pop_restores_prior_value() {
        // Vec-stack semantics (the reason meta_stack isn't a HashMap):
        // shadow-pop must restore the prior value, not delete the key.
        let src = "pushmeta loc: \"NYC\"\n\
                   pushmeta loc: \"LDN\"\n\
                   popmeta loc:\n\
                   2024-01-01 open Assets:Bank USD\n\
                   popmeta loc:\n";
        let result = parse_via_cst(src);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("expected Open");
        };
        assert_eq!(
            open.meta.get("loc"),
            Some(&MetaValue::String("NYC".to_string())),
            "shadow pop should restore NYC, got {:?}",
            open.meta.get("loc"),
        );
    }

    #[test]
    fn error_recovery_classifies_bom_in_directive_body() {
        // Finding 7: error-recovery path should distinguish BOM-in-
        // line from a generic SyntaxError so users see the
        // BOM-removal hint instead of "unexpected input".
        let src = "garbage\u{FEFF}content\n";
        let result = parse_via_cst(src);
        let bom_errors: Vec<_> = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, crate::ParseErrorKind::BomInDirectiveBody))
            .collect();
        assert_eq!(bom_errors.len(), 1, "errors: {:?}", result.errors);
        assert!(
            bom_errors[0].hint.is_some(),
            "BomInDirectiveBody should carry BOM_REMOVAL_HINT",
        );
    }

    #[test]
    fn error_recovery_emits_both_invalid_account_and_bom_for_dual_line() {
        // Round-2 finding: legacy `parser.rs:2258-2263` emits a
        // SECONDARY `BomInDirectiveBody` whenever the line ALSO
        // contains a BOM byte and the primary diagnostic isn't
        // BOM itself. Without this, a Windows-exported file with
        // a Unicode account AND an internal BOM loses the BOM
        // hint entirely.
        let src = "garbage Assets:Café\u{FEFF}content\n";
        let result = parse_via_cst(src);
        let invalid_account_count = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, crate::ParseErrorKind::InvalidAccount(_)))
            .count();
        let bom_count = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, crate::ParseErrorKind::BomInDirectiveBody))
            .count();
        assert_eq!(
            invalid_account_count, 1,
            "expected one InvalidAccount: {:?}",
            result.errors
        );
        assert_eq!(
            bom_count, 1,
            "expected secondary BomInDirectiveBody: {:?}",
            result.errors
        );
        // The secondary BOM diagnostic must carry the hint so
        // miette renders the remediation step.
        let bom_err = result
            .errors
            .iter()
            .find(|e| matches!(e.kind, crate::ParseErrorKind::BomInDirectiveBody))
            .unwrap();
        assert!(bom_err.hint.is_some());
    }

    #[test]
    fn error_recovery_classifies_unicode_account() {
        // Finding 7: a Unicode-character account name (Assets:Café)
        // should surface as InvalidAccount, not generic SyntaxError.
        // We embed it in a malformed line so the parser routes to
        // the error-recovery path.
        let src = "garbage Assets:Café content\n";
        let result = parse_via_cst(src);
        let unicode_errors: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::InvalidAccount(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(unicode_errors, vec!["Assets:Café".to_string()]);
    }

    #[test]
    fn transaction_with_pipe_emits_deprecated_pipe_symbol() {
        // Finding 7 (transaction path): legacy emits
        // DeprecatedPipeSymbol when a `|` separates payee/narration.
        let src = "2024-01-15 * \"Acme\" | \"invoice\"\n  Assets:Cash  -5 USD\n  Expenses:X\n";
        let result = parse_via_cst(src);
        let pipe_count = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, crate::ParseErrorKind::DeprecatedPipeSymbol))
            .count();
        assert_eq!(pipe_count, 1, "errors: {:?}", result.errors);
        // and the transaction itself is kept (legacy behavior).
        assert_eq!(result.directives.len(), 1);
    }

    #[test]
    fn transaction_trailing_comments_after_final_posting() {
        // Finding 8: comments that appear AFTER the last posting
        // but inside the transaction body belong to
        // Transaction::trailing_comments, not lost.
        let src = "2024-01-15 * \"x\"\n  \
                   Assets:Cash  -5 USD\n  \
                   Expenses:X\n  \
                   ; trailing one\n  \
                   ; trailing two\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(
            t.trailing_comments.len(),
            2,
            "got: {:?}",
            t.trailing_comments
        );
        assert!(t.trailing_comments[0].contains("trailing one"));
        assert!(t.trailing_comments[1].contains("trailing two"));
    }

    // ---- arithmetic AMOUNT evaluation (phase 3.7 flip blocker) -

    #[test]
    fn posting_amount_evaluates_division() {
        // Regression for `test_arithmetic_expressions_consistency`:
        // `120 / 3 USD` must evaluate to 40 USD so the transaction
        // balances. Without this the CST flip breaks every ledger
        // using arithmetic split syntax.
        let src = "2024-01-15 * \"split\"\n  \
                   Expenses:Food   120 / 3 USD\n  \
                   Assets:Bank    -40 USD\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let Some(IncompleteAmount::Complete(amt)) = &t.postings[0].value.units else {
            panic!("expected complete amount on posting 0");
        };
        assert_eq!(amt.number, Decimal::from(40));
        assert_eq!(amt.currency.as_str(), "USD");
    }

    #[test]
    fn posting_amount_evaluates_addition_and_multiplication_precedence() {
        // `2 + 3 * 4 USD` = 14 USD (standard precedence).
        let src = "2024-01-15 * \"x\"\n  \
                   Expenses:X   2 + 3 * 4 USD\n  \
                   Assets:Y   -14 USD\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let Some(IncompleteAmount::Complete(amt)) = &t.postings[0].value.units else {
            panic!("expected complete amount");
        };
        assert_eq!(amt.number, Decimal::from(14));
    }

    #[test]
    fn posting_amount_evaluates_parens_override_precedence() {
        // `(2 + 3) * 4 USD` = 20 USD.
        let src = "2024-01-15 * \"x\"\n  \
                   Expenses:X   (2 + 3) * 4 USD\n  \
                   Assets:Y   -20 USD\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let Some(IncompleteAmount::Complete(amt)) = &t.postings[0].value.units else {
            panic!("expected complete amount");
        };
        assert_eq!(amt.number, Decimal::from(20));
    }

    #[test]
    fn posting_amount_evaluates_subtraction_left_associative() {
        // `10 - 3 - 2 USD` = 5 USD (left-associative, not 9).
        let src = "2024-01-15 * \"x\"\n  \
                   Expenses:X   10 - 3 - 2 USD\n  \
                   Assets:Y   -5 USD\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let Some(IncompleteAmount::Complete(amt)) = &t.postings[0].value.units else {
            panic!("expected complete amount");
        };
        assert_eq!(amt.number, Decimal::from(5));
    }

    #[test]
    fn posting_amount_division_by_zero_drops_number() {
        // `5 / 0 USD` - legacy returns parse error; we return None
        // from the evaluator, which degrades to CurrencyOnly here.
        // The transaction won't balance and downstream validation
        // surfaces that as the user-facing error.
        let src = "2024-01-15 * \"x\"\n  \
                   Expenses:X   5 / 0 USD\n  \
                   Assets:Y\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        // Either the units degrade to CurrencyOnly (number lost)
        // or to None - both are acceptable since the input is
        // semantically invalid. The strict assertion is that we
        // DON'T silently return 5 (the first NUMBER) as the value.
        match &t.postings[0].value.units {
            None | Some(IncompleteAmount::CurrencyOnly(_)) => {}
            other => panic!("div-by-zero leaked: {other:?}"),
        }
    }

    // ---- round-8 final compat regressions (#1282 flip) ---------

    #[test]
    fn indented_top_level_directive_emits_error() {
        // A top-level directive that starts at column N>0 is a
        // syntax error per the Beancount spec; the CST grammar
        // accepts it silently, so the converter has to surface
        // the diagnostic at directive-content-start position.
        let src = "2020-07-28 open Assets:Foo\n  2020-07-28 open Assets:Bar\n";
        let result = parse_via_cst(src);
        let indent_errs = result
            .errors
            .iter()
            .filter(|e| match &e.kind {
                crate::ParseErrorKind::SyntaxError(s) => s.contains("column 0"),
                _ => false,
            })
            .count();
        assert_eq!(
            indent_errs, 1,
            "expected one column-0 diagnostic, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn indented_directive_after_blank_line_still_emits_error() {
        // Same as above but with a blank line between the
        // first directive and the indented one - the blank line
        // shouldn't mask the indentation error.
        let src = "2020-07-28 open Assets:Foo\n\n  2020-07-28 open Assets:Bar\n";
        let result = parse_via_cst(src);
        let indent_errs = result
            .errors
            .iter()
            .filter(|e| match &e.kind {
                crate::ParseErrorKind::SyntaxError(s) => s.contains("column 0"),
                _ => false,
            })
            .count();
        assert_eq!(indent_errs, 1, "errors: {:?}", result.errors);
    }

    #[test]
    fn top_level_directive_at_column_0_no_diagnostic() {
        // Sanity: well-formed top-level directives must NOT
        // trigger the indent diagnostic.
        let src = "2020-07-28 open Assets:Foo\n2020-07-28 open Assets:Bar\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn custom_directive_with_bare_currency_emits_error() {
        // `bean-check` rejects bare currency literals in custom
        // value position; the CST converter mirrors that.
        let src = "2025-01-01 custom \"x\" 10 USD \"y\" NZD\n";
        let result = parse_via_cst(src);
        let bare_curr_errs = result
            .errors
            .iter()
            .filter(|e| match &e.kind {
                crate::ParseErrorKind::SyntaxError(s) => s.contains("bare currency"),
                _ => false,
            })
            .count();
        assert_eq!(
            bare_curr_errs, 1,
            "expected one bare-currency diagnostic, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn custom_directive_with_amount_no_error() {
        // Sanity: `10 USD` (NUMBER + CURRENCY paired as Amount)
        // is a valid custom value and must NOT trigger the
        // bare-currency diagnostic.
        let src = "2025-01-01 custom \"x\" 10 USD\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    // ---- round-7 compat regressions (#1282 flip) ---------------

    #[test]
    fn balance_assertion_evaluates_arithmetic_value() {
        // PR #1282 compat regression: rledger emitted a balance
        // failure for `Assets:X  0.25+ 0.75 GBP` because only
        // the first NUMBER (0.25) was used as the assertion
        // target. CST converters for BALANCE/PRICE now evaluate
        // arithmetic the same way posting AMOUNTs do.
        let src = "2024-01-01 open Assets:X GBP\n\
                   2024-01-01 open Equity:Open GBP\n\
                   2024-01-02 * \"deposit\"\n  \
                   Assets:X         1.00 GBP\n  \
                   Equity:Open     -1.00 GBP\n\
                   2024-01-03 balance Assets:X  0.25 + 0.75 GBP\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let bal = result
            .directives
            .iter()
            .find_map(|d| match &d.value {
                Directive::Balance(b) => Some(b),
                _ => None,
            })
            .expect("expected a Balance directive");
        assert_eq!(bal.amount.number, Decimal::from(1));
        assert_eq!(bal.amount.currency.as_str(), "GBP");
    }

    #[test]
    fn price_directive_evaluates_arithmetic_value() {
        let src = "2024-01-01 price USD  1/2 EUR\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Price(p) = &result.directives[0].value else {
            panic!("expected Price");
        };
        assert_eq!(p.amount.number, Decimal::new(5, 1));
        assert_eq!(p.amount.currency.as_str(), "EUR");
    }

    // ---- round-5 architecture review (#1281) -------------------

    #[test]
    fn body_line_tag_does_not_drop_following_postings_comment() {
        // F2-bis: trailing TAG / LINK tokens on transaction body
        // lines are valid Beancount (extend the transaction's
        // tag/link set). Before the exemption was added, the
        // `pending.clear()` over-fired on the TAG and silently
        // dropped the preceding comment that semantically
        // belonged to the next posting.
        let src = "2024-01-01 * \"x\"\n  \
                   Assets:A   100 USD\n  \
                   ; comment-for-B\n  \
                   #late-tag\n  \
                   Assets:B   -100 USD\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        // The trailing tag joins the transaction's tag set.
        assert!(
            t.tags.iter().any(|tag| tag.as_str() == "late-tag"),
            "expected #late-tag in tags: {:?}",
            t.tags,
        );
        // And the comment survives - attached to the next posting.
        let b = t.postings.last().expect("at least one posting");
        assert_eq!(b.value.account.as_str(), "Assets:B");
        assert!(
            b.value.comments.iter().any(|c| c.contains("comment-for-B")),
            "expected comment-for-B to survive on Assets:B: {:?}",
            b.value.comments,
        );
    }

    #[test]
    fn oversized_number_in_amount_emits_diagnostic() {
        // F5-bis: the non-arithmetic NUMBER path is now symmetric
        // with the arithmetic-evaluation path. A NUMBER whose
        // text the lexer accepts but `Decimal::from_str` rejects
        // (e.g., 30+ digits, exceeding the 28-digit precision
        // ceiling) used to silently degrade to `CurrencyOnly`.
        let huge = "1".to_string() + &"2345678901234567890".repeat(2); // 39 digits
        let src = format!("2024-01-15 * \"big\"\n  Expenses:X   {huge} USD\n  Assets:Y\n");
        let result = parse_via_cst(&src);
        let invalid_num = result
            .errors
            .iter()
            .filter(|e| match &e.kind {
                crate::ParseErrorKind::SyntaxError(s) => s.contains("invalid number"),
                _ => false,
            })
            .count();
        assert_eq!(
            invalid_num, 1,
            "expected one invalid-number diagnostic, got: {:?}",
            result.errors
        );
    }

    // ---- round-4 architecture review (#1281) -------------------

    #[test]
    fn posting_with_two_amount_siblings_emits_error_and_keeps_first() {
        // F1: a posting like `Expenses:Food  5 USD + 3 USD` builds
        // two sibling AMOUNT nodes in the CST. `Posting::amount()`
        // only returns the first. Without an explicit guard the
        // second AMOUNT plus the joining `+` would be silently
        // dropped - the user's transaction would balance against
        // 5 USD instead of the intended 8 USD with no diagnostic.
        let src = "2024-01-15 * \"ambig\"\n  \
                   Expenses:Food   5 USD + 3 USD\n  \
                   Assets:Bank\n";
        let result = parse_via_cst(src);
        let trailing_count = result
            .errors
            .iter()
            .filter(|e| match &e.kind {
                crate::ParseErrorKind::SyntaxError(s) => s.contains("trailing tokens"),
                _ => false,
            })
            .count();
        assert_eq!(
            trailing_count, 1,
            "expected one trailing-tokens diagnostic, got: {:?}",
            result.errors
        );
        // The first AMOUNT is still surfaced so partial recovery
        // works for downstream tooling.
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        let Some(IncompleteAmount::Complete(amt)) = &t.postings[0].value.units else {
            panic!("expected complete units from the first AMOUNT");
        };
        assert_eq!(amt.number, Decimal::from(5));
    }

    #[test]
    fn comments_dont_leak_across_failed_posting() {
        // F2: when convert_posting returns None, the queue of
        // pending pre-posting comments must be CLEARED so they
        // don't migrate forward and attach to the next valid
        // posting. Without the clear, comments labelled for the
        // failed posting would silently re-attach to the wrong
        // account, visibly misleading the user.
        let src = "2024-01-15 * \"test\"\n  \
                   Assets:A   100 USD\n  \
                   ; comment-for-bad\n  \
                   ; another-comment\n  \
                   bogus_token_line_no_account\n  \
                   ; comment-for-good\n  \
                   Assets:B   -100 USD\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        // Assets:B is the LAST successful posting; the only
        // comment that should attach to it is the one that
        // immediately precedes it (`; comment-for-good`). The
        // pre-failed-posting comments belong to the failed
        // posting and should be DROPPED with it.
        let b = t.postings.last().expect("at least one posting");
        assert_eq!(b.value.account.as_str(), "Assets:B");
        assert!(
            !b.value
                .comments
                .iter()
                .any(|c| c.contains("comment-for-bad")),
            "comment-for-bad leaked across failed posting onto Assets:B: {:?}",
            b.value.comments
        );
        assert!(
            !b.value
                .comments
                .iter()
                .any(|c| c.contains("another-comment")),
            "another-comment leaked: {:?}",
            b.value.comments
        );
    }

    #[test]
    fn arithmetic_overflow_in_amount_emits_diagnostic() {
        // F5: when `is_arithmetic` is true but the evaluator
        // gives up (overflow, div-by-zero), the converter used
        // to silently produce CurrencyOnly. Now an explicit
        // SyntaxError fires so the user sees the actual root
        // cause instead of just a downstream "doesn't balance".
        // Decimal max is 28 digits - `9999999999999999999999999999 *
        // 9999999999999999999999999999` overflows.
        let huge = "9999999999999999999999999999 * 9999999999999999999999999999";
        let src = format!("2024-01-15 * \"big\"\n  Expenses:X   {huge} USD\n  Assets:Y\n");
        let result = parse_via_cst(&src);
        let arith_errs = result
            .errors
            .iter()
            .filter(|e| match &e.kind {
                crate::ParseErrorKind::SyntaxError(s) => s.contains("arithmetic"),
                _ => false,
            })
            .count();
        assert_eq!(
            arith_errs, 1,
            "expected one arithmetic-error diagnostic, got: {:?}",
            result.errors
        );
    }

    // ---- 14 emission-gap regressions (#1281 round-3 review) ----

    #[test]
    fn date_with_single_digit_month_parses() {
        let result = parse_via_cst("2024-1-15 open Assets:Checking\n");
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("expected Open");
        };
        assert_eq!(open.date, naive_date(2024, 1, 15).unwrap());
    }

    #[test]
    fn date_with_single_digit_day_parses() {
        let result = parse_via_cst("2024-01-5 open Assets:Cash USD\n");
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("expected Open");
        };
        assert_eq!(open.date, naive_date(2024, 1, 5).unwrap());
    }

    #[test]
    fn date_with_single_digit_month_and_day_parses() {
        let result = parse_via_cst("2024-1-1 open Assets:Cash USD\n");
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("expected Open");
        };
        assert_eq!(open.date, naive_date(2024, 1, 1).unwrap());
    }

    #[test]
    fn date_with_month_out_of_range_emits_invalid_date_value() {
        let result = parse_via_cst("2024-13-01 open Assets:Cash USD\n");
        let invalid_date: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::InvalidDateValue(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(invalid_date.len(), 1, "errors: {:?}", result.errors);
        let msg = &invalid_date[0];
        assert!(
            msg.contains("month") && msg.contains("out of range"),
            "msg: {msg}"
        );
    }

    #[test]
    fn date_with_invalid_leap_year_emits_invalid_date_value() {
        let result = parse_via_cst("2023-02-29 open Assets:Cash USD\n");
        let invalid_date: Vec<_> = result
            .errors
            .iter()
            .filter_map(|e| match &e.kind {
                crate::ParseErrorKind::InvalidDateValue(s) => Some(s.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(invalid_date.len(), 1, "errors: {:?}", result.errors);
        let msg = &invalid_date[0];
        assert!(
            msg.contains("day") && msg.contains("out of range") && msg.contains("2023-02"),
            "msg: {msg}"
        );
    }

    #[test]
    fn date_with_completely_invalid_value_still_emits_error() {
        // `2024-13-45` has BOTH month and day out of range; any
        // error variant satisfies the original integration test's
        // `!result.errors.is_empty()` assertion.
        let result = parse_via_cst("2024-13-45 open Assets:Bank\n");
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn open_directive_without_account_emits_error() {
        // `2024-01-01 open` with no account is rejected by legacy
        // via the top-level error-recovery path. CST emits the
        // catch-all `SyntaxError` from `parse_via_cst`'s
        // is_directive_producing/errors_before tracker.
        let result = parse_via_cst("2024-01-01 open\n");
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn open_directive_with_lowercase_account_emits_error() {
        // `lowercase:invalid` doesn't match the ACCOUNT regex
        // (uppercase first letter required), so the open directive
        // has no ACCOUNT child. Same catch-all path as the no-
        // account case.
        let result = parse_via_cst("2024-01-01 open lowercase:invalid\n");
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn incomplete_open_at_eof_emits_error() {
        // Regression for the PR #740 "incomplete-at-EOF" finding:
        // `2024-01-01 open` at EOF with no trailing newline must
        // not be silently dropped.
        let result = parse_via_cst("2024-01-01 open");
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn balance_directive_without_amount_emits_error() {
        let result = parse_via_cst("2024-01-15 balance Assets:Checking\n");
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn pad_directive_without_source_account_emits_error() {
        let result = parse_via_cst("2024-01-15 pad Assets:Checking\n");
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn cost_spec_n_hash_t_uses_total_form() {
        use rust_decimal_macros::dec;
        let src = "2024-01-01 open Assets:Stock\n\
                   2024-01-01 open Assets:Cash USD\n\
                   2024-01-15 *\n  \
                   Assets:Stock  10 STK {50 # 1500 USD}\n  \
                   Assets:Cash  -1500.00 USD\n";
        let result = parse_via_cst(src);
        assert!(result.errors.is_empty(), "errors: {:?}", result.errors);
        let Directive::Transaction(txn) = &result.directives[2].value else {
            panic!("expected Transaction at index 2");
        };
        let cost = txn.postings[0]
            .value
            .cost
            .as_ref()
            .expect("cost spec present");
        assert_eq!(
            cost.number,
            Some(CostNumber::Total { value: dec!(1500) }),
            "the `{{N # T CCY}}` form must store the post-`#` total"
        );
    }

    #[test]
    fn unclosed_cost_brace_emits_error() {
        let src = "2024-01-01 open Assets:Stock\n\
                   2024-01-01 open Assets:Cash USD\n\
                   2024-01-15 *\n  \
                   Assets:Stock 10 AAPL {150 USD\n  \
                   Assets:Cash -1500 USD\n";
        let result = parse_via_cst(src);
        let has_unclosed: bool = result
            .errors
            .iter()
            .any(|e| e.message().contains("unclosed cost"));
        assert!(
            has_unclosed,
            "expected 'unclosed cost' error, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn unclosed_cost_brace_at_eof_emits_error() {
        let src = "2024-01-01 open Assets:Stock\n\
                   2024-01-01 open Assets:Cash USD\n\
                   2024-01-15 *\n  \
                   Assets:Stock 10 AAPL {150 USD";
        let result = parse_via_cst(src);
        let has_unclosed: bool = result
            .errors
            .iter()
            .any(|e| e.message().contains("unclosed cost"));
        assert!(
            has_unclosed,
            "expected 'unclosed cost' error at EOF, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn leading_decimal_in_posting_amount_emits_error() {
        // `.50 USD` (no integer part before the decimal) must be
        // rejected by both parsers; valid `0.50 USD` still works
        // (covered by other tests).
        let src = "2024-01-15 * \"Test\"\n  \
                   Expenses:Food  .50 USD\n  \
                   Assets:Checking\n";
        let result = parse_via_cst(src);
        assert!(!result.errors.is_empty(), "errors: {:?}", result.errors);
    }

    #[test]
    fn transaction_with_metadata_on_directive_and_posting() {
        let src = "2024-01-15 * \"x\"\n  \
                   tag1: \"hello\"\n  \
                   Assets:Cash  -5 USD\n    \
                       receipt: \"abc123\"\n";
        let result = parse_via_cst(src);
        let Directive::Transaction(t) = &result.directives[0].value else {
            panic!("expected Transaction");
        };
        assert_eq!(
            t.meta.get("tag1"),
            Some(&MetaValue::String("hello".to_string()))
        );
        let p_meta = &t.postings[0].value.meta;
        assert_eq!(
            p_meta.get("receipt"),
            Some(&MetaValue::String("abc123".to_string()))
        );
    }

    /// Pins the `ERROR_NODE` exclusion contract on
    /// `account_occurrences`. The rustdoc on `ParseResult::
    /// account_occurrences` distinguishes two failure modes:
    ///
    /// - **Typed-conversion failure** (e.g. `InvalidBookingMethod`
    ///   on an `open` whose booking string is garbage): the CST is
    ///   intact, the `ACCOUNT` node is NOT inside `ERROR_NODE`, so
    ///   the token IS tracked. The LSP rename can still hit it
    ///   during mid-edit.
    /// - **CST-recovery wrap**: a directive so garbled that the
    ///   CST wraps the region in `ERROR_NODE`. The `ACCOUNT` token
    ///   is inside `ERROR_NODE`, NOT tracked.
    ///
    /// The two policies are deliberate. This test pins both.
    #[test]
    fn account_occurrences_policy_for_failing_directives() {
        // Case A: typed-conversion failure. `open Assets:Bank
        // "GARBAGE"` parses syntactically but fails the booking-
        // method whitelist. The ACCOUNT token IS tracked.
        let src = "2024-01-01 open Assets:Bank \"GARBAGE\"\n";
        let r = parse_via_cst(src);
        assert!(
            r.account_occurrences
                .iter()
                .any(|o| o.value == "Assets:Bank"),
            "typed-conversion failure should keep the ACCOUNT token in \
             account_occurrences (got {:?}); rename mid-edit relies on this",
            r.account_occurrences,
        );

        // Case B: CST-recovery wrap. `opn Assets:Bank USD` (typo
        // `opn`) is unrecognized at the directive position and the
        // recovery walker wraps it in ERROR_NODE. The ACCOUNT
        // token is excluded.
        let src = "2024-01-01 opn Assets:Bank USD\n";
        let r = parse_via_cst(src);
        assert!(
            !r.account_occurrences
                .iter()
                .any(|o| o.value == "Assets:Bank"),
            "ERROR_NODE-wrapped ACCOUNT should be EXCLUDED from \
             account_occurrences (got {:?}); rename should not hit garbled \
             mid-edit syntax",
            r.account_occurrences,
        );
    }
}
