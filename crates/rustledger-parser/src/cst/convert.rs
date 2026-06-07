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
//! - Custom (heterogeneous value list)
//!
//! Implemented `ParseResult`-field extractors:
//! - Option, Include, Plugin
//!
//! Implemented Transaction (header + postings + metadata):
//! - Header: date, flag, payee, narration, tags, links, metadata
//! - Postings: flag, account, units (`IncompleteAmount`), cost spec
//!   (per-unit / total), price annotation (`@` / `@@`), metadata
//! - Arithmetic AMOUNT expressions are NOT yet evaluated; the
//!   converter takes the FIRST `NUMBER` child as the value.
//!
//! Pending:
//! - Pushtag, Poptag, Pushmeta, Popmeta (state-only side effects
//!   that mutate subsequent transactions; deferred — most corpus
//!   files don't use them)
//! - Arithmetic expression evaluation (Phase 2.4 CST shape; for
//!   now, treats `100+5 USD` as `100 USD`)
//! - Transaction trailing comments
//! - Posting comments / `trailing_comments`
//!
//! Pending lossless features (deferred):
//! - Document tags + links (need raw-token walk; field on
//!   `Document` struct currently filled empty)
//! - `currency_occurrences` field on `ParseResult` (downstream
//!   LSP rename/references depends on this — filled empty until
//!   Transaction lands)
//! - Standalone `comments` field

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
    let mut directive_nodes: Vec<crate::SyntaxNode> = Vec::new();
    let mut options: Vec<(String, String, Span)> = Vec::new();
    let mut includes: Vec<(String, Span)> = Vec::new();
    let mut plugins: Vec<(String, Option<String>, Span)> = Vec::new();
    let mut comments: Vec<Spanned<String>> = extract_top_level_comments(&source_file, bom_offset);
    comments.extend(extract_section_marker_comments(&source_file, bom_offset));
    // Merge in source order — legacy emits each line's comment
    // entry as parse_entry consumes it, so order matches start
    // offset.
    comments.sort_by_key(|s| s.span.start);
    let mut errors = extract_error_node_errors(&source_file, bom_offset);
    errors.extend(extract_transaction_body_errors(&source_file, bom_offset));
    errors.sort_by_key(|e| e.span.start);
    let warnings = Vec::new();
    let currency_occurrences = extract_currency_occurrences(&source_file, bom_offset);

    // pushtag/poptag/pushmeta/popmeta state. The legacy parser
    // maintains a stack across directives; each Transaction
    // inherits the active pushed-tag set, and EVERY directive
    // inherits the active pushed-meta set.
    let mut tag_stack: Vec<Tag> = Vec::new();
    let mut meta_stack: Metadata = Metadata::default();

    for directive in source_file.directives() {
        // Helper to push a successfully-converted directive
        // alongside its CST node so the post-pass span fixup
        // can index them in parallel.
        let cst_node = directive.syntax().clone();
        let pushed_directive = match directive {
            ast::Directive::Open(node) => convert_open(&node, bom_offset),
            ast::Directive::Close(node) => convert_close(&node, bom_offset),
            ast::Directive::Commodity(node) => convert_commodity(&node, bom_offset),
            ast::Directive::Note(node) => convert_note(&node, bom_offset),
            ast::Directive::Document(node) => convert_document(&node, bom_offset),
            ast::Directive::Event(node) => convert_event(&node, bom_offset),
            ast::Directive::Query(node) => convert_query(&node, bom_offset),
            ast::Directive::Price(node) => convert_price(&node, bom_offset),
            ast::Directive::Balance(node) => convert_balance(&node, bom_offset),
            ast::Directive::Pad(node) => convert_pad(&node, bom_offset),
            ast::Directive::Custom(node) => convert_custom(&node, bom_offset),
            ast::Directive::Transaction(node) => convert_transaction(&node, bom_offset),
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
                    tag_stack.push(Tag::new(tag_token.text().trim_start_matches('#')));
                }
                None
            }
            ast::Directive::Poptag(node) => {
                if let Some(tag_token) = node.tag() {
                    let name = tag_token.text().trim_start_matches('#');
                    if let Some(pos) = tag_stack.iter().rposition(|t| t.as_str() == name) {
                        tag_stack.remove(pos);
                    }
                }
                None
            }
            ast::Directive::Pushmeta(node) => {
                if let Some(key_token) = node.key() {
                    let key = key_token.text_without_colon().to_string();
                    let value = pushmeta_value(node.syntax());
                    meta_stack.insert(key, value);
                }
                None
            }
            ast::Directive::Popmeta(node) => {
                if let Some(key_token) = node.key() {
                    meta_stack.remove(key_token.text_without_colon());
                }
                None
            }
        };
        if let Some(mut spanned) = pushed_directive {
            apply_inherited_state(&mut spanned.value, &tag_stack, &meta_stack);
            directives.push(spanned);
            directive_nodes.push(cst_node);
        }
    }

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
    let mut number = parse_decimal_token(node.number()?.text())?;
    if node_has_minus_before_number(node.syntax()) {
        number = -number;
    }
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
    let mut number = parse_decimal_token(node.number()?.text())?;
    if node_has_minus_before_number(node.syntax()) {
        number = -number;
    }
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

fn convert_custom(node: &CustomDirective, bom_offset: u32) -> Option<Spanned<Directive>> {
    let date = parse_date_token(node.date()?.text())?;
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

fn convert_transaction(node: &AstTransaction, bom_offset: u32) -> Option<Spanned<Directive>> {
    let date = parse_date_token(node.date()?.text())?;

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

    let tags: Vec<Tag> = node
        .tags()
        .map(|t| Tag::new(t.text().trim_start_matches('#')))
        .collect();
    let links: Vec<Link> = node
        .links()
        .map(|l| Link::new(l.text().trim_start_matches('^')))
        .collect();

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
    // content).
    let postings = collect_postings_with_comments(node, bom_offset);

    let txn = rustledger_core::directive::Transaction {
        date,
        flag,
        payee,
        narration,
        tags,
        links,
        meta,
        postings,
        trailing_comments: Vec::new(),
    };
    let span = node_span(node.syntax(), bom_offset);
    Some(Spanned::new(Directive::Transaction(txn), span))
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
fn collect_postings_with_comments(node: &AstTransaction, bom_offset: u32) -> Vec<Spanned<Posting>> {
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
                if let Some(p) = ast::Posting::cast(n)
                    && let Some(mut spanned) = convert_posting(&p, bom_offset)
                {
                    if !pending.is_empty() {
                        spanned.value.comments = std::mem::take(&mut pending);
                    }
                    out.push(spanned);
                }
                // META_ENTRY child nodes: comments collected so
                // far don't apply to them (they're transaction
                // metadata). Drop them.
            }
        }
    }
    out
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

fn convert_posting(node: &ast::Posting, bom_offset: u32) -> Option<Spanned<Posting>> {
    let account = Account::new(node.account()?.text());

    let flag = node.flag().map(|f| flag_char_from_posting(&f));

    let units = node
        .amount()
        .and_then(|amt| convert_amount_to_incomplete(&amt));
    let cost = node.cost_spec().map(|cs| convert_cost_spec(&cs));
    let price = node
        .price_annotation()
        .map(|pa| convert_price_annotation(&pa));
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
/// is used. A proper expression evaluator is deferred — none of
/// the directive types we currently handle outside of postings
/// use AMOUNT shapes that the legacy parser would have evaluated
/// differently.
fn convert_amount_to_incomplete(amt: &ast::Amount) -> Option<IncompleteAmount> {
    let number = amt.number().and_then(|n| {
        let mut value = parse_decimal_token(n.text())?;
        if let Some(sign) = amt.sign()
            && sign.is_minus()
        {
            value = -value;
        }
        Some(value)
    });
    let currency = amt.currency().map(|c| Currency::new(c.text()));
    match (number, currency) {
        (Some(n), Some(c)) => Some(IncompleteAmount::Complete(Amount::new(n, c))),
        (Some(n), None) => Some(IncompleteAmount::NumberOnly(n)),
        (None, Some(c)) => Some(IncompleteAmount::CurrencyOnly(c)),
        (None, None) => None,
    }
}

fn convert_cost_spec(cs: &ast::CostSpec) -> CostSpec {
    let merge = cs.is_merge();
    let is_total = cs.is_total();

    let number = cs.number().and_then(|n| parse_decimal_token(n.text()));
    let cost_number = match (number, is_total) {
        (Some(v), true) => Some(CostNumber::Total { value: v }),
        (Some(v), false) => Some(CostNumber::PerUnit { value: v }),
        (None, _) => None,
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

fn convert_price_annotation(pa: &ast::PriceAnnotation) -> PriceAnnotation {
    let kind = if pa.is_total() {
        PriceKind::Total
    } else {
        PriceKind::Unit
    };
    let amount = pa.amount().and_then(|a| convert_amount_to_incomplete(&a));
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
fn apply_inherited_state(value: &mut Directive, tag_stack: &[Tag], meta_stack: &Metadata) {
    if let Directive::Transaction(txn) = value {
        for tag in tag_stack {
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
    for (k, v) in meta_stack {
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

/// Walk the source file and collect every "standalone" comment
/// line into `ParseResult.comments`, mirroring the legacy parser.
///
/// **Column-0 only.** The legacy parser's `parse_entry` matches
/// `Token::Comment` only when it's the first non-newline token
/// on its line. An indented comment (preceded by `WHITESPACE` on
/// the same line) becomes a parse error in the legacy parser,
/// not a comment entry. The CST trivia policy attaches indented
/// trailing trivia as a direct `SOURCE_FILE` child too, but we
/// must exclude those from `comments` to match.
///
/// **Inside directives.** Comment tokens that appear inside a
/// directive node BEFORE the first non-trivia content token (the
/// directive's inter-directive leading trivia from the trivia
/// policy) are inter-directive comments and the legacy parser
/// surfaces them as standalone. We apply the same column-0 rule
/// there.
///
/// **After content.** Comments that appear AFTER the directive's
/// first content token (e.g., trailing same-line comments on a
/// posting) belong to the directive, not to `comments`.
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
                    } else if !is_trivia_kind(t.kind()) && !is_comment_kind(t.kind()) {
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
/// `SyntaxError("unexpected input")` `ParseError` for each line
/// that is NEITHER a section marker (`*`-starting) NOR a
/// column-0 comment. Matches the legacy parser's behavior for
/// unrecognized content: `parse_entry`'s `_ => Err(())` arm
/// triggers error recovery which emits a `SyntaxError` for the
/// skipped span.
fn extract_error_node_errors(source_file: &SourceFile, bom_offset: u32) -> Vec<crate::ParseError> {
    let mut out = Vec::new();
    for child in source_file.syntax().children() {
        if child.kind() != crate::SyntaxKind::ERROR_NODE {
            continue;
        }
        let mut line_start: Option<u32> = None;
        let mut first_non_trivia: Option<crate::SyntaxKind> = None;
        let mut line_end: u32 = 0;
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
                    let _ = line_end;
                    let span = Span::new((ls + bom_offset) as usize, (end + bom_offset) as usize);
                    out.push(crate::ParseError::new(
                        crate::ParseErrorKind::SyntaxError("unexpected input".to_string()),
                        span,
                    ));
                }
                line_start = None;
                first_non_trivia = None;
                continue;
            }
            line_end = end;
            if first_non_trivia.is_none() && !is_trivia_kind(t.kind()) {
                first_non_trivia = Some(t.kind());
            }
        }
    }
    out
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

fn extract_top_level_comments(source_file: &SourceFile, bom_offset: u32) -> Vec<Spanned<String>> {
    let mut out = Vec::new();

    // Track whether a `WHITESPACE` token preceded the current
    // token on the same line. Reset on `NEWLINE`. A `COMMENT`
    // counts as standalone only when this is FALSE (i.e., the
    // comment starts at column 0). Indented comments are
    // skipped — the legacy parser's `parse_entry` fails on them.
    //
    // Walks ALL descendant tokens so comments inside ERROR_NODEs
    // (which the structured parser uses for unrecognized lines)
    // are still surfaced if they're column-0 within the line —
    // matching how the legacy parser sees each line.
    let mut preceded_by_ws = false;
    let mut just_entered_directive = false;
    for el in source_file.syntax().descendants_with_tokens() {
        match el {
            rowan::NodeOrToken::Node(n) => {
                // Inside a recognized directive's CONTENT region
                // (after its first non-trivia token), comments
                // belong to the directive (trailing comments on
                // postings, etc.) and are NOT standalone. Reset
                // tracking and use just_entered_directive as a
                // gate so we still see directive leading trivia.
                if ast::Directive::can_cast(n.kind()) {
                    preceded_by_ws = false;
                    just_entered_directive = true;
                } else {
                    just_entered_directive = false;
                }
            }
            rowan::NodeOrToken::Token(t) => match t.kind() {
                crate::SyntaxKind::NEWLINE => preceded_by_ws = false,
                crate::SyntaxKind::WHITESPACE => preceded_by_ws = true,
                k if is_comment_kind(k) => {
                    if !preceded_by_ws {
                        let range = t.text_range();
                        let start: u32 = range.start().into();
                        let end: u32 = range.end().into();
                        let span =
                            Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
                        out.push(Spanned::new(t.text().to_string(), span));
                    }
                }
                _ => {
                    // Hit a non-trivia content token. If this is
                    // the FIRST content token of a recognized
                    // directive, we crossed into the directive's
                    // body — subsequent comments belong to it,
                    // not to the standalone list. We approximate
                    // this by simply continuing to track ws/nl;
                    // trailing comments on posting lines have
                    // preceded_by_ws=true so they're already
                    // excluded by the column-0 rule.
                    let _ = just_entered_directive;
                    preceded_by_ws = false;
                }
            },
        }
    }
    out
}

// ---- ParseResult.currency_occurrences --------------------------

/// Walk every `CURRENCY` token under the source file (any
/// depth) in source order and emit a `Spanned<Currency>` with
/// the BOM-adjusted byte range. Mirrors the legacy parser's
/// `currency_occurrences` field, which downstream LSP rename /
/// references / document-highlight consumers walk to find every
/// place a currency identifier appears.
fn extract_currency_occurrences(
    source_file: &SourceFile,
    bom_offset: u32,
) -> Vec<Spanned<Currency>> {
    let mut out = Vec::new();
    // CURRENCY tokens inside an ERROR_NODE are content the
    // legacy parser couldn't classify (and so never advanced its
    // lexer through). To match the legacy parser's
    // currency_occurrences output we must SKIP CURRENCY tokens
    // that have an ancestor of kind ERROR_NODE.
    for el in source_file.syntax().descendants_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        if t.kind() != crate::SyntaxKind::CURRENCY {
            continue;
        }
        // Walk ancestors to check for ERROR_NODE.
        let in_error = t
            .parent_ancestors()
            .any(|a| a.kind() == crate::SyntaxKind::ERROR_NODE);
        if in_error {
            continue;
        }
        let range = t.text_range();
        let start: u32 = range.start().into();
        let end: u32 = range.end().into();
        let span = Span::new((start + bom_offset) as usize, (end + bom_offset) as usize);
        out.push(Spanned::new(Currency::new(t.text()), span));
    }
    out
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

/// Trivia kinds that don't count toward a span's start/end when
/// matching the legacy parser's span convention.
const fn is_trivia_kind(kind: crate::SyntaxKind) -> bool {
    matches!(
        kind,
        crate::SyntaxKind::WHITESPACE | crate::SyntaxKind::NEWLINE | crate::SyntaxKind::COMMENT
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
    for (i, spanned) in directives.iter_mut().enumerate() {
        let node = &converted_nodes[i];
        let raw_start: usize = (u32::from(node.text_range().start()) + bom_offset) as usize;
        let pos = all_starts
            .iter()
            .position(|(rs, _)| *rs == raw_start)
            .expect("converted node must appear in the all-directives list");
        let start = all_starts[pos].1;
        let end = all_starts
            .get(pos + 1)
            .map_or(source_end, |(_, content)| *content);
        spanned.span = Span::new(start, end);
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
}
