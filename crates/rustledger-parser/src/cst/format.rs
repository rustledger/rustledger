//! Opinionated CST-backed formatter (phase 4.1 of #1262).
//!
//! [`format_source_v2`] is a pure function `&str → String`: it
//! reparses the input into a CST and emits text in one canonical
//! form per AST shape. Two semantically-equivalent inputs produce
//! byte-identical output; idempotence (`f(f(x)) == f(x)`) follows
//! trivially.
//!
//! This is the gofmt-style replacement for [`crate::format_source`]
//! (the legacy `(source, ParseResult, FormatConfig) → String`
//! whole-file orchestrator that re-emitted via the AST-driven
//! `rustledger_core::format` path). The legacy entry stays in
//! place for the duration of PR 4.1; later sub-PRs sweep callers
//! and delete it.
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

/// Pre-computed alignment data for a whole source file: where
/// posting amounts and posting-line cost specs anchor.
///
/// One column per file: every posting's amount starts at the same
/// `amount_col`, padded with spaces from the end of the account
/// name. Matches the conventional Beancount layout (no per-
/// transaction local alignment).
#[derive(Debug, Clone, Copy)]
struct Alignment {
    /// Column index (0-indexed) at which the amount starts.
    amount_col: usize,
}

impl Alignment {
    /// Fallback used when a file contains zero postings — picks
    /// a reasonable column so a synthetic single-posting input
    /// emits `  Account  amount` (two spaces of pad).
    const DEFAULT_AMOUNT_COL: usize = 50;
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
#[must_use]
pub fn format_source_v2(source: &str) -> String {
    let (stripped, _had_bom) = crate::bom::strip_leading(source);
    let parsed = SourceFile::parse(stripped);
    format_node(parsed.syntax())
}

/// Format a `SOURCE_FILE` syntax node in opinionated canonical form.
///
/// The bare-node entry for callers that already parsed the CST
/// (typically LSP formatting providers). Output rules are the
/// same as [`format_source_v2`].
#[must_use]
pub fn format_node(node: &crate::SyntaxNode) -> String {
    let mut out = String::new();
    let source_file =
        SourceFile::cast(node.clone()).expect("format_node called on non-SOURCE_FILE node");
    let alignment = compute_alignment(&source_file);
    let mut first = true;
    for directive in source_file.directives() {
        if !first {
            out.push('\n');
        }
        first = false;
        emit_directive(&directive, alignment, &mut out);
    }
    if out.is_empty() {
        out.push('\n');
    } else if !out.ends_with('\n') {
        out.push('\n');
    }
    out
}

/// Pre-pass: walk every `TRANSACTION` and every `POSTING` in it,
/// take `max(indent + posting_lhs_width)` to anchor a single file-
/// wide amount column. `posting_lhs_width` = `[flag space] account`.
fn compute_alignment(sf: &SourceFile) -> Alignment {
    let mut max_lhs: usize = 0;
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
                lhs += flag.text().len() + 1; // `! ` etc.
            }
            if let Some(account) = p.account() {
                lhs += account.text().len();
            }
            max_lhs = max_lhs.max(lhs);
        }
    }
    if !any_posting {
        return Alignment {
            amount_col: Alignment::DEFAULT_AMOUNT_COL,
        };
    }
    // 2 spaces between the longest account end and the amount,
    // matching bean-format's default alignment gap.
    Alignment {
        amount_col: INDENT.len() + max_lhs + 2,
    }
}

fn emit_directive(d: &ast::Directive, align: Alignment, out: &mut String) {
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
        match t.kind() {
            crate::SyntaxKind::DATE | crate::SyntaxKind::CUSTOM_KW => {
                i += 1;
                continue;
            }
            crate::SyntaxKind::NUMBER => {
                out.push(' ');
                out.push_str(&canonical_number(t.text()));
                if matches!(
                    tokens.get(i + 1).map(|t| t.kind()),
                    Some(crate::SyntaxKind::CURRENCY)
                ) {
                    out.push(' ');
                    out.push_str(tokens[i + 1].text());
                    i += 2;
                    continue;
                }
            }
            _ => {
                out.push(' ');
                out.push_str(t.text());
            }
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
            out.push_str(INDENT);
            let trimmed = m.syntax().text().to_string();
            out.push_str(trimmed.trim_start());
            if !out.ends_with('\n') {
                out.push('\n');
            }
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
    out.push_str(INDENT);
    let mut col = INDENT.len();
    if let Some(flag) = p.flag() {
        out.push_str(flag.text());
        out.push(' ');
        col += flag.text().len() + 1;
    }
    let account_text = p
        .account()
        .map(|a| a.text().to_string())
        .unwrap_or_default();
    out.push_str(&account_text);
    col += account_text.len();

    let amount_str = p
        .amount()
        .as_ref()
        .map(format_amount)
        .filter(|s| !s.is_empty());
    if let Some(amt) = amount_str {
        // Pad with spaces to reach align.amount_col; fall back
        // to 2 spaces if we've already passed the column (the
        // posting's LHS exceeds the file's max).
        let padding = if col < align.amount_col {
            align.amount_col - col
        } else {
            2
        };
        for _ in 0..padding {
            out.push(' ');
        }
        out.push_str(&amt);
        if let Some(cs) = p.cost_spec() {
            out.push(' ');
            out.push_str(&format_cost_spec(&cs));
        }
        if let Some(pa) = p.price_annotation() {
            out.push(' ');
            out.push_str(&format_price_annotation(&pa));
        }
    }
    out.push('\n');
    // Posting-attached metadata: indent 4 (deeper than posting's 2).
    for m in p.meta_entries() {
        out.push_str("    ");
        let trimmed = m.syntax().text().to_string();
        out.push_str(trimmed.trim_start());
        if !out.ends_with('\n') {
            out.push('\n');
        }
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
fn format_cost_spec(cs: &ast::CostSpec) -> String {
    let (open, close) = if cs.is_total() {
        ("{{", "}}")
    } else {
        ("{", "}")
    };
    let mut inner = String::new();
    let mut prev_kind: Option<crate::SyntaxKind> = None;
    for el in cs.syntax().children_with_tokens() {
        let rowan::NodeOrToken::Token(t) = el else {
            continue;
        };
        match t.kind() {
            crate::SyntaxKind::L_BRACE
            | crate::SyntaxKind::R_BRACE
            | crate::SyntaxKind::L_DOUBLE_BRACE
            | crate::SyntaxKind::R_DOUBLE_BRACE
            | crate::SyntaxKind::L_BRACE_HASH
            | crate::SyntaxKind::WHITESPACE
            | crate::SyntaxKind::NEWLINE => {}
            _ => {
                let need_space = prev_kind.is_some();
                if need_space {
                    inner.push(' ');
                }
                if t.kind() == crate::SyntaxKind::NUMBER {
                    inner.push_str(&canonical_number(t.text()));
                } else {
                    inner.push_str(t.text());
                }
                prev_kind = Some(t.kind());
            }
        }
    }
    format!("{open}{inner}{close}")
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
fn is_trivia_kind(kind: crate::SyntaxKind) -> bool {
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
/// directive: tokens from the first `NUMBER` up to (but not
/// including) the first `CURRENCY` at paren-depth 0. Spacing
/// rules per [`write_expression_tokens`].
fn emit_amount_expression(node: &crate::SyntaxNode, out: &mut String) {
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
    write_expression_tokens(&raw[..end], out);
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
    write_expression_tokens(&tokens, out);
}

/// Shared spacing pass over an already-sliced expression-token
/// run. Rules:
///
/// - single space between adjacent operands / binary operators
/// - no space after `(` or before `)` (parens stay tight)
/// - no space after a unary `+` / `-` (one that opens the run
///   or follows `(` or another operator)
fn write_expression_tokens(tokens: &[crate::SyntaxToken], out: &mut String) {
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
/// each on its own indented line. Most directive types don't
/// have a `.meta_entries()` accessor on their typed wrapper; we
/// walk the syntax node directly to stay uniform.
fn emit_meta_entries_of(node: &crate::SyntaxNode, out: &mut String) {
    for entry in node.children().filter_map(MetaEntry::cast) {
        out.push_str(INDENT);
        // For now: passthrough the entry's source text minus its
        // leading trivia, ensuring exactly one newline at the
        // end. A proper canonical emit (key: <typed-value>) lands
        // in PR 4.1b alongside meta value normalization.
        let trimmed = entry.syntax().text().to_string();
        out.push_str(trimmed.trim_start());
        if !out.ends_with('\n') {
            out.push('\n');
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_input_yields_single_newline() {
        assert_eq!(format_source_v2(""), "\n");
    }

    #[test]
    fn open_directive_canonical() {
        let src = "2024-01-15   open    Assets:Cash\n";
        assert_eq!(format_source_v2(src), "2024-01-15 open Assets:Cash\n");
    }

    #[test]
    fn open_with_currencies_and_booking_canonical() {
        let src = "2024-01-15 open Assets:Brokerage USD,EUR \"STRICT\"\n";
        assert_eq!(
            format_source_v2(src),
            "2024-01-15 open Assets:Brokerage USD EUR \"STRICT\"\n"
        );
    }

    #[test]
    fn close_directive_canonical() {
        let src = "2024-12-31 close Assets:Cash\n";
        assert_eq!(format_source_v2(src), "2024-12-31 close Assets:Cash\n");
    }

    #[test]
    fn commodity_directive_canonical() {
        let src = "2024-01-01 commodity HOOL\n";
        assert_eq!(format_source_v2(src), "2024-01-01 commodity HOOL\n");
    }

    #[test]
    fn blank_line_between_directives() {
        let src = "2024-01-01 open Assets:A\n2024-01-02 open Assets:B\n";
        assert_eq!(
            format_source_v2(src),
            "2024-01-01 open Assets:A\n\n2024-01-02 open Assets:B\n"
        );
    }

    #[test]
    fn trailing_newline_always_present() {
        let src = "2024-01-01 open Assets:A";
        let formatted = format_source_v2(src);
        assert!(formatted.ends_with('\n'));
        assert!(!formatted.ends_with("\n\n"));
    }

    #[test]
    fn idempotent_on_canonical_input() {
        let src = "2024-01-01 open Assets:A\n\n2024-01-02 close Assets:A\n";
        let once = format_source_v2(src);
        let twice = format_source_v2(&once);
        assert_eq!(once, twice);
    }

    #[test]
    fn note_canonical() {
        let src = "2024-01-15   note   Assets:Cash   \"a note\"\n";
        assert_eq!(
            format_source_v2(src),
            "2024-01-15 note Assets:Cash \"a note\"\n"
        );
    }

    #[test]
    fn event_canonical() {
        let src = "2024-01-15  event  \"location\"   \"NYC\"\n";
        assert_eq!(
            format_source_v2(src),
            "2024-01-15 event \"location\" \"NYC\"\n"
        );
    }

    #[test]
    fn query_canonical() {
        let src = "2024-01-15 query \"q1\" \"SELECT account\"\n";
        assert_eq!(
            format_source_v2(src),
            "2024-01-15 query \"q1\" \"SELECT account\"\n"
        );
    }

    #[test]
    fn pad_canonical() {
        let src = "2024-01-15  pad   Assets:A   Equity:Opening\n";
        assert_eq!(
            format_source_v2(src),
            "2024-01-15 pad Assets:A Equity:Opening\n"
        );
    }

    #[test]
    fn document_with_tags_and_links_canonical() {
        let src = "2024-06-01 document Assets:Bank \"stmt.pdf\" #q1 ^scan42 #urgent\n";
        assert_eq!(
            format_source_v2(src),
            "2024-06-01 document Assets:Bank \"stmt.pdf\" #q1 ^scan42 #urgent\n"
        );
    }

    #[test]
    fn price_canonical_strips_thousands_separators() {
        let src = "2024-01-15 price USD  1,234.56 EUR\n";
        assert_eq!(format_source_v2(src), "2024-01-15 price USD 1234.56 EUR\n");
    }

    #[test]
    fn price_arithmetic_canonicalizes_spacing() {
        let src = "2024-01-15 price USD 1/2 EUR\n";
        assert_eq!(format_source_v2(src), "2024-01-15 price USD 1 / 2 EUR\n");
    }

    #[test]
    fn balance_canonical() {
        let src = "2024-01-15  balance  Assets:Cash   100.00  USD\n";
        assert_eq!(
            format_source_v2(src),
            "2024-01-15 balance Assets:Cash 100.00 USD\n"
        );
    }

    #[test]
    fn balance_with_tolerance_canonical() {
        let src = "2024-01-15 balance Assets:Cash 100.00 USD ~ 0.01 USD\n";
        assert_eq!(
            format_source_v2(src),
            "2024-01-15 balance Assets:Cash 100.00 USD ~ 0.01 USD\n"
        );
    }

    #[test]
    fn balance_arithmetic_canonical() {
        let src = "2024-01-15 balance Assets:Cash  0.25 + 0.75  USD\n";
        assert_eq!(
            format_source_v2(src),
            "2024-01-15 balance Assets:Cash 0.25 + 0.75 USD\n"
        );
    }

    #[test]
    fn custom_canonical() {
        let src = "2024-01-01 custom \"budget\" Expenses:Food 500.00 USD\n";
        assert_eq!(
            format_source_v2(src),
            "2024-01-01 custom \"budget\" Expenses:Food 500.00 USD\n"
        );
    }

    #[test]
    fn option_canonical() {
        let src = "option   \"title\"   \"My Ledger\"\n";
        assert_eq!(format_source_v2(src), "option \"title\" \"My Ledger\"\n");
    }

    #[test]
    fn include_canonical() {
        let src = "include  \"other.beancount\"\n";
        assert_eq!(format_source_v2(src), "include \"other.beancount\"\n");
    }

    #[test]
    fn plugin_canonical_with_config() {
        let src = "plugin  \"beancount.plugins.unrealized\"  \"Unrealized\"\n";
        assert_eq!(
            format_source_v2(src),
            "plugin \"beancount.plugins.unrealized\" \"Unrealized\"\n"
        );
    }

    #[test]
    fn plugin_canonical_without_config() {
        let src = "plugin   \"my.plugin\"\n";
        assert_eq!(format_source_v2(src), "plugin \"my.plugin\"\n");
    }

    #[test]
    fn pushtag_poptag_canonical() {
        let src = "pushtag  #active\npoptag  #active\n";
        assert_eq!(format_source_v2(src), "pushtag #active\n\npoptag #active\n");
    }

    #[test]
    fn pushmeta_popmeta_canonical() {
        let src = "pushmeta location: \"NYC\"\npopmeta location:\n";
        assert_eq!(
            format_source_v2(src),
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
        // max account width = 15 (Expenses:Coffee); amount_col = INDENT.len() + 15 + 2 = 19.
        // 2 + Assets:Cash (11) = 13 → pad 6 → amount at col 19.
        // 2 + Expenses:Coffee (15) = 17 → pad 2 → amount at col 19.
        let expected = "\
2024-01-15 * \"Coffee\"
  Assets:Cash      -5.00 USD
  Expenses:Coffee  5.00 USD
";
        assert_eq!(format_source_v2(src), expected);
    }

    #[test]
    fn transaction_payee_and_narration() {
        let src =
            "2024-01-15 * \"Starbucks\" \"Coffee\"\n  Assets:Cash -5.00 USD\n  Expenses:Coffee\n";
        let out = format_source_v2(src);
        assert!(
            out.contains("2024-01-15 * \"Starbucks\" \"Coffee\"\n"),
            "got: {out}"
        );
    }

    #[test]
    fn transaction_pending_flag() {
        let src = "2024-01-15 ! \"Pending\"\n  Assets:Cash -5.00 USD\n  Expenses:Misc\n";
        let out = format_source_v2(src);
        assert!(out.starts_with("2024-01-15 ! \"Pending\"\n"), "got: {out}");
    }

    #[test]
    fn transaction_txn_keyword_normalized_to_star() {
        // The `txn` keyword form is canonical-form equivalent to `*`.
        let src = "2024-01-15 txn \"x\"\n  Assets:Cash -1.00 USD\n  Expenses:Misc\n";
        let out = format_source_v2(src);
        assert!(out.starts_with("2024-01-15 * \"x\"\n"), "got: {out}");
    }

    #[test]
    fn transaction_header_tags_and_links() {
        let src =
            "2024-01-15 * \"x\" #tag1 ^link1 #tag2\n  Assets:Cash -1.00 USD\n  Expenses:Misc\n";
        let out = format_source_v2(src);
        assert!(
            out.starts_with("2024-01-15 * \"x\" #tag1 ^link1 #tag2\n"),
            "got: {out}"
        );
    }

    #[test]
    fn transaction_auto_balance_posting_no_amount() {
        let src = "2024-01-15 * \"x\"\n  Assets:Cash  -5.00 USD\n  Expenses:Misc\n";
        let out = format_source_v2(src);
        // The auto-balance posting has no amount; should just be
        // the indented account name.
        assert!(out.contains("\n  Expenses:Misc\n"), "got: {out}");
    }

    #[test]
    fn transaction_posting_with_cost_spec() {
        let src = "2024-01-15 * \"buy\"\n  Assets:Brokerage  10 HOOL {500.00 USD}\n  Assets:Cash  -5000.00 USD\n";
        let out = format_source_v2(src);
        assert!(out.contains("10 HOOL {500.00 USD}"), "got: {out}");
    }

    #[test]
    fn transaction_posting_with_total_cost_spec() {
        let src = "2024-01-15 * \"buy\"\n  Assets:Brokerage  10 HOOL {{5000.00 USD}}\n  Assets:Cash  -5000.00 USD\n";
        let out = format_source_v2(src);
        assert!(out.contains("10 HOOL {{5000.00 USD}}"), "got: {out}");
    }

    #[test]
    fn transaction_posting_with_per_unit_price() {
        let src = "2024-01-15 * \"buy\"\n  Assets:Brokerage  10 HOOL @ 500.00 USD\n  Assets:Cash  -5000.00 USD\n";
        let out = format_source_v2(src);
        assert!(out.contains("10 HOOL @ 500.00 USD"), "got: {out}");
    }

    #[test]
    fn transaction_posting_with_total_price() {
        let src = "2024-01-15 * \"buy\"\n  Assets:Brokerage  10 HOOL @@ 5000.00 USD\n  Assets:Cash  -5000.00 USD\n";
        let out = format_source_v2(src);
        assert!(out.contains("10 HOOL @@ 5000.00 USD"), "got: {out}");
    }

    #[test]
    fn transaction_posting_with_flag() {
        let src = "2024-01-15 * \"x\"\n  ! Assets:Cash  -5.00 USD\n  Expenses:Misc  5.00 USD\n";
        let out = format_source_v2(src);
        assert!(out.contains("\n  ! Assets:Cash"), "got: {out}");
    }

    #[test]
    fn transaction_negative_amount() {
        let src = "2024-01-15 * \"x\"\n  Assets:Cash -5.00 USD\n  Expenses:Misc 5.00 USD\n";
        let out = format_source_v2(src);
        assert!(out.contains("-5.00 USD"), "got: {out}");
        assert!(out.contains(" 5.00 USD"), "got: {out}");
    }

    #[test]
    fn transaction_strips_thousands_separators_in_postings() {
        let src = "2024-01-15 * \"x\"\n  Assets:Cash -1,000.00 USD\n  Expenses:Misc 1,000.00 USD\n";
        let out = format_source_v2(src);
        assert!(out.contains("-1000.00 USD"), "got: {out}");
        assert!(!out.contains("1,000"), "got: {out}");
    }

    #[test]
    fn transaction_arithmetic_amount() {
        let src =
            "2024-01-15 * \"x\"\n  Assets:Cash  -(1.00 + 2.00) USD\n  Expenses:Misc 3.00 USD\n";
        let out = format_source_v2(src);
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
        let once = format_source_v2(src);
        let twice = format_source_v2(&once);
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
        let out = format_source_v2(src);
        // Longest LHS = `Liabilities:CreditCard:Visa` (27) →
        // amount_col = 2 + 27 + 2 = 31. Every amount lines up.
        let amount_cols: Vec<usize> = out
            .lines()
            .filter(|l| l.starts_with("  ") && (l.contains(" USD") || l.contains(" EUR")))
            .filter_map(|l| l.find(|c: char| c == '-' || c.is_ascii_digit()))
            .collect();
        assert!(
            amount_cols.len() >= 4,
            "expected ≥4 posting lines, got {amount_cols:?} in {out}"
        );
        let first = amount_cols[0];
        assert!(
            amount_cols.iter().all(|&c| c == first),
            "expected all postings aligned at column {first}, got {amount_cols:?} in:\n{out}"
        );
    }

    #[test]
    fn transaction_posting_metadata_indented_four() {
        let src =
            "2024-01-15 * \"x\"\n  Assets:Cash -5.00 USD\n    foo: \"bar\"\n  Expenses:Misc\n";
        let out = format_source_v2(src);
        assert!(out.contains("\n    foo: \"bar\"\n"), "got: {out}");
    }
}
