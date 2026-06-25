//! Green-tree conversion path (PR 1 of the lossless-CST-tax removal — see the
//! profiling sizing spike: the CST→AST conversion is ~74% of the load, and
//! ~33% of that is red-node (`SyntaxNode` cursor) traversal that allocates +
//! refcounts a `NodeData` per node touch).
//!
//! This module walks the **immutable green tree** top-down, threading the
//! absolute byte offset, instead of materializing red nodes. It is built in
//! parallel with [`super::convert`] and gated by a differential oracle that
//! pins its output byte-identical to the red path.
//!
//! Status: full transaction conversion (header + postings + cost/price), wired
//! into `parse_via_cst_opts` with a **red fallback** — green returns `Some` only
//! when it exactly replicates red, bailing on transaction metadata, direct-child
//! comments, deprecated `|`, unparseable amounts, and posting flag/metadata/
//! arithmetic (those layer on next). Measured −16% load on a 10k-txn workload.
//! Pinned by field-level oracles + the `parse_green_eq_red_corpus` differential
//! test + the `fuzz_green_eq_red` fuzz target.

use super::convert::{
    decode_string_token, is_comment_kind, number_meta_value, parse_date_token, parse_decimal_token,
};
use rowan::{Language, NodeOrToken};
use rustledger_core::cost::{CostNumber, CostSpec};
use rustledger_core::directive::{PriceAnnotation, PriceKind};
use rustledger_core::{
    Account, Amount, Currency, IncompleteAmount, InternedStr, Link, MetaValue, Metadata, NaiveDate,
    Posting, Span, Spanned, Tag,
};

/// Every top-level (child-of-root) **node** paired with its source [`Span`],
/// computed by threading the absolute byte offset through the green tree — no
/// red-node allocation. Equivalent to `root.children().map(node_span)` on the
/// red tree; the differential test pins that equivalence. Offset drift (esp.
/// across a leading BOM and multi-byte text) is the #1 correctness hazard, so
/// this validates it before any body conversion rides on it.
// Span-validation helper exercised only by the differential tests (the wired
// path threads offsets inline); targeted allow so the rest of the module is
// still checked for dead code.
#[allow(dead_code)]
pub(super) fn top_level_node_spans(
    root: &crate::SyntaxNode,
    bom_offset: u32,
) -> Vec<(crate::SyntaxKind, Span)> {
    let green = root.green();
    let mut out = Vec::new();
    let mut offset = bom_offset as usize;
    for child in green.children() {
        let len = match &child {
            NodeOrToken::Node(n) => u32::from(n.text_len()) as usize,
            NodeOrToken::Token(t) => u32::from(t.text_len()) as usize,
        };
        if let NodeOrToken::Node(n) = child {
            let kind = crate::BeancountLanguage::kind_from_raw(n.kind());
            out.push((kind, Span::new(offset, offset + len)));
        }
        offset += len;
    }
    out
}

/// Flag char for a header flag-token kind. Mirrors `TransactionFlag::cast` +
/// `flag_char_from_transaction` in [`super::convert`]: STAR/TXN→`*`,
/// PENDING→`!`, HASH→`#`, FLAG/single-char-CURRENCY → first char.
fn flag_char(kind: crate::SyntaxKind, text: &str) -> Option<char> {
    use crate::SyntaxKind as K;
    match kind {
        K::STAR | K::TXN_KW => Some('*'),
        K::PENDING_KW => Some('!'),
        K::HASH => Some('#'),
        K::FLAG => text.chars().next(),
        K::CURRENCY if text.len() == 1 => text.chars().next(),
        _ => None,
    }
}

/// Convert a `TRANSACTION` green node's **header** (date / flag / payee+
/// narration / tags / links) and span, in a single fused pass over its direct
/// children — no red-node allocation. Metadata, postings, and trailing comments
/// are left empty here (next increment); the oracle compares only the header
/// fields for now. `base` is the node's absolute start offset (BOM-inclusive).
///
/// Returns `None` if the date is absent/invalid (matching red, which drops the
/// directive). Error emission for an invalid date lands with the next increment.
pub(super) fn convert_transaction_header(
    node: &rowan::GreenNodeData,
    base: usize,
) -> Option<(rustledger_core::directive::Transaction, Span)> {
    use crate::SyntaxKind as K;
    let span = Span::new(base, base + u32::from(node.text_len()) as usize);

    let mut date: Option<NaiveDate> = None;
    let mut date_seen = false;
    let mut flag = '*';
    let mut seen_flag = false;
    let mut seen_str_tag_link = false;
    let mut strings: Vec<String> = Vec::new();
    let mut tags: Vec<Tag> = Vec::new();
    let mut links: Vec<Link> = Vec::new();
    let mut past_header = false;

    for child in node.children() {
        let NodeOrToken::Token(t) = child else {
            // POSTING / META_ENTRY child nodes — handled in the next increment.
            continue;
        };
        let kind = crate::BeancountLanguage::kind_from_raw(t.kind());
        let text = t.text();
        if past_header {
            // Body-level flat TAG/LINK tokens (between postings) join the set,
            // deduped against what the header already contributed.
            match kind {
                K::TAG => {
                    let tg = Tag::new(text.trim_start_matches('#'));
                    if !tags.contains(&tg) {
                        tags.push(tg);
                    }
                }
                K::LINK => {
                    let lk = Link::new(text.trim_start_matches('^'));
                    if !links.contains(&lk) {
                        links.push(lk);
                    }
                }
                _ => {}
            }
        } else {
            match kind {
                K::NEWLINE => past_header = true,
                // Latch on the FIRST date token (like red's `node.date()`): if it
                // fails to parse, `date` stays None and the directive bails to red
                // — don't scan ahead to a later valid-looking date in junk input.
                K::DATE if !date_seen => {
                    date_seen = true;
                    date = parse_date_token(text);
                }
                K::STRING => {
                    seen_str_tag_link = true;
                    if let Some(s) = decode_string_token(text) {
                        strings.push(s);
                    }
                }
                K::TAG => {
                    seen_str_tag_link = true;
                    tags.push(Tag::new(text.trim_start_matches('#')));
                }
                K::LINK => {
                    seen_str_tag_link = true;
                    links.push(Link::new(text.trim_start_matches('^')));
                }
                // Flag region: the first flag-kind token before any STRING/TAG/LINK.
                k if !seen_flag && !seen_str_tag_link => {
                    if let Some(c) = flag_char(k, text) {
                        flag = c;
                        seen_flag = true;
                    }
                }
                _ => {}
            }
        }
    }
    let date = date?;

    // 0 -> empty narration; 1 -> narration only; 2 -> payee + narration;
    // 3+ -> last is narration, payee dropped (matches red).
    let mut it = strings.into_iter();
    let (payee_str, narration_str) = match (it.next(), it.next(), it.next()) {
        (None, _, _) => (None, String::new()),
        (Some(n), None, _) => (None, n),
        (Some(p), Some(n), None) => (Some(p), n),
        (Some(_), Some(_), Some(c)) => (None, it.last().unwrap_or(c)),
    };

    let txn = rustledger_core::directive::Transaction {
        date,
        flag,
        payee: payee_str.map(InternedStr::from),
        narration: InternedStr::from(narration_str),
        tags,
        links,
        meta: Metadata::default(),
        postings: Vec::new(),
        trailing_comments: Vec::new(),
    };
    Some((txn, span))
}

/// Convert a non-arithmetic `AMOUNT` green node into an `IncompleteAmount`.
/// Returns `None` for arithmetic-expression amounts (`5 + 3 USD`) — those are a
/// later increment; the simple oracle corpus excludes them.
fn simple_amount(node: &rowan::GreenNodeData) -> Option<IncompleteAmount> {
    use crate::SyntaxKind as K;
    let mut sign_minus = false;
    let mut number: Option<rust_decimal::Decimal> = None;
    let mut number_seen = false;
    let mut currency: Option<Currency> = None;
    let mut complex = false;
    for child in node.children() {
        let NodeOrToken::Token(t) = child else {
            complex = true;
            continue;
        };
        match crate::BeancountLanguage::kind_from_raw(t.kind()) {
            K::MINUS if !number_seen => sign_minus = true,
            K::PLUS if !number_seen => {}
            K::NUMBER if !number_seen => {
                number_seen = true;
                number = parse_decimal_token(t.text());
                // An unparseable NUMBER (e.g. >28 digits) makes red emit a
                // diagnostic; bail to red so the error isn't dropped.
                if number.is_none() {
                    complex = true;
                }
            }
            K::CURRENCY if currency.is_none() => currency = Some(Currency::new(t.text())),
            K::WHITESPACE => {}
            // Operator, second number, or extra currency => arithmetic/complex.
            K::NUMBER
            | K::PLUS
            | K::MINUS
            | K::STAR
            | K::SLASH
            | K::L_PAREN
            | K::R_PAREN
            | K::CURRENCY => complex = true,
            _ => {}
        }
    }
    if complex {
        return None;
    }
    let number = number.map(|n| if sign_minus { -n } else { n });
    match (number, currency) {
        (Some(n), Some(c)) => Some(IncompleteAmount::Complete(Amount::new(n, c))),
        (Some(n), None) => Some(IncompleteAmount::NumberOnly(n)),
        (None, Some(c)) => Some(IncompleteAmount::CurrencyOnly(c)),
        (None, None) => None,
    }
}

/// Convert a `COST_SPEC` green node into a `CostSpec` (forms `{N CCY}`,
/// `{{T CCY}}`, `{N # T CCY}`, `{*}` merge, plus optional date + label). Mirrors
/// `convert_cost_spec` / `cost_total_after_hash` in [`super::convert`]. Cost
/// numbers are plain `NUMBER` tokens (no arithmetic evaluation); an unparseable
/// one yields `number: None` like red, which emits no diagnostic for cost
/// numbers — so this needs no bail and always returns a `CostSpec`.
fn convert_cost_spec(node: &rowan::GreenNodeData) -> CostSpec {
    use crate::SyntaxKind as K;
    let mut is_total = false;
    let mut is_merge = false;
    let mut merge_phase = false; // after opener, while only WHITESPACE seen
    let mut first_number: Option<rust_decimal::Decimal> = None;
    let mut seen_number = false;
    let mut past_hash = false;
    let mut post_hash_total: Option<rust_decimal::Decimal> = None;
    let mut currency: Option<Currency> = None;
    let mut date: Option<NaiveDate> = None;
    let mut date_seen = false;
    let mut label: Option<String> = None;
    let mut label_seen = false;
    for child in node.children() {
        let NodeOrToken::Token(t) = child else {
            continue;
        };
        match crate::BeancountLanguage::kind_from_raw(t.kind()) {
            K::L_DOUBLE_BRACE => {
                is_total = true;
                merge_phase = true;
            }
            K::L_BRACE | K::L_BRACE_HASH => merge_phase = true,
            K::WHITESPACE => {} // keep merge_phase across leading whitespace
            K::STAR => {
                if merge_phase {
                    is_merge = true;
                }
                merge_phase = false;
            }
            K::NUMBER => {
                merge_phase = false;
                if past_hash && post_hash_total.is_none() {
                    post_hash_total = parse_decimal_token(t.text());
                } else if !seen_number {
                    seen_number = true;
                    first_number = parse_decimal_token(t.text());
                }
            }
            K::HASH => {
                merge_phase = false;
                if seen_number {
                    past_hash = true;
                }
            }
            K::CURRENCY if currency.is_none() => {
                merge_phase = false;
                currency = Some(Currency::new(t.text()));
            }
            K::DATE if !date_seen => {
                merge_phase = false;
                date_seen = true;
                date = parse_date_token(t.text());
            }
            K::STRING if !label_seen => {
                merge_phase = false;
                label_seen = true;
                label = decode_string_token(t.text());
            }
            _ => merge_phase = false,
        }
    }
    let number = if let Some(total) = post_hash_total {
        Some(CostNumber::Total { value: total })
    } else {
        match (first_number, is_total) {
            (Some(v), true) => Some(CostNumber::Total { value: v }),
            (Some(v), false) => Some(CostNumber::PerUnit { value: v }),
            (None, _) => None,
        }
    };
    CostSpec {
        number,
        currency,
        date,
        label,
        merge: is_merge,
    }
}

/// Convert a `PRICE_ANNOTATION` green node into a `PriceAnnotation`: `@@`→Total,
/// `@`→Unit, with the (non-arithmetic) amount. Returns `None` when the amount is
/// present but arithmetic/malformed, signalling the caller to bail (later
/// increment evaluates those).
fn convert_price_annotation(node: &rowan::GreenNodeData) -> Option<PriceAnnotation> {
    use crate::SyntaxKind as K;
    let mut is_total = false;
    let mut amount_present = false;
    let mut amount: Option<IncompleteAmount> = None;
    for child in node.children() {
        match &child {
            NodeOrToken::Token(t) => {
                if crate::BeancountLanguage::kind_from_raw(t.kind()) == K::AT_AT {
                    is_total = true;
                }
            }
            NodeOrToken::Node(n) => {
                if crate::BeancountLanguage::kind_from_raw(n.kind()) == K::AMOUNT && !amount_present
                {
                    amount_present = true;
                    amount = simple_amount(n);
                }
            }
        }
    }
    if amount_present && amount.is_none() {
        return None; // arithmetic / malformed price amount — bail
    }
    Some(PriceAnnotation {
        kind: if is_total {
            PriceKind::Total
        } else {
            PriceKind::Unit
        },
        amount,
    })
}

/// Derive the typed [`MetaValue`] of a `META_ENTRY` green node. Mirrors
/// `meta_value_from_entry` in [`super::convert`] exactly: priority is string >
/// number/amount > date > account > currency > bool > tag/link > none, and a
/// type that's present-but-unparseable (e.g. a malformed string, an
/// over-precision number, a bad date) falls through to the next, matching red.
fn meta_value(entry: &rowan::GreenNodeData) -> MetaValue {
    use crate::SyntaxKind as K;
    let mut string_t: Option<String> = None;
    let mut number_t: Option<String> = None;
    let mut currency_t: Option<String> = None;
    let mut date_t: Option<String> = None;
    let mut account_t: Option<String> = None;
    let mut bool_v: Option<bool> = None;
    let mut tag_link: Option<MetaValue> = None;
    // Minus sign negating the number: a MINUS token AFTER the key and BEFORE the
    // first NUMBER (mirrors `meta_entry_has_minus_sign`).
    let mut past_key = false;
    let mut minus = false;
    let mut minus_decided = false;

    for child in entry.children() {
        let NodeOrToken::Token(t) = child else {
            continue;
        };
        let kind = crate::BeancountLanguage::kind_from_raw(t.kind());
        // First-of-kind value tokens (matches red's `first_token` accessors).
        match kind {
            K::STRING if string_t.is_none() => string_t = Some(t.text().to_string()),
            K::NUMBER if number_t.is_none() => number_t = Some(t.text().to_string()),
            K::CURRENCY if currency_t.is_none() => currency_t = Some(t.text().to_string()),
            K::DATE if date_t.is_none() => date_t = Some(t.text().to_string()),
            K::ACCOUNT if account_t.is_none() => account_t = Some(t.text().to_string()),
            K::BOOL_TRUE if bool_v.is_none() => bool_v = Some(true),
            K::BOOL_FALSE if bool_v.is_none() => bool_v = Some(false),
            K::TAG if tag_link.is_none() => {
                tag_link = Some(MetaValue::Tag(Tag::new(t.text().trim_start_matches('#'))));
            }
            K::LINK if tag_link.is_none() => {
                tag_link = Some(MetaValue::Link(Link::new(t.text().trim_start_matches('^'))));
            }
            _ => {}
        }
        if past_key && !minus_decided {
            match kind {
                K::MINUS => {
                    minus = true;
                    minus_decided = true;
                }
                K::NUMBER => minus_decided = true,
                _ => {}
            }
        }
        if kind == K::META_KEY {
            past_key = true;
        }
    }

    if let Some(s) = string_t
        && let Some(decoded) = decode_string_token(&s)
    {
        return MetaValue::String(decoded);
    }
    if let Some(nt) = number_t
        && let Some(mut dec) = parse_decimal_token(&nt)
    {
        if minus {
            dec = -dec;
        }
        if let Some(c) = currency_t {
            return MetaValue::Amount(Amount::new(dec, Currency::new(&c)));
        }
        return number_meta_value(&nt, dec);
    }
    if let Some(dt) = date_t
        && let Some(date) = parse_date_token(&dt)
    {
        return MetaValue::Date(date);
    }
    if let Some(a) = account_t {
        return MetaValue::Account(Account::new(&a));
    }
    if let Some(c) = currency_t {
        return MetaValue::Currency(Currency::new(&c));
    }
    if let Some(b) = bool_v {
        return MetaValue::Bool(b);
    }
    if let Some(tl) = tag_link {
        return tl;
    }
    MetaValue::None
}

/// Key + typed value for a single `META_ENTRY` green node (key = first
/// `META_KEY` token with the trailing `:` stripped), or `None` if it has no key.
/// Folded directly into the posting/transaction conversion loops so the parent's
/// children are walked only once — no separate metadata pass over them.
fn meta_entry_kv(entry: &rowan::GreenNodeData) -> Option<(String, MetaValue)> {
    use crate::SyntaxKind as K;
    let key = entry.children().find_map(|c| match c {
        NodeOrToken::Token(t)
            if crate::BeancountLanguage::kind_from_raw(t.kind()) == K::META_KEY =>
        {
            Some(t.text().strip_suffix(':').unwrap_or(t.text()).to_string())
        }
        _ => None,
    })?;
    Some((key, meta_value(entry)))
}

/// Posting flag char. Mirrors `PostingFlag::cast` + `flag_char_from_posting`:
/// STAR→`*`, PENDING→`!`, HASH→`#`, FLAG/single-char-CURRENCY → first char.
/// Note: unlike a transaction flag this does NOT accept `txn`.
fn posting_flag_char(kind: crate::SyntaxKind, text: &str) -> Option<char> {
    use crate::SyntaxKind as K;
    match kind {
        K::STAR => Some('*'),
        K::PENDING_KW => Some('!'),
        K::HASH => Some('#'),
        K::FLAG => text.chars().next(),
        K::CURRENCY if text.len() == 1 => text.chars().next(),
        _ => None,
    }
}

/// Convert a `POSTING` green node (flag + account + non-arithmetic units + cost
/// spec + price annotation + per-posting metadata + span + same-line trailing
/// comments). Returns `None` for postings with a trailing-sibling amount or an
/// arithmetic amount — those fall back to red. `base` is the node's absolute
/// start offset. Span policy matches red `posting_span`: ends at the first
/// NEWLINE's start.
pub(super) fn convert_simple_posting(
    node: &rowan::GreenNodeData,
    base: usize,
) -> Option<Spanned<Posting>> {
    use crate::SyntaxKind as K;
    let mut flag: Option<char> = None;
    let mut flag_decided = false;
    let mut account: Option<Account> = None;
    let mut units: Option<IncompleteAmount> = None;
    let mut cost: Option<CostSpec> = None;
    let mut price: Option<PriceAnnotation> = None;
    let mut meta = Metadata::default();
    let mut trailing_comments: Vec<String> = Vec::new();
    let mut newline_off: Option<usize> = None;
    let mut amount_seen = false;
    let mut offset = base;
    for child in node.children() {
        let len = match &child {
            NodeOrToken::Node(n) => u32::from(n.text_len()) as usize,
            NodeOrToken::Token(t) => u32::from(t.text_len()) as usize,
        };
        match &child {
            NodeOrToken::Token(t) => {
                let kind = crate::BeancountLanguage::kind_from_raw(t.kind());
                if kind == K::ACCOUNT && account.is_none() {
                    flag_decided = true; // account reached; flag decision is settled
                    account = Some(Account::new(t.text()));
                } else if kind == K::NEWLINE && newline_off.is_none() {
                    newline_off = Some(offset);
                } else if newline_off.is_none() && is_comment_kind(kind) {
                    trailing_comments.push(t.text().to_string());
                } else if !flag_decided && account.is_none() && kind != K::WHITESPACE {
                    // First non-whitespace token before the account is the flag iff
                    // it's a flag kind (else `None`), matching red's `Posting::flag`.
                    flag_decided = true;
                    flag = posting_flag_char(kind, t.text());
                }
            }
            NodeOrToken::Node(n) => match crate::BeancountLanguage::kind_from_raw(n.kind()) {
                K::AMOUNT if !amount_seen => {
                    amount_seen = true;
                    // `?` bails on an arithmetic/malformed amount (later increment).
                    units = Some(simple_amount(n)?);
                }
                K::COST_SPEC if cost.is_none() => cost = Some(convert_cost_spec(n)),
                // `?` bails if the price amount is arithmetic/malformed.
                K::PRICE_ANNOTATION if price.is_none() => {
                    price = Some(convert_price_annotation(n)?);
                }
                K::META_ENTRY => {
                    if let Some((k, v)) = meta_entry_kv(n) {
                        meta.insert(k, v);
                    }
                }
                // second amount — arithmetic/multi-amount falls back to red.
                K::AMOUNT => return None,
                _ => {}
            },
        }
        offset += len;
    }
    let account = account?;
    let end = newline_off.unwrap_or(base + u32::from(node.text_len()) as usize);
    Some(Spanned::new(
        Posting {
            account,
            units,
            cost,
            price,
            flag,
            meta,
            comments: Vec::new(),
            trailing_comments,
        },
        Span::new(base, end),
    ))
}

/// Assemble a full `TRANSACTION` directive from its green node, or return `None`
/// to fall back to red. Returns `Some` **only** when the transaction is fully
/// and identically convertible on green: a valid date, all simple postings, and
/// no direct-child comments or deprecated `|` — those need red's attach +
/// diagnostic logic the green path doesn't yet replicate. Header fields,
/// postings, and transaction-level metadata are all converted here. Bailing to
/// red keeps the hybrid's output exactly equal to red. `base` is the node start.
pub(super) fn convert_transaction(
    node: &rowan::GreenNodeData,
    base: usize,
) -> Option<Spanned<rustledger_core::Directive>> {
    use crate::SyntaxKind as K;
    let (mut txn, span) = convert_transaction_header(node, base)?;
    let mut postings = Vec::new();
    let mut meta = Metadata::default();
    let mut offset = base;
    for child in node.children() {
        let len = match &child {
            NodeOrToken::Node(n) => u32::from(n.text_len()) as usize,
            NodeOrToken::Token(t) => u32::from(t.text_len()) as usize,
        };
        match &child {
            NodeOrToken::Token(t) => {
                let kind = crate::BeancountLanguage::kind_from_raw(t.kind());
                // Direct-child comments (header-trailing / inter-posting /
                // txn-trailing) and the deprecated `|` need red's attach +
                // diagnostic logic — bail.
                if is_comment_kind(kind) || kind == K::PIPE {
                    return None;
                }
            }
            // One pass: postings and transaction-level metadata (posting
            // metadata lives inside the POSTING nodes, handled per-posting).
            NodeOrToken::Node(n) => match crate::BeancountLanguage::kind_from_raw(n.kind()) {
                K::POSTING => postings.push(convert_simple_posting(n, offset)?),
                K::META_ENTRY => {
                    if let Some((k, v)) = meta_entry_kv(n) {
                        meta.insert(k, v);
                    }
                }
                _ => {}
            },
        }
        offset += len;
    }
    txn.postings = postings;
    txn.meta = meta;
    Some(Spanned::new(
        rustledger_core::Directive::Transaction(txn),
        span,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{SyntaxKind, parse_structured};
    use rustledger_core::Directive;

    fn red_spans(root: &crate::SyntaxNode, bom: u32) -> Vec<(SyntaxKind, Span)> {
        root.children()
            .map(|n| {
                let r = n.text_range();
                let s = (u32::from(r.start()) + bom) as usize;
                let e = (u32::from(r.end()) + bom) as usize;
                (n.kind(), Span::new(s, e))
            })
            .collect()
    }

    #[test]
    fn green_node_spans_match_red() {
        let cases = [
            "",
            "2020-01-01 open Assets:Cash USD\n",
            "2020-01-01 * \"p\" \"m\"\n  Assets:Cash 5.00 USD\n  Income:X\n",
            "; leading comment\n\n2020-01-01 open A\n2020-01-02 close A\n",
            "option \"title\" \"x\"\n2020-01-01 commodity USD\n",
            "2020-01-01 price AAPL 5 USD\n2020-01-01 balance A 0 USD\n",
            "\u{feff}2020-01-01 open A\n",
            "2020-01-01 * \"é\" \"münts\"\n  A 1 EUR\n  B\n",
            "garbage !! line\n2020-01-01 open A\n",
            "2020-01-01 txn \"x\"\n  A 10 AAPL {2.00 USD}\n  B -20.00 USD\n",
        ];
        for src in cases {
            let (stripped, has_bom) = crate::bom::strip_leading(src);
            let bom = if has_bom { 3 } else { 0 };
            let root = parse_structured(stripped);
            assert_eq!(
                top_level_node_spans(&root, bom),
                red_spans(&root, bom),
                "green vs red node spans diverged for: {src:?}"
            );
        }
    }

    /// Field-level oracle: green transaction-header fields must equal the red
    /// path's. (No BOM in these cases, so absolute offset == stripped offset.)
    #[test]
    fn green_txn_header_matches_red() {
        let cases = [
            "2020-01-01 * \"payee\" \"narr\"\n  A 1 USD\n  B\n",
            "2020-01-01 ! \"only narration\"\n  A 1 USD\n  B\n",
            "2020-01-01 txn \"n\"\n  A 1 USD\n  B\n",
            "2020-01-01 # \"flagged\"\n  A 1 USD\n  B\n",
            "2020-01-01 *\n  A 1 USD\n  B\n",
            "2020-01-01 * \"p\" \"n\" #tag1 #tag2 ^link-a\n  A 1 USD\n  B\n",
            "2020-01-01 * \"esc \\\"q\\\" tab\\there\"\n  A 1 USD\n  B\n",
            "2020-01-01 * \"é payee\" \"münts\"\n  A 1 EUR\n  B\n",
        ];
        for src in cases {
            // green: find the first TRANSACTION node + its offset, convert header.
            let root = parse_structured(src);
            let green = root.green();
            let mut offset = 0usize;
            let mut txn_node = None;
            for child in green.children() {
                let len = match &child {
                    NodeOrToken::Node(n) => u32::from(n.text_len()) as usize,
                    NodeOrToken::Token(t) => u32::from(t.text_len()) as usize,
                };
                if let NodeOrToken::Node(n) = child
                    && crate::BeancountLanguage::kind_from_raw(n.kind()) == SyntaxKind::TRANSACTION
                {
                    txn_node = Some((n, offset));
                    break;
                }
                offset += len;
            }
            let (txn_green, base) = txn_node.expect("transaction node");
            let (g, g_span) = convert_transaction_header(txn_green, base).expect("green header");

            // red: full parse, pull the first transaction directive.
            let red = crate::parse(src);
            let red_sp = &red.directives[0];
            let Directive::Transaction(r) = &red_sp.value else {
                panic!("expected transaction for {src:?}");
            };
            assert_eq!(g.date, r.date, "date {src:?}");
            assert_eq!(g.flag, r.flag, "flag {src:?}");
            assert_eq!(g.payee, r.payee, "payee {src:?}");
            assert_eq!(g.narration, r.narration, "narration {src:?}");
            assert_eq!(g.tags, r.tags, "tags {src:?}");
            assert_eq!(g.links, r.links, "links {src:?}");
            assert_eq!(g_span, red_sp.span, "span {src:?}");
        }
    }

    /// Field oracle: green simple-posting conversion must equal the red path's,
    /// for simple postings (account + non-arithmetic units + trailing comment +
    /// elided units). No BOM in these cases.
    #[test]
    fn green_simple_posting_matches_red() {
        let cases = [
            "2020-01-01 * \"p\"\n  Assets:Cash 5.00 USD\n  Income:X\n",
            "2020-01-01 * \"p\"\n  Assets:A -10 EUR\n  Assets:B 10 EUR\n",
            "2020-01-01 * \"p\"\n  A 5 USD  ; note here\n  B\n",
            "2020-01-01 * \"p\"\n  A 1234.5678 USD\n  B 0 USD\n",
            // cost specs
            "2020-01-01 * \"p\"\n  Assets:Stock 10 AAPL {2.00 USD}\n  Assets:Cash -20.00 USD\n",
            "2020-01-01 * \"p\"\n  Assets:Stock 10 AAPL {{20.00 USD}}\n  Assets:Cash -20.00 USD\n",
            "2020-01-01 * \"p\"\n  A 10 AAPL {2.00 USD, 2021-06-01}\n  B -20.00 USD\n",
            "2020-01-01 * \"p\"\n  A 10 AAPL {2.00 USD, \"lot-1\"}\n  B -20.00 USD\n",
            "2020-01-01 * \"p\"\n  A -5 AAPL {1.50 # 8.00 USD}\n  B 8.00 USD\n  Income:G\n",
            // prices (@ unit, @@ total) + cost+price together
            "2020-01-01 * \"p\"\n  A 10 AAPL @ 3.00 USD\n  B -30.00 USD\n",
            "2020-01-01 * \"p\"\n  A 10 AAPL @@ 25.00 USD\n  B -25.00 USD\n",
            "2020-01-01 * \"p\"\n  A -5 AAPL {2.00 USD} @ 3.00 USD\n  B 15.00 USD\n  Income:G\n",
        ];
        for src in cases {
            let red = crate::parse(src);
            let Directive::Transaction(rtxn) = &red.directives[0].value else {
                panic!("txn {src:?}");
            };
            let root = parse_structured(src);
            let green = root.green();
            // locate the TRANSACTION node + base
            let mut off = 0usize;
            let mut txn = None;
            for child in green.children() {
                let len = match &child {
                    NodeOrToken::Node(n) => u32::from(n.text_len()) as usize,
                    NodeOrToken::Token(t) => u32::from(t.text_len()) as usize,
                };
                if let NodeOrToken::Node(n) = child
                    && crate::BeancountLanguage::kind_from_raw(n.kind()) == SyntaxKind::TRANSACTION
                {
                    txn = Some((n, off));
                    break;
                }
                off += len;
            }
            let (txn_node, txn_base) = txn.expect("txn node");
            // walk its POSTING children, comparing each to red.
            let mut poff = txn_base;
            let mut gi = 0usize;
            for child in txn_node.children() {
                let len = match &child {
                    NodeOrToken::Node(n) => u32::from(n.text_len()) as usize,
                    NodeOrToken::Token(t) => u32::from(t.text_len()) as usize,
                };
                if let NodeOrToken::Node(n) = child
                    && crate::BeancountLanguage::kind_from_raw(n.kind()) == SyntaxKind::POSTING
                {
                    let gp = convert_simple_posting(n, poff).expect("simple posting");
                    let rp = &rtxn.postings[gi];
                    assert_eq!(gp.value, rp.value, "posting {gi} value {src:?}");
                    assert_eq!(gp.span, rp.span, "posting {gi} span {src:?}");
                    gi += 1;
                }
                poff += len;
            }
            assert_eq!(gi, rtxn.postings.len(), "posting count {src:?}");
        }
    }

    /// End-to-end differential: the green-wired `parse` must equal the pure-red
    /// `parse_red_only` on every input — exercising the green path (simple txns)
    /// AND every red-fallback trigger (flag / metadata / comment / arithmetic /
    /// multi-amount / pipe / invalid date), plus non-transaction directives,
    /// BOM, multi-byte, and error recovery. (The fuzz target generalizes this.)
    #[test]
    fn parse_green_eq_red_corpus() {
        let corpus = [
            "",
            "2020-01-01 * \"p\" \"n\"\n  A 1 USD\n  B\n",
            "2020-01-01 ! \"x\" #t ^l\n  A 10 AAPL {2 USD} @ 3 USD\n  B -20 USD\n  Income:G\n",
            "2020-01-01 * \"p\"\n  ! A 1 USD\n  B\n", // posting flag -> red fallback
            "2020-01-01 * \"p\"\n  A 1 USD\n    note: \"m\"\n  B\n", // posting meta -> fallback
            "2020-01-01 * \"p\"\n  meta: \"x\"\n  A 1 USD\n  B\n", // txn meta -> fallback
            "2020-01-01 * \"p\"\n  ; a comment\n  A 1 USD\n  B\n", // body comment -> fallback
            "2020-01-01 * \"p\"\n  A 5 USD + 3 USD\n  B\n", // arithmetic -> fallback
            "2020-01-01 * \"p\"\n  A 5 USD 3 USD\n  B\n", // multi-amount -> fallback
            "2020-01-01 * \"p\" | \"n\"\n  A 1 USD\n  B\n", // deprecated pipe -> fallback
            "2020-13-99 * \"bad date\"\n  A 1 USD\n  B\n", // invalid date -> fallback
            // Regression (fuzz_green_eq_red crash-a45e3089): an invalid FIRST date
            // followed by a valid-looking later date token. Green must latch the
            // first date (-> None -> bail to red, which drops the directive), NOT
            // scan ahead to the second date and keep a directive red discards.
            "2020-99-99 * \"x\" 2021-01-01\n  A 1 USD\n  B\n",
            "3333/33/3 X\n", // the minimized fuzz shape (slash date, month 33)
            "\u{feff}2020-01-01 * \"p\"\n  A 1 USD\n  B\n", // BOM
            "2020-01-01 * \"é\" \"münts\"\n  Aaa 1 EUR\n  B\n", // multi-byte
            "garbage\n2020-01-01 open A\n2020-01-01 * \"p\"\n  A 1 USD\n  B\n", // error recovery
            "2020-01-01 open A\n2020-01-02 close A\noption \"x\" \"y\"\n", // non-txn
            // posting flags (now green, were red fallback)
            "2020-01-01 * \"p\"\n  ! Assets:A 1 USD\n  * Assets:B -1 USD\n",
            "2020-01-01 * \"p\"\n  A Assets:Letter 1 USD\n  Assets:B -1 USD\n",
            "2020-01-01 * \"p\"\n  # Assets:A 1 USD\n  Assets:B -1 USD\n",
            // per-posting metadata — every MetaValue type
            "2020-01-01 * \"p\"\n  Assets:A 1 USD\n    str: \"hello\"\n    int: 42\n    neg: -7\n    dec: 3.14\n    amt: 5.00 USD\n    dt: 2021-06-01\n    acct: Assets:Other\n    cur: EUR\n    yes: TRUE\n    no: FALSE\n    tg: #atag\n    lk: ^alink\n    empty:\n  Assets:B -1 USD\n",
            // transaction-level metadata (now green, was red fallback)
            "2020-01-01 * \"p\"\n  meta1: \"x\"\n  count: 3\n  Assets:A 1 USD\n  Assets:B -1 USD\n",
            // flag + cost + price + posting-meta together
            "2020-01-01 * \"p\"\n  ! Assets:S 10 AAPL {2 USD} @ 3 USD\n    lot: \"q1\"\n  Assets:C 15 USD\n  Income:G\n",
        ];
        for src in corpus {
            let g = crate::parse(src);
            let r = crate::cst::parse_red_only(src);
            let dbg = |p: &crate::ParseResult| {
                (
                    format!("{:?}", p.directives),
                    format!("{:?}", p.errors),
                    format!("{:?}", p.comments),
                    format!("{:?}", p.options),
                )
            };
            assert_eq!(
                dbg(&g),
                dbg(&r),
                "green-wired parse diverged from red for: {src:?}"
            );
        }
    }
}
