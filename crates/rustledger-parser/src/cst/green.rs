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
//! comments, deprecated `|`, unparsable amounts, and posting flag/metadata/
//! arithmetic (those layer on next). Measured −16% load on a 10k-txn workload.
//! Pinned by field-level oracles + the `parse_green_eq_red_corpus` differential
//! test + the `fuzz_green_eq_red` fuzz target.

use super::ast::AstNode as _; // brings `Directive::can_cast` into scope
use super::convert::{
    DescendantsWalkResult, TopLevelWalkResult, classify_recovery_error, cost_spec_from_tokens,
    decode_string_token, is_comment_kind, is_trivia_kind, meta_value_from_tokens, parse_date_token,
    parse_decimal_token,
};
use rowan::{Language, NodeOrToken};
use rustledger_core::cost::CostSpec;
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
                // An unparsable NUMBER (e.g. >28 digits) makes red emit a
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
    // `negate_python`, not a bare `-n`: negating a zero must yield a POSITIVE
    // zero, so a literal `-0.00` loads as `0.00` exactly as beancount parses
    // it (`Decimal('0.00')`, unsigned). The red path applies the same rule in
    // `convert_amount_to_incomplete`; the two MUST agree, and this is the one
    // postings actually take.
    let number = number.map(|n| {
        if sign_minus {
            rustledger_core::negate_python(n)
        } else {
            n
        }
    });
    match (number, currency) {
        (Some(n), Some(c)) => Some(IncompleteAmount::Complete(Amount::new(n, c))),
        (Some(n), None) => Some(IncompleteAmount::NumberOnly(n)),
        (None, Some(c)) => Some(IncompleteAmount::CurrencyOnly(c)),
        (None, None) => None,
    }
}

/// Convert a `COST_SPEC` green node into a `CostSpec`. Delegates to the
/// shared token-level [`cost_spec_from_tokens`] — the SAME implementation the
/// red walker uses, so the dual number semantics (#1713), the compound-`#`
/// rules (#1700/#1704), and the positional `{*}` merge flag cannot drift
/// between the walkers again. Red emits no diagnostic for unparsable cost
/// numbers, so this needs no bail and always returns a `CostSpec`.
fn convert_cost_spec(node: &rowan::GreenNodeData) -> CostSpec {
    cost_spec_from_tokens(node.children().filter_map(NodeOrToken::into_token))
}

/// Convert a `PRICE_ANNOTATION` green node into a `PriceAnnotation`: `@@`→Total,
/// `@`→Unit, with the (non-arithmetic) amount. Returns `None` when the amount is
/// present but arithmetic/malformed, signaling the caller to bail (later
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

/// Derive the typed [`MetaValue`] of a `META_ENTRY` green node. Delegates to
/// the shared token-level [`meta_value_from_tokens`] — the same implementation
/// the red walker uses (priority ladder, minus detection, first-of-kind
/// latches), so the two cannot drift.
fn meta_value(entry: &rowan::GreenNodeData) -> MetaValue {
    meta_value_from_tokens(entry.children().filter_map(NodeOrToken::into_token))
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

/// Green-side mirror of [`super::convert::orphaned_amount_prefix`]: is there a
/// non-trivia token between the account and the amount?
///
/// The two walk the same shape over different representations (green nodes have
/// no absolute ranges), so they answer the same question and are pinned
/// together by `fuzz_green_eq_red`.
fn green_has_orphaned_amount_prefix(node: &rowan::GreenNodeData) -> bool {
    use crate::SyntaxKind as K;
    let mut seen_account = false;
    for child in node.children() {
        match &child {
            NodeOrToken::Node(n) => {
                if crate::BeancountLanguage::kind_from_raw(n.kind()) == K::AMOUNT {
                    return false;
                }
            }
            NodeOrToken::Token(t) => {
                let kind = crate::BeancountLanguage::kind_from_raw(t.kind());
                if kind == K::ACCOUNT {
                    seen_account = true;
                    continue;
                }
                if !seen_account || kind == K::WHITESPACE || is_comment_kind(kind) {
                    continue;
                }
                if kind == K::NEWLINE {
                    return false;
                }
                // Same narrow set as red — see `orphaned_amount_prefix`.
                if matches!(kind, K::MINUS | K::PLUS | K::COMMA) {
                    return true;
                }
            }
        }
    }
    false
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
    // A token stranded between the account and the amount means the posting is
    // malformed (e.g. `-,123.00 USD`, whose sign the conversion would drop in
    // silence). Bail so red handles it and owns the diagnostic — keeping ONE
    // definition of "well formed" across the two paths.
    if green_has_orphaned_amount_prefix(node) {
        return None;
    }
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

/// Green-tree re-implementation of `walk_descendants_once` — the #1 allocation
/// site in the conversion (red `descendants_with_tokens()` heap-allocates +
/// refcounts a `NodeData` per node touched, over EVERY token in the file).
///
/// Recursively walks the green tree threading three pieces of state that red got
/// for free from the red cursor: the absolute byte `offset`, an `in_error_node`
/// flag (replacing red's per-token `parent_ancestors()` `ERROR_NODE` probe — the
/// green tree has no parent pointers), and the linear `preceded_by_ws` column-0
/// comment state. Produces a byte-identical [`DescendantsWalkResult`]. Tree
/// depth is grammar-bounded (~6 levels; arithmetic and error recovery don't nest
/// structurally), so the recursion can't blow the stack on adversarial input.
pub(super) fn walk_descendants(
    root: &crate::SyntaxNode,
    bom_offset: u32,
    collect_occurrences: bool,
) -> DescendantsWalkResult {
    let mut w = DescendantsWalker {
        offset: bom_offset as usize,
        preceded_by_ws: false,
        collect_occurrences,
        result: DescendantsWalkResult {
            inline_errors: Vec::new(),
            top_level_comments: Vec::new(),
            currency_occurrences: Vec::new(),
            account_occurrences: Vec::new(),
        },
    };
    w.walk(root.green(), false);
    w.result
}

struct DescendantsWalker {
    offset: usize,
    preceded_by_ws: bool,
    collect_occurrences: bool,
    result: DescendantsWalkResult,
}

impl DescendantsWalker {
    fn walk(&mut self, node: &rowan::GreenNodeData, in_error_node: bool) {
        use crate::SyntaxKind as K;
        for child in node.children() {
            match child {
                NodeOrToken::Node(n) => {
                    let kind = crate::BeancountLanguage::kind_from_raw(n.kind());
                    // Directive nodes reset the column-0 comment state (mirrors the
                    // red walk's `Node` arm).
                    if super::ast::Directive::can_cast(kind) {
                        self.preceded_by_ws = false;
                    }
                    self.walk(n, in_error_node || kind == K::ERROR_NODE);
                }
                NodeOrToken::Token(t) => {
                    let start = self.offset;
                    let len = u32::from(t.text_len()) as usize;
                    self.offset += len;
                    let kind = crate::BeancountLanguage::kind_from_raw(t.kind());
                    self.token(kind, t.text(), start, len, in_error_node);
                }
            }
        }
    }

    fn token(
        &mut self,
        kind: crate::SyntaxKind,
        text: &str,
        start: usize,
        len: usize,
        in_error_node: bool,
    ) {
        use crate::SyntaxKind as K;
        // ---- column-0 comment state machine ----
        match kind {
            K::NEWLINE => self.preceded_by_ws = false,
            K::WHITESPACE => self.preceded_by_ws = true,
            k if is_comment_kind(k) => {
                if !self.preceded_by_ws {
                    self.result.top_level_comments.push(Spanned::new(
                        text.to_string(),
                        Span::new(start, start + len),
                    ));
                }
            }
            _ => self.preceded_by_ws = false,
        }

        // ---- inline errors + occurrence collection ----
        if kind == K::BOM {
            return;
        }
        let has_bom = text.contains(crate::bom::BOM_CHAR);
        let is_error_token = kind == K::ERROR_TOKEN;
        // The ERROR_NODE check is only consulted for tokens whose emission depends
        // on it; gate the rest out fast (most tokens are plain whitespace/idents).
        let needs = (self.collect_occurrences && matches!(kind, K::CURRENCY | K::ACCOUNT))
            || has_bom
            || is_error_token;
        if !needs {
            return;
        }
        let span = Span::new(start, start + len);
        if self.collect_occurrences && kind == K::CURRENCY && !in_error_node {
            self.result
                .currency_occurrences
                .push(Spanned::new(Currency::new(text), span));
        }
        if self.collect_occurrences && kind == K::ACCOUNT && !in_error_node {
            self.result
                .account_occurrences
                .push(Spanned::new(Account::new(text), span));
        }
        // Inline errors: a BOM byte (-> BomInDirectiveBody) or ERROR_TOKEN
        // (-> SyntaxError) in a recognized directive; skip inside ERROR_NODE.
        if (!has_bom && !is_error_token) || in_error_node {
            return;
        }
        if has_bom {
            self.result.inline_errors.push(
                crate::ParseError::new(crate::ParseErrorKind::BomInDirectiveBody, span)
                    .with_hint(crate::diagnostics::BOM_REMOVAL_HINT),
            );
        } else {
            self.result.inline_errors.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError("unexpected input".to_string()),
                span,
            ));
        }
    }
}

/// Length of a green child (node or token) in bytes.
fn child_len(child: NodeOrToken<&rowan::GreenNodeData, &rowan::GreenTokenData>) -> usize {
    match child {
        NodeOrToken::Node(n) => u32::from(n.text_len()) as usize,
        NodeOrToken::Token(t) => u32::from(t.text_len()) as usize,
    }
}

/// Green-tree re-implementation of `walk_top_level_once`: per-top-level-directive
/// validation (indentation, custom-value, transaction-body, error-node, and
/// org-section-marker comments). Iterates the green root's direct children
/// threading the stripped-frame byte offset — no per-child red-node allocation —
/// and dispatches the same five checks, producing a byte-identical
/// [`TopLevelWalkResult`]. `offset` is stripped-frame; spans add `bom_offset`.
pub(super) fn walk_top_level(
    root: &crate::SyntaxNode,
    stripped: &str,
    bom_offset: u32,
) -> TopLevelWalkResult {
    use crate::SyntaxKind as K;
    let mut errors = Vec::new();
    let mut section_marker_comments = Vec::new();
    let green = root.green();
    let mut offset = 0usize;
    for child in green.children() {
        let len = child_len(child);
        if let NodeOrToken::Node(n) = &child {
            let kind = crate::BeancountLanguage::kind_from_raw(n.kind());
            if super::ast::Directive::can_cast(kind) {
                tl_indented_check(n, offset, bom_offset, stripped, &mut errors);
            }
            match kind {
                K::CUSTOM_DIRECTIVE => tl_custom_check(n, offset, bom_offset, &mut errors),
                K::TRANSACTION => {
                    tl_transaction_header_check(n, offset, bom_offset, stripped, &mut errors);
                    tl_transaction_body_check(n, offset, bom_offset, &mut errors);
                }
                K::ERROR_NODE => {
                    tl_error_node_check(n, offset, bom_offset, stripped, &mut errors);
                    tl_section_marker_check(n, offset, bom_offset, &mut section_marker_comments);
                }
                _ => {}
            }
        }
        offset += len;
    }
    TopLevelWalkResult {
        errors,
        section_marker_comments,
    }
}

/// `indented_directive_check` on green: a directive's first non-trivia token
/// starting past its line's column 0 is a "must start at column 0" error.
fn tl_indented_check(
    node: &rowan::GreenNodeData,
    base: usize,
    bom_offset: u32,
    stripped: &str,
    out: &mut Vec<crate::ParseError>,
) {
    let mut offset = base;
    let mut content: Option<(usize, usize)> = None;
    for child in node.children() {
        let len = child_len(child);
        if let NodeOrToken::Token(t) = &child
            && !is_trivia_kind(crate::BeancountLanguage::kind_from_raw(t.kind()))
        {
            content = Some((offset, offset + len));
            break;
        }
        offset += len;
    }
    let Some((content_start, content_end)) = content else {
        return;
    };
    // Line start: last '\n' before content_start (byte scan — boundary-agnostic).
    let line_start = stripped
        .as_bytes()
        .get(..content_start)
        .and_then(|bytes| bytes.iter().rposition(|&b| b == b'\n'))
        .map_or(0, |nl| nl + 1);
    if content_start > line_start {
        let span = Span::new(
            line_start + bom_offset as usize,
            content_end + bom_offset as usize,
        );
        out.push(crate::ParseError::new(
            crate::ParseErrorKind::SyntaxError(
                "top-level directive must start at column 0".to_string(),
            ),
            span,
        ));
    }
}

/// `custom_value_check` on green: after the header (date / `custom` / type
/// string), a bare CURRENCY (not paired as `NUMBER CURRENCY`) is invalid.
fn tl_custom_check(
    node: &rowan::GreenNodeData,
    base: usize,
    bom_offset: u32,
    out: &mut Vec<crate::ParseError>,
) {
    use crate::SyntaxKind as K;
    // Non-trivia direct tokens with their stripped offsets.
    let mut toks: Vec<(crate::SyntaxKind, usize, usize)> = Vec::new();
    let mut offset = base;
    for child in node.children() {
        let len = child_len(child);
        if let NodeOrToken::Token(t) = &child {
            let kind = crate::BeancountLanguage::kind_from_raw(t.kind());
            if !is_trivia_kind(kind) {
                toks.push((kind, offset, len));
            }
        }
        offset += len;
    }
    let mut seen_type_string = false;
    for i in 0..toks.len() {
        let (kind, start, len) = toks[i];
        if !seen_type_string {
            if kind == K::STRING {
                seen_type_string = true;
            }
            continue;
        }
        if kind == K::CURRENCY && !(i > 0 && toks[i - 1].0 == K::NUMBER) {
            let span = Span::new(
                start + bom_offset as usize,
                start + len + bom_offset as usize,
            );
            out.push(crate::ParseError::new(
                crate::ParseErrorKind::SyntaxError(
                    "bare currency literal is not a valid custom directive value".to_string(),
                ),
                span,
            ));
        }
    }
}

/// The `unexpected input` diagnostic for one catch-all transaction-body line.
///
/// Shared by the newline-terminated and EOF-terminated paths in
/// [`tl_transaction_body_check`] so the two cannot drift.
fn unexpected_body_input(line_start: usize, end: usize, bom_offset: u32) -> crate::ParseError {
    crate::ParseError::new(
        crate::ParseErrorKind::SyntaxError("unexpected input".to_string()),
        Span::new(line_start + bom_offset as usize, end + bom_offset as usize),
    )
}

/// `transaction_body_check` on green: a body line with catch-all tokens (outside
/// `POSTING` / `META_ENTRY` nodes) is "unexpected input".
/// `transaction_header_check` on green (#2008 cases 3, 4, 6, 7).
///
/// The rule lives in [`super::txn_header`]; this only enumerates the header
/// token run, mirroring `Transaction::header_tokens`: skip leading trivia,
/// then take tokens up to (not past) the terminating `NEWLINE`. A direct
/// child NODE ends the header too — `POSTING` / `META_ENTRY` are body, and a
/// header that reaches one without a `NEWLINE` has no more header left.
fn tl_transaction_header_check(
    node: &rowan::GreenNodeData,
    base: usize,
    bom_offset: u32,
    stripped: &str,
    out: &mut Vec<crate::ParseError>,
) {
    use crate::SyntaxKind as K;
    let mut tokens: Vec<(crate::SyntaxKind, std::ops::Range<usize>)> = Vec::new();
    let mut started = false;
    let mut offset = base;
    for child in node.children() {
        let len = child_len(child);
        match &child {
            NodeOrToken::Token(t) => {
                let kind = crate::BeancountLanguage::kind_from_raw(t.kind());
                if !started {
                    // Leading trivia per the Directive-Terminator Rule. BOM
                    // stays OUT of the skip set, exactly as in
                    // `Transaction::header_tokens`: a mid-file BOM is a
                    // corruption to surface, not trivia.
                    if matches!(
                        kind,
                        K::WHITESPACE
                            | K::NEWLINE
                            | K::COMMENT
                            | K::PERCENT_COMMENT
                            | K::SHEBANG
                            | K::EMACS_DIRECTIVE
                    ) {
                        offset += len;
                        continue;
                    }
                    started = true;
                }
                if kind == K::NEWLINE {
                    break;
                }
                tokens.push((kind, offset..offset + len));
            }
            NodeOrToken::Node(_) => break,
        }
        offset += len;
    }
    if let Some((defect, range)) = super::txn_header::first_header_defect(tokens) {
        out.push(super::convert::header_defect_error(
            defect, &range, stripped, bom_offset,
        ));
    }
}

fn tl_transaction_body_check(
    node: &rowan::GreenNodeData,
    base: usize,
    bom_offset: u32,
    out: &mut Vec<crate::ParseError>,
) {
    use crate::SyntaxKind as K;
    let mut past_header = false;
    let mut saw_header_content = false;
    let mut line_start: Option<usize> = None;
    let mut line_has_content = false;
    let mut offset = base;
    for child in node.children() {
        let len = child_len(child);
        match &child {
            NodeOrToken::Token(t) => {
                let kind = crate::BeancountLanguage::kind_from_raw(t.kind());
                let (start, end) = (offset, offset + len);
                if past_header {
                    if line_start.is_none() {
                        line_start = Some(start);
                    }
                    if kind == K::NEWLINE {
                        if line_has_content && let Some(ls) = line_start {
                            out.push(unexpected_body_input(ls, end, bom_offset));
                        }
                        line_start = None;
                        line_has_content = false;
                    } else if !is_trivia_kind(kind)
                        && !is_comment_kind(kind)
                        && !matches!(kind, K::TAG | K::LINK)
                    {
                        line_has_content = true;
                    }
                } else if kind == K::NEWLINE {
                    if saw_header_content {
                        past_header = true;
                    }
                } else if !is_trivia_kind(kind) {
                    saw_header_content = true;
                }
            }
            NodeOrToken::Node(_) => {
                // POSTING / META_ENTRY: not catch-all. Reset line state.
                line_start = None;
                line_has_content = false;
                past_header = true;
            }
        }
        offset += len;
    }
    // EOF terminates the final body line just as a newline would. Without this,
    // a transaction whose last body line is junk AND whose file has no trailing
    // newline reported one fewer error than the same file with one (#1884).
    if past_header
        && line_has_content
        && let Some(ls) = line_start
    {
        out.push(unexpected_body_input(ls, offset, bom_offset));
    }
}

/// Emit the recovery diagnostics for one `ERROR_NODE` line.
///
/// Split out of [`tl_error_node_check`] so the newline-terminated and the
/// EOF-terminated line go through the SAME code. Inlining it at both call
/// sites is how the two would drift.
fn emit_error_node_line(
    first_non_trivia: Option<crate::SyntaxKind>,
    line_start: Option<usize>,
    end: usize,
    bom_offset: u32,
    stripped: &str,
    out: &mut Vec<crate::ParseError>,
) {
    use crate::SyntaxKind as K;
    let is_section = first_non_trivia == Some(K::STAR);
    let is_comment = matches!(first_non_trivia, Some(k) if is_comment_kind(k));
    if is_section || is_comment || first_non_trivia.is_none() {
        return;
    }
    let Some(ls) = line_start else { return };
    let span = Span::new(ls + bom_offset as usize, end + bom_offset as usize);
    let line_text = stripped.get(ls..end).unwrap_or("");
    let primary = classify_recovery_error(line_text, span);
    let primary_is_bom = matches!(primary.kind, crate::ParseErrorKind::BomInDirectiveBody);
    out.push(primary);
    if !primary_is_bom && line_text.contains(crate::bom::BOM_CHAR) {
        out.push(
            crate::ParseError::new(crate::ParseErrorKind::BomInDirectiveBody, span)
                .with_hint(crate::diagnostics::BOM_REMOVAL_HINT),
        );
    }
}

/// `error_node_check` on green: each `ERROR_NODE` line that is neither a section
/// marker nor a column-0 comment emits a classified recovery error (+ a
/// secondary BOM diagnostic when the line also contains a BOM byte).
///
/// A line is terminated by a NEWLINE **or by the end of input** — the trailing
/// newline is optional, and beancount treats EOF as a terminator (its lexer
/// does, so `bean-check` reports the same error with or without it). Without
/// the EOF flush below, a malformed LAST line produced no diagnostic at all and
/// `rledger check` exited 0 on a ledger it had not understood (#1884): two
/// files differing by one `0a` byte gave opposite verdicts.
fn tl_error_node_check(
    node: &rowan::GreenNodeData,
    base: usize,
    bom_offset: u32,
    stripped: &str,
    out: &mut Vec<crate::ParseError>,
) {
    use crate::SyntaxKind as K;
    let mut line_start: Option<usize> = None;
    let mut first_non_trivia: Option<crate::SyntaxKind> = None;
    let mut offset = base;
    for child in node.children() {
        let len = child_len(child);
        if let NodeOrToken::Token(t) = &child {
            let kind = crate::BeancountLanguage::kind_from_raw(t.kind());
            let (start, end) = (offset, offset + len);
            if line_start.is_none() {
                line_start = Some(start);
            }
            if kind == K::NEWLINE {
                emit_error_node_line(first_non_trivia, line_start, end, bom_offset, stripped, out);
                line_start = None;
                first_non_trivia = None;
            } else if first_non_trivia.is_none() && !is_trivia_kind(kind) {
                first_non_trivia = Some(kind);
            }
        }
        offset += len;
    }
    // EOF terminates the final line just as a newline would.
    emit_error_node_line(
        first_non_trivia,
        line_start,
        offset,
        bom_offset,
        stripped,
        out,
    );
}

/// `section_marker_check` on green: emit an empty-string comment for each
/// `*`-starting (org-mode section) line inside an `ERROR_NODE`.
///
/// EOF terminates the final line, same as [`tl_error_node_check`] — a file
/// ending `* Section` with no trailing newline used to yield no comment at all.
/// Cosmetic next to the error case, but the same defect, and leaving one of the
/// three line-walkers newline-only is how the rule gets forgotten.
fn tl_section_marker_check(
    node: &rowan::GreenNodeData,
    base: usize,
    bom_offset: u32,
    out: &mut Vec<Spanned<String>>,
) {
    use crate::SyntaxKind as K;
    let mut line_start: Option<usize> = None;
    let mut first_non_trivia: Option<crate::SyntaxKind> = None;
    let mut offset = base;
    let emit = |first_non_trivia: Option<crate::SyntaxKind>,
                line_start: Option<usize>,
                end: usize,
                out: &mut Vec<Spanned<String>>| {
        if first_non_trivia == Some(K::STAR)
            && let Some(ls) = line_start
        {
            out.push(Spanned::new(
                String::new(),
                Span::new(ls + bom_offset as usize, end + bom_offset as usize),
            ));
        }
    };
    for child in node.children() {
        let len = child_len(child);
        if let NodeOrToken::Token(t) = &child {
            let kind = crate::BeancountLanguage::kind_from_raw(t.kind());
            let (start, end) = (offset, offset + len);
            if line_start.is_none() {
                line_start = Some(start);
            }
            if kind == K::NEWLINE {
                emit(first_non_trivia, line_start, end, out);
                line_start = None;
                first_non_trivia = None;
            } else if first_non_trivia.is_none() && !is_trivia_kind(kind) {
                first_non_trivia = Some(kind);
            }
        }
        offset += len;
    }
    emit(first_non_trivia, line_start, offset, out);
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
            // Regression (fuzz_green_eq_red cost-merge): a malformed cost `{,{*`
            // — opener, a non-`*` token (red's is_merge decides not-merge and
            // stops), then a SECOND opener + `*`. Green must mirror red and not
            // re-arm on the later `{`, which used to flip `merge` to true.
            "2020-01-01 *\n Aa:B 1 USD{,{*",
            // Regression (fuzz_green_eq_red cost-number): `{N # <X> T}` where the
            // first post-`#` token is a NUMBER that does NOT parse (here
            // `\u{06f6}`, an Arabic-Indic digit the lexer tokenizes as NUMBER but
            // rust_decimal rejects). Both sides now RETRY past it to the later
            // parseable `0` (red's `cost_compound_numbers` is_none() guards;
            // green mirrors it since #1713) and agree on `Compound{7, 0}` —
            // this entry pins that they keep agreeing.
            "7046/7/1D\n\tA:F{7#\u{06f6}>0",
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
            // walk_descendants distinctive paths:
            "; column-0 comment\n  ; indented comment\n2020-01-01 open Assets:A USD\n",
            "2020-01-01 * \"p\"\n  Assets:Cash 5 USD\n  Income:Salary -5 EUR\n", // occurrences
            "!!garbage Assets:InError 5 BAD!!\n2020-01-01 open Assets:Real USD\n", // error-node suppresses occ
            "* Org Section Heading\n** Sub\n2020-01-01 open A\n", // org-mode section markers
            "2020-01-01 open A\n2020-01-01 open B\n2020-01-01 open C\n", // many account occurrences
            // walk_top_level distinctive checks:
            "  2020-01-01 open Assets:A USD\n", // indented directive -> col-0 error
            "\t2020-01-01 close Assets:A\n",    // tab-indented directive
            "2020-01-01 custom \"budget\" USD\n", // bare currency in custom -> error
            "2020-01-01 custom \"b\" 10 USD \"ok\" NZD\n", // amount ok, trailing bare cur -> error
            "2020-01-01 * \"p\"\n  unexpected junk here\n  A 1 USD\n  B\n", // txn body catch-all
            "2020-01-01 * \"p\" #tag1\n  A 1 USD\n  #bodytag\n  B\n", // body tag/link is valid (no error)
            "@@@ totally invalid line @@@\n2020-01-01 open A\n", // error-node classified recovery error
            "* Section\n**  Indented Sub\n; c0 comment\n2020-01-01 open A\n", // section markers + comment
            // transaction-header check (#2008). Both walkers must agree on
            // the defect AND its span, so a multi-byte case is included: the
            // green walker sums green child lengths while the red walker
            // reads rowan text ranges, and a char-vs-byte slip would show up
            // here as a differing span (or a panic in the message slice).
            "2020-01-01 * #tag \"after tag\" ^lnk\n  A 1 USD\n  B\n", // string after tag
            "2020-01-01 * \"a\" \"b\" \"c\"\n  A 1 USD\n  B\n",       // too many strings
            "2020-01-01 * \"a\" \"b\" \"c\" \"d\"\n  A 1 USD\n  B\n", // four strings
            "2020-01-01 * \"Dinner\" A:*:B\n  A 1 USD\n  B\n",        // junk in header
            "2020-01-01 * \"é\" \"münts\" \"ü\"\n  A 1 EUR\n  B\n",   // multi-byte + too many
            "2020-01-01 * \"é payee\" X:*:Y\n  A 1 EUR\n  B\n",       // multi-byte + junk
            // Valid shapes that must stay clean on BOTH paths.
            "2012-12-17 P \"Payee\" \"Narration\"\n  A 1 USD\n  B\n", // 1-char CURRENCY flag
            "2020-01-01 * \"p\" \"n\" ; trailing comment\n  A 1 USD\n  B\n",
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
                    // The green walk_descendants produces these too.
                    format!("{:?}", p.account_occurrences),
                    format!("{:?}", p.currency_occurrences),
                    // Remaining observables: the green conversion doesn't
                    // produce these today (shared top-level walk), so they
                    // hold trivially — pinned so a future green expansion
                    // that touches them can't diverge unnoticed. Mirrors
                    // the fuzz_green_eq_red target's field list.
                    p.includes.clone(),
                    p.plugins.clone(),
                    format!("{:?}", p.warnings),
                    p.has_leading_bom,
                    p.alignment,
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

#[cfg(test)]
mod negative_zero_tests {
    use crate::parse;
    use rustledger_core::Directive;

    /// A literal `-0.00` must load as an UNSIGNED zero, as beancount parses it.
    ///
    /// beancount gives `Decimal('0.00')` (checked against 3.2.3 via
    /// `load_string`) and bean-query prints `0.00`. The green path applied the
    /// sign with a bare `-n`, which flips `rust_decimal`'s sign bit even on
    /// zero, so the posting archived a signed zero and rendered `-0.00`
    /// everywhere downstream — including `SUM`, where it turned an exactly
    /// balanced CNY column into `-0.00`.
    ///
    /// This is the GREEN path specifically. The red path's equivalent
    /// (`convert_amount_to_incomplete`) was fixed in the same change, but
    /// postings take this one, and fixing only the red one left the output
    /// unchanged — which is how the dual-path rule earns its keep.
    ///
    /// Asserts on `to_string()`: `==` cannot see a sign on zero, so
    /// `assert_eq!(number, dec!(0.00))` would pass against the bug.
    #[test]
    fn a_literal_negative_zero_loads_unsigned() {
        let parsed = parse(
            "2024-01-01 open Assets:A\n\
             2024-01-01 open Expenses:T\n\
             2024-01-02 * \"t\"\n\
             \x20 Assets:A    0.00 CNY\n\
             \x20 Expenses:T -0.00 CNY\n",
        );

        let mut rendered = Vec::new();
        for spanned in &parsed.directives {
            if let Directive::Transaction(txn) = &spanned.value {
                for posting in &txn.postings {
                    if let Some(amount) = posting.amount() {
                        rendered.push(amount.number.to_string());
                    }
                }
            }
        }

        assert_eq!(
            rendered,
            vec!["0.00".to_string(), "0.00".to_string()],
            "a `-0.00` literal must not archive a signed zero",
        );
    }

    /// The sign is still applied to non-zero amounts — the guard above must
    /// not have turned negation off.
    #[test]
    fn a_literal_negative_amount_keeps_its_sign() {
        let parsed = parse(
            "2024-01-01 open Assets:A\n\
             2024-01-02 * \"t\"\n\
             \x20 Assets:A -12.34 CNY\n",
        );

        let number = parsed
            .directives
            .iter()
            .find_map(|s| match &s.value {
                Directive::Transaction(t) => t.postings.first()?.amount().map(|a| a.number),
                _ => None,
            })
            .expect("one posting");
        assert_eq!(number.to_string(), "-12.34");
    }
}
