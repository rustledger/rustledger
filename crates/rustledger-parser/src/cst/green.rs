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
//! Status: foundation + transaction **header** conversion (date / flag /
//! payee+narration / tags / links / span), reusing the shared text parsers in
//! [`super::convert`]. Postings + metadata + comments + error recovery layer on
//! next; the field-level oracle (`green_txn_header_matches_red`) pins each field
//! against the red path as it's built.

// PR1 WIP: this parallel green path is built + verified by the differential
// tests below before being wired into `parse_via_cst`; until that wiring lands
// its functions are exercised only by tests.
#![allow(dead_code)]

use super::convert::{decode_string_token, parse_date_token};
use rowan::{Language, NodeOrToken};
use rustledger_core::{InternedStr, Link, Metadata, NaiveDate, Span, Tag};

/// Every top-level (child-of-root) **node** paired with its source [`Span`],
/// computed by threading the absolute byte offset through the green tree — no
/// red-node allocation. Equivalent to `root.children().map(node_span)` on the
/// red tree; the differential test pins that equivalence. Offset drift (esp.
/// across a leading BOM and multi-byte text) is the #1 correctness hazard, so
/// this validates it before any body conversion rides on it.
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
                K::DATE if date.is_none() => date = parse_date_token(text),
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
                if let NodeOrToken::Node(n) = child {
                    if crate::BeancountLanguage::kind_from_raw(n.kind()) == SyntaxKind::TRANSACTION
                    {
                        txn_node = Some((n, offset));
                        break;
                    }
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
}
