//! Source-driven tests for `parse_structured` (phase 2.1a).
//!
//! Each test feeds real Beancount source through the structured
//! parser and asserts the resulting tree shape against the
//! Directive-Terminator Rule (see `cst::trivia`).
//!
//! These complement (do NOT replace) the hand-constructed-tree
//! tests in `cst::trivia::tests` — those pin the policy as
//! invariants on tree shape, these pin that
//! `parse_structured(source)` actually PRODUCES trees matching
//! those invariants on real source.

// Each test references many `SyntaxKind` variants for its expected
// children sequence; a per-test glob import is the cleanest local
// shape. Clippy's enum_glob_use lint is the wrong call here.
#![allow(clippy::enum_glob_use)]

use rustledger_parser::{SyntaxKind, SyntaxNode, parse_structured};

/// Per-child kind sequence for a node. Distinguishes tokens from
/// nested nodes so a test can assert both leaf trivia and structural
/// wrapping at the same node level.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Element {
    Tok(SyntaxKind),
    Node(SyntaxKind),
}

fn elements_of(node: &SyntaxNode) -> Vec<Element> {
    node.children_with_tokens()
        .map(|el| match el {
            rowan::NodeOrToken::Token(t) => Element::Tok(t.kind()),
            rowan::NodeOrToken::Node(n) => Element::Node(n.kind()),
        })
        .collect()
}

fn tok_seq(kinds: &[SyntaxKind]) -> Vec<Element> {
    kinds.iter().copied().map(Element::Tok).collect()
}

/// Find direct-children directive nodes of any specific
/// `*_DIRECTIVE` kind under `root`.
fn directives(root: &SyntaxNode) -> Vec<SyntaxNode> {
    root.children()
        .filter(|c| {
            matches!(
                c.kind(),
                SyntaxKind::OPEN_DIRECTIVE
                    | SyntaxKind::CLOSE_DIRECTIVE
                    | SyntaxKind::BALANCE_DIRECTIVE
                    | SyntaxKind::PAD_DIRECTIVE
                    | SyntaxKind::EVENT_DIRECTIVE
                    | SyntaxKind::QUERY_DIRECTIVE
                    | SyntaxKind::NOTE_DIRECTIVE
                    | SyntaxKind::DOCUMENT_DIRECTIVE
                    | SyntaxKind::PRICE_DIRECTIVE
                    | SyntaxKind::COMMODITY_DIRECTIVE
                    | SyntaxKind::PUSHTAG_DIRECTIVE
                    | SyntaxKind::POPTAG_DIRECTIVE
                    | SyntaxKind::PUSHMETA_DIRECTIVE
                    | SyntaxKind::POPMETA_DIRECTIVE
                    | SyntaxKind::TRANSACTION
            )
        })
        .collect()
}

/// Round-trip property: the tree's text must equal the source for
/// every input. Asserted at the top of every test.
fn assert_round_trip(source: &str, tree: &SyntaxNode) {
    assert_eq!(
        tree.text().to_string(),
        source,
        "structured parser must round-trip byte-identically",
    );
}

// ---------- 10 dated directives ----------

#[test]
fn open_directive_with_currency() {
    use SyntaxKind::*;
    let source = "2024-01-01 open Assets:Cash USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), OPEN_DIRECTIVE);
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[
            DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, WHITESPACE, CURRENCY, NEWLINE
        ]),
    );
}

#[test]
fn close_directive() {
    use SyntaxKind::*;
    let source = "2024-12-31 close Assets:Cash\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), CLOSE_DIRECTIVE);
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[DATE, WHITESPACE, CLOSE_KW, WHITESPACE, ACCOUNT, NEWLINE]),
    );
}

#[test]
fn balance_directive() {
    use SyntaxKind::*;
    let source = "2024-06-30 balance Assets:Cash 100.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), BALANCE_DIRECTIVE);
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[
            DATE, WHITESPACE, BALANCE_KW, WHITESPACE, ACCOUNT, WHITESPACE, NUMBER, WHITESPACE,
            CURRENCY, NEWLINE,
        ]),
    );
}

#[test]
fn pad_directive() {
    use SyntaxKind::*;
    let source = "2024-01-01 pad Assets:Cash Equity:Opening-Balances\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), PAD_DIRECTIVE);
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[
            DATE, WHITESPACE, PAD_KW, WHITESPACE, ACCOUNT, WHITESPACE, ACCOUNT, NEWLINE,
        ]),
    );
}

#[test]
fn event_directive() {
    use SyntaxKind::*;
    let source = "2024-01-15 event \"location\" \"Berlin\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), EVENT_DIRECTIVE);
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[
            DATE, WHITESPACE, EVENT_KW, WHITESPACE, STRING, WHITESPACE, STRING, NEWLINE,
        ]),
    );
}

#[test]
fn query_directive() {
    use SyntaxKind::*;
    let source = "2024-01-01 query \"income\" \"SELECT *\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), QUERY_DIRECTIVE);
}

#[test]
fn note_directive() {
    use SyntaxKind::*;
    let source = "2024-01-15 note Assets:Cash \"deposit\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), NOTE_DIRECTIVE);
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[
            DATE, WHITESPACE, NOTE_KW, WHITESPACE, ACCOUNT, WHITESPACE, STRING, NEWLINE,
        ]),
    );
}

#[test]
fn document_directive() {
    use SyntaxKind::*;
    let source = "2024-01-15 document Assets:Cash \"/path/to/file.pdf\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), DOCUMENT_DIRECTIVE);
}

#[test]
fn price_directive() {
    use SyntaxKind::*;
    let source = "2024-01-15 price USD 1.10 EUR\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), PRICE_DIRECTIVE);
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[
            DATE, WHITESPACE, PRICE_KW, WHITESPACE, CURRENCY, WHITESPACE, NUMBER, WHITESPACE,
            CURRENCY, NEWLINE,
        ]),
    );
}

#[test]
fn commodity_directive() {
    use SyntaxKind::*;
    let source = "2024-01-01 commodity USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), COMMODITY_DIRECTIVE);
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[
            DATE,
            WHITESPACE,
            COMMODITY_KW,
            WHITESPACE,
            CURRENCY,
            NEWLINE
        ]),
    );
}

// ---------- 4 standalone-keyword directives ----------

#[test]
fn pushtag_directive() {
    use SyntaxKind::*;
    let source = "pushtag #project-x\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), PUSHTAG_DIRECTIVE);
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[PUSHTAG_KW, WHITESPACE, TAG, NEWLINE]),
    );
}

#[test]
fn poptag_directive() {
    use SyntaxKind::*;
    let source = "poptag #project-x\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), POPTAG_DIRECTIVE);
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[POPTAG_KW, WHITESPACE, TAG, NEWLINE]),
    );
}

#[test]
fn pushmeta_directive() {
    use SyntaxKind::*;
    let source = "pushmeta key: \"value\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), PUSHMETA_DIRECTIVE);
}

#[test]
fn popmeta_directive() {
    use SyntaxKind::*;
    let source = "popmeta key:\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), POPMETA_DIRECTIVE);
}

// ---------- Trivia attachment tests (Directive-Terminator Rule) ----------

#[test]
fn rule_1_same_line_trailing_comment_inside_directive() {
    use SyntaxKind::*;
    let source = "2024-01-01 open Assets:Cash  ; main checking\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), OPEN_DIRECTIVE);
    // Rule 1: WS + COMMENT + terminator NEWLINE all INSIDE the directive.
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[
            DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, WHITESPACE, COMMENT, NEWLINE,
        ]),
    );
}

#[test]
fn rule_2_blank_line_leads_following_directive() {
    use SyntaxKind::*;
    let source = "2024-01-01 open Assets:Cash\n\
                  \n\
                  2024-01-02 open Assets:Bank\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 2);
    // Rule 1: d1 owns its own terminator NEWLINE.
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, NEWLINE]),
    );
    // Rule 2: the blank-line NEWLINE leads d2.
    assert_eq!(
        elements_of(&ds[1]),
        tok_seq(&[
            NEWLINE, DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, NEWLINE
        ]),
    );
}

#[test]
fn rule_3_copyright_header_under_source_file() {
    use SyntaxKind::*;
    let source = ";; Copyright 2024\n\
                  2024-01-01 open Assets:Cash\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    // Rule 3: header trivia is direct under SOURCE_FILE, NOT inside d1.
    assert_eq!(
        elements_of(&tree),
        vec![
            Element::Tok(COMMENT),
            Element::Tok(NEWLINE),
            Element::Node(OPEN_DIRECTIVE),
        ],
    );
}

#[test]
fn rule_4_trailing_comment_block_under_source_file() {
    use SyntaxKind::*;
    let source = "2024-01-01 open Assets:Cash\n\
                  ;; closing remarks\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    // Rule 4: trailing comment block is direct under SOURCE_FILE,
    // NOT inside the file-final directive.
    assert_eq!(
        elements_of(&tree),
        vec![
            Element::Node(OPEN_DIRECTIVE),
            Element::Tok(COMMENT),
            Element::Tok(NEWLINE),
        ],
    );
}

#[test]
fn rule_5_unterminated_final_directive() {
    use SyntaxKind::*;
    let source = "2024-01-01 open Assets:Cash";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    // Rule 5: no terminator. Directive ends at last content token.
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT]),
    );
}

#[test]
fn rule_5_unterminated_with_same_line_trailing_trivia() {
    use SyntaxKind::*;
    let source = "2024-01-01 open Assets:Cash  ; eol-no-nl";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    // Rules 1+5: same-line trailing trivia stays INSIDE the
    // directive even without a terminator NEWLINE.
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[
            DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, WHITESPACE, COMMENT,
        ]),
    );
}

#[test]
fn mixed_directive_kinds_each_get_their_own_node() {
    use SyntaxKind::*;
    let source = "2024-01-01 open Assets:Cash USD\n\
                  pushtag #x\n\
                  2024-01-02 close Assets:Cash\n\
                  poptag #x\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 4);
    assert_eq!(ds[0].kind(), OPEN_DIRECTIVE);
    assert_eq!(ds[1].kind(), PUSHTAG_DIRECTIVE);
    assert_eq!(ds[2].kind(), CLOSE_DIRECTIVE);
    assert_eq!(ds[3].kind(), POPTAG_DIRECTIVE);
}

// ---------- Phase 2.1b: TRANSACTION header recognition ----------

#[test]
fn transaction_with_star_flag_header_only() {
    use SyntaxKind::*;
    // `*` indicates a completed transaction. Header-only (no
    // postings yet — that's the simplest TRANSACTION shape).
    let source = "2024-01-15 * \"Coffee\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), TRANSACTION);
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[DATE, WHITESPACE, STAR, WHITESPACE, STRING, NEWLINE]),
    );
}

#[test]
fn transaction_with_pending_kw_flag() {
    use SyntaxKind::*;
    // `!` lexes as PENDING_KW (`Token::Pending` →
    // `SyntaxKind::PENDING_KW`), NOT as `FLAG`. It signals an
    // incomplete/warning transaction in Beancount syntax.
    let source = "2024-01-15 ! \"WIP\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), TRANSACTION);
    // Pin the exact token sequence so a regression that
    // mistokenizes `!` or fails to wrap the full header fires.
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[DATE, WHITESPACE, PENDING_KW, WHITESPACE, STRING, NEWLINE]),
    );
}

#[test]
fn transaction_with_txn_keyword() {
    use SyntaxKind::*;
    // Explicit `txn` keyword form.
    let source = "2024-01-15 txn \"explicit\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), TRANSACTION);
}

#[test]
fn transaction_with_postings_wraps_full_multi_line_body() {
    use SyntaxKind::*;
    // Per cst::trivia's multi-line clause, TRANSACTION owns its
    // header AND every indented sub-line until non-indented
    // content (or EOF). Postings here are flat tokens inside
    // TRANSACTION; PR 2.2 will introduce POSTING / AMOUNT / etc.
    // sub-nodes.
    let source = "2024-01-15 * \"Coffee\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n\
                  \x20\x20Expenses:Food  5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), TRANSACTION);
    // SOURCE_FILE owns ONLY the TRANSACTION node — no orphaned
    // posting tokens.
    assert_eq!(elements_of(&tree), vec![Element::Node(TRANSACTION)]);
}

#[test]
fn transaction_with_metadata_and_postings() {
    use SyntaxKind::*;
    // Transactions can carry intra-transaction metadata AND
    // postings. All sub-lines inside TRANSACTION.
    let source = "2024-01-15 * \"Coffee\"\n\
                  \x20\x20note: \"morning\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n\
                  \x20\x20Expenses:Food  5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(elements_of(&tree), vec![Element::Node(TRANSACTION)]);
}

#[test]
fn transaction_with_payee_and_narration() {
    use SyntaxKind::*;
    // Full transaction header with payee + narration + tag + link.
    let source = "2024-01-15 * \"Coffee Shop\" \"Morning coffee\" #daily ^trip1\n\
                  \x20\x20Assets:Cash  -5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), TRANSACTION);
}

#[test]
fn transaction_terminates_at_next_top_level_directive() {
    use SyntaxKind::*;
    // After a transaction's postings, a non-indented DATE starts
    // a NEW directive. TRANSACTION must close cleanly; the next
    // OPEN_DIRECTIVE must not be absorbed.
    let source = "2024-01-15 * \"Coffee\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n\
                  2024-01-16 open Assets:Bank\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 2);
    assert_eq!(ds[0].kind(), TRANSACTION);
    assert_eq!(ds[1].kind(), OPEN_DIRECTIVE);
}

#[test]
fn transaction_terminates_at_blank_line_before_next_directive() {
    use SyntaxKind::*;
    // A blank line after a transaction's last posting ends it.
    // The blank-line NEWLINE becomes inter-directive trivia
    // leading the next directive (rule 2).
    let source = "2024-01-15 * \"Coffee\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n\
                  \n\
                  2024-01-16 open Assets:Bank\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 2);
    assert_eq!(ds[0].kind(), TRANSACTION);
    assert_eq!(ds[1].kind(), OPEN_DIRECTIVE);
    // The blank-line NEWLINE leads OPEN per rule 2.
    let d2_first = elements_of(&ds[1]).first().copied();
    assert_eq!(d2_first, Some(Element::Tok(NEWLINE)));
}

#[test]
fn transaction_with_indented_comment_between_postings() {
    use SyntaxKind::*;
    // Comments interleaved with postings stay inside TRANSACTION.
    let source = "2024-01-15 * \"Coffee\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n\
                  \x20\x20; documentation comment\n\
                  \x20\x20Expenses:Food  5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(elements_of(&tree), vec![Element::Node(TRANSACTION)]);
}

#[test]
fn transaction_with_implied_flag_via_bare_string() {
    use SyntaxKind::*;
    // Beancount accepts the implied-transaction shorthand:
    // `DATE WS STRING ...` with no explicit flag. The legacy
    // AST parser at parser.rs:1713 dispatches `Token::String(_)`
    // to parse_transaction_directive with an implied `*`. Common
    // in real ledgers as a convenient shorthand.
    let source = "2024-01-15 \"Coffee\"\n\
                  \x20\x20Assets:Cash 100 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), TRANSACTION);
    // SOURCE_FILE owns only the TRANSACTION — no orphaned posting.
    assert_eq!(elements_of(&tree), vec![Element::Node(TRANSACTION)]);
}

#[test]
fn transaction_with_hash_flag() {
    use SyntaxKind::*;
    // `#` is promoted to a transaction flag when it appears in
    // the post-DATE flag slot. The lexer's `Token::is_txn_flag`
    // includes Hash and the AST parser's `parse_flag` accepts it;
    // the CST mirrors that contract.
    let source = "2024-01-15 # \"pending hash\"\n\
                  \x20\x20Assets:Cash 100 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), TRANSACTION);
    // SOURCE_FILE owns only the TRANSACTION — no orphaned posting.
    assert_eq!(elements_of(&tree), vec![Element::Node(TRANSACTION)]);
}

#[test]
fn transaction_with_single_char_currency_as_flag() {
    use SyntaxKind::*;
    // NYSE/NASDAQ-style single-letter tickers (T, V, F, X, ...)
    // tokenize as CURRENCY (priority 3 over FLAG in the lexer)
    // but are accepted as transaction flags. The AST parser's
    // `parse_flag` arm `Token::Currency(s) if s.len() == 1` does
    // this; the CST mirrors it.
    let source = "2024-01-15 T \"AT&T dividend\"\n\
                  \x20\x20Assets:Brokerage 10 T\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), TRANSACTION);
    assert_eq!(elements_of(&tree), vec![Element::Node(TRANSACTION)]);
}

#[test]
fn transaction_multi_char_currency_after_date_is_not_a_flag() {
    // Guard against the reverse: `USD` (a real currency, length 3)
    // must NOT be treated as a transaction flag. The CURRENCY arm
    // gates on length == 1.
    let source = "2024-01-15 USD \"garbled\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    // No directive recognized — falls into the passthrough branch.
    let ds = directives(&tree);
    assert!(
        ds.is_empty(),
        "multi-char CURRENCY after DATE must not be a transaction flag",
    );
}

#[test]
fn transaction_blank_line_inside_body_terminates_and_orphans_subsequent_postings() {
    use SyntaxKind::*;
    // Pins the documented blank-line termination behavior (matches
    // Python beancount). The second posting after the blank line
    // ends up flat under SOURCE_FILE, not inside the TRANSACTION.
    // PR 2.2b's POSTING-wrapping work must NOT accidentally widen
    // the body scope across blank lines; this test guards that.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash 100 USD\n\
                  \n\
                  \x20\x20Liab:Card -100 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    // Exactly ONE recognized directive (the transaction). The
    // post-blank posting is flat passthrough, not a second
    // structural node.
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), TRANSACTION);

    // The TRANSACTION header tokens (DATE, STAR) are direct flat
    // children. The first posting line is wrapped in a POSTING
    // node; the second posting (post-blank) is NOT.
    let header_kinds: Vec<SyntaxKind> = elements_of(&ds[0])
        .iter()
        .filter_map(|e| match e {
            Element::Tok(k) => Some(*k),
            Element::Node(_) => None,
        })
        .collect();
    assert!(
        header_kinds.contains(&DATE) && header_kinds.contains(&STAR),
        "tx contains header",
    );
    // Exactly one POSTING is wrapped inside the TRANSACTION; the
    // post-blank posting is orphaned under SOURCE_FILE.
    let postings_inside_tx = ds[0].children().filter(|n| n.kind() == POSTING).count();
    assert_eq!(
        postings_inside_tx, 1,
        "only the FIRST posting is wrapped inside the tx; the second is orphaned",
    );
    // ACCOUNT count across the whole tree: 2 (one in the wrapped
    // POSTING, one orphaned flat under SOURCE_FILE).
    let total_accounts = tree
        .descendants_with_tokens()
        .filter(|e| e.kind() == ACCOUNT)
        .count();
    assert_eq!(total_accounts, 2);
}

#[test]
fn transaction_trailing_indented_comment_at_eof_stays_inside() {
    use SyntaxKind::*;
    // TRANSACTION deliberately diverges from rule 4 (which puts
    // indented trailing comments under SOURCE_FILE for the 14
    // single-line directive kinds). The transaction body
    // predicate accepts any indented non-blank line, so a
    // trailing indented comment after the last posting stays
    // inside the TRANSACTION. Compare with
    // `indented_comment_at_eof_after_no_metadata_directive_is_file_trailing`
    // earlier in this file for the OPEN_DIRECTIVE policy.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash 100 USD\n\
                  \x20\x20Liab:Card -100 USD\n\
                  \x20\x20; closing note for this transaction\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), TRANSACTION);
    // SOURCE_FILE owns ONLY the TRANSACTION — comment is inside.
    assert_eq!(elements_of(&tree), vec![Element::Node(TRANSACTION)]);
}

#[test]
fn transaction_unterminated_at_eof_with_postings() {
    use SyntaxKind::*;
    // No final NEWLINE on the last posting line. Per rule 5,
    // TRANSACTION wraps content up to EOF without fabricating
    // a terminator.
    let source = "2024-01-15 * \"Coffee\"\n\
                  \x20\x20Assets:Cash  -5.00 USD";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), TRANSACTION);
}

// ---------- Pass-through for still-unrecognized content ----------

// ---------- Phase 2.2a: META_ENTRY structural wrapping ----------

/// Walk all `META_ENTRY` descendants of a node, in source order.
fn meta_entries(node: &SyntaxNode) -> Vec<SyntaxNode> {
    node.descendants()
        .filter(|n| n.kind() == SyntaxKind::META_ENTRY)
        .collect()
}

#[test]
fn meta_entry_wraps_metadata_sub_line_inside_open_directive() {
    use SyntaxKind::*;
    let source = "2024-01-01 open Assets:Cash\n  description: \"main checking\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let mes = meta_entries(&tree);
    assert_eq!(mes.len(), 1);
    assert_eq!(
        elements_of(&mes[0]),
        tok_seq(&[WHITESPACE, META_KEY, WHITESPACE, STRING, NEWLINE]),
    );
}

#[test]
fn meta_entry_wraps_each_of_multiple_metadata_sub_lines() {
    use SyntaxKind::*;
    let source = "2024-01-01 open Assets:Cash\n\
                  \x20\x20key1: \"value1\"\n\
                  \x20\x20key2: \"value2\"\n\
                  \x20\x20key3: \"value3\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let mes = meta_entries(&tree);
    assert_eq!(mes.len(), 3);
    for me in &mes {
        assert_eq!(
            elements_of(me),
            tok_seq(&[WHITESPACE, META_KEY, WHITESPACE, STRING, NEWLINE]),
        );
    }
}

#[test]
fn meta_entry_does_not_wrap_indented_comments() {
    use SyntaxKind::*;
    // An indented `;`-comment between metadata entries stays as
    // flat children of the parent directive — NOT inside a
    // META_ENTRY. META_ENTRY is reserved for metadata sub-lines
    // proper (the `WS META_KEY ... NEWLINE` shape).
    let source = "2024-01-01 open Assets:Cash\n\
                  \x20\x20k1: \"v1\"\n\
                  \x20\x20; doc comment\n\
                  \x20\x20k2: \"v2\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let mes = meta_entries(&tree);
    assert_eq!(mes.len(), 2, "only k1 and k2 are META_ENTRYs");

    // The indented comment line lives as flat tokens (WS, COMMENT,
    // NEWLINE) inside the OPEN_DIRECTIVE between the two
    // META_ENTRY nodes.
    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    let kids: Vec<Element> = elements_of(&ds[0]);
    let comment_pos = kids
        .iter()
        .position(|e| matches!(e, Element::Tok(COMMENT)))
        .expect("indented COMMENT lives flat in the directive");
    let n_me_before_comment = kids[..comment_pos]
        .iter()
        .filter(|e| matches!(e, Element::Node(META_ENTRY)))
        .count();
    let n_me_after_comment = kids[comment_pos..]
        .iter()
        .filter(|e| matches!(e, Element::Node(META_ENTRY)))
        .count();
    assert_eq!(n_me_before_comment, 1, "k1 META_ENTRY precedes the comment");
    assert_eq!(n_me_after_comment, 1, "k2 META_ENTRY follows the comment");
}

#[test]
fn meta_entry_inside_transaction_body() {
    use SyntaxKind::*;
    // Transactions can carry intra-transaction metadata. The
    // META_ENTRY wrapping applies there too.
    let source = "2024-01-15 * \"Coffee\"\n\
                  \x20\x20note: \"morning\"\n\
                  \x20\x20Assets:Cash -5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let mes = meta_entries(&tree);
    assert_eq!(mes.len(), 1);
    assert_eq!(
        elements_of(&mes[0]),
        tok_seq(&[WHITESPACE, META_KEY, WHITESPACE, STRING, NEWLINE]),
    );

    // The `note:` line is at the same indent as the posting (2
    // spaces) and appears BEFORE the posting, so it's
    // TRANSACTION-level metadata: META_ENTRY is a direct child of
    // TRANSACTION. The posting line is now wrapped in POSTING
    // (PR 2.2b).
    let txs: Vec<SyntaxNode> = tree
        .children()
        .filter(|c| c.kind() == TRANSACTION)
        .collect();
    assert_eq!(txs.len(), 1);
    let n_meta_entries_in_tx = txs[0].children().filter(|n| n.kind() == META_ENTRY).count();
    assert_eq!(n_meta_entries_in_tx, 1);
    let n_postings_in_tx = txs[0].children().filter(|n| n.kind() == POSTING).count();
    assert_eq!(n_postings_in_tx, 1);
}

#[test]
fn meta_entry_at_eof_without_trailing_newline() {
    use SyntaxKind::*;
    // Per rule 5 of `cst::trivia` (unterminated final directive),
    // a metadata sub-line that ends mid-content without a final
    // NEWLINE still gets wrapped in META_ENTRY — the META_ENTRY
    // simply has no NEWLINE child. Pins the rustdoc claim.
    let source = "2024-01-01 open Assets:Cash\n  key: \"v\"";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let mes = meta_entries(&tree);
    assert_eq!(mes.len(), 1);
    // The META_ENTRY contains WS + META_KEY + WS + STRING and NO
    // NEWLINE (last token reached EOF).
    assert_eq!(
        elements_of(&mes[0]),
        tok_seq(&[WHITESPACE, META_KEY, WHITESPACE, STRING]),
    );
}

#[test]
fn meta_entry_with_value_kinds_other_than_string() {
    use SyntaxKind::*;
    // Metadata values can be a NUMBER, ACCOUNT, CURRENCY, DATE,
    // boolean, etc. META_ENTRY wraps the whole sub-line regardless
    // of the value kind — phase 3's typed AST will surface
    // `value()` accessors that decode by inspecting children.
    let source = "2024-01-01 open Assets:Cash\n\
                  \x20\x20count: 42\n\
                  \x20\x20since: 2024-01-01\n\
                  \x20\x20mirror: Assets:Mirror\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let mes = meta_entries(&tree);
    assert_eq!(mes.len(), 3);
    // Spot-check the second (DATE-valued) entry's value-token kind.
    let date_me_kinds = elements_of(&mes[1]);
    assert!(date_me_kinds.contains(&Element::Tok(DATE)));
}

// ---------- Phase 2.2b: POSTING structural wrapping ----------

/// Walk all `POSTING` descendants of a node, in source order.
fn postings(node: &SyntaxNode) -> Vec<SyntaxNode> {
    node.descendants()
        .filter(|n| n.kind() == SyntaxKind::POSTING)
        .collect()
}

#[test]
fn posting_wraps_account_only_line() {
    use SyntaxKind::*;
    // The simplest posting: indent + ACCOUNT (no amount). Beancount
    // calls this an "auto" posting — booking infers the amount from
    // the others. Round-trip + a single POSTING wrapper around the
    // sub-line.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    assert_eq!(
        elements_of(&ps[0]),
        tok_seq(&[WHITESPACE, ACCOUNT, NEWLINE]),
    );
}

#[test]
fn posting_wraps_account_with_amount_and_currency() {
    use SyntaxKind::*;
    // A normal posting with amount + currency. POSTING contains the
    // indent WHITESPACE, ACCOUNT, inter-token WHITESPACE, NUMBER,
    // WHITESPACE, CURRENCY, NEWLINE. AMOUNT sub-node wrapping is
    // PR 2.2c — for now, amount tokens are flat children of POSTING.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    assert_eq!(
        elements_of(&ps[0]),
        tok_seq(&[
            WHITESPACE, ACCOUNT, WHITESPACE, MINUS, NUMBER, WHITESPACE, CURRENCY, NEWLINE
        ]),
    );
}

#[test]
fn posting_wraps_each_of_multiple_postings_in_a_transaction() {
    use SyntaxKind::*;
    // Two postings → two POSTING nodes; each contains exactly its
    // own sub-line.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n\
                  \x20\x20Expenses:Food  5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 2);
    for p in &ps {
        let kinds: Vec<SyntaxKind> = elements_of(p)
            .iter()
            .filter_map(|e| match e {
                Element::Tok(k) => Some(*k),
                Element::Node(_) => None,
            })
            .collect();
        assert!(kinds.contains(&ACCOUNT) && kinds.contains(&NUMBER) && kinds.contains(&CURRENCY));
    }
}

#[test]
fn posting_with_pending_flag_wraps_flag_inside_node() {
    use SyntaxKind::*;
    // Beancount accepts `! Account ...` and `* Account ...` for
    // posting-level flags. The PENDING_KW / STAR / single-char FLAG
    // sits between the indent and the ACCOUNT inside the POSTING.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20! Assets:Cash  -5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    let kinds: Vec<SyntaxKind> = elements_of(&ps[0])
        .iter()
        .filter_map(|e| match e {
            Element::Tok(k) => Some(*k),
            Element::Node(_) => None,
        })
        .collect();
    assert_eq!(
        kinds,
        vec![
            WHITESPACE, PENDING_KW, WHITESPACE, ACCOUNT, WHITESPACE, MINUS, NUMBER, WHITESPACE,
            CURRENCY, NEWLINE
        ],
    );
}

#[test]
fn posting_attached_meta_entry_lives_inside_posting() {
    use SyntaxKind::*;
    // The key PR 2.2b semantic: a META_ENTRY sub-line at STRICTLY
    // GREATER indent than the preceding POSTING attaches to that
    // POSTING (not to the TRANSACTION). Mirrors the legacy AST
    // parser's `parse_posting_metadata` (DeepIndent loop), which
    // accumulates metadata into `posting.meta`.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n\
                  \x20\x20\x20\x20note: \"posting-attached\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let txs: Vec<SyntaxNode> = tree
        .children()
        .filter(|c| c.kind() == TRANSACTION)
        .collect();
    assert_eq!(txs.len(), 1);
    // TRANSACTION direct children: ONE POSTING, ZERO META_ENTRY
    // (the deeper-indented META_ENTRY belongs to the POSTING, not
    // to TRANSACTION).
    let tx_posting_count = txs[0].children().filter(|n| n.kind() == POSTING).count();
    let tx_meta_count = txs[0].children().filter(|n| n.kind() == META_ENTRY).count();
    assert_eq!(tx_posting_count, 1);
    assert_eq!(tx_meta_count, 0);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    // POSTING's children include the META_ENTRY as a structural
    // child (alongside the posting's flat tokens).
    let posting_meta_count = ps[0].children().filter(|n| n.kind() == META_ENTRY).count();
    assert_eq!(posting_meta_count, 1);
}

#[test]
fn posting_attached_meta_entry_at_same_indent_stays_at_transaction_level() {
    use SyntaxKind::*;
    // The complementary case: a META_ENTRY at the SAME indent as
    // the preceding POSTING is NOT posting-attached. It terminates
    // the POSTING and becomes a direct TRANSACTION-level child
    // (Beancount treats this as transaction-level metadata
    // interspersed between postings).
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n\
                  \x20\x20note: \"transaction-level\"\n\
                  \x20\x20Expenses:Food  5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let txs: Vec<SyntaxNode> = tree
        .children()
        .filter(|c| c.kind() == TRANSACTION)
        .collect();
    assert_eq!(txs.len(), 1);
    // TRANSACTION direct children: TWO POSTINGs (interspersed) +
    // ONE META_ENTRY at the SAME indent depth.
    let tx_posting_count = txs[0].children().filter(|n| n.kind() == POSTING).count();
    let tx_meta_count = txs[0].children().filter(|n| n.kind() == META_ENTRY).count();
    assert_eq!(tx_posting_count, 2);
    assert_eq!(tx_meta_count, 1);
    // Neither POSTING has a META_ENTRY child.
    for p in postings(&tree) {
        let inner_meta = p.children().filter(|n| n.kind() == META_ENTRY).count();
        assert_eq!(inner_meta, 0);
    }
}

#[test]
fn posting_attached_multiple_meta_entries_all_inside_posting() {
    use SyntaxKind::*;
    // Multiple deeper-indented metadata lines following the same
    // POSTING all attach to it.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n\
                  \x20\x20\x20\x20key1: \"v1\"\n\
                  \x20\x20\x20\x20key2: \"v2\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    let posting_meta_count = ps[0].children().filter(|n| n.kind() == META_ENTRY).count();
    assert_eq!(posting_meta_count, 2);
}

#[test]
fn posting_attached_meta_entry_terminates_at_next_posting() {
    use SyntaxKind::*;
    // After posting-attached metadata, a NEW POSTING line at the
    // standard indent closes the current POSTING and opens a new
    // one. The new POSTING starts empty (no inherited metadata).
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n\
                  \x20\x20\x20\x20note: \"on cash\"\n\
                  \x20\x20Expenses:Food  5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 2);
    // First POSTING owns the META_ENTRY; second is clean.
    let first_meta = ps[0].children().filter(|n| n.kind() == META_ENTRY).count();
    let second_meta = ps[1].children().filter(|n| n.kind() == META_ENTRY).count();
    assert_eq!(first_meta, 1);
    assert_eq!(second_meta, 0);
}

#[test]
fn postings_at_increasing_indents_produce_siblings_and_meta_attributes_to_latest() {
    use SyntaxKind::*;
    // Defensive shape: Beancount normally uses uniform posting
    // indentation. But the state machine doesn't enforce
    // monotonic indent — two posting lines at different indents
    // produce sibling POSTING nodes, and a subsequent META_ENTRY
    // attributes against the MOST-RECENTLY-OPENED POSTING's
    // indent. Pins this behavior so any future "monotonic indent"
    // refactor is a visible, intentional break.
    //
    // Source:
    //   posting at 2 spaces
    //   posting at 4 spaces  (DEEPER than the first)
    //   meta at 2 spaces     (NOT strictly deeper than 4)
    //
    // Expected: two POSTING siblings; the meta closes the second
    // (its indent is shallower) and lands at TRANSACTION level.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:A\n\
                  \x20\x20\x20\x20Assets:B  10 USD\n\
                  \x20\x20note: \"transaction-level\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 2, "two POSTING siblings at different indents");

    let txs: Vec<SyntaxNode> = tree
        .children()
        .filter(|c| c.kind() == TRANSACTION)
        .collect();
    assert_eq!(txs.len(), 1);
    let tx_meta = txs[0].children().filter(|n| n.kind() == META_ENTRY).count();
    assert_eq!(
        tx_meta, 1,
        "meta at shallower indent than the open POSTING lands at TRANSACTION level",
    );
    // Neither POSTING owns the META_ENTRY.
    for p in &ps {
        let inner_meta = p.children().filter(|n| n.kind() == META_ENTRY).count();
        assert_eq!(inner_meta, 0);
    }
}

#[test]
fn meta_entry_before_first_posting_stays_at_transaction_level() {
    use SyntaxKind::*;
    // A META_ENTRY that appears BEFORE any POSTING (regardless of
    // indent depth, since there's no preceding POSTING to attach
    // to) is always TRANSACTION-level.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20\x20\x20note: \"before posting\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let txs: Vec<SyntaxNode> = tree
        .children()
        .filter(|c| c.kind() == TRANSACTION)
        .collect();
    assert_eq!(txs.len(), 1);
    let tx_meta = txs[0].children().filter(|n| n.kind() == META_ENTRY).count();
    let tx_posting = txs[0].children().filter(|n| n.kind() == POSTING).count();
    assert_eq!(tx_meta, 1);
    assert_eq!(tx_posting, 1);
    // The POSTING itself has no META_ENTRY child.
    let ps = postings(&tree);
    assert_eq!(
        ps[0].children().filter(|n| n.kind() == META_ENTRY).count(),
        0
    );
}

#[test]
fn deeper_indented_comment_stays_inside_posting_with_following_meta() {
    use SyntaxKind::*;
    // Doc-comment-for-following-posting-metadata idiom: an indented
    // `;` comment at indent STRICTLY GREATER than the open POSTING
    // (and at the same depth as the subsequent posting-attached
    // META_ENTRY) belongs to the POSTING. Both the comment AND the
    // META_ENTRY land inside the POSTING node.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n\
                  \x20\x20\x20\x20; comment about note\n\
                  \x20\x20\x20\x20note: \"deeper\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);

    // The deeper-indented META_ENTRY is attached to the POSTING.
    let posting_meta_count = ps[0].children().filter(|n| n.kind() == META_ENTRY).count();
    assert_eq!(posting_meta_count, 1);

    // The deeper-indented COMMENT token is also inside POSTING.
    let posting_comment_count = ps[0]
        .children_with_tokens()
        .filter(|e| e.kind() == COMMENT)
        .count();
    assert_eq!(
        posting_comment_count, 1,
        "deeper-indented `;` comment stays inside POSTING with following meta",
    );

    // TRANSACTION's direct children have ZERO orphaned META_ENTRY
    // or COMMENT.
    let txs: Vec<SyntaxNode> = tree
        .children()
        .filter(|c| c.kind() == TRANSACTION)
        .collect();
    let tx_meta = txs[0].children().filter(|n| n.kind() == META_ENTRY).count();
    let tx_comment = txs[0]
        .children_with_tokens()
        .filter(|e| e.kind() == COMMENT)
        .count();
    assert_eq!(tx_meta, 0);
    assert_eq!(tx_comment, 0);
}

#[test]
fn deeper_indented_comment_stays_inside_posting_even_without_following_meta() {
    use SyntaxKind::*;
    // Rule is purely indent-based: a deeper-indented comment
    // belongs to the open POSTING regardless of whether a
    // META_ENTRY follows. Pins the rule's edge so the predicate
    // can't drift to "only attach when followed by meta".
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n\
                  \x20\x20\x20\x20; trailing posting doc\n\
                  \x20\x20Expenses:Food  5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 2);
    let first_comment_count = ps[0]
        .children_with_tokens()
        .filter(|e| e.kind() == COMMENT)
        .count();
    let second_comment_count = ps[1]
        .children_with_tokens()
        .filter(|e| e.kind() == COMMENT)
        .count();
    assert_eq!(first_comment_count, 1);
    assert_eq!(second_comment_count, 0);
}

#[test]
fn posting_with_indented_comment_between_postings_terminates_posting() {
    use SyntaxKind::*;
    // An indented `;`-comment between two posting lines is
    // TRANSACTION-level inter-posting trivia: it closes the
    // current POSTING. The comment ends up as flat tokens between
    // the two POSTING nodes (matches the existing
    // `transaction_with_indented_comment_between_postings`
    // structural intent).
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash  -5.00 USD\n\
                  \x20\x20; doc comment\n\
                  \x20\x20Expenses:Food  5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 2);
    // The COMMENT token lives between the two POSTING nodes as a
    // flat child of TRANSACTION, NOT inside either POSTING.
    let txs: Vec<SyntaxNode> = tree
        .children()
        .filter(|c| c.kind() == TRANSACTION)
        .collect();
    let tx_kids = elements_of(&txs[0]);
    let first_posting_idx = tx_kids
        .iter()
        .position(|e| matches!(e, Element::Node(POSTING)))
        .unwrap();
    let comment_idx = tx_kids
        .iter()
        .position(|e| matches!(e, Element::Tok(COMMENT)))
        .expect("indented comment is a flat TRANSACTION child");
    assert!(
        comment_idx > first_posting_idx,
        "comment follows first POSTING"
    );
}

#[test]
fn posting_at_eof_without_trailing_newline_still_wrapped() {
    use SyntaxKind::*;
    // Per rule 5 of `cst::trivia` (unterminated final directive),
    // a POSTING that reaches EOF mid-content without a final
    // NEWLINE still gets wrapped — the POSTING simply has no
    // NEWLINE child.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash  -5.00 USD";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    let kinds: Vec<SyntaxKind> = elements_of(&ps[0])
        .iter()
        .filter_map(|e| match e {
            Element::Tok(k) => Some(*k),
            Element::Node(_) => None,
        })
        .collect();
    assert_eq!(
        kinds,
        vec![
            WHITESPACE, ACCOUNT, WHITESPACE, MINUS, NUMBER, WHITESPACE, CURRENCY
        ],
    );
}

#[test]
fn star_flagged_posting_wraps_flag_inside_node() {
    use SyntaxKind::*;
    // `* Account ...` (STAR-flagged posting) is also a valid
    // beancount posting shape. The STAR sits between the indent
    // and the ACCOUNT inside POSTING.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20* Assets:Cash  -5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    let kinds: Vec<SyntaxKind> = elements_of(&ps[0])
        .iter()
        .filter_map(|e| match e {
            Element::Tok(k) => Some(*k),
            Element::Node(_) => None,
        })
        .collect();
    assert!(kinds.starts_with(&[WHITESPACE, STAR, WHITESPACE, ACCOUNT]));
}

#[test]
fn flagged_posting_with_question_mark_wraps_flag_inside_node() {
    use SyntaxKind::*;
    // `? Account ...` — the `?` flag emits a FLAG token (the
    // single-letter alphabetic flags P/S/T/C/U/R/M are tokenized
    // as CURRENCY by lexer priority 3 — covered by
    // `single_char_currency_flagged_posting_wraps_currency_as_flag`).
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20? Assets:Cash  -5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    let kinds: Vec<SyntaxKind> = elements_of(&ps[0])
        .iter()
        .filter_map(|e| match e {
            Element::Tok(k) => Some(*k),
            Element::Node(_) => None,
        })
        .collect();
    assert!(kinds.starts_with(&[WHITESPACE, FLAG, WHITESPACE, ACCOUNT]));
}

#[test]
fn hash_flagged_posting_wraps_hash_inside_node() {
    use SyntaxKind::*;
    // `# Account ...` is a valid Beancount posting flag (legacy
    // `parse_flag` accepts `Token::Hash`; `identify_directive`
    // accepts HASH as a transaction trigger). Pin that
    // `starts_posting_sub_line` recognizes it so the line is
    // wrapped in POSTING rather than falling through as flat
    // tokens.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20# Assets:Cash  -5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    let kinds: Vec<SyntaxKind> = elements_of(&ps[0])
        .iter()
        .filter_map(|e| match e {
            Element::Tok(k) => Some(*k),
            Element::Node(_) => None,
        })
        .collect();
    assert!(kinds.starts_with(&[WHITESPACE, HASH, WHITESPACE, ACCOUNT]));
}

#[test]
fn hash_flagged_posting_attached_meta_entry_lives_inside_posting() {
    use SyntaxKind::*;
    // Combines HASH flag with posting-attached META_ENTRY (the
    // shape the bare hash_flagged_posting_wraps_hash_inside_node
    // test alone couldn't catch a regression on). If a future
    // change drops HASH from `starts_posting_sub_line`, this test
    // fails because the line would no longer open a POSTING and
    // the deeper-indented META_ENTRY would orphan to TRANSACTION.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20# Assets:Cash  -5.00 USD\n\
                  \x20\x20\x20\x20note: \"hash-flagged\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    let posting_meta_count = ps[0].children().filter(|n| n.kind() == META_ENTRY).count();
    assert_eq!(posting_meta_count, 1);

    let txs: Vec<SyntaxNode> = tree
        .children()
        .filter(|c| c.kind() == TRANSACTION)
        .collect();
    let tx_meta = txs[0].children().filter(|n| n.kind() == META_ENTRY).count();
    assert_eq!(tx_meta, 0);
}

#[test]
fn deeper_indented_trailing_comment_at_eof_stays_inside_posting() {
    use SyntaxKind::*;
    // Doc-comment-attribution rule extended to the EOF case: a
    // deeper-indented `;` comment that is the LAST sub-line of the
    // file (no final NEWLINE) still attaches to the open POSTING.
    // Per rule 5 of `cst::trivia` (recursive application: an
    // unterminated POSTING ends at its last content token without a
    // NEWLINE child of its own).
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash 1 USD\n\
                  \x20\x20\x20\x20; deep trailing";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    let posting_comment_count = ps[0]
        .children_with_tokens()
        .filter(|e| e.kind() == COMMENT)
        .count();
    assert_eq!(
        posting_comment_count, 1,
        "EOF-trailing deep `;` comment is a child of POSTING",
    );

    // No COMMENT orphaned to TRANSACTION level.
    let txs: Vec<SyntaxNode> = tree
        .children()
        .filter(|c| c.kind() == TRANSACTION)
        .collect();
    let tx_comment = txs[0]
        .children_with_tokens()
        .filter(|e| e.kind() == COMMENT)
        .count();
    assert_eq!(tx_comment, 0);
}

#[test]
fn deeper_indented_emacs_directive_attaches_to_open_posting() {
    use SyntaxKind::*;
    // `is_comment_token` includes EMACS_DIRECTIVE (`#+`). The
    // indented-comment branch in `emit_transaction_body` routes it
    // through the same indent-attribution rule as COMMENT: deeper-
    // indented than the open POSTING = stays INSIDE POSTING.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash 1 USD\n\
                  \x20\x20\x20\x20#+STARTUP: overview\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    let emacs_inside_posting = ps[0]
        .children_with_tokens()
        .filter(|e| e.kind() == EMACS_DIRECTIVE)
        .count();
    assert_eq!(
        emacs_inside_posting, 1,
        "EMACS_DIRECTIVE recognized as comment-class trivia, attaches by indent",
    );
}

#[test]
fn deeper_indented_shebang_attaches_to_open_posting() {
    use SyntaxKind::*;
    // Companion to the EMACS_DIRECTIVE test: pin that SHEBANG
    // (`#!`) is also recognized as comment-class trivia via
    // `is_comment_token` and follows the same indent-attribution
    // rule. Catches a regression that drops SHEBANG from the
    // helper while leaving EMACS_DIRECTIVE in place.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash 1 USD\n\
                  \x20\x20\x20\x20#!/usr/bin/env something\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    let shebang_inside_posting = ps[0]
        .children_with_tokens()
        .filter(|e| e.kind() == SHEBANG)
        .count();
    assert_eq!(
        shebang_inside_posting, 1,
        "SHEBANG recognized as comment-class trivia, attaches by indent",
    );
}

#[test]
fn deeper_indented_percent_comment_attaches_to_open_posting() {
    use SyntaxKind::*;
    // PERCENT_COMMENT (`%`) is included in `is_comment_token` but
    // every other comment-attribution test uses `;`. Pin the `%`
    // path so a regression that demotes PERCENT_COMMENT (e.g., via
    // a typo or split refactor) fails here.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash 1 USD\n\
                  \x20\x20\x20\x20% percent-style doc\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    let pct_inside_posting = ps[0]
        .children_with_tokens()
        .filter(|e| e.kind() == PERCENT_COMMENT)
        .count();
    assert_eq!(
        pct_inside_posting, 1,
        "PERCENT_COMMENT recognized as comment-class trivia, attaches by indent",
    );
}

#[test]
fn directive_body_absorbs_indented_emacs_directive_when_block_has_meta() {
    use SyntaxKind::*;
    // The `is_comment_token` widening also affects
    // `upcoming_indented_block_has_meta` and
    // `is_indented_directive_continuation` for NON-transaction
    // directives. Pin that an indented `#+STARTUP` line inside an
    // OPEN_DIRECTIVE that ALSO contains a meta line is absorbed as
    // a continuation (rather than orphaning to SOURCE_FILE).
    // Mirrors the existing `indented_comment_before_first_metadata`
    // / `indented_comment_between_metadata_lines` tests, which use
    // `;` only; this pins the SHEBANG/EMACS_DIRECTIVE branch.
    let source = "2024-01-01 open Assets:Cash\n\
                  \x20\x20#+STARTUP: overview\n\
                  \x20\x20key: \"v\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), OPEN_DIRECTIVE);

    // The EMACS_DIRECTIVE token lives inside the OPEN_DIRECTIVE,
    // not orphaned anywhere else in the tree. Use `descendants`
    // symmetrically on both sides so a future refactor that wraps
    // SOURCE_FILE trivia in any nested node doesn't make the
    // orphan check vacuously pass.
    let emacs_total = tree
        .descendants_with_tokens()
        .filter(|e| e.kind() == EMACS_DIRECTIVE)
        .count();
    let emacs_in_directive = ds[0]
        .descendants_with_tokens()
        .filter(|e| e.kind() == EMACS_DIRECTIVE)
        .count();
    assert_eq!(emacs_total, 1, "exactly one EMACS_DIRECTIVE in the tree");
    assert_eq!(
        emacs_in_directive, 1,
        "EMACS_DIRECTIVE absorbed by OPEN_DIRECTIVE"
    );

    // The block_has_meta look-ahead is what kept the EMACS line
    // inside the directive: the subsequent `key: "v"` becomes a
    // META_ENTRY child of OPEN_DIRECTIVE. Assert that META_ENTRY
    // actually appears so a regression that breaks the META_KEY
    // arm (closing the directive AFTER the EMACS line but BEFORE
    // the meta) fails here, not silently.
    let meta_entries_in_directive = ds[0]
        .descendants()
        .filter(|n| n.kind() == META_ENTRY)
        .count();
    assert_eq!(meta_entries_in_directive, 1, "META_ENTRY also absorbed");
}

#[test]
fn directive_body_does_not_absorb_indented_emacs_directive_when_no_meta() {
    use SyntaxKind::*;
    // Complementary case: when an OPEN_DIRECTIVE has NO meta block,
    // an indented EMACS_DIRECTIVE / SHEBANG / `;`-comment that
    // follows the header is NOT a continuation (per the
    // block_has_meta gate). Pins that the widening did not
    // accidentally make these tokens unconditional continuations.
    let source = "2024-01-01 open Assets:Cash\n\
                  \x20\x20#+STARTUP: trailing only\n\
                  2024-01-02 open Assets:Bank\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(
        ds.len(),
        2,
        "two OPEN_DIRECTIVES, separated by EMACS_DIRECTIVE rule-2 trivia"
    );
    assert_eq!(ds[0].kind(), OPEN_DIRECTIVE);
    assert_eq!(ds[1].kind(), OPEN_DIRECTIVE);

    // The EMACS_DIRECTIVE is rule-2 inter-directive trivia: it
    // attaches as LEADING trivia of the SECOND directive (per
    // `cst::trivia`), NOT as a continuation of the first.
    // Symmetric `descendants` walks on both sides and a total-
    // count sanity check guard against future structural changes
    // that wrap trivia in a nested node.
    let emacs_total = tree
        .descendants_with_tokens()
        .filter(|e| e.kind() == EMACS_DIRECTIVE)
        .count();
    let emacs_in_first = ds[0]
        .descendants_with_tokens()
        .filter(|e| e.kind() == EMACS_DIRECTIVE)
        .count();
    let emacs_in_second = ds[1]
        .descendants_with_tokens()
        .filter(|e| e.kind() == EMACS_DIRECTIVE)
        .count();
    assert_eq!(emacs_total, 1, "exactly one EMACS_DIRECTIVE in the tree");
    assert_eq!(
        emacs_in_first, 0,
        "EMACS_DIRECTIVE is NOT absorbed by header-only directive"
    );
    assert_eq!(
        emacs_in_second, 1,
        "EMACS_DIRECTIVE leads the next directive as rule-2 trivia"
    );
}

#[test]
fn catch_all_indented_unknown_content_closes_posting_and_emits_flat() {
    use SyntaxKind::*;
    // Catch-all `else` branch of emit_transaction_body: an indented
    // sub-line that is neither posting, meta, nor comment closes
    // any open POSTING and emits flat at TRANSACTION level.
    // Examples: a stray bare STRING on its own indented line. Pin
    // the behavior so PR 2.2c (AMOUNT continuations etc.) doesn't
    // silently shift attribution without an explicit test update.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash 1 USD\n\
                  \x20\x20\"stray string on own line\"\n\
                  \x20\x20Expenses:Food 1 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(
        ps.len(),
        2,
        "stray indented STRING closes POSTING; next POSTING opens fresh"
    );

    let txs: Vec<SyntaxNode> = tree
        .children()
        .filter(|c| c.kind() == TRANSACTION)
        .collect();
    // The stray STRING token is a flat child of TRANSACTION (not
    // inside either POSTING). TRANSACTION's direct STRING tokens
    // include the header narration "x" PLUS the stray, for a total
    // of 2.
    let tx_strings: usize = txs[0]
        .children_with_tokens()
        .filter(|e| e.kind() == STRING)
        .count();
    assert_eq!(tx_strings, 2);
    for p in &ps {
        let inside_string = p
            .children_with_tokens()
            .filter(|e| e.kind() == STRING)
            .count();
        assert_eq!(inside_string, 0);
    }
}

#[test]
fn same_indent_comment_between_posting_and_deeper_meta_orphans_meta() {
    use SyntaxKind::*;
    // The same-indent `;` comment between a posting and a deeper-
    // indented META_KEY closes the POSTING (per the
    // indent-attribution rule: comment indent is not strictly
    // greater than posting indent). The subsequent deeper-indented
    // META_KEY then has no open POSTING and lands at TRANSACTION
    // level. Matches the legacy AST parser's
    // `parse_posting_metadata` loop, which terminates posting-
    // attached metadata at any indented sub-line that is not a
    // DeepIndent META_KEY (a same-indent COMMENT being one such
    // terminator). Python beancount parity is NOT verified here —
    // a future compat audit may find Python attaches the deeper
    // META to the still-open posting, in which case this test is
    // the touch-point. Pinned so a future refactor can't silently
    // flip the attribution without a test update.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20Assets:Cash -5 USD\n\
                  \x20\x20; explicit break at posting indent\n\
                  \x20\x20\x20\x20key: \"orphaned\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    let posting_meta_count = ps[0].children().filter(|n| n.kind() == META_ENTRY).count();
    assert_eq!(
        posting_meta_count, 0,
        "same-indent comment ends posting-attached meta block; deeper meta orphans to TRANSACTION",
    );

    let txs: Vec<SyntaxNode> = tree
        .children()
        .filter(|c| c.kind() == TRANSACTION)
        .collect();
    let tx_meta = txs[0].children().filter(|n| n.kind() == META_ENTRY).count();
    assert_eq!(tx_meta, 1);
}

#[test]
fn single_char_currency_flagged_posting_wraps_currency_as_flag() {
    use SyntaxKind::*;
    // `P Account ...` — `P` tokenizes as CURRENCY (lexer priority
    // 3) but functions as a posting flag, mirroring the transaction
    // header's same Currency-vs-Flag tie-break. POSTING still wraps
    // the line.
    let source = "2024-01-15 * \"x\"\n\
                  \x20\x20P Assets:Cash  -5.00 USD\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ps = postings(&tree);
    assert_eq!(ps.len(), 1);
    let kinds: Vec<SyntaxKind> = elements_of(&ps[0])
        .iter()
        .filter_map(|e| match e {
            Element::Tok(k) => Some(*k),
            Element::Node(_) => None,
        })
        .collect();
    assert!(kinds.starts_with(&[WHITESPACE, CURRENCY, WHITESPACE, ACCOUNT]));
}

#[test]
fn commodity_with_metadata_wraps_full_multi_line_directive() {
    use SyntaxKind::*;
    // Per cst::trivia, a directive that carries indented metadata
    // sub-lines spans MULTIPLE LINES — the directive's last content
    // token is the last content token of its LAST sub-line, not
    // the header. The COMMODITY_DIRECTIVE node must therefore span
    // the header AND the metadata line.
    let source = "2024-01-01 commodity HOOL\n  name: \"Hooli Common shares.\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), COMMODITY_DIRECTIVE);
    // PR 2.2a: the metadata sub-line is now wrapped in META_ENTRY.
    // The directive owns the header tokens followed by the
    // META_ENTRY node (which contains the indented metadata's
    // tokens internally).
    assert_eq!(
        elements_of(&ds[0]),
        vec![
            Element::Tok(DATE),
            Element::Tok(WHITESPACE),
            Element::Tok(COMMODITY_KW),
            Element::Tok(WHITESPACE),
            Element::Tok(CURRENCY),
            Element::Tok(NEWLINE),
            Element::Node(META_ENTRY),
        ],
    );

    // Drill into the META_ENTRY: it owns the indent + key +
    // value tokens + terminator NEWLINE.
    let me = ds[0]
        .children()
        .find(|n| n.kind() == META_ENTRY)
        .expect("directive contains a META_ENTRY child");
    assert_eq!(
        elements_of(&me),
        tok_seq(&[WHITESPACE, META_KEY, WHITESPACE, STRING, NEWLINE]),
    );

    // SOURCE_FILE owns ONLY the directive — no orphaned metadata.
    assert_eq!(elements_of(&tree), vec![Element::Node(COMMODITY_DIRECTIVE)]);
}

#[test]
fn open_with_multiple_metadata_lines_wraps_all_inside_directive() {
    use SyntaxKind::*;
    let source = "2024-01-01 open Assets:Cash USD\n\
                  \x20\x20description: \"main checking\"\n\
                  \x20\x20priority: \"high\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), OPEN_DIRECTIVE);
    // OPEN_DIRECTIVE node should contain header + BOTH metadata
    // lines (no orphaned content under SOURCE_FILE).
    assert_eq!(elements_of(&tree), vec![Element::Node(OPEN_DIRECTIVE)]);
}

#[test]
fn directive_with_metadata_then_next_directive() {
    use SyntaxKind::*;
    // After a metadata-carrying directive, the next directive
    // starts cleanly — the metadata-loop must stop when the indent
    // pattern ends.
    let source = "2024-01-01 open Assets:Cash USD\n\
                  \x20\x20description: \"main\"\n\
                  2024-01-02 close Assets:Cash\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 2);
    assert_eq!(ds[0].kind(), OPEN_DIRECTIVE);
    assert_eq!(ds[1].kind(), CLOSE_DIRECTIVE);
}

#[test]
fn indented_comment_after_no_metadata_directive_leads_next_directive() {
    use SyntaxKind::*;
    // An indented comment AFTER a directive that has no metadata
    // is inter-directive trivia per rule 2 — it leads the NEXT
    // directive, NOT trailing into the previous one. The widening
    // of is_indented_directive_continuation must be gated on a
    // prior META_KEY in the body; otherwise this comment is
    // wrongly absorbed into the preceding directive.
    let source = "2024-01-01 open Assets:Cash\n\
                  \x20\x20; documentation for the next directive\n\
                  2024-01-02 close Assets:Cash\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 2);
    assert_eq!(ds[0].kind(), OPEN_DIRECTIVE);
    assert_eq!(ds[1].kind(), CLOSE_DIRECTIVE);

    // d1 OWNS its header NEWLINE only — no trailing trivia.
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, NEWLINE]),
        "rule 2: indented comment after header-only directive must NOT be absorbed; \
         it's inter-directive trivia leading the next directive",
    );

    // d2 leads with the indented comment + its NEWLINE.
    let d2_first = elements_of(&ds[1])
        .iter()
        .take_while(|e| !matches!(e, Element::Tok(DATE)))
        .copied()
        .collect::<Vec<_>>();
    assert_eq!(
        d2_first,
        tok_seq(&[WHITESPACE, COMMENT, NEWLINE]),
        "rule 2: leading trivia of d2 must include the inter-directive comment",
    );
}

#[test]
fn indented_comment_at_eof_after_no_metadata_directive_is_file_trailing() {
    use SyntaxKind::*;
    // An indented comment at EOF following a header-only directive
    // is file-trailing trivia per rule 4 — it attaches to
    // SOURCE_FILE, NOT inside the directive. v3's overbroad
    // widening incorrectly absorbed this; the META_KEY gate
    // restores rule 4 conformance.
    let source = "2024-01-01 open Assets:Cash\n\
                  \x20\x20; trailing indented comment\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(
        elements_of(&ds[0]),
        tok_seq(&[DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, NEWLINE]),
        "directive owns ONLY its header + terminator NEWLINE",
    );

    // SOURCE_FILE owns the trailing WS + COMMENT + NEWLINE.
    assert_eq!(
        elements_of(&tree),
        vec![
            Element::Node(OPEN_DIRECTIVE),
            Element::Tok(WHITESPACE),
            Element::Tok(COMMENT),
            Element::Tok(NEWLINE),
        ],
        "rule 4: indented trailing comment is file-trailing under SOURCE_FILE",
    );
}

#[test]
fn indented_comment_before_first_metadata_stays_inside_directive() {
    use SyntaxKind::*;
    // The "documentation-comment-for-the-following-field" idiom
    // — an indented `;` line BEFORE the first META_KEY. v4's per-
    // line `body_has_meta` couldn't see the META_KEY that came
    // after the comment, so v4 silently closed the directive at
    // the comment and orphaned the metadata. v5's prospective
    // upcoming_indented_block_has_meta scan catches it.
    let source = "2024-01-01 open Assets:Cash\n\
                  \x20\x20; documentation for the next field\n\
                  \x20\x20description: \"main checking\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), OPEN_DIRECTIVE);
    // The OPEN_DIRECTIVE owns the entire input — header, the
    // documentation comment, AND the metadata line. SOURCE_FILE
    // has no orphaned children.
    assert_eq!(elements_of(&tree), vec![Element::Node(OPEN_DIRECTIVE)]);
    // Specifically: NO bare META_KEY appears as a direct child of
    // SOURCE_FILE (would mean the v4 orphaning regression).
    let sf_token_kinds: Vec<SyntaxKind> = elements_of(&tree)
        .iter()
        .filter_map(|e| match e {
            Element::Tok(k) => Some(*k),
            Element::Node(_) => None,
        })
        .collect();
    assert!(
        !sf_token_kinds.contains(&META_KEY),
        "META_KEY orphaned to SOURCE_FILE: {sf_token_kinds:?}",
    );
}

#[test]
fn indented_comment_between_metadata_lines_stays_inside_directive() {
    use SyntaxKind::*;
    // Beancount idiom: documentation comments between metadata
    // entries. They MUST stay inside the directive — otherwise the
    // metadata that follows is orphaned to SOURCE_FILE, losing
    // structural ownership and producing a tree where bare
    // META_KEY tokens sit directly under SOURCE_FILE.
    let source = "2024-01-01 open Assets:Cash\n\
                  \x20\x20k1: \"v1\"\n\
                  \x20\x20; doc comment for k2\n\
                  \x20\x20k2: \"v2\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 1);
    assert_eq!(ds[0].kind(), OPEN_DIRECTIVE);
    // The entire multi-line body — header + k1 + indented comment
    // + k2 — must be inside the OPEN_DIRECTIVE. SOURCE_FILE owns
    // ONLY the directive node.
    assert_eq!(elements_of(&tree), vec![Element::Node(OPEN_DIRECTIVE)]);
    // Specifically: no META_KEY appears as a direct child of
    // SOURCE_FILE (would mean orphaning).
    let sf_children: Vec<SyntaxKind> = elements_of(&tree)
        .iter()
        .filter_map(|e| match e {
            Element::Tok(k) => Some(*k),
            Element::Node(_) => None,
        })
        .collect();
    assert!(
        !sf_children.contains(&META_KEY),
        "META_KEY orphaned to SOURCE_FILE: {sf_children:?}",
    );
}

#[test]
fn blank_line_between_metadata_lines_terminates_directive() {
    use SyntaxKind::*;
    // A blank line breaks the indented-metadata run; the second
    // metadata line is NOT part of the same directive. Conservative
    // interpretation: stop at the first non-indented-meta line.
    let source = "2024-01-01 open Assets:Cash USD\n\
                  \x20\x20description: \"main\"\n\
                  \n\
                  2024-01-02 close Assets:Cash\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 2);
    assert_eq!(ds[0].kind(), OPEN_DIRECTIVE);
    assert_eq!(ds[1].kind(), CLOSE_DIRECTIVE);
    // The blank-line NEWLINE leads d2 per rule 2.
    let d2_first = elements_of(&ds[1]).first().copied();
    assert_eq!(d2_first, Some(Element::Tok(NEWLINE)));
}

#[test]
fn malformed_date_then_keyword_on_next_line_is_not_a_directive() {
    // Beancount directive headers are single-line: `DATE keyword
    // ...` on ONE line. If a DATE is followed by a NEWLINE (then
    // a keyword on the next line), the identifier MUST NOT
    // recognize it as a directive — otherwise emit_through_terminator
    // would stop at the first NEWLINE and produce a node
    // containing only `[DATE, NEWLINE]`, orphaning the keyword.
    let source = "2024-01-01\nopen Assets:Cash\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);
    // Neither line is a recognized directive — both pass through
    // flat.
    let ds = directives(&tree);
    assert!(
        ds.is_empty(),
        "DATE alone on a line is malformed; identifier must not pretend it starts an OPEN_DIRECTIVE just because the next non-trivia token (skipping the NEWLINE) happens to be OPEN_KW",
    );
}

#[test]
fn option_directive_passes_through_flat() {
    // PR 2.3 handles `option`. Until then: flat passthrough.
    let source = "option \"title\" \"My Ledger\"\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert!(ds.is_empty());
}

#[test]
fn recognized_and_passthrough_can_coexist() {
    use SyntaxKind::*;
    // OPTION is still pass-through (PR 2.3). The other three are
    // recognized: OPEN, TRANSACTION (PR 2.1b), CLOSE.
    let source = "option \"title\" \"My Ledger\"\n\
                  2024-01-01 open Assets:Cash\n\
                  2024-01-15 * \"Coffee\"\n\
                  2024-01-16 close Assets:Cash\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    let ds = directives(&tree);
    assert_eq!(ds.len(), 3);
    assert_eq!(ds[0].kind(), OPEN_DIRECTIVE);
    assert_eq!(ds[1].kind(), TRANSACTION);
    assert_eq!(ds[2].kind(), CLOSE_DIRECTIVE);
}

// ---------- Edge cases ----------

#[test]
fn empty_source() {
    let tree = parse_structured("");
    assert_round_trip("", &tree);
    assert_eq!(tree.kind(), SyntaxKind::SOURCE_FILE);
    assert!(directives(&tree).is_empty());
}

#[test]
fn only_trivia_no_directives() {
    use SyntaxKind::*;
    let source = ";; only a comment\n\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    assert!(directives(&tree).is_empty());
    // All under SOURCE_FILE.
    assert_eq!(
        elements_of(&tree),
        vec![
            Element::Tok(COMMENT),
            Element::Tok(NEWLINE),
            Element::Tok(NEWLINE)
        ],
    );
}

#[test]
fn bom_under_source_file_directive_follows() {
    use SyntaxKind::*;
    let source = "\u{FEFF}2024-01-01 open Assets:Cash\n";
    let tree = parse_structured(source);
    assert_round_trip(source, &tree);

    // BOM is file-leading; first directive comes after.
    assert_eq!(
        elements_of(&tree),
        vec![Element::Tok(BOM), Element::Node(OPEN_DIRECTIVE)],
    );
}
