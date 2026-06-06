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
    // PR 2.2's POSTING-wrapping work must NOT accidentally widen
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

    // The TRANSACTION owns only header + first posting line.
    let tx_kinds: Vec<SyntaxKind> = elements_of(&ds[0])
        .iter()
        .filter_map(|e| match e {
            Element::Tok(k) => Some(*k),
            Element::Node(_) => None,
        })
        .collect();
    assert!(
        tx_kinds.contains(&DATE) && tx_kinds.contains(&STAR),
        "tx contains header",
    );
    // The second ACCOUNT (Liab:Card) is NOT inside the transaction.
    let accounts_inside_tx = tx_kinds.iter().filter(|k| **k == ACCOUNT).count();
    assert_eq!(
        accounts_inside_tx, 1,
        "only the FIRST posting's ACCOUNT is inside the tx; the second is orphaned",
    );
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

    // The posting line (WS ACCOUNT WS ...) stays flat under
    // TRANSACTION — PR 2.2b will wrap it in POSTING.
    let txs: Vec<SyntaxNode> = tree
        .children()
        .filter(|c| c.kind() == TRANSACTION)
        .collect();
    assert_eq!(txs.len(), 1);
    let n_meta_entries_in_tx = txs[0].children().filter(|n| n.kind() == META_ENTRY).count();
    assert_eq!(n_meta_entries_in_tx, 1);
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
