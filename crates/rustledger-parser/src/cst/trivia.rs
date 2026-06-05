//! Trivia attachment policy for the CST. Phase 2.0 of #1262.
//!
//! Phase 1 emits a flat tree: every token (content AND trivia) is a
//! direct child of `SOURCE_FILE`, so trivia attachment is a
//! non-question. Phase 2.1+ introduces structural nodes
//! (`DIRECTIVE` wrappers, then `POSTING` / `AMOUNT` / `COST_SPEC` /
//! `META_ENTRY` / ...). Once those nodes exist, every trivia token
//! must end up inside exactly one of them — that's the contract
//! this module pins.
//!
//! # The Directive-Terminator Rule
//!
//! **Every directive structural node OWNS its content tokens PLUS
//! its terminating `NEWLINE`** — the first `NEWLINE` token (not
//! byte; see below) the lexer emits after its last content token.
//!
//! Five corollaries:
//!
//! 1. **Same-line trailing trivia.** Whitespace and EOL comments
//!    that appear AFTER the last content token but BEFORE the
//!    terminating `NEWLINE` are INSIDE the directive. In
//!    `2024-01-01 open Assets:Cash  ; bank\n`, the `  ; bank` and
//!    the terminating `\n` are all children of the same directive
//!    node.
//!
//! 2. **Inter-directive leading trivia.** Trivia that appears
//!    AFTER one directive's terminator `NEWLINE` and BEFORE the
//!    next directive's first content token (blank lines, mid-file
//!    comment blocks) leads the NEXT directive. A blank line
//!    between two directives belongs to the second directive's
//!    leading trivia.
//!
//! 3. **File-leading trivia.** Trivia BEFORE the first content
//!    token in the file (BOM, shebang, copyright comment header,
//!    leading blank lines) attaches to `SOURCE_FILE` as direct
//!    children. There is no preceding directive, and the first
//!    directive's `text_range` should not silently swallow a
//!    copyright header.
//!
//! 4. **File-trailing trivia.** Trivia AFTER the last directive's
//!    terminator `NEWLINE` (and before EOF) also attaches to
//!    `SOURCE_FILE` directly. Same rationale as rule 3, but at
//!    the other end: closing-remarks comments at EOF are file
//!    metadata, not part of the file-final directive.
//!
//! 5. **Unterminated final directive.** If the file ends mid-
//!    content (no `NEWLINE` after the last content token), the
//!    final directive STILL applies rule 1 to any same-line
//!    trailing trivia it carries (WHITESPACE + EOL COMMENT
//!    immediately after content) — they sit INSIDE the directive.
//!    The directive simply has no terminator child; its range
//!    ends at the last trivia token attached by rule 1, or at the
//!    last content token if no trailing trivia exists.
//!
//! ## "NEWLINE" means the NEWLINE token kind, not a `\n` byte
//!
//! Beancount STRING tokens may contain literal `\n` bytes
//! (multi-line strings in `note` / `document` / transaction
//! narrations). The Directive-Terminator Rule keys off the lexer's
//! NEWLINE token (regex `\r?\n` at the top level of
//! `logos_lexer.rs`), not raw byte content. A multi-line STRING is
//! a SINGLE content token regardless of its internal `\n` bytes;
//! the directive's terminator is the next NEWLINE token AFTER the
//! STRING token, not somewhere inside it.
//!
//! # Provenance and worked example
//!
//! This rule matches **Roslyn's documented model** ([Microsoft
//! Learn](https://learn.microsoft.com/en-us/dotnet/csharp/roslyn-sdk/work-with-syntax)):
//!
//! > "A token owns any trivia after it on the same line up to the
//! > next token. Any trivia after that line is associated with the
//! > following token."
//!
//! Roslyn additionally says: "The first token in the source file
//! gets all the initial trivia, and the last sequence of trivia
//! in the file is tacked onto the end-of-file token." Beancount's
//! CST has no synthesized end-of-file token, and absorbing
//! file-leading / file-trailing trivia into the first / last
//! directive is the wrong intuition for a Beancount user (a
//! copyright header at the top is not part of the first directive
//! the user happens to have written). **The Directive-Terminator
//! Rule deviates from Roslyn on this single point**: rules 3 and
//! 4 attach file-leading / file-trailing trivia to `SOURCE_FILE`
//! directly, not to the first / last directive.
//!
//! **It does NOT match rust-analyzer**, despite what earlier
//! drafts of this module claimed. RA's trivia-attachment helper
//! (in `crates/parser/src/shortcuts.rs`) walks trivia in reverse
//! from the next item, breaking on a blank-line whitespace, and
//! attaches same-line trailing comments to the FOLLOWING item.
//! That is the opposite of what Beancount users expect — a
//! `; deposit` after an amount visually belongs to the posting it
//! shares a line with, not to the next directive.
//!
//! Worked example (`2024-01-01 open Assets:Cash  ; bank\n\n2024-01-02 open Assets:Bank\n`):
//!
//! | trivia run | rule | home |
//! |---|---|---|
//! | `  ; bank` between `Assets:Cash` and `\n` | 1 | inside d1 |
//! | `\n` terminating d1 line | 1 | inside d1 |
//! | `\n` blank line | 2 | leading trivia of d2 |
//! | `\n` terminating d2 line | 1 | inside d2 |
//!
//! No trivia escapes to `SOURCE_FILE`; both directives have
//! symmetric shape `[content..., terminator-NEWLINE]`.
//!
//! # Scope and recursive application
//!
//! This module pins the policy at the TOP-LEVEL inter-directive
//! level. The rule is RECURSIVE: phase 2.1 applies the same shape
//! to nested structural elements (a `POSTING` inside a
//! `TRANSACTION`, a `META_ENTRY` inside any directive that carries
//! metadata). At each level, the structural node owns its content
//! tokens plus its own terminating `NEWLINE`, by the same rule.
//!
//! ## Multi-line directives (with postings or metadata)
//!
//! Beancount directives that carry sub-lines — transactions with
//! postings, and any directive with indented `key: "value"`
//! metadata — span MULTIPLE LINES. The Directive-Terminator Rule
//! says "the first `NEWLINE` after the directive's last content
//! token"; for a multi-line directive, **the directive's last
//! content token is the last content token of its LAST SUB-LINE**,
//! not the header.
//!
//! Worked example (`2024-01-01 open Assets:Cash\n  description: "x"\n  currency: "USD"\n`):
//!
//! ```text
//! OPEN_DIRECTIVE                       // outer directive node
//! ├── DATE("2024-01-01")
//! ├── WHITESPACE(" ")
//! ├── OPEN_KW("open")
//! ├── WHITESPACE(" ")
//! ├── ACCOUNT("Assets:Cash")
//! ├── NEWLINE("\n")                    // intra-directive: closes header line
//! ├── META_ENTRY                       // nested structural node, recursive
//! │   ├── WHITESPACE("  ")             // intra-meta-entry indent
//! │   ├── META_KEY("description")
//! │   ├── ... content tokens ...
//! │   └── NEWLINE("\n")                // META_ENTRY's terminator
//! ├── META_ENTRY                       // second meta entry
//! │   ├── WHITESPACE("  ")
//! │   ├── META_KEY("currency")
//! │   ├── ... content tokens ...
//! │   └── NEWLINE("\n")                // OPEN_DIRECTIVE's terminator
//! ```
//!
//! Two consequences worth pinning:
//!
//! 1. **The header `NEWLINE` lives INSIDE the directive**, not as
//!    its terminator. The directive's terminator is the LAST
//!    `NEWLINE` (the one after the final sub-line). Deleting the
//!    outer directive deletes its metadata too — what users
//!    expect.
//! 2. **Each `META_ENTRY` is itself a structural node** and owns
//!    its own terminating `NEWLINE` by the recursive application.
//!    The "last" `META_ENTRY`'s terminator NEWLINE is BOTH the
//!    `META_ENTRY`'s terminator AND the outer directive's
//!    terminator — it sits structurally INSIDE the `META_ENTRY`,
//!    which is itself a child of the outer directive.
//!
//! ## `Indent` and `DeepIndent` are trivia
//!
//! The Logos lexer's AST-side `tokenize` pass synthesizes
//! `Token::Indent(level)` and `Token::DeepIndent(level)` tokens
//! for indented posting/metadata lines. The LOSSLESS path
//! ([`crate::cst::lossless_tokens::lossless_kind_tokens`]) does
//! NOT emit these — it keeps the raw `Token::Whitespace` runs
//! that the indent tokens were summarizing. If a synthesized
//! `Indent`/`DeepIndent` somehow reaches `lossless_kind_tokens`,
//! the kind map at `cst/lossless_tokens.rs::map_kind` classifies
//! it as `SyntaxKind::WHITESPACE` — i.e., trivia under
//! `SyntaxKind::is_trivia`. The Directive-Terminator Rule treats
//! these indent runs like any other intra-directive whitespace.
//! No special policy line is required.
//!
//! # Phase 2.1 grammar option: typed comment accessor
//!
//! `polarmutex/tree-sitter-beancount` (the closest Beancount-
//! specific lossless prior art) exposes each directive's same-
//! line trailing comment via a `field("comment", optional($.comment))`
//! declaration. In tree-sitter terms, the field is a NAME on one of
//! the directive's existing children — the COMMENT is still in its
//! source-order position as a child of the directive; the field
//! just provides a named accessor.
//!
//! Phase 2.1 may adopt the equivalent in our typed-AST layer
//! (`Posting::trailing_comment() -> Option<&SyntaxToken>` scanning
//! the posting's direct token children for a `COMMENT`). **This
//! is additive on top of the Directive-Terminator Rule:** the
//! COMMENT remains a direct child token of the directive in the
//! same source-order position rule 1 puts it; the typed accessor
//! is a method on the typed AST wrapper, NOT a structural sub-node
//! kind. The tree shape pinned by this module's tests is unchanged.
//!
//! If phase 2.1 instead chose a STRUCTURAL trailing-comment slot —
//! a new `TRAILING_COMMENT_GROUP` wrapper node around the
//! `WHITESPACE + COMMENT` run — that would be a TREE-SHAPE change,
//! not additive, and would require updating rule 1 (and this
//! module's tests). That option is out of scope for this PR; flag
//! it explicitly if you go that direction.
//!
//! # Why
//!
//! - **Same-line trailing inside the directive.** Beancount has
//!   inline EOL comments everywhere; the user visually associates
//!   the comment with the line it shares.
//! - **Directive owns its terminator.** Makes
//!   `directive.text_range()` uniformly cover the directive's
//!   visual line for every directive in the file, including the
//!   final one.
//! - **File-leading / file-trailing under `SOURCE_FILE`.** A
//!   copyright comment at the top of the file is file-level
//!   metadata; the user doesn't expect deleting the first
//!   directive to also delete the copyright. Same at EOF.
//! - **Symmetric.** Every directive has the same children shape
//!   (optional leading trivia + content + optional same-line
//!   trailing + terminator `NEWLINE`). No EOF special case.
//!
//! # Test approach: tree-shape regression, NO production helper
//!
//! Phase 2.0 deliberately exports NO classifier function. The
//! policy is a set of invariants on the SHAPE of phase 2.1+
//! structural trees, NOT a per-token classifier. Each test
//! hand-constructs the expected tree under the policy using
//! `GreenNodeBuilder`, then asserts:
//!
//! - Byte-identical round-trip: `tree.text() == source` — the
//!   tree we built actually represents the source we claim.
//! - **Exact** trivia and content sequences inside each
//!   structural node — phase 2.1's parser must produce trees
//!   matching the exact shape, not a superset.
//!
//! When phase 2.1 lands specific directive kinds (`TRANSACTION`,
//! ...), these tests do NOT auto-carry-over to validate the real
//! parser. They constrain hand-built trees; phase 2.1's PR adds
//! parallel source-driven tests
//! (`parse_structured(source); assert tree.descendants() ...`)
//! that exercise the same shapes from the parser's output. The
//! tests in this module remain as documentation-by-example of
//! the policy.

#[cfg(test)]
mod tests {
    //! Tree-shape regression tests pinning the Directive-Terminator Rule.

    use rowan::GreenNodeBuilder;

    use crate::cst::SyntaxKind::{
        ACCOUNT, BOM, COMMENT, DATE, DIRECTIVE, EMACS_DIRECTIVE, NEWLINE, OPEN_KW, PERCENT_COMMENT,
        SHEBANG, SOURCE_FILE, WHITESPACE,
    };
    use crate::cst::SyntaxNode;

    /// All kinds of every DIRECT child of `node`, in source order,
    /// distinguishing tokens (carrying their kind) from nested
    /// nodes (carrying their kind too). Returning a single sequence
    /// of `Element`s lets each test assert the EXACT shape of a
    /// node's children — both trivia/content tokens AND any nested
    /// structural sub-nodes — in one assertion, instead of two
    /// separate `direct_trivia_kinds` + `direct_content_kinds`
    /// helpers that silently dropped nested-node children.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Element {
        Tok(crate::cst::SyntaxKind),
        Node(crate::cst::SyntaxKind),
    }

    fn elements_of(node: &SyntaxNode) -> Vec<Element> {
        node.children_with_tokens()
            .map(|el| match el {
                rowan::NodeOrToken::Token(t) => Element::Tok(t.kind()),
                rowan::NodeOrToken::Node(n) => Element::Node(n.kind()),
            })
            .collect()
    }

    /// Convenience for assertions: turn a token-kind list into the
    /// equivalent `Element::Tok` sequence.
    fn tok_seq(kinds: &[crate::cst::SyntaxKind]) -> Vec<Element> {
        kinds.iter().copied().map(Element::Tok).collect()
    }

    fn top_level_directives(root: &SyntaxNode) -> Vec<SyntaxNode> {
        root.children().filter(|c| c.kind() == DIRECTIVE).collect()
    }

    // ----- Helpers to build directives -----------------------------

    /// Open-directive token run with optional same-line trailing
    /// trivia + optional terminator. Centralizes the test-tree
    /// construction so each test reads as "policy assertion,"
    /// not "tree-builder boilerplate."
    fn build_open_directive(
        b: &mut GreenNodeBuilder<'_>,
        date: &str,
        account: &str,
        same_line_trailing: &[(crate::cst::SyntaxKind, &str)],
        terminator: Option<&str>,
    ) {
        b.start_node(DIRECTIVE.into());
        b.token(DATE.into(), date);
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), account);
        for (kind, text) in same_line_trailing {
            b.token((*kind).into(), text);
        }
        if let Some(nl) = terminator {
            b.token(NEWLINE.into(), nl);
        }
        b.finish_node();
    }

    /// Same as `build_open_directive` but with leading trivia
    /// emitted INSIDE the directive (after `start_node`, before
    /// the content tokens) — the structural shape required by
    /// rule 2 for any directive with inter-directive leading
    /// trivia.
    fn build_open_directive_with_leading(
        b: &mut GreenNodeBuilder<'_>,
        leading: &[(crate::cst::SyntaxKind, &str)],
        date: &str,
        account: &str,
        same_line_trailing: &[(crate::cst::SyntaxKind, &str)],
        terminator: Option<&str>,
    ) {
        b.start_node(DIRECTIVE.into());
        for (kind, text) in leading {
            b.token((*kind).into(), text);
        }
        b.token(DATE.into(), date);
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), account);
        for (kind, text) in same_line_trailing {
            b.token((*kind).into(), text);
        }
        if let Some(nl) = terminator {
            b.token(NEWLINE.into(), nl);
        }
        b.finish_node();
    }

    // ----- Tests -----------------------------------------------------

    #[test]
    fn rule_1_same_line_trailing_inside_preceding_directive() {
        // Source under test:
        //   2024-01-01 open Assets:Cash  ; EOL comment
        //   2024-01-02 open Assets:Bank
        //
        // Per rule 1: `  ; EOL comment` AND the directive's
        // terminator `\n` are all CHILDREN OF THE FIRST DIRECTIVE.
        // Per rule 2: directive 2 starts at `2024-01-02` with NO
        // leading trivia (none exists between d1's terminator and
        // d2's first content).
        let source = "2024-01-01 open Assets:Cash  ; EOL comment\n\
                      2024-01-02 open Assets:Bank";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());
        build_open_directive(
            &mut b,
            "2024-01-01",
            "Assets:Cash",
            &[(WHITESPACE, "  "), (COMMENT, "; EOL comment")],
            Some("\n"),
        );
        build_open_directive(&mut b, "2024-01-02", "Assets:Bank", &[], None);
        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);

        let directives = top_level_directives(&tree);
        assert_eq!(directives.len(), 2);

        // EXACT shape, not contains/starts_with.
        assert_eq!(
            elements_of(&directives[0]),
            tok_seq(&[
                DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, WHITESPACE, COMMENT, NEWLINE,
            ]),
            "rule 1: d1 owns its same-line trailing + terminator NEWLINE",
        );
        assert_eq!(
            elements_of(&directives[1]),
            tok_seq(&[DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT]),
            "d2 has no leading trivia (none exists between d1 terminator and d2 first content)",
        );
        assert_eq!(
            elements_of(&tree),
            vec![Element::Node(DIRECTIVE), Element::Node(DIRECTIVE)],
            "SOURCE_FILE owns exactly the two directives — no trivia leaks",
        );
    }

    #[test]
    fn rule_2_blank_line_leads_following_directive() {
        // Source under test:
        //   2024-01-01 open Assets:Cash\n
        //   \n                              <-- blank line
        //   2024-01-02 open Assets:Bank\n
        //
        // Per rule 1: d1 owns its terminator `\n` (the first one).
        // Per rule 2: the blank `\n` between d1's terminator and
        // d2's first content leads d2.
        // Per rule 1: d2 owns its own terminator `\n`.
        let source = "2024-01-01 open Assets:Cash\n\
                      \n\
                      2024-01-02 open Assets:Bank\n";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());
        build_open_directive(&mut b, "2024-01-01", "Assets:Cash", &[], Some("\n"));
        build_open_directive_with_leading(
            &mut b,
            &[(NEWLINE, "\n")], // the blank line, INSIDE d2 as leading
            "2024-01-02",
            "Assets:Bank",
            &[],
            Some("\n"),
        );
        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);

        let directives = top_level_directives(&tree);
        assert_eq!(directives.len(), 2);

        assert_eq!(
            elements_of(&directives[0]),
            tok_seq(&[DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, NEWLINE]),
            "rule 1: d1 owns its terminator NEWLINE",
        );
        assert_eq!(
            elements_of(&directives[1]),
            tok_seq(&[
                NEWLINE, DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, NEWLINE
            ]),
            "rule 2: blank line leads d2; rule 1: d2 owns its terminator NEWLINE",
        );
    }

    #[test]
    fn rule_3_copyright_header_under_source_file() {
        // Source under test:
        //   ;; Copyright 2024\n
        //   ;; All rights reserved\n
        //   2024-01-01 open Assets:Cash\n
        //
        // The copyright header is BEFORE any content token; per
        // rule 3 it sits under SOURCE_FILE as direct children, NOT
        // inside the first directive.
        let source = ";; Copyright 2024\n\
                      ;; All rights reserved\n\
                      2024-01-01 open Assets:Cash\n";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());
        b.token(COMMENT.into(), ";; Copyright 2024");
        b.token(NEWLINE.into(), "\n");
        b.token(COMMENT.into(), ";; All rights reserved");
        b.token(NEWLINE.into(), "\n");
        build_open_directive(&mut b, "2024-01-01", "Assets:Cash", &[], Some("\n"));
        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);

        assert_eq!(
            elements_of(&tree),
            vec![
                Element::Tok(COMMENT),
                Element::Tok(NEWLINE),
                Element::Tok(COMMENT),
                Element::Tok(NEWLINE),
                Element::Node(DIRECTIVE),
            ],
            "rule 3: copyright header is direct under SOURCE_FILE; directive follows",
        );
        let directives = top_level_directives(&tree);
        assert_eq!(
            elements_of(&directives[0]),
            tok_seq(&[DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, NEWLINE]),
            "d1 has no leading trivia (header is under SOURCE_FILE) and owns its terminator",
        );
    }

    #[test]
    fn rule_3_bom_and_shebang_under_source_file() {
        // Source under test:
        //   <BOM>#!/usr/bin/env bean-check\n
        //   2024-01-01 open Assets:Cash\n
        let source = "\u{FEFF}#!/usr/bin/env bean-check\n\
                      2024-01-01 open Assets:Cash\n";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());
        b.token(BOM.into(), "\u{FEFF}");
        b.token(SHEBANG.into(), "#!/usr/bin/env bean-check");
        b.token(NEWLINE.into(), "\n");
        build_open_directive(&mut b, "2024-01-01", "Assets:Cash", &[], Some("\n"));
        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);

        assert_eq!(
            elements_of(&tree),
            vec![
                Element::Tok(BOM),
                Element::Tok(SHEBANG),
                Element::Tok(NEWLINE),
                Element::Node(DIRECTIVE),
            ],
        );
    }

    #[test]
    fn rule_4_trailing_comment_block_under_source_file() {
        // Source under test:
        //   2024-01-01 open Assets:Cash\n
        //   ;; closing remarks\n
        //
        // Per rule 1: d1 owns its terminator `\n`.
        // Per rule 4: the comment block AFTER d1's terminator
        // sits under SOURCE_FILE as direct children, NOT inside d1
        // — symmetric with rule 3.
        let source = "2024-01-01 open Assets:Cash\n\
                      ;; closing remarks\n";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());
        build_open_directive(&mut b, "2024-01-01", "Assets:Cash", &[], Some("\n"));
        b.token(COMMENT.into(), ";; closing remarks");
        b.token(NEWLINE.into(), "\n");
        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);

        assert_eq!(
            elements_of(&tree),
            vec![
                Element::Node(DIRECTIVE),
                Element::Tok(COMMENT),
                Element::Tok(NEWLINE),
            ],
            "rule 4: closing remarks are direct under SOURCE_FILE, NOT inside d1",
        );
        let directives = top_level_directives(&tree);
        assert_eq!(
            elements_of(&directives[0]),
            tok_seq(&[DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, NEWLINE]),
            "d1 owns its terminator but NOT the closing remarks",
        );
    }

    #[test]
    fn rule_5_unterminated_final_directive() {
        // Source under test:
        //   2024-01-01 open Assets:Cash    <-- no trailing newline
        //
        // Per rule 5: d1 has no terminator. Its range ends at
        // ACCOUNT. SOURCE_FILE has no direct children other than d1.
        let source = "2024-01-01 open Assets:Cash";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());
        build_open_directive(&mut b, "2024-01-01", "Assets:Cash", &[], None);
        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);

        assert_eq!(elements_of(&tree), vec![Element::Node(DIRECTIVE)],);
        let directives = top_level_directives(&tree);
        assert_eq!(
            elements_of(&directives[0]),
            tok_seq(&[DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT]),
            "rule 5: no terminator means directive range ends at last content",
        );
    }

    #[test]
    fn rule_1_plus_rule_5_unterminated_directive_with_same_line_trailing() {
        // Source under test:
        //   2024-01-01 open Assets:Cash  ; eol-no-nl     <-- EOF mid-comment, no terminator
        //
        // This is the case the v3 review flagged as ambiguous: rule 1
        // says same-line trailing trivia lives INSIDE the directive;
        // rule 5 says no terminator means the range ends at last
        // content "no fabrication." The rule 5 wording in v3 wasn't
        // explicit that same-line trailing trivia ALSO survives the
        // no-terminator case. v4 makes it explicit: rule 1 fires
        // (no NEWLINE was needed for rule 1; it only triggers off
        // the trivia run between last content and the directive's
        // terminator-OR-EOF), and the directive owns the trailing
        // WS + COMMENT even though no terminator NEWLINE exists.
        //
        // Beancount files saved without a final newline are common
        // (editors that don't enforce POSIX line termination); this
        // test pins behavior on a realistic case.
        let source = "2024-01-01 open Assets:Cash  ; eol-no-nl";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());
        build_open_directive(
            &mut b,
            "2024-01-01",
            "Assets:Cash",
            &[(WHITESPACE, "  "), (COMMENT, "; eol-no-nl")],
            None,
        );
        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);

        // No file-trailing trivia under SOURCE_FILE — the trailing
        // WS+COMMENT live INSIDE the directive (rule 1).
        assert_eq!(elements_of(&tree), vec![Element::Node(DIRECTIVE)]);
        let directives = top_level_directives(&tree);
        assert_eq!(
            elements_of(&directives[0]),
            tok_seq(&[
                DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, WHITESPACE, COMMENT,
            ]),
            "rules 1+5: same-line trailing trivia stays INSIDE the directive \
             even when there's no terminator NEWLINE",
        );
    }

    #[test]
    fn percent_comment_obeys_directive_terminator_rule() {
        // PERCENT_COMMENT is the second comment variant; same
        // policy as COMMENT.
        //
        // Source: 2024-01-01 open Assets:Cash  % EOL\n
        //         2024-01-02 open Assets:Bank
        let source = "2024-01-01 open Assets:Cash  % EOL\n\
                      2024-01-02 open Assets:Bank";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());
        build_open_directive(
            &mut b,
            "2024-01-01",
            "Assets:Cash",
            &[(WHITESPACE, "  "), (PERCENT_COMMENT, "% EOL")],
            Some("\n"),
        );
        build_open_directive(&mut b, "2024-01-02", "Assets:Bank", &[], None);
        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);
        let directives = top_level_directives(&tree);
        assert_eq!(
            elements_of(&directives[0]),
            tok_seq(&[
                DATE,
                WHITESPACE,
                OPEN_KW,
                WHITESPACE,
                ACCOUNT,
                WHITESPACE,
                PERCENT_COMMENT,
                NEWLINE,
            ]),
            "PERCENT_COMMENT obeys rule 1 the same as COMMENT",
        );
    }

    #[test]
    fn emacs_directive_obeys_file_leading_rule() {
        // EMACS_DIRECTIVE (org-mode property line like `#+OPTIONS`)
        // is also trivia. At the top of the file, rule 3 puts it
        // under SOURCE_FILE.
        //
        // Source: #+OPTIONS toc:nil\n
        //         2024-01-01 open Assets:Cash\n
        let source = "#+OPTIONS toc:nil\n\
                      2024-01-01 open Assets:Cash\n";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());
        b.token(EMACS_DIRECTIVE.into(), "#+OPTIONS toc:nil");
        b.token(NEWLINE.into(), "\n");
        build_open_directive(&mut b, "2024-01-01", "Assets:Cash", &[], Some("\n"));
        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);
        assert_eq!(
            elements_of(&tree),
            vec![
                Element::Tok(EMACS_DIRECTIVE),
                Element::Tok(NEWLINE),
                Element::Node(DIRECTIVE),
            ],
            "rule 3: EMACS_DIRECTIVE before any content is under SOURCE_FILE",
        );
    }

    #[test]
    fn adjacent_directives_no_blank_line() {
        // Source under test:
        //   2024-01-01 open Assets:Cash\n
        //   2024-01-02 open Assets:Bank\n
        //
        // Two directives back-to-back. Per rule 1, each owns its
        // own terminator `\n`. No inter-directive trivia exists.
        let source = "2024-01-01 open Assets:Cash\n\
                      2024-01-02 open Assets:Bank\n";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());
        build_open_directive(&mut b, "2024-01-01", "Assets:Cash", &[], Some("\n"));
        build_open_directive(&mut b, "2024-01-02", "Assets:Bank", &[], Some("\n"));
        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);
        let directives = top_level_directives(&tree);
        assert_eq!(directives.len(), 2);
        assert_eq!(
            elements_of(&directives[0]),
            tok_seq(&[DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, NEWLINE]),
        );
        assert_eq!(
            elements_of(&directives[1]),
            tok_seq(&[DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, NEWLINE]),
            "Two adjacent directives have IDENTICAL child shape — full symmetry",
        );
    }

    #[test]
    fn file_with_only_trivia() {
        // Source: ;; only a comment\n\n
        //
        // No content tokens at all → no directive node opened, all
        // trivia stays under SOURCE_FILE.
        let source = ";; only a comment\n\n";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());
        b.token(COMMENT.into(), ";; only a comment");
        b.token(NEWLINE.into(), "\n");
        b.token(NEWLINE.into(), "\n");
        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);
        assert!(top_level_directives(&tree).is_empty());
        assert_eq!(
            elements_of(&tree),
            vec![
                Element::Tok(COMMENT),
                Element::Tok(NEWLINE),
                Element::Tok(NEWLINE),
            ],
        );
    }

    #[test]
    fn empty_file() {
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());
        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), "");
        assert!(top_level_directives(&tree).is_empty());
        assert!(elements_of(&tree).is_empty());
    }

    #[test]
    fn all_rules_combined() {
        // Exercise rules 1+2+3+4 in one tree:
        //   ;; copyright\n                              <-- rule 3: SOURCE_FILE
        //   2024-01-01 open Assets:Cash  ; eol1\n       <-- rule 1: same-line, then terminator
        //   \n                                          <-- rule 2: blank line, leads d2
        //   2024-01-02 open Assets:Bank\n               <-- d2 with leading + content + terminator
        //   ;; footer\n                                 <-- rule 4: SOURCE_FILE
        let source = ";; copyright\n\
                      2024-01-01 open Assets:Cash  ; eol1\n\
                      \n\
                      2024-01-02 open Assets:Bank\n\
                      ;; footer\n";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());

        // Rule 3: file-leading copyright
        b.token(COMMENT.into(), ";; copyright");
        b.token(NEWLINE.into(), "\n");

        // d1: content + same-line trailing + terminator (rules 1)
        build_open_directive(
            &mut b,
            "2024-01-01",
            "Assets:Cash",
            &[(WHITESPACE, "  "), (COMMENT, "; eol1")],
            Some("\n"),
        );

        // d2: leading blank (rule 2) + content + terminator (rule 1)
        build_open_directive_with_leading(
            &mut b,
            &[(NEWLINE, "\n")],
            "2024-01-02",
            "Assets:Bank",
            &[],
            Some("\n"),
        );

        // Rule 4: file-trailing footer
        b.token(COMMENT.into(), ";; footer");
        b.token(NEWLINE.into(), "\n");

        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);

        // SOURCE_FILE direct children: file-leading + d1 + d2 +
        // file-trailing. EXACT shape.
        assert_eq!(
            elements_of(&tree),
            vec![
                Element::Tok(COMMENT),
                Element::Tok(NEWLINE),
                Element::Node(DIRECTIVE),
                Element::Node(DIRECTIVE),
                Element::Tok(COMMENT),
                Element::Tok(NEWLINE),
            ],
            "SOURCE_FILE owns file-leading copyright + 2 directives + file-trailing footer",
        );

        let directives = top_level_directives(&tree);
        assert_eq!(directives.len(), 2);
        assert_eq!(
            elements_of(&directives[0]),
            tok_seq(&[
                DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, WHITESPACE, COMMENT, NEWLINE,
            ]),
            "d1: rule 1 (same-line + terminator)",
        );
        assert_eq!(
            elements_of(&directives[1]),
            tok_seq(&[
                NEWLINE, DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, NEWLINE,
            ]),
            "d2: rule 2 leading + rule 1 terminator",
        );
    }
}
