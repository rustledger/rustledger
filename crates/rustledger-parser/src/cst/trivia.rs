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
//! its terminating `NEWLINE`** — the first `NEWLINE` encountered
//! after its last content token. This is the actual rust-analyzer
//! / Roslyn convention, and matches the user's intuition that "a
//! directive ends at the end of its line."
//!
//! Four corollaries:
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
//!    final directive owns its content tokens plus any same-line
//!    trailing trivia. No terminator means the directive's range
//!    ends at its last token, period — no fabrication.
//!
//! # Why
//!
//! - **Same-line trailing.** Beancount has inline EOL comments
//!   everywhere (`2024-01-01 open Assets:Cash  ; my main checking`).
//!   The user visually associates the comment with the line it
//!   shares — splitting it onto the next directive would be a
//!   surprise in LSP hover, code lens, and formatter output.
//! - **Directive owns its terminator.** Makes
//!   `directive.text_range()` uniformly cover the directive's
//!   visual line for every directive in the file, including the
//!   final one. LSP `selection-range`, code-lens placement,
//!   folding ranges, and "select directive" all get a consistent
//!   answer.
//! - **File-leading / file-trailing under `SOURCE_FILE`.** A
//!   copyright comment at the top of the file is file-level
//!   metadata. The user doesn't expect deleting the first
//!   directive to also delete the copyright. The same intuition
//!   applies to closing-remarks comments at the bottom.
//! - **Symmetric.** No EOF special case. Every directive has the
//!   same children shape (optional leading trivia + content +
//!   optional same-line trailing + terminator `NEWLINE`).
//!   Consumers iterating directives never need to special-case
//!   the file-final one.
//! - **Matches rust-analyzer (and Roslyn, and most lossless-CST
//!   parsers).** Reviewers familiar with that family don't have
//!   to relearn the convention.
//!
//! # Scope
//!
//! This module pins the policy at the TOP-LEVEL inter-directive
//! level. The rule is RECURSIVE: phase 2.1 applies it to nested
//! structural elements (`POSTING` inside `TRANSACTION`,
//! `META_ENTRY` inside any directive). Each level's "directive"
//! is just "the structural node currently being closed." A
//! posting owns its terminating `NEWLINE`; mid-transaction blank
//! lines lead the next posting (or close the transaction body,
//! depending on phase 2.1's grammar — that's a grammar question,
//! not a trivia question).
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
        assert!(
            elements_of(&tree)
                .iter()
                .all(|e| matches!(e, Element::Node(DIRECTIVE))),
            "SOURCE_FILE has no direct trivia children (no file-leading or file-trailing)",
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
