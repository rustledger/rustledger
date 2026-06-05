//! Trivia attachment policy for the CST. Phase 2.0 of #1262.
//!
//! Phase 1 emits a flat tree: every token (content AND trivia) is a
//! direct child of `SOURCE_FILE`, so trivia attachment is a
//! non-question. Phase 2.1+ introduces structural nodes
//! (`DIRECTIVE` wrappers, then `POSTING` / `AMOUNT` / `COST_SPEC` /
//! `META_ENTRY` / ...). Once those nodes exist, every trivia token
//! must end up inside exactly one of them — that's the contract this
//! module pins.
//!
//! # The Two-Line Rule
//!
//! Pick the trivia's home by asking ONE question of the trivia run
//! between two content tokens (or between content and EOF / SOF):
//! does it cross a `NEWLINE` from the preceding content?
//!
//! 1. **Same-line trailing trivia.** A trivia run that starts AFTER a
//!    content token and ends BEFORE the first `NEWLINE` (i.e., does
//!    not cross a line boundary from the preceding content) attaches
//!    to the **preceding** directive node. Example: the
//!    `  ; EOL comment` after a posting's amount, before the
//!    terminating newline. This is what reviewers familiar with
//!    rust-analyzer's trivia-attachment convention expect.
//!
//! 2. **Leading trivia.** A trivia run that crosses a `NEWLINE` from
//!    the preceding content (or has no preceding content) attaches
//!    to the **following** directive node. Example: the blank line
//!    between two top-level directives. Includes the `NEWLINE` that
//!    crosses the line boundary — that newline is part of the next
//!    directive's leading-trivia run, not the previous directive's
//!    trailing.
//!
//! 3. **File-leading trivia (`SOURCE_FILE` direct child).** Trivia
//!    before any content token has no preceding directive, so rule 2
//!    would attach it to "the following directive" — but for the
//!    file's FIRST directive, "leading" trivia is conceptually file-
//!    level metadata (BOM, shebang, copyright header). Attach it to
//!    `SOURCE_FILE` directly, NOT to the first directive. This keeps
//!    `directive.text_range()` on the first directive from
//!    awkwardly including the copyright header.
//!
//! 4. **EOF trailing trivia.** Trivia after the last content token
//!    has no following directive to lead into. Attach it to the
//!    preceding directive (the file-final one) — the rule-1 rule by
//!    fallback.
//!
//! # Why
//!
//! - **Same-line trailing.** Beancount has many inline EOL comments
//!   (`2024-01-01 open Assets:Cash  ; my main checking`). The user
//!   visually associates the comment with the directive it shares a
//!   line with. Forwarding it to the NEXT directive would surprise
//!   them in LSP hover, code lens placement, and would produce
//!   churny rewrites in the formatter.
//! - **Leading attaches forward.** Blank lines between directives
//!   visually separate the next directive from the previous one,
//!   not the other way around. Putting the blank line at the start
//!   of the next directive makes `directive.text_range()` cover its
//!   visual leading whitespace — useful for LSP hover and selection
//!   range.
//! - **File-leading is `SOURCE_FILE`.** A copyright comment block at
//!   the top of the file is file-level metadata, not part of the
//!   first directive. The user does not consider deleting the first
//!   directive to also delete the copyright.
//! - **EOF.** No following directive exists. Rule-2 trivia at EOF
//!   has nowhere to go forward, so the preceding directive absorbs
//!   it. This breaks structural symmetry (the last directive gets
//!   trailing children that no other directive has), but the
//!   alternative is dangling trivia under `SOURCE_FILE` with no
//!   structural home, which is worse for consumers iterating
//!   directives.
//! - **Matches rust-analyzer.** RA's parser walks trivia from the
//!   end of a structural node backward and attaches as trailing as
//!   much as fits "on the same line." Same rule, just expressed
//!   from the opposite direction.
//!
//! # Scope
//!
//! This module pins the policy at the **top-level inter-directive
//! level**. Intra-directive trivia (the `NEWLINE` between a
//! transaction header and its postings, the WHITESPACE around `+`
//! inside an amount expression) is GRAMMAR-DRIVEN — the structural
//! node that opens the directive simply contains its intra-directive
//! trivia as children. There's no classification question because
//! the trivia is already inside the right node.
//!
//! # Why this module ships no production code
//!
//! Phase 2.0 deliberately exports NO function. The policy is a set
//! of invariants on the SHAPE of phase 2.1+ structural trees, not a
//! per-token classifier. Each regression test in this module
//! hand-constructs a small tree under the policy and asserts the
//! shape; phase 2.1's parser writes its own (streaming, state-aware)
//! predicate that produces trees matching these shapes. If the
//! parser drifts from the policy, the regression here fires.
//!
//! Locking the policy with TREE-SHAPE assertions instead of a
//! per-token classifier sidesteps the API-shape lock-in problem
//! that a speculative `classify_trivia` function would have
//! introduced before phase 2.1 validated the call site. See PR
//! #1271 review for the discarded design.

#[cfg(test)]
mod tests {
    //! Tree-shape regression tests pinning the Two-Line Rule.
    //!
    //! Each test hand-constructs an expected tree under the policy
    //! using `GreenNodeBuilder`, then asserts:
    //!
    //! 1. The tree round-trips byte-identically to a documented
    //!    source string (sanity check — the tree we just built
    //!    actually represents the input we claim).
    //! 2. Specific tokens land inside the structural node the
    //!    policy says they should. Phase 2.1's structured parser
    //!    must produce trees matching these shapes; any drift fires
    //!    one of these assertions.

    use rowan::GreenNodeBuilder;

    use crate::cst::SyntaxKind::{
        ACCOUNT, BOM, COMMENT, DATE, DIRECTIVE, NEWLINE, OPEN_KW, PERCENT_COMMENT, SHEBANG,
        SOURCE_FILE, WHITESPACE,
    };
    use crate::cst::SyntaxNode;

    /// Find the trivia kinds inside a node's DIRECT children
    /// (excluding nested directive nodes). Used to assert which
    /// trivia tokens a directive node owns.
    fn direct_trivia_kinds(node: &SyntaxNode) -> Vec<crate::cst::SyntaxKind> {
        node.children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .filter(|t| t.kind().is_trivia())
            .map(|t| t.kind())
            .collect()
    }

    /// Find the non-trivia (content) kinds inside a node's direct
    /// children.
    fn direct_content_kinds(node: &SyntaxNode) -> Vec<crate::cst::SyntaxKind> {
        node.children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .filter(|t| !t.kind().is_trivia())
            .map(|t| t.kind())
            .collect()
    }

    /// Collect all `DIRECTIVE` nodes that are direct children of the
    /// root.
    fn top_level_directives(root: &SyntaxNode) -> Vec<SyntaxNode> {
        root.children().filter(|c| c.kind() == DIRECTIVE).collect()
    }

    #[test]
    fn rule_1_inline_eol_comment_trails_preceding_directive() {
        // Source under test:
        //   2024-01-01 open Assets:Cash  ; EOL comment
        //   2024-01-02 open Assets:Bank
        //
        // The `  ; EOL comment` run starts AFTER `Assets:Cash` and
        // ends BEFORE the terminating NEWLINE — it does not cross
        // a line boundary from the preceding content. Rule 1: it
        // trails the FIRST directive (NOT the second).
        let source = "2024-01-01 open Assets:Cash  ; EOL comment\n\
                      2024-01-02 open Assets:Bank";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());

        // First directive: content + same-line trailing trivia +
        // terminating NEWLINE. The NEWLINE is the line boundary
        // crossing; per rule 2 it belongs to the NEXT directive's
        // leading run. But it's the ONLY token before the next
        // content, so it's the leading run of length 1.
        b.start_node(DIRECTIVE.into());
        b.token(DATE.into(), "2024-01-01");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Cash");
        b.token(WHITESPACE.into(), "  ");
        b.token(COMMENT.into(), "; EOL comment");
        b.finish_node();

        // Second directive: the line-crossing NEWLINE leads it.
        b.start_node(DIRECTIVE.into());
        b.token(NEWLINE.into(), "\n");
        b.token(DATE.into(), "2024-01-02");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Bank");
        b.finish_node();

        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);
        let directives = top_level_directives(&tree);
        assert_eq!(directives.len(), 2);
        let d1_trivia = direct_trivia_kinds(&directives[0]);
        let d2_trivia = direct_trivia_kinds(&directives[1]);
        assert!(
            d1_trivia.contains(&COMMENT),
            "rule 1: same-line EOL COMMENT must trail PRECEDING directive (d1={d1_trivia:?})",
        );
        assert!(
            !d2_trivia.contains(&COMMENT),
            "rule 1: same-line EOL COMMENT must NOT lead following directive (d2={d2_trivia:?})",
        );
        assert!(
            d2_trivia.starts_with(&[NEWLINE]),
            "rule 2: line-crossing NEWLINE leads the SECOND directive (d2={d2_trivia:?})",
        );
    }

    #[test]
    fn rule_2_blank_line_between_directives_leads_following() {
        // Source under test:
        //   2024-01-01 open Assets:Cash
        //   <BLANK>
        //   2024-01-02 open Assets:Bank
        //
        // Two NEWLINEs between content: the first terminates
        // directive 1's line; the second is the blank line. The
        // run from after `Assets:Cash` to before `2024-01-02` is
        // `NEWLINE NEWLINE`, crosses a line boundary, attaches to
        // directive 2 as leading.
        let source = "2024-01-01 open Assets:Cash\n\
                      \n\
                      2024-01-02 open Assets:Bank";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());

        b.start_node(DIRECTIVE.into());
        b.token(DATE.into(), "2024-01-01");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Cash");
        b.finish_node();

        b.start_node(DIRECTIVE.into());
        b.token(NEWLINE.into(), "\n"); // terminates d1's line; leading of d2
        b.token(NEWLINE.into(), "\n"); // blank line; leading of d2
        b.token(DATE.into(), "2024-01-02");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Bank");
        b.finish_node();

        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);
        let directives = top_level_directives(&tree);
        assert_eq!(directives.len(), 2);
        let d1_trivia = direct_trivia_kinds(&directives[0]);
        let d2_trivia = direct_trivia_kinds(&directives[1]);
        assert_eq!(
            d1_trivia.iter().filter(|k| **k == NEWLINE).count(),
            0,
            "rule 2: directive 1 owns NO NEWLINE — both NEWLINEs lead directive 2 (d1={d1_trivia:?})",
        );
        assert_eq!(
            d2_trivia.iter().filter(|k| **k == NEWLINE).count(),
            2,
            "rule 2: directive 2 owns BOTH NEWLINEs (one line-terminator + one blank) (d2={d2_trivia:?})",
        );
    }

    #[test]
    fn rule_3_copyright_header_attaches_to_source_file() {
        // Source under test:
        //   ;; Copyright 2024
        //   ;; All rights reserved
        //   2024-01-01 open Assets:Cash
        //
        // Two COMMENT lines before the first directive. Rule 3:
        // file-leading trivia attaches to SOURCE_FILE directly,
        // not to the first directive.
        let source = ";; Copyright 2024\n\
                      ;; All rights reserved\n\
                      2024-01-01 open Assets:Cash";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());

        // File-leading trivia: direct children of SOURCE_FILE.
        b.token(COMMENT.into(), ";; Copyright 2024");
        b.token(NEWLINE.into(), "\n");
        b.token(COMMENT.into(), ";; All rights reserved");
        b.token(NEWLINE.into(), "\n");

        b.start_node(DIRECTIVE.into());
        b.token(DATE.into(), "2024-01-01");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Cash");
        b.finish_node();

        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);

        // The file-leading trivia is in SOURCE_FILE, not in the
        // directive.
        let source_file_direct_trivia = direct_trivia_kinds(&tree);
        assert_eq!(
            source_file_direct_trivia,
            vec![COMMENT, NEWLINE, COMMENT, NEWLINE],
            "rule 3: copyright header is a direct child of SOURCE_FILE",
        );
        let directives = top_level_directives(&tree);
        assert_eq!(directives.len(), 1);
        let d1_trivia = direct_trivia_kinds(&directives[0]);
        assert!(
            !d1_trivia.contains(&COMMENT),
            "rule 3: directive 1 must NOT own the copyright header (d1={d1_trivia:?})",
        );
    }

    #[test]
    fn rule_3_bom_and_shebang_attach_to_source_file() {
        // Source under test:
        //   <BOM>#!/usr/bin/env bean-check
        //   2024-01-01 open Assets:Cash
        //
        // BOM + SHEBANG at file start: rule 3 attaches them to
        // SOURCE_FILE, not to directive 1.
        let source = "\u{FEFF}#!/usr/bin/env bean-check\n\
                      2024-01-01 open Assets:Cash";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());

        b.token(BOM.into(), "\u{FEFF}");
        b.token(SHEBANG.into(), "#!/usr/bin/env bean-check");
        b.token(NEWLINE.into(), "\n");

        b.start_node(DIRECTIVE.into());
        b.token(DATE.into(), "2024-01-01");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Cash");
        b.finish_node();

        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);
        let sf_trivia = direct_trivia_kinds(&tree);
        assert_eq!(sf_trivia, vec![BOM, SHEBANG, NEWLINE]);
    }

    #[test]
    fn rule_4_trailing_newline_at_eof_attaches_to_last_directive() {
        // Source under test:
        //   2024-01-01 open Assets:Cash
        //
        // One directive, terminated by a NEWLINE at EOF. Rule 4:
        // no following directive exists, so the NEWLINE attaches
        // to the preceding directive (the file-final one).
        let source = "2024-01-01 open Assets:Cash\n";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());

        b.start_node(DIRECTIVE.into());
        b.token(DATE.into(), "2024-01-01");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Cash");
        b.token(NEWLINE.into(), "\n"); // EOF trailing: owned by d1
        b.finish_node();

        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);
        let directives = top_level_directives(&tree);
        assert_eq!(directives.len(), 1);
        let d1_trivia = direct_trivia_kinds(&directives[0]);
        assert!(
            d1_trivia.ends_with(&[NEWLINE]),
            "rule 4: EOF NEWLINE attaches to the LAST directive (d1={d1_trivia:?})",
        );
        // SOURCE_FILE has no direct trivia children for this input.
        assert!(direct_trivia_kinds(&tree).is_empty());
    }

    #[test]
    fn rule_4_trailing_comment_block_at_eof_attaches_to_last_directive() {
        // Source under test:
        //   2024-01-01 open Assets:Cash
        //   ;; closing remarks
        //
        // Trailing comment block at EOF. Rule 4: the entire
        // post-content trivia run (NEWLINE COMMENT NEWLINE) belongs
        // to the preceding directive.
        let source = "2024-01-01 open Assets:Cash\n\
                      ;; closing remarks\n";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());

        b.start_node(DIRECTIVE.into());
        b.token(DATE.into(), "2024-01-01");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Cash");
        b.token(NEWLINE.into(), "\n");
        b.token(COMMENT.into(), ";; closing remarks");
        b.token(NEWLINE.into(), "\n");
        b.finish_node();

        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);
        let directives = top_level_directives(&tree);
        assert_eq!(directives.len(), 1);
        let d1_trivia = direct_trivia_kinds(&directives[0]);
        assert!(d1_trivia.contains(&COMMENT));
        // No trivia is a direct child of SOURCE_FILE.
        assert!(direct_trivia_kinds(&tree).is_empty());
    }

    #[test]
    fn percent_comment_obeys_the_two_line_rule() {
        // Cover the second comment variant: PERCENT_COMMENT (the
        // `%` line-comment some Beancount-adjacent tooling emits)
        // gets the same policy as COMMENT.
        //
        // Source under test:
        //   2024-01-01 open Assets:Cash  % EOL percent comment
        //   2024-01-02 open Assets:Bank
        let source = "2024-01-01 open Assets:Cash  % EOL percent comment\n\
                      2024-01-02 open Assets:Bank";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());

        b.start_node(DIRECTIVE.into());
        b.token(DATE.into(), "2024-01-01");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Cash");
        b.token(WHITESPACE.into(), "  ");
        b.token(PERCENT_COMMENT.into(), "% EOL percent comment");
        b.finish_node();

        b.start_node(DIRECTIVE.into());
        b.token(NEWLINE.into(), "\n");
        b.token(DATE.into(), "2024-01-02");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Bank");
        b.finish_node();

        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);
        let directives = top_level_directives(&tree);
        let d1_trivia = direct_trivia_kinds(&directives[0]);
        assert!(
            d1_trivia.contains(&PERCENT_COMMENT),
            "PERCENT_COMMENT must follow the Two-Line Rule the same as COMMENT (d1={d1_trivia:?})",
        );
    }

    #[test]
    fn adjacent_directives_no_blank_line_share_only_a_newline() {
        // Source under test:
        //   2024-01-01 open Assets:Cash
        //   2024-01-02 open Assets:Bank
        //
        // No blank line between the two directives. The only
        // inter-directive trivia is the single NEWLINE that
        // terminates d1's line; per rule 2 it crosses a line
        // boundary and attaches as LEADING of d2.
        let source = "2024-01-01 open Assets:Cash\n\
                      2024-01-02 open Assets:Bank";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());

        b.start_node(DIRECTIVE.into());
        b.token(DATE.into(), "2024-01-01");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Cash");
        b.finish_node();

        b.start_node(DIRECTIVE.into());
        b.token(NEWLINE.into(), "\n"); // line-crossing → leads d2
        b.token(DATE.into(), "2024-01-02");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Bank");
        b.finish_node();

        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);
        let directives = top_level_directives(&tree);
        let d1_content = direct_content_kinds(&directives[0]);
        let d2_content = direct_content_kinds(&directives[1]);
        let d1_trivia = direct_trivia_kinds(&directives[0]);
        let d2_trivia = direct_trivia_kinds(&directives[1]);
        assert_eq!(d1_content, vec![DATE, OPEN_KW, ACCOUNT]);
        assert_eq!(d2_content, vec![DATE, OPEN_KW, ACCOUNT]);
        assert!(
            !d1_trivia.contains(&NEWLINE),
            "rule 2: the line-terminator NEWLINE is NOT inside d1 (d1={d1_trivia:?})",
        );
        assert_eq!(
            d2_trivia.iter().filter(|k| **k == NEWLINE).count(),
            1,
            "rule 2: the line-terminator NEWLINE leads d2 (d2={d2_trivia:?})",
        );
    }

    #[test]
    fn file_with_only_trivia_attaches_everything_to_source_file() {
        // Source under test:
        //   ;; only a comment
        //   <blank>
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
        assert!(
            top_level_directives(&tree).is_empty(),
            "no content → no DIRECTIVE node",
        );
        assert_eq!(direct_trivia_kinds(&tree), vec![COMMENT, NEWLINE, NEWLINE]);
    }

    #[test]
    fn empty_file_is_an_empty_source_file_node() {
        // Edge case: zero bytes of source. SOURCE_FILE exists but
        // has no children. The policy has nothing to apply.
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());
        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), "");
        assert!(top_level_directives(&tree).is_empty());
        assert!(direct_trivia_kinds(&tree).is_empty());
    }

    #[test]
    fn leading_and_trailing_coexist() {
        // Source under test combines all 4 rules:
        //   ;; copyright              (rule 3: SOURCE_FILE)
        //   2024-01-01 open Assets:Cash  ; eol1   (rule 1: trails d1)
        //   <blank>                   (rule 2: leads d2)
        //   2024-01-02 open Assets:Bank
        //   ;; footer                 (rule 4: trails d2 — EOF case)
        let source = ";; copyright\n\
                      2024-01-01 open Assets:Cash  ; eol1\n\
                      \n\
                      2024-01-02 open Assets:Bank\n\
                      ;; footer\n";
        let mut b = GreenNodeBuilder::new();
        b.start_node(SOURCE_FILE.into());

        // File-leading (rule 3)
        b.token(COMMENT.into(), ";; copyright");
        b.token(NEWLINE.into(), "\n");

        // Directive 1: trailing EOL comment (rule 1)
        b.start_node(DIRECTIVE.into());
        b.token(DATE.into(), "2024-01-01");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Cash");
        b.token(WHITESPACE.into(), "  ");
        b.token(COMMENT.into(), "; eol1");
        b.finish_node();

        // Directive 2: leading newlines (rule 2) + EOF trailing
        // comment (rule 4) all belong to d2.
        b.start_node(DIRECTIVE.into());
        b.token(NEWLINE.into(), "\n"); // line-crosser
        b.token(NEWLINE.into(), "\n"); // blank line
        b.token(DATE.into(), "2024-01-02");
        b.token(WHITESPACE.into(), " ");
        b.token(OPEN_KW.into(), "open");
        b.token(WHITESPACE.into(), " ");
        b.token(ACCOUNT.into(), "Assets:Bank");
        b.token(NEWLINE.into(), "\n"); // d2 line terminator
        b.token(COMMENT.into(), ";; footer");
        b.token(NEWLINE.into(), "\n"); // final EOF newline
        b.finish_node();

        b.finish_node();
        let tree = SyntaxNode::new_root(b.finish());

        assert_eq!(tree.text().to_string(), source);

        let sf_trivia = direct_trivia_kinds(&tree);
        assert_eq!(
            sf_trivia,
            vec![COMMENT, NEWLINE],
            "SOURCE_FILE owns ONLY the file-leading copyright (sf={sf_trivia:?})",
        );

        let directives = top_level_directives(&tree);
        assert_eq!(directives.len(), 2);

        let d1_trivia = direct_trivia_kinds(&directives[0]);
        assert!(
            d1_trivia.contains(&COMMENT) && !d1_trivia.contains(&NEWLINE),
            "d1 owns the EOL comment but NOT the line-terminating NEWLINE (d1={d1_trivia:?})",
        );

        let d2_trivia = direct_trivia_kinds(&directives[1]);
        assert_eq!(
            d2_trivia.iter().filter(|k| **k == COMMENT).count(),
            1,
            "d2 owns the footer COMMENT (rule 4 EOF case) (d2={d2_trivia:?})",
        );
        assert_eq!(
            d2_trivia.iter().filter(|k| **k == NEWLINE).count(),
            4,
            "d2 owns 4 NEWLINEs: line-crosser, blank, d2-terminator, EOF (d2={d2_trivia:?})",
        );
    }
}
