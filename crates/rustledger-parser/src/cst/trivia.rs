//! Trivia attachment policy for the CST. Phase 2.0 of #1262.
//!
//! Phase 1 emits a flat tree: every token (content AND trivia) is a
//! direct child of `SOURCE_FILE`. Phase 2.1+ introduces structural
//! nodes (DIRECTIVE wrappers, then POSTING, AMOUNT, ...). The
//! question this module answers: when a trivia run sits between two
//! content tokens, which structural node owns it?
//!
//! # The policy (rust-analyzer convention)
//!
//! 1. **Leading attaches forward.** Trivia (WHITESPACE, NEWLINE,
//!    COMMENT, BOM, ...) that appears BETWEEN two content tokens
//!    attaches to the FOLLOWING content token's structural parent.
//!    A blank line between two directives belongs to the SECOND
//!    directive, not the first.
//! 2. **EOF is the exception.** Trivia appearing AFTER the last
//!    content token attaches to the PRECEDING content token's
//!    structural parent. There is no following node to attach to,
//!    so the preceding directive absorbs it.
//! 3. **`SOURCE_FILE` is the parent of last resort.** Trivia
//!    appearing BEFORE any content token (BOM, shebang, copyright
//!    comment header, leading blank lines) attaches to `SOURCE_FILE`
//!    as a direct child — there is no preceding directive.
//! 4. **A file containing only trivia** has every token under
//!    `SOURCE_FILE` directly. Both edge cases (no content, only
//!    trivia) collapse to `FileLeading`.
//!
//! # Why this convention
//!
//! - Most consumers (typed AST surface, validators, semantic
//!   tooling) iterate over directives and want to skip trivia at
//!   entry. The "leading attaches forward" rule means each
//!   directive's `SyntaxNode` covers the blank lines preceding it,
//!   so `node.text_range()` is the directive's full source span
//!   including its visual separation. Consumers that don't care
//!   about trivia skip it on enter; the formatter walks the full
//!   tree and never skips, so either direction is lossless for it.
//! - Matches rust-analyzer (and Roslyn, and most other lossless-CST
//!   parsers). Reviewers familiar with that family don't have to
//!   relearn the convention.
//! - "Trailing attaches backward" would leave each directive's
//!   `text_range()` ending mid-blank-line, making span arithmetic
//!   awkward in tooling that wants whole-directive bounds (LSP
//!   hover, selection range, code lens placement).
//!
//! # Scope
//!
//! This module operates on the FLAT token kind sequence and
//! identifies what each trivia token's attachment WOULD be once
//! structural nodes wrap top-level directives. It is the helper
//! phase 2.1+ parsers call when deciding whether to consume trivia
//! BEFORE opening a new DIRECTIVE node (`Leading` / `FileLeading`)
//! or AFTER closing one (`EofTrailing`).
//!
//! Within a directive, intra-directive trivia (the NEWLINE between
//! a transaction header and its postings, the WHITESPACE around a
//! `+` in an amount expression, etc.) is GRAMMAR-DRIVEN and lives
//! inside whatever structural node the grammar opens. That's phase
//! 2.1's parser logic, not this module's.

use crate::cst::syntax_kind::SyntaxKind;

/// Where a trivia token attaches when phase 2+ wraps top-level
/// directives in structural nodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TriviaAttachment {
    /// Trivia appearing before any content token in the file.
    /// Attaches to `SOURCE_FILE` as a direct child. Examples: a
    /// leading BOM, a copyright-header comment block, blank lines
    /// at the very top of the file.
    FileLeading,
    /// Trivia appearing between two content tokens. Attaches to the
    /// FOLLOWING content token's structural parent (typically the
    /// next directive node). Examples: the blank line between two
    /// directives, the whitespace before a directive's date.
    Leading,
    /// Trivia appearing after the last content token in the file.
    /// Attaches to the PRECEDING content token's structural parent
    /// (the last directive). Example: a trailing newline at EOF.
    EofTrailing,
}

/// Classify each token in a flat kind sequence as either non-trivia
/// content (`None`) or trivia with an attachment intent (`Some`).
///
/// The returned `Vec` is the same length as `kinds`; index `i` of
/// the result describes how the input's token at index `i` would
/// attach when phase 2.1+ introduces structural directive nodes.
///
/// See the module-level rustdoc for the policy this implements.
#[must_use]
pub fn classify_trivia(kinds: &[SyntaxKind]) -> Vec<Option<TriviaAttachment>> {
    let first_content = kinds.iter().position(|k| !k.is_trivia());
    let last_content = kinds.iter().rposition(|k| !k.is_trivia());

    let (Some(first), Some(last)) = (first_content, last_content) else {
        // No content tokens at all: every token is FileLeading.
        return kinds
            .iter()
            .map(|_| Some(TriviaAttachment::FileLeading))
            .collect();
    };

    kinds
        .iter()
        .enumerate()
        .map(|(i, kind)| {
            if !kind.is_trivia() {
                None
            } else if i < first {
                Some(TriviaAttachment::FileLeading)
            } else if i > last {
                Some(TriviaAttachment::EofTrailing)
            } else {
                Some(TriviaAttachment::Leading)
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::TriviaAttachment::{EofTrailing, FileLeading, Leading};
    use super::*;
    use crate::cst::SyntaxKind::{
        ACCOUNT, BOM, COMMENT, DATE, NEWLINE, OPEN_KW, SHEBANG, WHITESPACE,
    };

    #[test]
    fn empty_input_returns_empty() {
        assert!(classify_trivia(&[]).is_empty());
    }

    #[test]
    fn single_content_token_has_no_attachment() {
        assert_eq!(classify_trivia(&[DATE]), vec![None]);
    }

    #[test]
    fn only_trivia_collapses_to_file_leading() {
        // Whole file is blank lines + a comment.
        let kinds = [NEWLINE, COMMENT, NEWLINE];
        assert_eq!(
            classify_trivia(&kinds),
            vec![Some(FileLeading), Some(FileLeading), Some(FileLeading)],
        );
    }

    #[test]
    fn bom_at_start_is_file_leading() {
        let kinds = [BOM, DATE, OPEN_KW];
        assert_eq!(classify_trivia(&kinds), vec![Some(FileLeading), None, None],);
    }

    #[test]
    fn shebang_at_start_is_file_leading() {
        let kinds = [SHEBANG, NEWLINE, DATE, OPEN_KW];
        assert_eq!(
            classify_trivia(&kinds),
            vec![Some(FileLeading), Some(FileLeading), None, None],
        );
    }

    #[test]
    fn copyright_header_before_first_directive_is_file_leading() {
        // ;; Copyright header
        // ;; ...
        // 2024-01-01 open Assets:Cash
        let kinds = [COMMENT, NEWLINE, COMMENT, NEWLINE, DATE, OPEN_KW, ACCOUNT];
        assert_eq!(
            classify_trivia(&kinds),
            vec![
                Some(FileLeading),
                Some(FileLeading),
                Some(FileLeading),
                Some(FileLeading),
                None,
                None,
                None,
            ],
        );
    }

    #[test]
    fn trailing_newline_at_eof_is_eof_trailing() {
        let kinds = [DATE, OPEN_KW, NEWLINE];
        assert_eq!(classify_trivia(&kinds), vec![None, None, Some(EofTrailing)]);
    }

    #[test]
    fn multiple_trailing_blank_lines_are_eof_trailing() {
        // Last directive followed by two blank lines at EOF.
        let kinds = [DATE, OPEN_KW, NEWLINE, NEWLINE, NEWLINE];
        assert_eq!(
            classify_trivia(&kinds),
            vec![
                None,
                None,
                Some(EofTrailing),
                Some(EofTrailing),
                Some(EofTrailing)
            ],
        );
    }

    #[test]
    fn blank_line_between_directives_attaches_forward_as_leading() {
        // The load-bearing test: pins the rust-analyzer convention.
        //
        //   2024-01-01 open Assets:Cash
        //   <blank>
        //   2024-01-02 open Assets:Bank
        //
        // The blank-line NEWLINE belongs to the SECOND directive
        // (Leading), not the first (Trailing). If a future refactor
        // flips this rule, this assertion fires and the policy
        // change has to be deliberate.
        let kinds = [
            DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, NEWLINE, // first directive
            NEWLINE, // <-- blank line
            DATE, WHITESPACE, OPEN_KW, WHITESPACE, ACCOUNT, NEWLINE, // second directive
        ];
        let got = classify_trivia(&kinds);
        // Indices of trivia: 1, 3, 5, 6, 8, 10, 12.
        // Last content token is index 11 (ACCOUNT). Index 12 is past it.
        assert_eq!(got[1], Some(Leading), "intra-first WHITESPACE");
        assert_eq!(got[3], Some(Leading), "intra-first WHITESPACE");
        assert_eq!(got[5], Some(Leading), "end-of-first NEWLINE");
        assert_eq!(
            got[6],
            Some(Leading),
            "BLANK LINE attaches FORWARD (load-bearing assertion)",
        );
        assert_eq!(got[8], Some(Leading), "intra-second WHITESPACE");
        assert_eq!(got[10], Some(Leading), "intra-second WHITESPACE");
        assert_eq!(got[12], Some(EofTrailing), "trailing NEWLINE at EOF");
    }

    #[test]
    fn comment_block_between_directives_attaches_forward() {
        //   2024-01-01 open Assets:Cash
        //   ;; comment about the next account
        //   2024-01-02 open Assets:Bank
        let kinds = [
            DATE, OPEN_KW, ACCOUNT, NEWLINE, // first directive
            COMMENT, NEWLINE, // mid-file comment
            DATE, OPEN_KW, ACCOUNT, // second directive
        ];
        let got = classify_trivia(&kinds);
        assert_eq!(got[4], Some(Leading), "mid-file COMMENT attaches forward");
        assert_eq!(got[5], Some(Leading), "comment-terminating NEWLINE");
    }

    #[test]
    fn trailing_comment_block_at_eof_is_eof_trailing() {
        //   2024-01-01 open Assets:Cash
        //   ;; closing remarks
        let kinds = [DATE, OPEN_KW, ACCOUNT, NEWLINE, COMMENT, NEWLINE];
        let got = classify_trivia(&kinds);
        assert_eq!(got[3], Some(EofTrailing));
        assert_eq!(got[4], Some(EofTrailing));
        assert_eq!(got[5], Some(EofTrailing));
    }

    #[test]
    fn leading_and_trailing_coexist_with_content() {
        //   ;; header
        //   2024-01-01 open Assets:Cash
        //   <blank>
        //   2024-01-02 open Assets:Bank
        //   ;; footer
        let kinds = [
            COMMENT, NEWLINE, // file-leading
            DATE, OPEN_KW, ACCOUNT, NEWLINE, NEWLINE, // blank between directives
            DATE, OPEN_KW, ACCOUNT, NEWLINE, COMMENT, NEWLINE, // file-trailing
        ];
        let got = classify_trivia(&kinds);
        assert_eq!(got[0], Some(FileLeading));
        assert_eq!(got[1], Some(FileLeading));
        assert_eq!(got[5], Some(Leading));
        assert_eq!(got[6], Some(Leading));
        assert_eq!(got[10], Some(EofTrailing));
        assert_eq!(got[11], Some(EofTrailing));
        assert_eq!(got[12], Some(EofTrailing));
    }

    #[test]
    fn classification_length_matches_input() {
        // Property: classify_trivia returns one entry per input
        // token, in the same order. Phase 2.1's parser relies on
        // index correspondence.
        let kinds = [
            BOM, COMMENT, NEWLINE, DATE, WHITESPACE, OPEN_KW, ACCOUNT, NEWLINE,
        ];
        let got = classify_trivia(&kinds);
        assert_eq!(got.len(), kinds.len());
    }

    #[test]
    fn non_trivia_is_always_none() {
        // Every non-trivia variant must return None regardless of
        // position. Guard against a future variant being silently
        // misclassified.
        let content_kinds = [DATE, OPEN_KW, ACCOUNT];
        let got = classify_trivia(&content_kinds);
        for (i, c) in got.iter().enumerate() {
            assert_eq!(*c, None, "index {i}: content token returned attachment");
        }
    }
}
