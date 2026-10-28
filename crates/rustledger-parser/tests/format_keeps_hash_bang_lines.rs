//! `rledger format` must keep `#!` and `#+` lines wherever they appear
//! (#2776).
//!
//! The lexer has four line-comment kinds: `;`, `%`, `#!` (`SHEBANG`) and
//! `#+` (`EMACS_DIRECTIVE`). The formatter's trivia emitters only knew the
//! first two, so a `#!` or `#+` line that came after a directive was
//! silently deleted: as a directive's leading trivia (where it also stopped
//! the scan, dropping the comments after it), as a same-line trailing
//! comment, and inside a transaction body. At the top of the file a
//! different path kept them. The emitters now use the parser's canonical
//! `is_comment_kind`, which covers all four.

use rustledger_parser::format::try_format_source;

/// Each input is already canonical, so formatting must return it byte for
/// byte, and formatting again must be a no-op.
fn assert_kept(label: &str, src: &str) {
    let formatted = try_format_source(src).expect("the file formats");
    assert_eq!(formatted, src, "{label}");
    assert_eq!(
        try_format_source(&formatted).expect("the output formats"),
        formatted,
        "{label}: not idempotent"
    );
}

#[test]
fn test_try_format_source_keeps_hash_bang_lines_between_directives() {
    assert_kept(
        "between directives",
        "2024-01-01 open Assets:A\n#!x\n#+y\n2024-01-02 open Assets:B\n",
    );
}

/// The `; d` after the `#+` line was lost too: the leading-trivia scan
/// stopped at the first kind it did not know.
#[test]
fn test_try_format_source_keeps_comments_around_a_hash_plus_line() {
    assert_kept(
        "among comments",
        "2024-01-01 open Assets:A\n; c\n#+y\n; d\n2024-01-02 open Assets:B\n",
    );
}

#[test]
fn test_try_format_source_keeps_a_same_line_hash_plus_comment() {
    assert_kept(
        "same-line trailing",
        "2024-01-01 open Assets:A #+stray\n2024-01-02 open Assets:B\n",
    );
}

#[test]
fn test_try_format_source_keeps_hash_bang_lines_in_a_transaction_body() {
    assert_kept(
        "before the postings",
        "2024-01-01 * \"x\"\n  #+note\n  Assets:A  1 USD\n  Assets:B\n",
    );
    assert_kept(
        "between postings",
        "2024-01-01 * \"x\"\n  Assets:A  1 USD\n  #!p\n  Assets:B\n",
    );
}

/// The positions that already worked stay as they were.
#[test]
fn test_try_format_source_keeps_hash_bang_lines_at_the_file_edges() {
    assert_kept("top of file", "#!x\n#+y\n2024-01-01 open Assets:A\n");
    assert_kept("end of file", "2024-01-01 open Assets:A\n#!x\n");
}
