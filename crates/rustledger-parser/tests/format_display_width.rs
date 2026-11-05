//! The formatter aligns amounts by display width, not code points (#2852).
//!
//! In a monospaced editor an East Asian Wide or Fullwidth character takes
//! two cells and a combining mark none, so padding by code points puts the
//! amounts of an account with such characters in a different visible
//! column. rledger pads by display width. bean-format 3.2.3 never lines
//! these up: it leaves a line like `Expenses:생활  12345 KRW`, or one with an
//! emoji or a combining mark in the account, as written (its alignment regex
//! needs each component after the root to start with an uppercase letter or a
//! digit, and every character to be a letter, a digit or a hyphen) and pads a
//! line that does match (`Expenses:X생활`) by code points. A deliberate difference, documented in
//! `docs/reference/compatibility.md` ("Amount Alignment With Wide
//! Characters"). ASCII-only alignment is unchanged.

use rustledger_parser::format::{display_width, try_format_source};

/// The display width of each posting line up to the end of its number,
/// that is, the visible column the right-justified amounts share.
fn number_end_columns(out: &str) -> Vec<usize> {
    out.lines()
        .filter(|l| l.starts_with("  "))
        .map(|l| {
            let cut = l.rfind(' ').expect("a currency after the number");
            display_width(&l[..cut])
        })
        .collect()
}

fn assert_aligned_and_idempotent(label: &str, src: &str, want: &str) {
    let out = try_format_source(src).unwrap_or_else(|e| panic!("{label}: {e:?}"));
    assert_eq!(out, want, "{label}");
    let cols = number_end_columns(&out);
    assert!(
        cols.windows(2).all(|w| w[0] == w[1]),
        "{label}: amounts end in different visible columns: {cols:?}"
    );
    assert_eq!(
        try_format_source(&out).expect("formatted output parses"),
        out,
        "{label}: not idempotent"
    );
}

/// The issue's example: `생활` is two characters but four cells.
#[test]
fn test_try_format_source_aligns_a_korean_account_by_display_width() {
    assert_aligned_and_idempotent(
        "Korean",
        "2021-01-01 open Assets:Bank KRW\n2021-01-01 open Expenses:생활 KRW\n2021-01-02 * \"x\"\n  Expenses:생활  12345 KRW\n  Assets:Bank   -12345 KRW\n",
        "2021-01-01 open Assets:Bank KRW\n2021-01-01 open Expenses:생활 KRW\n2021-01-02 * \"x\"\n  Expenses:생활   12345 KRW\n  Assets:Bank    -12345 KRW\n",
    );
}

/// CJK (two cells each), a combining acute accent (zero cells) and an emoji
/// (two cells, per `unicode-width`) in one transaction.
#[test]
fn test_try_format_source_aligns_cjk_combining_marks_and_emoji_by_display_width() {
    assert_aligned_and_idempotent(
        "CJK, combining mark, emoji",
        "2021-01-02 * \"x\"\n  Expenses:食品  1.00 USD\n  Expenses:Cafe\u{301}  2.00 USD\n  Expenses:Fun🎉  3.00 USD\n  Assets:Cash  -6.00 USD\n",
        "2021-01-02 * \"x\"\n  Expenses:食品    1.00 USD\n  Expenses:Cafe\u{301}    2.00 USD\n  Expenses:Fun🎉   3.00 USD\n  Assets:Cash     -6.00 USD\n",
    );
}

/// ASCII-only input is unaffected: the same output as by code points.
#[test]
fn test_try_format_source_ascii_alignment_is_unchanged() {
    assert_aligned_and_idempotent(
        "ASCII",
        "2021-01-02 * \"x\"\n  Expenses:Food  1.00 USD\n  Assets:Cash  -1.00 USD\n",
        "2021-01-02 * \"x\"\n  Expenses:Food   1.00 USD\n  Assets:Cash    -1.00 USD\n",
    );
}

#[test]
fn test_display_width_counts_terminal_cells() {
    assert_eq!(display_width("Assets:Bank"), 11);
    assert_eq!(display_width("생활"), 4);
    assert_eq!(display_width("食品"), 4);
    assert_eq!(display_width("Cafe\u{301}"), 4);
    assert_eq!(display_width("🎉"), 2);
    // Ambiguous-width characters (here GREEK SMALL LETTER ALPHA) count as
    // one cell, as most terminals render them.
    assert_eq!(display_width("α"), 1);
}
