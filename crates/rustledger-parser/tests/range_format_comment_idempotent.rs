//! Range-formatting a selection that ends on a top-level comment is a no-op
//! on a canonical file, however often it runs (#2838).
//!
//! A directive owns the NEWLINE that ends it; a top-level comment token does
//! not, while the emitter ends the comment's line with one. The snap used to
//! stop at the comment token, so each run replaced `; c` with `; c\n` and the
//! file gained a blank line every time. The snap now takes the comment's own
//! NEWLINE.

use rustledger_parser::format::{GroupingStyle, format_parsed_range};
use rustledger_parser::{TextRange, TextSize, parse};

fn ts(n: usize) -> TextSize {
    TextSize::try_from(n).expect("offset fits")
}

/// Range-format `start..end` of `src` and splice the edit back in.
fn apply(src: &str, start: usize, end: usize) -> String {
    let parsed = parse(src);
    let (snap, out) = format_parsed_range(
        &parsed,
        TextRange::new(ts(start), ts(end)),
        GroupingStyle::default(),
    )
    .unwrap_or_else(|| panic!("{src:?}: range formatting declined"));
    let (s, e) = (usize::from(snap.start()), usize::from(snap.end()));
    format!("{}{}{}", &src[..s], out, &src[e..])
}

#[test]
fn test_format_parsed_range_on_a_leading_comment_is_idempotent() {
    for (label, src) in [
        ("clean file", "; c\n2024-01-01 open Assets:A\n"),
        (
            "a blank line after the comment",
            "; c\n\n2024-01-01 open Assets:A\n",
        ),
        (
            "a parse error later in the file",
            "; c\n2024-01-01 open   Assets:A junk\n2024-01-02 open Assets:B\n",
        ),
        ("two comment lines", "; c\n; d\n2024-01-01 open Assets:A\n"),
        (
            "a comment between directives",
            "2024-01-01 open Assets:A\n; c\n2024-01-02 open Assets:B\n",
        ),
    ] {
        // Select the first comment's first character, as an editor's
        // format-selection on that line sends.
        let at = src.find(';').expect("a comment");
        let once = apply(src, at, at + 1);
        assert_eq!(once, src, "{label}: the first run changed a canonical file");
        assert_eq!(
            apply(&once, at, at + 1),
            src,
            "{label}: the second run changed it"
        );
    }
}

/// A comment at the end of the file with no newline gets one, once.
#[test]
fn test_format_parsed_range_adds_a_final_newline_after_a_trailing_comment_once() {
    let src = "2024-01-01 open Assets:A\n; c";
    let at = src.find(';').expect("a comment");
    let once = apply(src, at, at + 1);
    assert_eq!(once, "2024-01-01 open Assets:A\n; c\n");
    assert_eq!(apply(&once, at, at + 1), once);
}
