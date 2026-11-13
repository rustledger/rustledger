//! A `#!` or `#+` that does not start its line is a `#` and the token after
//! it, as in beancount (#2928), so the line is a syntax error there. The
//! error names the `#!` / `#+` and says that only `;` starts a comment that
//! is indented or in the middle of a line, at the `#`, wherever the line
//! stands: under a posting, in a directive's metadata, at the top level, or
//! after a column-0 `#+` line. Each count is bean-check 3.2.3's.

use rustledger_parser::cst::parse_red_only;
use rustledger_parser::{ParseResult, parse};

/// Parse `src` on the green and the red path, require them to agree on the
/// errors, and return the green result.
fn parse_both(src: &str) -> ParseResult {
    let green = parse(src);
    let red = parse_red_only(src);
    assert_eq!(
        format!("{:?}", green.errors),
        format!("{:?}", red.errors),
        "green vs red diverged for {src:?}"
    );
    green
}

fn hint(marker: &str) -> String {
    format!(
        "parse error: unexpected {marker:?}: only `;` starts a comment that is indented or in \
         the middle of a line; `{marker}` starts one only at the beginning of a line"
    )
}

/// Each indented `#!` / `#+` line: the line's error is at the `#` (byte
/// `at`, the two characters of the marker), with the hint, and the counts
/// stay beancount's (`errors` in all).
#[test]
fn test_parse_indented_hash_bang_line_names_the_marker() {
    for (src, marker, at, errors) in [
        // Under a posting.
        (
            "2024-01-01 open Assets:A\n2024-01-02 * \"p\"\n  Assets:A  1 USD\n    #+x\n  Assets:B\n",
            "#+",
            "2024-01-01 open Assets:A\n2024-01-02 * \"p\"\n  Assets:A  1 USD\n    ".len(),
            2,
        ),
        (
            "2024-01-02 * \"p\"\n  #! note\n  Assets:A  1 USD\n  Assets:B\n",
            "#!",
            "2024-01-02 * \"p\"\n  ".len(),
            1,
        ),
        // At the top level, under no directive.
        ("  #+STARTUP: showall\n", "#+", 2, 2),
        // After a column-0 `#+` line, which is still a comment.
        ("#+TITLE\n  #+STARTUP: x\n", "#+", "#+TITLE\n  ".len(), 2),
        ("#+TITLE\n\t#!x\n", "#!", "#+TITLE\n\t".len(), 2),
        // In an `open`'s metadata. (The metadata line after it is one error
        // more than in beancount, as after any indented error line there:
        // beancount's recovery, #2872.)
        (
            "2024-01-01 open Assets:A\n  aa: \"v1\"\n  #+m\n",
            "#+",
            "2024-01-01 open Assets:A\n  aa: \"v1\"\n  ".len(),
            2,
        ),
    ] {
        let result = parse_both(src);
        assert_eq!(result.errors.len(), errors, "{src:?}: {:?}", result.errors);
        let e = &result.errors[0];
        assert_eq!((e.span.start, e.span.end), (at, at + 2), "{src:?}: {e:?}");
        assert_eq!(e.message(), hint(marker), "{src:?}");
    }
}

/// A `#!` / `#+` after a posting's amount or on a directive's header line:
/// the defect reported at the `#` names both characters and keeps the hint.
#[test]
fn test_parse_same_line_hash_bang_defect_names_the_marker() {
    let src = "2024-01-02 * \"p\"\n  Assets:A  1 USD #!x\n  Assets:B\n";
    let result = parse_both(src);
    assert_eq!(result.errors.len(), 2, "{:?}", result.errors);
    let e = &result.errors[0];
    let at = src.find("#!").expect("the marker");
    assert_eq!((e.span.start, e.span.end), (at, at + 2), "{e:?}");
    assert_eq!(
        e.message(),
        "parse error: unexpected \"#!\" in a posting: expected the end of the line. Only \
         `;` starts a comment in the middle of a line; `#!` starts one only at the beginning \
         of a line"
    );
    let src = "2024-01-01 open Assets:A #+x\n";
    let result = parse_both(src);
    assert_eq!(result.errors.len(), 2, "{:?}", result.errors);
    let e = &result.errors[0];
    let at = src.find("#+").expect("the marker");
    assert_eq!((e.span.start, e.span.end), (at, at + 2), "{e:?}");
    assert!(
        e.message()
            .starts_with("parse error: unexpected \"#+\" in the open directive"),
        "{e:?}"
    );
    assert!(
        e.message()
            .ends_with("`#+` starts one only at the beginning of a line"),
        "{e:?}"
    );
}

/// A `#!` / `#+` inside a string or a `;` comment is neither a marker nor
/// renamed, and a column-0 one is a comment, no error.
#[test]
fn test_parse_hash_bang_in_a_string_or_comment_or_at_column_0_is_left_alone() {
    for src in [
        "#!x\n#+y\n2024-01-01 open Assets:A\n",
        "2024-01-01 open Assets:A ; #!x\n",
        "2024-01-01 note Assets:A \"a #!x\"\n",
    ] {
        assert!(parse_both(src).errors.is_empty(), "{src:?}");
    }
}
