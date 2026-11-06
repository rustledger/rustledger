//! Column-0 marker lines are read as beancount reads them (#2779).
//!
//! Beancount's lexer ignores a whole line that starts at column 0 with `*`,
//! `:`, `#` or a flag character (`^[\*\:\#]/.` and `^{FLAGS}/.`, with
//! `FLAGS [!&#?%]`). rledger reported a `!`, `&`, `?` or `:` line as a syntax
//! error, so `rledger check` failed files that `bean-check` accepts. Both
//! rules need one more character on the line (flex's `.`, which a `\r`
//! satisfies): a bare marker, with its line ending right after it, is a token
//! there and an error (`unexpected FLAG`, `HASH`, `ASTERISK` or `COLON`),
//! where rledger accepted a bare `#`, `%` or `*` line as a comment.
//!
//! Every expectation here was checked against bean-check 3.2.3.

use rustledger_core::Directive;
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::format::{format_source, try_format_source};
use rustledger_parser::{parse, parse_structured};

/// The parsed opens, as `date account`, and the 1-based lines of the parse
/// errors, from both conversion paths (they must agree).
fn summary(src: &str) -> (Vec<String>, Vec<usize>) {
    let result = parse(src);
    let red = parse_red_only(src);
    assert_eq!(
        format!("{:?}", result.directives),
        format!("{:?}", red.directives),
        "{src:?}: green and red directives differ"
    );
    assert_eq!(
        format!("{:?}", result.errors),
        format!("{:?}", red.errors),
        "{src:?}: green and red errors differ"
    );
    assert_eq!(
        parse_structured(src).text().to_string(),
        src,
        "{src:?}: not lossless"
    );
    let opens = result
        .directives
        .iter()
        .map(|d| match &d.value {
            Directive::Open(o) => format!("{} {}", o.date, o.account),
            other => panic!("{src:?}: unexpected directive {other:?}"),
        })
        .collect();
    let lines = result
        .errors
        .iter()
        .map(|e| src[..e.span.start].matches('\n').count() + 1)
        .collect();
    (opens, lines)
}

#[test]
fn test_parse_ignores_column_0_flag_and_colon_lines() {
    for marker in ['!', '&', '?', ':'] {
        for rest in [" x", "x", " \"q", "\t", "x \"q\" Assets:A 1 USD"] {
            for eol in ["\n", "\r\n"] {
                let src = format!(
                    "{marker}{rest}{eol}2024-01-02 open Assets:B{eol}\
                     {marker}{rest}{eol}2024-01-03 open Assets:C{eol}"
                );
                assert_eq!(
                    summary(&src),
                    (
                        vec![
                            "2024-01-02 Assets:B".to_string(),
                            "2024-01-03 Assets:C".to_string()
                        ],
                        vec![]
                    ),
                    "{src:?}"
                );
            }
        }
    }
}

/// The ignored line is a comment: it is kept verbatim, and a `"` on it does
/// not open a string (the second string on the note is read as one).
#[test]
fn test_parse_column_0_flag_line_is_a_comment() {
    let src = "! a \"q\n& b \"q\n? c \"q\n: d \"q\n2024-01-02 open Assets:B\n";
    let result = parse(src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let comments: Vec<&str> = result.comments.iter().map(|c| c.value.as_str()).collect();
    assert_eq!(comments, ["! a \"q", "& b \"q", "? c \"q", ": d \"q"]);
    assert_eq!(format_source(src), src);
}

/// Only column 0: an indented `!` or `&` is a posting flag, and `:` or `?`
/// there is an error, as in beancount.
#[test]
fn test_parse_indented_flag_is_not_a_comment() {
    let src = "2024-01-01 *\n  ! Assets:A  1 USD\n  & Assets:B  -1 USD\n";
    let result = parse(src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let Directive::Transaction(txn) = &result.directives[0].value else {
        panic!("not a transaction: {:?}", result.directives);
    };
    let flags: Vec<Option<char>> = txn.postings.iter().map(|p| p.flag).collect();
    assert_eq!(flags, [Some('!'), Some('&')]);
    for marker in [':', '?'] {
        let src = format!("2024-01-01 open Assets:A\n  {marker} x\n");
        assert!(!parse(&src).errors.is_empty(), "{src:?}");
    }
}

/// A bare marker, with its line ending or the end of the file right after
/// it, is an error on its own line, for every marker (bean-check 3.2.3:
/// `unexpected FLAG`, `HASH`, `ASTERISK` or `COLON`). With a `\r` after it,
/// the line is ignored.
#[test]
fn test_parse_reports_a_bare_column_0_marker() {
    for marker in ['!', '&', '?', ':', '#', '%', '*'] {
        let src = format!("2024-01-01 open Assets:A\n{marker}\n2024-01-02 open Assets:B\n");
        let (opens, lines) = summary(&src);
        assert_eq!(opens.len(), 2, "{src:?}");
        assert_eq!(lines, [2], "{src:?}");

        let src = format!("2024-01-01 open Assets:A\n{marker}");
        assert_eq!(summary(&src).1, [2], "{src:?}");

        let src = format!("2024-01-01 open Assets:A\r\n{marker}\r\n2024-01-02 open Assets:B\r\n");
        let (opens, lines) = summary(&src);
        assert_eq!((opens.len(), lines), (2, vec![]), "{src:?}");
    }
}

/// An indented line after an ignored line has nothing to continue, so it is
/// `unexpected INDENT` as after any column-0 comment: here both that and the
/// invalid date on it are reported, on line 3, as bean-check reports them
/// (#2872).
#[test]
fn test_parse_indented_line_after_flag_line_has_nothing_to_continue() {
    for marker in ["!x", "&x", ":x", "?x", "; x"] {
        for eol in ["\n", "\r\n"] {
            let src = format!("2024-01-01 open Assets:A{eol}{marker}{eol}  2024-02-30 5{eol}");
            assert_eq!(summary(&src).1, [3, 3], "{src:?}");
        }
    }
}

/// The formatter keeps the line verbatim, and a `"` on it does not flip the
/// line-ending pass into a string: on a CRLF file every line ending, the one
/// after the `"` included, comes out as LF.
#[test]
fn test_format_keeps_column_0_flag_line() {
    for eol in ["\n", "\r\n"] {
        let src = format!("! a \"q{eol}2024-01-02 note Assets:B \"x\"{eol}: b{eol}");
        let formatted = try_format_source(&src).expect("the file parses");
        assert_eq!(formatted, src.replace("\r\n", "\n"), "{src:?}");
    }
}
