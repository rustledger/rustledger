//! A date in a value position that is not a real calendar date is reported,
//! as the directive's own date is (#2811). It used to load as no value, with
//! no error. beancount 3.2.3 reports every row below (`day is out of range for
//! month`, `month must be in 1..12`, `year 0 is out of range`).
//!
//! The directive is kept and the key gets no value, as for an expression with
//! no value (`kk: 1/0`, #2814): the error is reported, nothing cascades. A
//! `pushmeta` with an invalid date pushes nothing, as in beancount, so its
//! `popmeta` reports the absent key.

use rustledger_core::{Directive, MetaValue};
use rustledger_parser::{ParseErrorKind, parse};

const OPENS: &str = "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n";

/// The one `InvalidDateValue` error `src` must give, over `date`, with the
/// directives kept.
fn assert_invalid_date(label: &str, src: &str, date: &str, message: &str, directives: usize) {
    let result = parse(src);
    let date_errors: Vec<_> = result
        .errors
        .iter()
        .filter(|e| matches!(e.kind, ParseErrorKind::InvalidDateValue(_)))
        .collect();
    assert_eq!(date_errors.len(), 1, "{label}: {:?}", result.errors);
    let err = date_errors[0];
    assert_eq!(&src[err.span.start..err.span.end], date, "{label}");
    assert!(
        err.to_string().contains(message),
        "{label}: {err} does not contain {message:?}"
    );
    assert_eq!(
        result.directives.len(),
        directives,
        "{label}: directive kept"
    );
}

#[test]
fn test_parse_reports_an_invalid_date_in_metadata() {
    for (label, body, date, message) in [
        (
            "directive metadata",
            "2024-01-02 open Assets:C\n  kk: 2024-02-30\n",
            "2024-02-30",
            "day 30 out of range for 2024-02",
        ),
        (
            "transaction metadata",
            "2024-01-02 * \"x\"\n  kk: 2024-13-01\n  Assets:A  1 USD\n  Assets:B\n",
            "2024-13-01",
            "month 13 out of range",
        ),
        (
            "posting metadata",
            "2024-01-02 * \"x\"\n  Assets:A  1 USD\n    kk: 2023-02-29\n  Assets:B\n",
            "2023-02-29",
            "day 29 out of range for 2023-02",
        ),
        (
            "month 0",
            "2024-01-02 open Assets:C\n  kk: 2024-00-01\n",
            "2024-00-01",
            "month 0 out of range",
        ),
        (
            "day 0",
            "2024-01-02 open Assets:C\n  kk: 2024-01-00\n",
            "2024-01-00",
            "day 0 out of range",
        ),
        (
            "one-digit day 0",
            "2024-01-02 open Assets:C\n  kk: 2024-02-0\n",
            "2024-02-0",
            "day 0 out of range",
        ),
        (
            "year 0",
            "2024-01-02 open Assets:C\n  kk: 0000-01-01\n",
            "0000-01-01",
            "year 0 out of range",
        ),
        (
            "event metadata",
            "2024-01-02 event \"e\" \"v\"\n  kk: 2024-02-30\n",
            "2024-02-30",
            "day 30 out of range",
        ),
    ] {
        let directives = OPENS.lines().count() + 1;
        assert_invalid_date(label, &format!("{OPENS}{body}"), date, message, directives);
    }
}

/// The key is kept with no value, as `kk: 1/0` is, not as a date.
#[test]
fn test_parse_keeps_the_key_of_an_invalid_metadata_date_with_no_value() {
    let result = parse("2024-01-02 open Assets:C\n  kk: 2024-02-30\n  jj: 2024-02-29\n");
    let Directive::Open(open) = &result.directives[0].value else {
        panic!("expected an open: {:?}", result.directives);
    };
    assert_eq!(open.meta.get("kk"), Some(&MetaValue::None));
    assert!(matches!(open.meta.get("jj"), Some(MetaValue::Date(_))));
}

#[test]
fn test_parse_reports_an_invalid_date_in_a_custom_value() {
    for (label, src) in [
        ("only value", "2024-01-02 custom \"x\" 2024-02-30\n"),
        (
            "among values",
            "2024-01-02 custom \"x\" \"a\" 2024-02-30 10 USD\n",
        ),
    ] {
        assert_invalid_date(label, src, "2024-02-30", "day 30 out of range", 1);
    }
}

#[test]
fn test_parse_reports_an_invalid_pushmeta_date_and_pushes_nothing() {
    let src = format!(
        "{OPENS}pushmeta kk: 2024-02-30\n2024-01-02 * \"x\"\n  Assets:A  1 USD\n  Assets:B\npopmeta kk:\n"
    );
    let result = parse(&src);
    assert!(
        matches!(result.errors[0].kind, ParseErrorKind::InvalidDateValue(_)),
        "{:?}",
        result.errors
    );
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(&e.kind, ParseErrorKind::InvalidPopmeta(k) if k == "kk")),
        "{:?}",
        result.errors
    );
    let txn = result
        .directives
        .iter()
        .find_map(|d| match &d.value {
            Directive::Transaction(t) => Some(t),
            _ => None,
        })
        .expect("the transaction is kept");
    assert_eq!(txn.meta.get("kk"), None);
}

/// A header date of year 0 is refused too, as beancount refuses it.
#[test]
fn test_parse_reports_a_year_zero_header_date() {
    let result = parse("0000-01-01 open Assets:A\n");
    assert!(
        result.errors.iter().any(|e| matches!(
            &e.kind,
            ParseErrorKind::InvalidDateValue(m) if m.contains("year 0 out of range")
        )),
        "{:?}",
        result.errors
    );
}

/// A date with extra digits is one date, as beancount reads its `DATE` token
/// (`[0-9]{4,}[-/][0-9]+[-/][0-9]+`, the fields read as integers): `2024-02-002`
/// is 2024-02-02, a value with no error, where our lexer used to split it
/// (#2808).
#[test]
fn test_parse_reads_a_long_form_value_date_as_beancount_does() {
    let want = rustledger_core::naive_date(2024, 2, 2).expect("a date");
    for value in ["2024-02-002", "2024-002-02", "02024-02-02", "2024/002/002"] {
        let src = format!("2024-01-02 open Assets:C\n  kk: {value}\n");
        let result = parse(&src);
        assert!(result.errors.is_empty(), "{src:?}: {:?}", result.errors);
        let Directive::Open(open) = &result.directives[0].value else {
            panic!("{src:?}: an open");
        };
        assert_eq!(
            open.meta.as_map().get("kk"),
            Some(&MetaValue::Date(want)),
            "{src:?}"
        );
        let src = format!("2024-01-02 custom \"x\" {value}\n");
        let result = parse(&src);
        assert!(result.errors.is_empty(), "{src:?}: {:?}", result.errors);
        let Directive::Custom(custom) = &result.directives[0].value else {
            panic!("{src:?}: a custom");
        };
        assert_eq!(custom.values, vec![MetaValue::Date(want)], "{src:?}");
        let src = format!("pushmeta kk: {value}\npopmeta kk:\n");
        assert!(parse(&src).errors.is_empty(), "{src:?}");
    }
    // Past 9999 the year is out of range, in beancount and here.
    let result = parse("2024-01-02 open Assets:C\n  kk: 20024-02-02\n");
    assert_eq!(result.errors.len(), 1, "{:?}", result.errors);
    assert!(
        result.errors[0]
            .to_string()
            .contains("year 20024 out of range"),
        "{}",
        result.errors[0]
    );
}

/// beancount names a bad date wherever it stands, since it builds the date
/// while lexing, and that error stands for the line (#2856): no grammar error
/// on top, two bad dates on one line are two errors, and the bad dates under a
/// directive with a bad date of its own are reported too. Every count below is
/// bean-check 3.2.3's on the same input.
#[test]
fn test_parse_names_an_invalid_date_in_every_position_as_beancount_does() {
    for (label, body, errors) in [
        ("event value", "2024-01-02 event \"e\" 2024-02-30\n", 1),
        ("price amount", "2024-01-02 price HOOL 2024-02-30\n", 1),
        (
            "@ price",
            "2024-01-02 *\n  Assets:A  1 HOOL @ 2024-02-30\n  Assets:B\n",
            1,
        ),
        (
            "transaction header",
            "2024-01-02 * \"x\" 2024-02-30\n  Assets:A  1 USD\n  Assets:B\n",
            1,
        ),
        ("option", "option \"title\" 2024-02-30\n", 1),
        ("plugin", "plugin \"x\" 2024-02-30\n", 1),
        ("orphan metadata line", "  kk: 2024-02-30\n", 1),
        (
            "bad header date over a bad value date",
            "2024-02-30 open Assets:C\n  kk: 2024-02-31\n",
            2,
        ),
        (
            "bad header date and value date",
            "2024-02-30 custom \"x\" 2024-02-31\n",
            2,
        ),
        (
            "two bad dates in one custom",
            "2024-01-02 custom \"x\" 2024-02-30 2024-13-01\n",
            2,
        ),
    ] {
        let src = format!("{OPENS}{body}");
        let result = parse(&src);
        assert_eq!(result.errors.len(), errors, "{label}: {:?}", result.errors);
        assert!(
            result
                .errors
                .iter()
                .all(|e| matches!(e.kind, ParseErrorKind::InvalidDateValue(_))),
            "{label}: only date errors, {:?}",
            result.errors
        );
    }
    // A valid date where the grammar wants none is still a syntax error.
    let result = parse(&format!("{OPENS}2024-01-02 event \"e\" 2024-02-02\n"));
    assert_eq!(result.errors.len(), 1, "{:?}", result.errors);
    assert!(
        !matches!(result.errors[0].kind, ParseErrorKind::InvalidDateValue(_)),
        "{:?}",
        result.errors
    );
}

/// Valid dates stay values, including a leap day and the slash form.
#[test]
fn test_parse_keeps_valid_value_dates() {
    for src in [
        "2024-01-02 open Assets:C\n  kk: 2024-02-29\n",
        "2024-01-02 open Assets:C\n  kk: 2024/2/29\n",
        "2024-01-02 custom \"x\" 2024-02-29\n",
        "pushmeta kk: 0001-01-01\npopmeta kk:\n",
    ] {
        let result = parse(src);
        assert!(result.errors.is_empty(), "{src:?}: {:?}", result.errors);
    }
}

#[test]
fn test_parse_reports_an_invalid_cost_date() {
    let src = format!(
        "{OPENS}2024-01-02 * \"x\"\n  Assets:A  1 HOOL {{1 USD, 2024-02-30}}\n  Assets:B\n"
    );
    let directives = OPENS.lines().count() + 1;
    assert_invalid_date(
        "cost date",
        &src,
        "2024-02-30",
        "day 30 out of range",
        directives,
    );
}

/// A valid cost date is not reported as an invalid calendar date.
#[test]
fn test_parse_does_not_report_valid_cost_dates() {
    // Including one with extra digits, one date as in beancount (#2808).
    for date in ["2024-02-29", "2024-02-002"] {
        let src = format!(
            "{OPENS}2024-01-02 * \"x\"\n  Assets:A  1 HOOL {{1 USD, {date}}}\n  Assets:B\n"
        );
        let result = parse(&src);
        assert!(result.errors.is_empty(), "{date}: {:?}", result.errors);
    }
}

/// A bad date stands for its line's GRAMMAR errors, not its lexer errors:
/// beancount's lexer goes on past the date, so a character no token takes, or
/// a mid-file BOM, on the same line is reported too. Each count is bean-check
/// 3.2.3's (the date, then `Invalid token`).
#[test]
fn test_parse_keeps_lexer_errors_on_a_line_with_an_invalid_date() {
    for (label, body) in [
        ("custom", "2024-01-02 custom \"x\" 2024-02-30 `\n"),
        (
            "cost",
            "2024-01-02 * \"x\"\n  Assets:A  1 HOOL {10 USD, 2024-02-30} `\n  Assets:B\n",
        ),
        (
            "mid-file BOM",
            "2024-01-02 custom \"x\" 2024-02-30 \u{feff}\n",
        ),
    ] {
        let result = parse(&format!("{OPENS}{body}"));
        assert_eq!(result.errors.len(), 2, "{label}: {:?}", result.errors);
        assert!(
            matches!(result.errors[0].kind, ParseErrorKind::InvalidDateValue(_)),
            "{label}: {:?}",
            result.errors
        );
        assert!(
            !matches!(result.errors[1].kind, ParseErrorKind::InvalidDateValue(_)),
            "{label}: {:?}",
            result.errors
        );
    }
}

/// A field too long for any integer is named as written, not as a saturated
/// `u64` (`year 18446744073709551615 out of range`).
#[test]
fn test_parse_names_an_overlong_date_field_as_written() {
    let long = "99999999999999999999999";
    for (date, message) in [
        (format!("{long}-1-1"), format!("year {long} out of range")),
        (
            format!("2024-{long}-1"),
            format!("month {long} out of range"),
        ),
        (
            format!("2024-1-{long}"),
            format!("day {long} out of range for 2024-01"),
        ),
    ] {
        let src = format!("{OPENS}2024-01-02 custom \"x\" {date}\n");
        let directives = OPENS.lines().count() + 1;
        assert_invalid_date(&date, &src, &date, &message, directives);
    }
}

/// A date's digits are ASCII, as in beancount's `[0-9]`: a Unicode digit
/// (`𑄶`, `١`) ends the date, so no token here is a date, and bean-check 3.2.3
/// reports `Invalid token` rather than a bad date.
#[test]
fn test_parse_does_not_read_unicode_digits_as_a_date() {
    for value in ["6665/2\u{11136}3130-7", "2024-0\u{661}-01"] {
        let result = parse(&format!("{OPENS}2024-01-02 custom \"x\" {value}\n"));
        assert!(!result.errors.is_empty(), "{value}");
        assert!(
            !result
                .errors
                .iter()
                .any(|e| matches!(e.kind, ParseErrorKind::InvalidDateValue(_))),
            "{value}: {:?}",
            result.errors
        );
        assert_eq!(rustledger_parser::leading_date_len(value), None, "{value}");
    }
}

/// `parse_date` takes a date only if the parser would: one `DATE` token, so a
/// year of four or more ASCII digits. `24-01-15` and `1-1-1` are refused, as
/// in a header, where they would otherwise read as years 24 and 1.
#[test]
fn test_parse_date_takes_only_what_the_parser_reads_as_a_date() {
    let ymd = |y, m, d| rustledger_core::naive_date(y, m, d).unwrap();
    for (text, date) in [
        ("2024-01-15", ymd(2024, 1, 15)),
        ("2024/1/5", ymd(2024, 1, 5)),
        ("02024-001-015", ymd(2024, 1, 15)),
        ("0001-01-01", ymd(1, 1, 1)),
    ] {
        assert_eq!(rustledger_parser::parse_date(text), Ok(date), "{text}");
    }
    for text in [
        "24-01-15",
        "1-1-1",
        "2024-01-15 ",
        " 2024-01-15",
        "2024-01-15x",
        "2024-0\u{661}-01",
        "",
    ] {
        assert!(rustledger_parser::parse_date(text).is_err(), "{text:?}");
    }
    assert_eq!(
        rustledger_parser::parse_date("0000-01-01"),
        Err("year 0 out of range".to_string())
    );
    for header in ["24-01-15 open Assets:C\n", "1-1-1 open Assets:C\n"] {
        assert!(!parse(header).errors.is_empty(), "{header:?}");
    }
}

/// beancount's lexer takes an invalid character and the rest of its run of
/// non-blank characters as one invalid token, so a date inside that run is
/// never read and never named; after a blank it is. Counts are bean-check
/// 3.2.3's.
#[test]
fn test_parse_does_not_name_a_date_inside_an_invalid_token() {
    // `errors` is bean-check's count where rledger matches it; on `` `x2024-02-30 ``
    // rledger reports the `` ` `` and the rest of the run as two errors, as for
    // any such run, so only the date is pinned there.
    for (label, value, errors, dates) in [
        ("glued to the invalid character", "`2024-02-30", Some(1), 0),
        ("after more of the run", "`x2024-02-30", None, 0),
        ("after a blank", "` 2024-02-30", Some(2), 1),
    ] {
        let result = parse(&format!("{OPENS}2024-01-02 custom \"x\" {value}\n"));
        if let Some(errors) = errors {
            assert_eq!(result.errors.len(), errors, "{label}: {:?}", result.errors);
        }
        let named = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, ParseErrorKind::InvalidDateValue(_)))
            .count();
        assert_eq!(named, dates, "{label}: {:?}", result.errors);
    }
}

/// A grammar error BEFORE the bad date still stands: beancount's parser fails
/// at that earlier token before its lexer reaches the date, so it reports both
/// (bean-check 3.2.3: `syntax error, unexpected CURRENCY` / `unexpected
/// NUMBER, expecting STRING`, then `day is out of range for month`). Errors at
/// or after the date are still dropped.
///
/// Each row is checked after the directives directly, after a blank line and
/// after a comment line: a dropped directive's error span takes in the lines
/// before it, which once kept an error the date had caused. An indented line
/// after a blank or comment line is no directive's continuation, so beancount
/// fails at the indent (`unexpected INDENT`) and reports that too. Every
/// count, and every error's line, is bean-check 3.2.3's on the same input.
#[test]
fn test_parse_keeps_a_grammar_error_before_an_invalid_date() {
    const TXN: &str = "2024-01-02 * \"t\"\n  Assets:A  1 USD\n  Assets:B\n";
    // (label, in a transaction body, line, errors directly after, errors
    // after a blank or comment line)
    for (label, in_body, line, direct, after_gap) in [
        (
            "balance currency",
            false,
            "2024-01-02 balance Assets:A USD 2024-02-30",
            2,
            2,
        ),
        (
            "note number",
            false,
            "2024-01-02 note Assets:A 5 2024-02-30",
            2,
            2,
        ),
        ("open", false, "2024-01-02 open 2024-02-30", 1, 1),
        ("price", false, "2024-01-02 price 2024-02-30", 1, 1),
        (
            "custom paren",
            false,
            "2024-01-02 custom \"x\" 2024-02-30 (",
            1,
            1,
        ),
        ("close", false, "2024-01-02 close 2024-02-30", 1, 1),
        ("commodity", false, "2024-01-02 commodity 2024-02-30", 1, 1),
        (
            "pad source",
            false,
            "2024-01-02 pad Assets:A 2024-02-30",
            1,
            1,
        ),
        (
            "pad target",
            false,
            "2024-01-02 pad 2024-02-30 Assets:A",
            1,
            1,
        ),
        (
            "balance amount",
            false,
            "2024-01-02 balance Assets:A 2024-02-30",
            1,
            1,
        ),
        (
            "document",
            false,
            "2024-01-02 document Assets:A 2024-02-30",
            1,
            1,
        ),
        ("query", false, "2024-01-02 query \"q\" 2024-02-30", 1, 1),
        ("event", false, "2024-01-02 event \"e\" 2024-02-30", 1, 1),
        (
            "note string",
            false,
            "2024-01-02 note Assets:A 2024-02-30",
            1,
            1,
        ),
        (
            "orphan posting",
            false,
            "  Assets:A 5 USD USD 2024-02-30",
            2,
            2,
        ),
        ("orphan string", false, "  \"x\" 2024-02-30", 2, 2),
        ("orphan date first", false, "  2024-02-30 5", 1, 2),
        ("orphan metadata", false, "  kk: 2024-02-30", 1, 2),
        ("body number", true, "  5 2024-02-30", 2, 2),
        ("body string", true, "  \"x\" 2024-02-30", 2, 2),
        (
            "body posting",
            true,
            "  Assets:B 5 USD USD 2024-02-30",
            2,
            2,
        ),
        (
            "body posting date",
            true,
            "  Assets:B 5 USD 2024-02-30",
            1,
            1,
        ),
    ] {
        for (gap, errors) in [("", direct), ("\n", after_gap), ("; c\n", after_gap)] {
            // In a body the gap goes before the transaction: a blank line
            // inside one would end it.
            let txn = if in_body { TXN } else { "" };
            let src = format!("{OPENS}{gap}{txn}{line}\n");
            let result = parse(&src);
            let label = format!("{label} after {gap:?}");
            assert_eq!(result.errors.len(), errors, "{label}: {:?}", result.errors);
            let dates = result
                .errors
                .iter()
                .filter(|e| matches!(e.kind, ParseErrorKind::InvalidDateValue(_)))
                .count();
            assert_eq!(dates, 1, "{label}: {:?}", result.errors);
            // Every error is on the row's own line, as in bean-check: an
            // error placed on the blank or comment line before it is wrong
            // even when the count is right.
            let row = src.lines().count();
            assert_eq!(
                error_lines(&src, &result.errors),
                vec![row; errors],
                "{label}: {:?}",
                result.errors
            );
        }
    }
    // bean-check 3.2.3's error lines for a dropped directive after a comment
    // line, two after one blank line, and an indented line after each
    // directive that takes no metadata, `%` or `# ` comment or org-mode
    // heading, and none after a line inside a multi-line string.
    for (src, lines) in [
        (
            "2024-01-01 open Assets:A\n; c\n2024-01-02 balance Assets:A USD 2024-02-30\n",
            vec![3, 3],
        ),
        (
            "2024-01-01 open Assets:A\n\n2024-01-02 balance Assets:A USD 2024-02-30\n\
             2024-01-02 balance Assets:A USD 2024-02-30\n",
            vec![3, 3, 4, 4],
        ),
        ("option \"title\" \"x\"\n  2024-02-30 5\n", vec![2, 2]),
        ("include \"none.beancount\"\n  2024-02-30 5\n", vec![2, 2]),
        ("plugin \"x\"\n  2024-02-30 5\n", vec![2, 2]),
        ("* Heading\n  2024-02-30 5\n", vec![2, 2]),
        ("%note\n  2024-02-30 5\n", vec![2, 2]),
        ("# note\n  2024-02-30 5\n", vec![2, 2]),
        // A column-0 `*`, `%` or `#` with more on the line is a comment, but
        // not `#` starting a tag, which is a token like any other.
        (
            "2024-01-01 open Assets:A\n*\tx\n  2024-02-30 5\n",
            vec![3, 3],
        ),
        ("2024-01-01 open Assets:A\n%x\n  2024-02-30 5\n", vec![3, 3]),
        ("2024-01-01 open Assets:A\n;\n  2024-02-30 5\n", vec![3, 3]),
        (
            "2024-01-01 open Assets:A\n#note\n  2024-02-30 5\n",
            vec![2, 3],
        ),
        (
            "2024-01-01 open Assets:A\n#a.b\n  2024-02-30 5\n",
            vec![2, 3],
        ),
        // flex's `.` takes a `\r`, so `#\r` is a marker and one more
        // character: a comment.
        (
            "2024-01-01 open Assets:A\n#\r\n  2024-02-30 5\n",
            vec![3, 3],
        ),
        (
            "2024-01-01 open Assets:A\n%\r\n  2024-02-30 5\n",
            vec![3, 3],
        ),
        (
            "2024-01-01 open Assets:A\n*\r\n  2024-02-30 5\n",
            vec![3, 3],
        ),
        // A directive that takes no metadata but is already a syntax error is
        // no gap: beancount's recovery swallows the indented line.
        ("option \"a\" \"b\" \"c\"\n  2024-02-30 5\n", vec![1, 2]),
        ("plugin \"a\" \"b\" \"c\"\n  2024-02-30 5\n", vec![1, 2]),
        ("include \"a\" \"b\"\n  2024-02-30 5\n", vec![1, 2]),
        ("option \"title\" \"a\nb\" x\n  2024-02-30 5\n", vec![2, 3]),
        (
            "option \"title\" \"a\nb\" \"c\"\n  2024-02-30 5\n",
            vec![2, 3],
        ),
        ("include \"a\nb\" \"c\"\n  2024-02-30 5\n", vec![2, 3]),
        ("pushmeta kk: \"a\nb\" \"c\"\n  2024-02-30 5\n", vec![2, 3]),
        // A valid one still is.
        ("plugin \"a\nb\" \"c\"\n  2024-02-30 5\n", vec![3, 3]),
        // A multi-line string belongs to the line it starts on: after one in a
        // directive that takes no metadata, the indented line is no
        // continuation.
        ("option \"title\" \"a\nb\"\n  2024-02-30 5\n", vec![3, 3]),
        ("plugin \"a\nb\"\n  2024-02-30 5\n", vec![3, 3]),
        ("include \"a\nb\"\n  2024-02-30 5\n", vec![3, 3]),
        (
            "pushmeta kk: \"a\nb\"\n  2024-02-30 5\npopmeta kk:\n",
            vec![3, 3],
        ),
        (
            "2024-01-01 open Assets:A\n2024-01-02 * \"a\nb\"\n  2024-02-30 5\n",
            vec![4],
        ),
        ("pushtag #t\n  2024-02-30 5\npoptag #t\n", vec![2, 2]),
        ("pushtag #t\npoptag #t\n  2024-02-30 5\n", vec![3, 3]),
        (
            "pushmeta kk: \"v\"\n  2024-02-30 5\npopmeta kk:\n",
            vec![2, 2],
        ),
        (
            "pushmeta kk: \"v\"\npopmeta kk:\n  2024-02-30 5\n",
            vec![3, 3],
        ),
        // A line that starts inside a multi-line string is the string's text,
        // not a gap, whatever it starts with.
        (
            "2024-01-01 open Assets:A\n2024-01-02 * \"multi\n* line\"\n  2024-02-30 5\n",
            vec![4],
        ),
        (
            "2024-01-01 open Assets:A\n2024-01-02 * \"multi\n; x\"\n  2024-02-30 5\n",
            vec![4],
        ),
        (
            "2024-01-01 open Assets:A\n2024-01-02 * \"multi\noption x\"\n  2024-02-30 5\n",
            vec![4],
        ),
        (
            "2024-01-01 open Assets:A\n2024-01-02 custom \"a\" \"multi\npushtag y\"\n  2024-02-30 5\n",
            vec![4],
        ),
        ("  2024-02-30 5\n", vec![1, 1]),
        // An indented comment continues the directive above; it is no gap.
        ("2024-01-01 open Assets:A\n  ; c\n  2024-02-30 5\n", vec![3]),
    ] {
        let result = parse(src);
        assert_eq!(
            error_lines(src, &result.errors),
            lines,
            "{src:?}: {:?}",
            result.errors
        );
    }
    // A bare `#`, `%` or `*` line is a token to beancount, not a comment, so
    // it is no gap: no `unexpected INDENT` on the indented line after it,
    // only the date. (bean-check also reports the bare marker on its own
    // line; rledger, before this change as after, does not.)
    for marker in ["#", "%", "*"] {
        let src = format!("2024-01-01 open Assets:A\n{marker}\n  2024-02-30 5\n");
        let result = parse(&src);
        assert_eq!(
            error_lines(&src, &result.errors),
            vec![3],
            "{marker:?}: {:?}",
            result.errors
        );
    }
}

/// The 1-based line each error starts on, in order.
fn error_lines(src: &str, errors: &[rustledger_parser::ParseError]) -> Vec<usize> {
    let mut lines: Vec<usize> = errors
        .iter()
        .map(|e| src[..e.span.start].matches('\n').count() + 1)
        .collect();
    lines.sort_unstable();
    lines
}
