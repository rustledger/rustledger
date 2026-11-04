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

/// A date beancount reads whole and our lexer splits (`2024-02-002`, #2808)
/// lexes as an invalid `2024-02-00` plus `2`: it keeps its one split-date
/// error, and is not reported a second time as an invalid date.
#[test]
fn test_parse_reports_a_split_date_once() {
    for src in [
        "2024-01-02 open Assets:C\n  kk: 2024-02-002\n",
        "2024-01-02 custom \"x\" 2024-02-002\n",
        "pushmeta kk: 2024-02-002\npopmeta kk:\n",
    ] {
        let result = parse(src);
        assert_eq!(result.errors.len(), 1, "{src:?}: {:?}", result.errors);
        assert!(
            !matches!(result.errors[0].kind, ParseErrorKind::InvalidDateValue(_)),
            "{src:?}: {:?}",
            result.errors
        );
    }
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

/// A valid cost date, and a split cost date, are not reported as invalid
/// calendar dates.
#[test]
fn test_parse_does_not_report_valid_or_split_cost_dates_as_invalid() {
    let ok = format!(
        "{OPENS}2024-01-02 * \"x\"\n  Assets:A  1 HOOL {{1 USD, 2024-02-29}}\n  Assets:B\n"
    );
    assert!(parse(&ok).errors.is_empty(), "{:?}", parse(&ok).errors);
    let split = format!(
        "{OPENS}2024-01-02 * \"x\"\n  Assets:A  1 HOOL {{1 USD, 2024-02-002}}\n  Assets:B\n"
    );
    let result = parse(&split);
    assert!(
        !result
            .errors
            .iter()
            .any(|e| matches!(e.kind, ParseErrorKind::InvalidDateValue(_))),
        "{:?}",
        result.errors
    );
}
