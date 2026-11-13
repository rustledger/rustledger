//! End-to-end conformance for transaction headers beancount rejects (#2008).
//!
//! The unit tests in `cst::txn_header` pin the rule against synthetic token
//! streams. These pin it against the real lexer + parser on the actual
//! `parser-lima` fixtures the issue was filed from — `parser-lima` is a
//! beancount *parser conformance* corpus, so these files exist precisely to be
//! rejected.
//!
//! The fixture bodies are inlined rather than read from
//! `tests/compatibility/files/`: that corpus is downloaded by CI and is
//! gitignored, so a test that reads it would silently pass by skipping on any
//! machine that has not fetched it — the failure mode AGENTS.md calls out
//! under "Availability-gated tests must fail loudly somewhere".

use rustledger_parser::cst::parse_red_only;
use rustledger_parser::parse;

/// Every diagnostic the transaction-header rule can produce, so a test can
/// assert "this file is rejected by *this* rule" and not be satisfied by some
/// unrelated error that happens to be present.
fn header_errors(src: &str) -> Vec<String> {
    parse(src)
        .errors
        .iter()
        .map(std::string::ToString::to_string)
        .filter(|m| {
            m.contains("transaction description")
                || m.contains("after a tag or link")
                || m.contains("in transaction header")
        })
        .collect()
}

/// #2008 case 3 — `test-cases_Transactions.TagThenLink.beancount`.
///
/// beancount: `syntax error, unexpected STRING, expecting end of file or EOL
/// or TAG or LINK`. Its grammar is `txn_strings tags_links`, so a string may
/// not follow a tag.
#[test]
fn string_after_tag_is_rejected() {
    let src = "2014-04-20 * #trip \"Money from CC\" ^610fa7f17e7a\n\
               \x20 Expenses:Restaurant         100 USD\n\
               \x20 Assets:US:Cash             -100 USD\n";
    let errs = header_errors(src);
    assert_eq!(
        errs.len(),
        1,
        "expected exactly one header error, got {errs:?}"
    );
    assert!(
        errs[0].contains("after a tag or link"),
        "wrong diagnostic: {}",
        errs[0]
    );
    // The message must name the offending string, not just complain abstractly
    // — the whole point of #2008 is that the real defect was never named.
    assert!(
        errs[0].contains("Money from CC"),
        "diagnostic does not name the offending string: {}",
        errs[0]
    );
}

/// #2008 case 4 — `test-cases_SyntaxErrors.ErrorInTransactionLine.beancount`.
///
/// beancount rejects `A:*:B` at the lexer (`Invalid token: 'A:*:B'`). We reach
/// the same verdict structurally: `A` lexes as a one-character `CURRENCY`,
/// which is a valid flag *in the flag position* and junk after a string.
#[test]
fn junk_after_the_narration_is_rejected() {
    let src = "2013-05-01 open Assets:US:Cash\n\
               \n\
               2013-05-02 * \"Dinner\" A:*:B\n\
               \x20 Expenses:Restaurant               100 USD\n\
               \x20 Assets:US:Cash                   -100 USD\n";
    let errs = header_errors(src);
    assert_eq!(
        errs.len(),
        1,
        "expected exactly one header error, got {errs:?}"
    );
    assert!(
        errs[0].contains("in transaction header"),
        "wrong diagnostic: {}",
        errs[0]
    );
}

/// #2008 cases 6 and 7 — `ParserEntryTypes.TransactionThreeStrings` and
/// `Transactions.TooManyStrings`. beancount: `Too many strings on transaction
/// description`.
#[test]
fn three_header_strings_are_rejected() {
    for src in [
        "2013-05-18 * \"Mermaid Inn\" \"Nice dinner\" \"With Caroline\"\n\
         \x20 Expenses:Restaurant         100 USD\n\
         \x20 Assets:US:Cash             -100 USD\n",
        "2013-05-18 * \"A\" \"B\" \"C\"\n\
         \x20 Expenses:Restaurant         100 USD\n\
         \x20 Assets:US:Cash             -100 USD\n",
    ] {
        let errs = header_errors(src);
        assert_eq!(errs.len(), 1, "expected one header error, got {errs:?}");
        assert!(
            errs[0].contains("found 3"),
            "diagnostic should report the count: {}",
            errs[0]
        );
    }
}

/// #2905: beancount's `txn` (a flag or the `txn` keyword) is required after
/// the date, so a header that starts with a string has none. beancount:
/// `syntax error, unexpected STRING`, on the header line, with or without a
/// payee, tags or links. Both converters (green, and red alone) report it, and
/// both keep the transaction, as for every other header defect.
#[test]
fn a_header_with_no_flag_is_rejected() {
    let bodies = "\x20 Expenses:R  100 USD\n\x20 Assets:C   -100 USD\n";
    for header in [
        "2024-01-02 \"x\"",
        "2024-01-02 \"p\" \"x\"",
        "2024-01-02 \"x\" #t ^l",
        "2024-01-02 \"p\" \"x\" ^l #t ; note",
    ] {
        let src = format!("{header}\n{bodies}");
        for (name, result) in [("parse", parse(&src)), ("red", parse_red_only(&src))] {
            assert_eq!(
                result.errors.len(),
                1,
                "{name} {header:?}: expected one error, got {:?}",
                result.errors
            );
            let msg = result.errors[0].to_string();
            assert!(
                msg.contains("needs a flag"),
                "{name} {header:?}: wrong diagnostic: {msg}"
            );
            // Reported at the first string, the token beancount fails on.
            let first = header.find('"').unwrap();
            let end = first + 1 + header[first + 1..].find('"').unwrap() + 1;
            assert_eq!(
                (result.errors[0].span.start, result.errors[0].span.end),
                (first, end),
                "{name} {header:?}"
            );
            assert_eq!(result.directives.len(), 1, "{name} {header:?}");
        }
    }
}

/// #2905: beancount's grammar fails at the first string of a header with no
/// flag and discards the rest of the line, so a `|` (its deprecation warning
/// comes from the grammar) or a mid-line `#!` / `#+` after it is not reported
/// there: one error. With a flag, both are still reported. An invalid token
/// later on the line is its lexer's error, not the grammar's, so it is
/// reported all the same: `#+ y` is two errors there (#2928).
#[test]
fn nothing_after_a_missing_flag_is_reported_on_the_line() {
    let bodies = "\x20 Expenses:R  100 USD\n\x20 Assets:C   -100 USD\n";
    for header in [
        "2024-01-02 \"p\" | \"x\"",
        "2024-01-02 \"x\" #!",
        "2024-01-02 \"x\" #+ Y",
        // The first string spans two lines: the header line ends at the
        // NEWLINE token after it, not at the `\n` inside the string.
        "2024-01-02 \"a\nb\" #!",
    ] {
        let src = format!("{header}\n{bodies}");
        for (name, result) in [("parse", parse(&src)), ("red", parse_red_only(&src))] {
            assert_eq!(
                result.errors.len(),
                1,
                "{name} {header:?}: expected one error, got {:?}",
                result.errors
            );
            assert!(
                result.errors[0].to_string().contains("needs a flag"),
                "{name} {header:?}: {:?}",
                result.errors
            );
        }
    }
    // The invalid token after the `#+` (`y`, where `Y` lexes) is reported, as
    // beancount's lexer reports it after the grammar has given up.
    let src = format!("2024-01-02 \"x\" #+ y\n{bodies}");
    let y_at = src.find(" y\n").expect("the header has the token") + 1;
    for (name, result) in [("parse", parse(&src)), ("red", parse_red_only(&src))] {
        let errors = &result.errors;
        assert_eq!(errors.len(), 2, "{name}: {errors:?}");
        assert!(
            errors[0].to_string().contains("needs a flag"),
            "{name}: {errors:?}"
        );
        assert_eq!(
            (errors[1].span.start, errors[1].span.end),
            (y_at, y_at + 1),
            "{name}: {errors:?}"
        );
    }
    // Controls: with a flag the pipe warns and the `#!` is an error.
    for header in ["2024-01-02 * \"p\" | \"x\"", "2024-01-02 * \"x\" #!"] {
        let src = format!("{header}\n{bodies}");
        assert_eq!(parse(&src).errors.len(), 1, "{header:?}");
        assert!(
            !parse(&src).errors[0].to_string().contains("needs a flag"),
            "{header:?}"
        );
    }
}

/// #2905: a header whose first token after the date is a tag or a link has no
/// flag either. beancount: `syntax error, unexpected TAG` (or `LINK`), one
/// error, on the header line. Its postings belong to it, so they are not each
/// reported as stray indented lines, as they were.
#[test]
fn a_header_opening_with_a_tag_or_link_is_one_error() {
    let bodies = "\x20 Expenses:R  100 USD\n\x20 Assets:C   -100 USD\n";
    for (header, at) in [("2024-01-02 #t ^l", "#t"), ("2024-01-02 ^l \"y\"", "^l")] {
        let src = format!("{header}\n{bodies}");
        for (name, result) in [("parse", parse(&src)), ("red", parse_red_only(&src))] {
            assert_eq!(
                result.errors.len(),
                1,
                "{name} {header:?}: expected one error, got {:?}",
                result.errors
            );
            assert!(
                result.errors[0].to_string().contains("needs a flag"),
                "{name} {header:?}: {:?}",
                result.errors
            );
            let start = header.find(at).unwrap();
            assert_eq!(
                (result.errors[0].span.start, result.errors[0].span.end),
                (start, start + at.len()),
                "{name} {header:?}"
            );
        }
    }
}

/// #2905, from the review of #2903: `2024-01-02 "x" $` is two errors in
/// beancount, `syntax error, unexpected STRING` and `Invalid token: '$'`. The
/// missing flag comes first, so the invalid token after it does not hide it.
#[test]
fn a_header_with_no_flag_and_an_invalid_token_reports_both() {
    let src = "2024-01-02 \"x\" $\n\x20 Expenses:R  100 USD\n\x20 Assets:C   -100 USD\n";
    for (name, result) in [("parse", parse(src)), ("red", parse_red_only(src))] {
        let errs: Vec<String> = result.errors.iter().map(ToString::to_string).collect();
        assert_eq!(errs.len(), 2, "{name}: {errs:?}");
        assert!(errs[0].contains("needs a flag"), "{name}: {errs:?}");
        assert_eq!(
            result.errors[1].span.start,
            src.find('$').unwrap(),
            "{name}"
        );
    }
}

/// The rule must stay silent on everything beancount accepts. A sweep of the
/// 731-file compatibility corpus produced exactly the four diagnostics above
/// and nothing else; these are the shapes that sweep proves are safe, kept
/// here so they are checked without the corpus present.
#[test]
fn valid_headers_are_untouched() {
    let bodies = "\x20 Expenses:R  100 USD\n\x20 Assets:C   -100 USD\n";
    for header in [
        "2014-04-20 * \"payee\" \"narration\"",
        "2014-04-20 * \"narration only\"",
        "2014-04-20 *",
        "2014-04-20 txn \"n\"",
        "2014-04-20 ! \"pending\"",
        "2014-04-20 # \"hash flag\"",
        "2014-04-20 * \"p\" \"n\" #tag1 #tag2 ^link-a ^link-b",
        "2014-04-20 * #tag-only",
        "2014-04-20 * \"p\" \"n\" ; trailing comment",
        // A one-character CURRENCY is a real flag: this line is corpus
        // content (fava/tests_data_example.beancount).
        "2012-12-17 P \"Payee\" \"Narration\"",
        // Multi-byte payee/narration — the rule slices source text for its
        // message, so a non-boundary slice would panic here.
        "2014-04-20 * \"é payee\" \"münts narration\"",
        // Exactly two strings is the canonical form and the off-by-one that
        // would break every real ledger.
        "2014-04-20 * \"two\" \"strings\"",
    ] {
        let src = format!("{header}\n{bodies}");
        assert!(
            header_errors(&src).is_empty(),
            "valid header wrongly rejected: {header:?} -> {:?}",
            header_errors(&src)
        );
    }
}

/// The deprecated `|` payee/narration separator keeps its own recoverable
/// diagnostic and must not be re-reported as a header defect.
#[test]
fn deprecated_pipe_is_not_reported_twice() {
    let src = "2014-04-20 * \"payee\" | \"narration\"\n\
               \x20 Expenses:R  100 USD\n\
               \x20 Assets:C   -100 USD\n";
    assert!(
        header_errors(src).is_empty(),
        "pipe must keep its DeprecatedPipeSymbol diagnostic, not gain a header one"
    );
    let all: Vec<String> = parse(src)
        .errors
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    assert!(
        all.iter()
            .any(|m| m.contains("pipe") || m.contains("Pipe") || m.contains('|')),
        "expected the deprecated-pipe diagnostic, got {all:?}"
    );
}

/// Only one defect is reported per header: `A:*:B` lexes into five tokens that
/// would each trip the rule, and beancount reports one error per transaction.
#[test]
fn one_defect_per_header() {
    let src = "2013-05-02 * \"Dinner\" A:*:B\n\x20 Expenses:R  100 USD\n\x20 Assets:C -100 USD\n";
    assert_eq!(header_errors(src).len(), 1);
}

// ---- cost-spec component shape (#2008 cases 1 and 2) ----------------------

fn cost_errors(src: &str) -> Vec<String> {
    parse(src)
        .errors
        .iter()
        .map(std::string::ToString::to_string)
        .filter(|m| m.contains("cost spec") || m.contains("cost-spec component"))
        .collect()
}

/// #2008 case 1 — `test-cases_ParseLots.CostEmptyComponents.beancount`.
/// beancount: `syntax error, unexpected COMMA, expecting HASH or CAPITAL or
/// CURRENCY`.
#[test]
fn empty_cost_component_is_rejected() {
    let src = "2014-01-01 *\n\
               \x20 Assets:Invest:AAPL      10 AAPL {, 100.0 USD, , }\n\
               \x20 Assets:Invest:Cash  -19.90 USD\n";
    let errs = cost_errors(src);
    assert_eq!(errs.len(), 1, "expected one cost-spec error, got {errs:?}");
    assert!(errs[0].contains("empty cost-spec component"), "{}", errs[0]);
}

/// #2008 case 2 — `test-cases_ParseLots.CostWithSlashes.beancount`.
/// beancount: `syntax error, unexpected SLASH, expecting RCURL or COMMA`.
#[test]
fn junk_after_a_complete_cost_component_is_rejected() {
    let src = "2014-01-01 *\n\
               \x20 Assets:Invest:AAPL      1.1 AAPL {45.23 USD / 2015-07-16 / \"blabla\"}\n\
               \x20 Assets:Invest:Cash   -45.23 USD\n";
    let errs = cost_errors(src);
    assert_eq!(errs.len(), 1, "expected one cost-spec error, got {errs:?}");
    assert!(errs[0].contains("already complete"), "{}", errs[0]);
}

/// Cost specs that must stay clean. `{{...}}` is the one that matters: an
/// earlier draft omitted `}}` from the closer set and lit up 42 real
/// total-cost specs across the corpus.
#[test]
fn valid_cost_specs_are_untouched() {
    for spec in [
        "{}",
        "{100.00 USD}",
        "{100.00 USD, 2015-01-01}",
        "{100.00 USD, \"lot-label\"}",
        "{100.00 USD, 2015-01-01, \"lot\"}",
        "{{500.00 USD}}",
        "{{500.00 USD, 2015-01-01}}",
        "{# 500.00 USD}",
        // arithmetic: `/` and `*` are number_expr operators, not junk
        "{10.00 * 3 USD}",
        "{30.00 / 3 USD}",
        "{10.00 + 2 USD}",
        "{*}",
        // #2008 case 5 stays accepted here on purpose - it is a booker-level
        // currency-group judgment, not a shape defect.
        "{USD}",
        "{ # USD}",
    ] {
        let src = format!(
            "2014-01-01 *\n  Assets:I:AAPL  10 AAPL {spec}\n  Assets:I:Cash  -100.00 USD\n"
        );
        assert!(
            cost_errors(&src).is_empty(),
            "valid cost spec wrongly rejected: {spec} -> {:?}",
            cost_errors(&src)
        );
    }
}
