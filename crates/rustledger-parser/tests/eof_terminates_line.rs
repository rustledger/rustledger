//! A malformed FINAL line must be reported whether or not the file ends with a
//! newline (#1884).
//!
//! `rledger check` exited 0 on a ledger whose last line it had not understood,
//! purely because the file lacked a trailing `\n` — two files differing by one
//! `0a` byte gave opposite verdicts. Python beancount reports the same error
//! either way (its lexer treats EOF as a terminator), so this was a plain
//! compatibility defect, not a deliberate deviation.
//!
//! The error-recovery walkers flushed a pending line only on `NEWLINE` and had
//! no EOF flush, in BOTH the green and red conversion paths.

/// The reported case: garbage with and without the trailing newline agree.
#[test]
fn a_malformed_final_line_is_reported_without_a_trailing_newline() {
    for body in [
        "@@@ not beancount @@@",
        "2024-01-01 invalid directive",
        "2024-01-01 open Assets:Cash USD\n@@@ garbage @@@",
    ] {
        let without = rustledger_parser::parse(body);
        let with = rustledger_parser::parse(&format!("{body}\n"));
        assert!(
            !without.errors.is_empty(),
            "no diagnostic for {body:?} without a trailing newline — this is \
             the silent pass of #1884"
        );
        assert_eq!(
            without.errors.len(),
            with.errors.len(),
            "{body:?}: error count depends on the trailing newline"
        );
    }
}

/// A transaction body's last line is covered too, not just top level.
#[test]
fn a_malformed_final_body_line_is_reported_without_a_trailing_newline() {
    let body = "2024-01-01 * \"x\"\n  Assets:A  1 USD\n  @@@ junk";
    let without = rustledger_parser::parse(body);
    let with = rustledger_parser::parse(&format!("{body}\n"));
    assert!(!without.errors.is_empty(), "body junk went unreported");
    assert_eq!(without.errors.len(), with.errors.len());
}

/// A trailing org-mode section marker still yields its comment.
#[test]
fn a_final_section_marker_is_recorded_without_a_trailing_newline() {
    let without = rustledger_parser::parse("* Section");
    let with = rustledger_parser::parse("* Section\n");
    assert_eq!(without.comments.len(), 1, "section comment dropped at EOF");
    assert_eq!(without.comments.len(), with.comments.len());
}

/// The flush must not INVENT diagnostics: valid or empty tails stay clean.
///
/// The risk of "flush whatever is pending at EOF" is firing on a line that was
/// never a problem, which would be a far worse regression than the bug.
#[test]
fn the_eof_flush_does_not_invent_errors() {
    for body in [
        "",
        "   ",
        "\n\n",
        "; a trailing comment",
        "2024-01-01 open Assets:Cash USD",
        "2024-01-01 open Assets:Cash USD\n2024-01-02 close Assets:Cash",
        "option \"title\" \"x\"",
        "* Section",
    ] {
        let r = rustledger_parser::parse(body);
        assert!(
            r.errors.is_empty(),
            "{body:?} must parse clean, got {:?}",
            r.errors.iter().map(ToString::to_string).collect::<Vec<_>>()
        );
    }
}

/// Green and red must agree on unterminated input.
///
/// Green is gated by a differential oracle against red, and `parse_red_only`
/// is the hook that oracle uses. Fixing only green would have made the two
/// disagree on exactly the inputs this is about — the existing corpus contains
/// no unterminated case, so nothing would have caught it. Verified by
/// sabotage: removing either path's EOF flush fails this.
#[test]
fn green_and_red_agree_on_unterminated_input() {
    for body in [
        "@@@ garbage @@@",
        "* section header",
        "2024-01-01 open Assets:A USD\n@@@ junk",
        "2024-01-01 * \"x\"\n  Assets:A 1 USD\n  @@@ junk",
        "2024-01-01 open Assets:A USD",
        "; trailing comment",
        "",
        "   ",
        "\n\n@@@ x",
    ] {
        let green = rustledger_parser::parse(body);
        let red = rustledger_parser::cst::parse_red_only(body);
        assert_eq!(
            green.errors.len(),
            red.errors.len(),
            "{body:?}: green {} errors, red {} — the differential oracle's \
             invariant is broken",
            green.errors.len(),
            red.errors.len()
        );
        assert_eq!(
            green.comments.len(),
            red.comments.len(),
            "{body:?}: comment counts differ between green and red"
        );
        assert_eq!(
            green.directives.len(),
            red.directives.len(),
            "{body:?}: directive counts differ between green and red"
        );
    }
}

/// The newline makes no difference, on either path.
#[test]
fn the_trailing_newline_does_not_change_the_parse() {
    for body in [
        "@@@ garbage @@@",
        "* section header",
        "2024-01-01 open Assets:A USD\n@@@ junk",
        "2024-01-01 * \"x\"\n  Assets:A 1 USD\n  @@@ junk",
    ] {
        for parse in [
            rustledger_parser::parse as fn(&str) -> rustledger_parser::ParseResult,
            rustledger_parser::cst::parse_red_only,
        ] {
            let a = parse(body);
            let b = parse(&format!("{body}\n"));
            assert_eq!(
                (a.errors.len(), a.comments.len(), a.directives.len()),
                (b.errors.len(), b.comments.len(), b.directives.len()),
                "{body:?}: the trailing newline changed the parse"
            );
        }
    }
}
