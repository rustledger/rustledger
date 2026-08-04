//! Regression tests for crashes found by the fuzzers.
//!
//! The parser must satisfy a no-panic invariant: for ANY UTF-8 input it may
//! return errors, but must never panic. Each test here pins a previously
//! crashing input from `cargo fuzz`.

/// `fuzz_parse` crash (char-boundary panic in `indented_directive_check`).
///
/// A top-level directive whose first content token starts inside a multi-byte
/// UTF-8 char made the indent check slice the source string at a byte index
/// that was not a char boundary — `stripped[..content_start]` in
/// `cst/convert.rs` panicked with "end byte index N is not a char boundary".
/// The parser must handle this gracefully.
#[test]
fn fuzz_parse_indented_directive_char_boundary_no_panic() {
    let data = include_bytes!("fuzz_regressions/crash_indented_directive_char_boundary.bin");
    // The fuzz target only parses valid UTF-8; this corpus entry is valid UTF-8.
    let input = std::str::from_utf8(data).expect("crash fixture is valid UTF-8");
    // Must not panic. We don't assert on the (error) result — only no panic.
    let _ = rustledger_parser::parse(input);
}

/// `fuzz_green_eq_red` divergence (#1713): green latched the first pre-hash
/// NUMBER *token* of a compound cost while red's `cost_compound_numbers`
/// retries past unparsable tokens until a parse SUCCEEDS — on garbage like
/// `{<unparsable> 2 # ...}` red recovered `per_unit: 2` while green produced
/// `per_unit: 0`. Green now carries both semantics: a retried tracker for the
/// compound path and the latched first-token tracker for the plain
/// `cs.number()` path.
#[test]
fn fuzz_green_eq_red_compound_cost_unparsable_number() {
    let data = include_bytes!("fuzz_regressions/diverge_compound_cost_unparsable_number.bin");
    let input = std::str::from_utf8(data).expect("divergence fixture is valid UTF-8");
    let green = rustledger_parser::parse(input);
    let red = rustledger_parser::cst::parse_red_only(input);
    assert_eq!(
        format!("{:?}", green.directives),
        format!("{:?}", red.directives),
        "green-wired parse must exactly match red-only parse"
    );
}

/// #1939: arithmetic inside a COST SPEC was truncated to its first operand.
///
/// The price path has always evaluated expressions; the cost path latched the
/// first `NUMBER` token and dropped the rest, so `{10.00 * 3 USD}` booked a
/// cost of `10.00`. That is a wrong cost basis, and because the weight follows
/// the cost it also produced a FALSE "does not balance" on a file beancount
/// accepts.
///
/// Asserted on the units the user can observe (the resolved cost number), not
/// on a substring of the debug output — a bare `contains("30.00")` would be
/// satisfied by the price, which is `20.00 * 2` and also renders `40.00`.
#[test]
fn cost_spec_arithmetic_is_evaluated() {
    let src = "2013-05-18 * \"t\"\n  Assets:A   2 HOOL {10.00 * 3 USD}\n  Assets:B  -60.00 USD\n";
    let parsed = rustledger_parser::parse(src);
    let mut seen = 0;
    for d in &parsed.directives {
        if let rustledger_core::Directive::Transaction(t) = &**d {
            for p in &t.postings {
                if let Some(cs) = &p.cost {
                    seen += 1;
                    // The typed accessor, not a Debug string: the value is the
                    // claim, and coupling to formatting makes the test fail for
                    // reasons that are not about cost bases.
                    assert_eq!(
                        cs.number
                            .as_ref()
                            .and_then(rustledger_core::CostNumber::per_unit),
                        Some(rust_decimal_macros::dec!(30.00)),
                        "cost spec arithmetic must be evaluated, not truncated",
                    );
                }
            }
        }
    }
    assert_eq!(seen, 1, "fixture must actually exercise one cost spec");
}

/// The same expression must evaluate identically on BOTH conversion paths.
///
/// Every historical cost-spec divergence (#1704, #1713, the `{*}` merge flag)
/// landed in a hand-mirrored copy of these semantics, so a fix that touches
/// cost-spec numbers is exactly the shape that drifts. This is cheap insurance
/// that the shared `cost_spec_from_tokens` really is shared.
#[test]
fn cost_spec_arithmetic_green_eq_red() {
    for src in [
        "2013-05-18 * \"t\"\n  Assets:A  2 HOOL {10.00 * 3 USD}\n  Assets:B  -60.00 USD\n",
        "2013-05-18 * \"t\"\n  Assets:A  2 HOOL {(1 + 2) * 5 USD}\n  Assets:B  -30.00 USD\n",
        "2013-05-18 * \"t\"\n  Assets:A  2 HOOL {10.00 USD, 2014-02-25}\n  Assets:B  -20.00 USD\n",
        "2013-05-18 * \"t\"\n  Assets:A  2 HOOL {3 # 2 * 10 USD}\n  Assets:B  -26.00 USD\n",
        // Malformed: must degrade the same way on both paths, not just fail
        // the same way by accident on one.
        "2013-05-18 * \"t\"\n  Assets:A  2 HOOL {10.00 * USD}\n  Assets:B  -20.00 USD\n",
        "2013-05-18 * \"t\"\n  Assets:A  2 HOOL {1 / 0 USD}\n  Assets:B  -20.00 USD\n",
    ] {
        let green = rustledger_parser::parse(src);
        let red = rustledger_parser::cst::parse_red_only(src);
        assert_eq!(
            format!("{:?}", green.directives),
            format!("{:?}", red.directives),
            "green and red must agree on cost-spec arithmetic for: {src}",
        );
    }
}

/// A NEGATIVE cost kept its sign only by accident before #1939, and did not.
///
/// This was NOT the bug being hunted — it surfaced as unexplained corpus
/// baseline drift on two `TotalsAndSigns` fixtures while fixing the arithmetic
/// truncation, and turned out to be the same root cause wearing a different
/// hat. `{-200.00 USD}` starts with a `MINUS`, which the token latch never
/// treated as part of the number, so the cost was booked as **+200.00**: the
/// sign of a cost basis, silently inverted. Routing it through the shared
/// evaluator (which handles unary minus) fixes it, and both fixtures now agree
/// with beancount exactly.
///
/// Kept as its own test because "arithmetic is evaluated" and "a leading sign
/// is part of the number" are different claims, and a future refactor could
/// easily satisfy one while breaking the other.
#[test]
fn negative_cost_keeps_its_sign() {
    use rust_decimal_macros::dec;
    use rustledger_core::CostNumber;

    // Matched structurally rather than via Debug strings. `Compound` carries
    // BOTH halves and neither `per_unit()` nor `total()` can express it (both
    // return None by design, since the effective per-unit is unknown until the
    // units are), so a typed accessor alone cannot state this claim.
    let parsed = rustledger_parser::parse(
        "2013-05-18 * \"t\"\n  Assets:A  -10 MSFT {-200.00 USD}\n  Assets:B  2000.00 USD\n",
    );
    let mut seen = 0;
    for d in &parsed.directives {
        if let rustledger_core::Directive::Transaction(t) = &**d {
            for p in &t.postings {
                if let Some(cs) = &p.cost {
                    seen += 1;
                    assert!(
                        matches!(cs.number, Some(CostNumber::PerUnit { value }) if value == dec!(-200.00)),
                        "a negative per-unit cost must keep its sign, got {:?}",
                        cs.number,
                    );
                }
            }
        }
    }
    assert_eq!(seen, 1, "fixture must exercise exactly one cost spec");

    let parsed = rustledger_parser::parse(
        "2013-05-18 * \"t\"\n  Assets:A  -10 MSFT {# -200.00 USD}\n  Assets:B  200.00 USD\n",
    );
    let mut seen = 0;
    for d in &parsed.directives {
        if let rustledger_core::Directive::Transaction(t) = &**d {
            for p in &t.postings {
                if let Some(cs) = &p.cost {
                    seen += 1;
                    assert!(
                        matches!(
                            cs.number,
                            Some(CostNumber::Compound { total, .. }) if total == dec!(-200.00)
                        ),
                        "a negative TOTAL cost must keep its sign, got {:?}",
                        cs.number,
                    );
                }
            }
        }
    }
    assert_eq!(seen, 1, "fixture must exercise exactly one cost spec");
}

/// #1944: the same truncation as #1939, in the two OTHER number-bearing
/// positions that never reached the shared evaluator.
///
/// Both were found by sweeping the eleven `parse_decimal_token` call sites
/// against the three evaluator entry points, after #1939 turned out to be an
/// instance of a class rather than a one-off.
#[test]
fn arithmetic_is_evaluated_in_metadata_and_tolerances() {
    // Metadata: silent. Any plugin or query reading `num` got a third of it.
    let meta_src = concat!(
        "2013-05-18 * \"t\"\n",
        "  num: 2 * 3\n",
        "  Assets:A   10.00 USD\n",
        "  Assets:B  -10.00 USD\n",
    );
    let parsed = rustledger_parser::parse(meta_src);
    let mut checked = false;
    for d in &parsed.directives {
        if let rustledger_core::Directive::Transaction(t) = &**d {
            assert_eq!(
                t.meta.get("num"),
                Some(&rustledger_core::MetaValue::Int(6)),
                "metadata arithmetic must be evaluated (beancount reports 6)",
            );
            checked = true;
        }
    }
    assert!(checked, "fixture must exercise a transaction");

    // Tolerance: worse than silent — it REJECTED a file beancount accepts,
    // and the E2002 message printed the truncated figure.
    let tol_src = concat!(
        "2013-01-01 open Assets:A\n",
        "2013-01-01 open Assets:B\n",
        "2013-05-18 * \"t\"\n",
        "  Assets:A   10.008 USD\n",
        "  Assets:B  -10.008 USD\n",
        "2014-01-01 balance Assets:A   10.00 ~ 0.005 * 2 USD\n",
    );
    let parsed = rustledger_parser::parse(tol_src);
    let mut seen = 0;
    for d in &parsed.directives {
        if let rustledger_core::Directive::Balance(b) = &**d {
            seen += 1;
            assert_eq!(
                b.tolerance,
                Some(rust_decimal_macros::dec!(0.010)),
                "tolerance arithmetic must be evaluated; 0.005 would reject a valid file",
            );
        }
    }
    assert_eq!(seen, 1, "fixture must exercise one balance directive");
}

/// Both new positions must agree across the green and red conversion paths,
/// for the same reason the cost-spec fix carries this guard.
#[test]
fn metadata_and_tolerance_arithmetic_green_eq_red() {
    for src in [
        "2013-05-18 * \"t\"\n  num: 2 * 3\n  Assets:A  1.00 USD\n  Assets:B  -1.00 USD\n",
        "2013-05-18 * \"t\"\n  num: -(5662.23 + 22.3)\n  Assets:A  1.00 USD\n  Assets:B  -1.00 USD\n",
        "2014-01-01 balance Assets:A  10.00 ~ 0.005 * 2 USD\n",
        "2014-01-01 balance Assets:A  10.00 ~ 0.005 USD\n",
        // Malformed: must degrade identically, not merely fail identically.
        "2013-05-18 * \"t\"\n  num: 2 * \n  Assets:A  1.00 USD\n  Assets:B  -1.00 USD\n",
        "2014-01-01 balance Assets:A  10.00 ~ 1 / 0 USD\n",
    ] {
        let green = rustledger_parser::parse(src);
        let red = rustledger_parser::cst::parse_red_only(src);
        assert_eq!(
            format!("{:?}", green.directives),
            format!("{:?}", red.directives),
            "green and red must agree for: {src}",
        );
    }
}
