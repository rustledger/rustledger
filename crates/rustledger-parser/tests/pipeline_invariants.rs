//! Pipeline-boundary property test for parse/format (#1235).
//!
//! The canonical-form contract: `format_source` is a fixed point
//! (`format(format(x)) == format(x)`) and its output always re-parses
//! cleanly. This is the proptest complement to the corpus-based fixtures
//! in `format_compat.rs` — random amounts, accounts of differing length
//! (drawn from a fixed set), payees, and (deliberately non-canonical)
//! inner spacing exercise the alignment / normalization paths far more
//! widely than fixed cases. A formatter that
//! emits text the parser rejects (e.g. a `format_posting` drift) or that
//! isn't idempotent fails here.

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_parser::format::format_source;
use rustledger_parser::parse;

fn account() -> impl Strategy<Value = &'static str> {
    prop_oneof![
        Just("Assets:Bank"),
        Just("Expenses:Food:Groceries"),
        Just("Income:Salary"),
        Just("Liabilities:Card"),
    ]
}

fn currency() -> impl Strategy<Value = &'static str> {
    prop_oneof![Just("USD"), Just("EUR")]
}

fn amount_str() -> impl Strategy<Value = String> {
    prop_oneof![
        // Plain number, scales 0..4.
        (-1_000_000i64..1_000_000, 0u32..4, currency()).prop_map(|(n, scale, ccy)| format!(
            "{} {}",
            Decimal::new(n, scale),
            ccy
        )),
        // Thousands-separated literals, so the formatter's comma-stripping
        // normalization is exercised (and asserted not to change the value).
        (
            prop_oneof![
                Just("1,234.56"),
                Just("12,345.00"),
                Just("1,000"),
                Just("9,999.99")
            ],
            currency()
        )
            .prop_map(|(num, ccy)| format!("{num} {ccy}")),
    ]
}

/// A posting line — plain, cost-bearing (`{N CCY}`), or priced (`@ N CCY`) —
/// with a deliberately-random gap so the formatter's alignment and
/// cost/price normalization are exercised.
fn posting_line() -> impl Strategy<Value = String> {
    prop_oneof![
        (account(), amount_str(), 1usize..8).prop_map(|(acct, amt, gap)| format!(
            "  {}{}{}",
            acct,
            " ".repeat(gap),
            amt
        )),
        (account(), "1[0-9]{0,3} HOOL", amount_str())
            .prop_map(|(acct, units, cost)| format!("  {acct}  {units} {{{cost}}}")),
        (account(), "1[0-9]{0,3} HOOL", amount_str())
            .prop_map(|(acct, units, price)| format!("  {acct}  {units} @ {price}")),
    ]
}

/// Transaction header after the date: narration-only, or payee + narration
/// (two strings), so the formatter's payee handling is actually exercised.
fn header() -> impl Strategy<Value = String> {
    prop_oneof![
        "[A-Za-z ]{0,12}".prop_map(|n| format!("\"{n}\"")),
        ("[A-Za-z ]{1,10}", "[A-Za-z ]{0,12}").prop_map(|(p, n)| format!("\"{p}\" \"{n}\"")),
    ]
}

fn txn_block() -> impl Strategy<Value = String> {
    (
        2000i32..2100,
        1u32..13,
        1u32..=28,
        header(),
        prop::collection::vec(posting_line(), 2..5),
    )
        .prop_map(|(y, m, d, head, lines)| {
            format!("{y:04}-{m:02}-{d:02} * {head}\n{}\n", lines.join("\n"))
        })
}

fn source() -> impl Strategy<Value = String> {
    prop::collection::vec(txn_block(), 1..6).prop_map(|blocks| blocks.join("\n"))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn format_is_idempotent_and_preserves_ast(src in source()) {
        // The generator only emits well-formed ledgers; assert that so a
        // generator bug can't silently turn the content check below into a
        // comparison of error-recovery output.
        let original = parse(&src);
        prop_assert!(
            original.errors.is_empty(),
            "generator produced unparsable source: {:?}\n{}",
            original.errors,
            src
        );

        let once = format_source(&src);
        let twice = format_source(&once);
        prop_assert_eq!(&once, &twice, "format_source is not idempotent");

        let reparsed = parse(&once);
        prop_assert!(
            reparsed.errors.is_empty(),
            "formatted output failed to re-parse: {:?}",
            reparsed.errors
        );

        // The real round-trip contract: formatting changes layout, never
        // content. `Spanned`'s PartialEq compares values only (ignoring byte
        // offsets), so this asserts the parsed AST is unchanged — catching a
        // formatter drift (dropped/reordered posting, mangled amount, lost
        // payee) that still emits syntactically valid output and would slip
        // past the "re-parses cleanly" check above.
        prop_assert_eq!(
            reparsed.directives,
            original.directives,
            "formatting changed the parsed AST (content drift, not just layout)"
        );
    }
}
