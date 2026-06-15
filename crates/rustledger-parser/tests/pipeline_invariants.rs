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

fn amount_str() -> impl Strategy<Value = String> {
    (
        -1_000_000i64..1_000_000,
        0u32..4,
        prop_oneof![Just("USD"), Just("EUR")],
    )
        .prop_map(|(n, scale, ccy)| format!("{} {}", Decimal::new(n, scale), ccy))
}

/// A posting line with a deliberately-random gap between account and
/// amount, so the formatter's alignment normalization is exercised.
fn posting_line() -> impl Strategy<Value = String> {
    (account(), amount_str(), 1usize..8)
        .prop_map(|(acct, amt, gap)| format!("  {}{}{}", acct, " ".repeat(gap), amt))
}

fn txn_block() -> impl Strategy<Value = String> {
    (
        2000i32..2100,
        1u32..13,
        1u32..=28,
        "[A-Za-z ]{0,12}",
        prop::collection::vec(posting_line(), 2..5),
    )
        .prop_map(|(y, m, d, payee, lines)| {
            format!("{y:04}-{m:02}-{d:02} * \"{payee}\"\n{}\n", lines.join("\n"))
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
