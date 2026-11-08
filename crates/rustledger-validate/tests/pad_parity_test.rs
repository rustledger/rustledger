//! Drift guard: the validator's inline padding agrees with
//! `rustledger_booking::process_pads`.
//!
//! The balance check pads its own booked inventories in its walk
//! (`validate_balance_late`), while the loader's balance view, BQL and the
//! reports read the padding transactions `process_pads` synthesizes. Both go
//! through `rustledger_booking::PadTracker`, the one pad rule, but each sums
//! its own inventories, which is where #2896 came from: `process_pads`
//! ignored an unopened target's postings, and the validator ignored an
//! unopened target's balance and let a zero difference or a superseded pad
//! leave a pad usable.
//!
//! So this compares the two end to end on exactly those shapes, each checked
//! against bean-check / bean-query 3.2.3:
//!
//! - the validator's balance failures on the ledger must be the failures of
//!   the same ledger with every `pad` replaced by the padding `process_pads`
//!   synthesizes (validated with no pads left, so nothing is padded inline),
//! - the pads the validator calls unused must be the ones `process_pads` does,
//! - and both must be what beancount reports.

mod common;

use common::validate;
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use rustledger_core::{Directive, NaiveDate};
use rustledger_validate::ErrorCode;

const HEAD: &str = "2024-01-01 open Equity:O\n2024-01-01 open Assets:B\n";

struct Shape {
    name: String,
    source: String,
    /// Padding beancount inserts into the target, in order.
    padding: Vec<Decimal>,
    /// Dates of beancount's `Balance failed` errors.
    failed: Vec<&'static str>,
    /// Dates of beancount's `Unused Pad entry` errors.
    unused: Vec<&'static str>,
}

fn shapes() -> Vec<Shape> {
    let txn = |n: i32| {
        format!(
            "2024-01-03 * \"t\"\n  Assets:A  {n} USD\n  Assets:B  {} USD\n",
            -n
        )
    };
    let later_open = "2024-02-01 open Assets:A\n";
    let open = "2024-01-01 open Assets:A\n";
    let mut out = Vec::new();
    for (opened, suffix) in [("", "never opened"), (later_open, "opened later")] {
        // bean-query: target 100, source -130.
        out.push(Shape {
            name: format!("unopened target's own postings, {suffix}"),
            source: format!(
                "{HEAD}{opened}2024-01-02 pad Assets:A Equity:O\n{}\
                 2024-01-05 balance Assets:A 100 USD\n",
                txn(-30)
            ),
            padding: vec![dec!(130)],
            failed: vec![],
            unused: vec![],
        });
        // Already satisfied: no padding, `Unused Pad entry`.
        out.push(Shape {
            name: format!("satisfied unopened target, {suffix}"),
            source: format!(
                "{HEAD}{opened}2024-01-02 pad Assets:A Equity:O\n{}\
                 2024-01-05 balance Assets:A 100 USD\n",
                txn(100)
            ),
            padding: vec![],
            failed: vec![],
            unused: vec!["2024-01-02"],
        });
        // A balance on an unopened target is compared: `Balance failed`.
        out.push(Shape {
            name: format!("balance on an unopened target, {suffix}"),
            source: format!(
                "{HEAD}{opened}{}2024-01-05 balance Assets:A 100 USD\n",
                txn(50)
            ),
            padding: vec![],
            failed: vec!["2024-01-05"],
            unused: vec![],
        });
        // A zero difference uses up the currency: `Unused Pad entry` and
        // `Balance failed` on the second balance, the target opened or not.
        let (target, state) = if opened.is_empty() {
            ("", "never opened")
        } else {
            (open, "opened")
        };
        out.push(Shape {
            name: format!("zero difference, target {state}"),
            source: format!(
                "{HEAD}{target}2024-01-02 pad Assets:A Equity:O\n\
                 2024-01-03 balance Assets:A 0 USD\n2024-01-05 balance Assets:A 10 USD\n"
            ),
            padding: vec![],
            failed: vec!["2024-01-05"],
            unused: vec!["2024-01-02"],
        });
    }
    // A superseded pad is never used again: `Unused Pad entry` on it and
    // `Balance failed` on the second balance.
    out.push(Shape {
        name: "superseded pad".into(),
        source: format!(
            "{HEAD}{open}2024-01-09 pad Assets:A Equity:O\n2024-01-10 pad Assets:A Equity:O\n\
             2024-01-11 balance Assets:A 100 USD\n2024-01-12 balance Assets:A 200 USD\n"
        ),
        padding: vec![dec!(100)],
        failed: vec!["2024-01-12"],
        unused: vec!["2024-01-09"],
    });
    // The ordinary case, as a control.
    out.push(Shape {
        name: "ordinary pad".into(),
        source: format!(
            "{HEAD}{open}2024-01-02 pad Assets:A Equity:O\n{}2024-01-05 balance Assets:A 100 USD\n\
             2024-01-06 balance Assets:A 100 USD\n",
            txn(-30)
        ),
        padding: vec![dec!(130)],
        failed: vec![],
        unused: vec![],
    });
    out
}

fn parse(source: &str) -> Vec<Directive> {
    let parsed = rustledger_parser::parse(source);
    assert!(parsed.errors.is_empty(), "{source:?}: {:?}", parsed.errors);
    parsed.directives.into_iter().map(|d| d.value).collect()
}

fn dates(of: impl IntoIterator<Item = NaiveDate>) -> Vec<String> {
    let mut out: Vec<String> = of.into_iter().map(|d| d.to_string()).collect();
    out.sort();
    out
}

/// The balance failures `errors` report, as `(date, message)`.
fn failures(errors: &[rustledger_validate::ValidationError]) -> Vec<(String, String)> {
    let mut out: Vec<_> = errors
        .iter()
        .filter(|e| e.code == ErrorCode::BalanceAssertionFailed)
        .map(|e| (e.date.to_string(), e.message.clone()))
        .collect();
    out.sort();
    out
}

#[test]
fn test_validator_padding_matches_process_pads_on_the_2896_shapes() {
    for shape in shapes() {
        let name = &shape.name;
        let directives = parse(&shape.source);

        // The canonical padding.
        let pads = rustledger_booking::process_pads(&directives);
        let padding: Vec<Decimal> = pads
            .padding_transactions
            .iter()
            .map(|t| {
                let target = &t.postings[0];
                assert_eq!(target.account.as_str(), "Assets:A", "{name}");
                target.amount().expect("padding has units").number
            })
            .collect();
        assert_eq!(padding, shape.padding, "{name}: process_pads vs beancount");
        let canonical_unused = dates(pads.errors.iter().map(|e| e.date));

        // The validator, padding inline.
        let errors = validate(&directives);
        let inline_failures = failures(&errors);
        let inline_unused = dates(
            errors
                .iter()
                .filter(|e| e.code == ErrorCode::PadWithoutBalance)
                .map(|e| e.date),
        );

        // The same ledger with the canonical padding written out and no pad
        // left to apply inline.
        let mut padded: Vec<Directive> = directives
            .iter()
            .filter(|d| !matches!(d, Directive::Pad(_)))
            .cloned()
            .collect();
        padded.extend(
            pads.padding_transactions
                .iter()
                .cloned()
                .map(Directive::Transaction),
        );
        let canonical_failures = failures(&validate(&padded));

        assert_eq!(
            inline_failures, canonical_failures,
            "{name}: the validator's padding disagrees with process_pads'"
        );
        assert_eq!(
            inline_unused, canonical_unused,
            "{name}: unused pads disagree between the validator and process_pads"
        );
        assert_eq!(
            inline_failures
                .iter()
                .map(|(d, _)| d.as_str())
                .collect::<Vec<_>>(),
            shape.failed,
            "{name}: balance failures vs beancount"
        );
        assert_eq!(
            inline_unused, shape.unused,
            "{name}: unused pads vs beancount"
        );
    }
}
