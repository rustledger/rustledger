//! Drift guard: the validator's padding agrees with
//! `rustledger_booking::process_pads`.
//!
//! Both take their padding from one computation,
//! `rustledger_booking::plan_pads`: `process_pads` writes it out as the
//! padding transactions the loader's balance view, BQL and the reports read,
//! and the validator adds it to its own booked inventories as its walk
//! reaches each `pad`. What can still differ is the inventories each one
//! sums, and the two used to be separate implementations, which is where
//! #2896 came from: `process_pads` ignored an unopened target's postings, and
//! the validator ignored an unopened target's balance, let a zero difference
//! or a superseded pad leave a pad usable, and padded at the balance rather
//! than at the pad. Then #2901: a pad group counted other pads' padding,
//! a balance on a sub-account did not reach its parent's pad, a difference
//! within the balance's tolerance was padded, and padding a currency held at
//! cost was not reported.
//!
//! So this compares the two end to end on exactly those shapes, each checked
//! against bean-check / bean-query 3.2.3:
//!
//! - the validator's balance failures on the ledger must be the failures of
//!   the same ledger with every `pad` replaced by the padding `process_pads`
//!   synthesizes (validated with no pads left, so nothing is padded),
//! - the pads the validator calls unused must be the ones `process_pads` does,
//! - and both must be what beancount reports, the padding's accounts and
//!   amounts and its `Attempt to pad an entry with cost` errors included.

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
    /// Padding beancount inserts, in order: the padded account and the units.
    padding: Vec<(&'static str, Decimal)>,
    /// Dates of beancount's `Balance failed` errors.
    failed: Vec<&'static str>,
    /// Dates of beancount's `Unused Pad entry` errors.
    unused: Vec<&'static str>,
    /// How many `Attempt to pad an entry with cost` errors beancount reports.
    cost_errors: usize,
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
            padding: vec![("Assets:A", dec!(130))],
            failed: vec![],
            unused: vec![],
            cost_errors: 0,
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
            cost_errors: 0,
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
            cost_errors: 0,
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
            cost_errors: 0,
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
        padding: vec![("Assets:A", dec!(100))],
        failed: vec!["2024-01-12"],
        unused: vec!["2024-01-09"],
        cost_errors: 0,
    });
    // The padding is dated at the pad, so a balance on the source between
    // the pad and the balance it satisfies sees it (bean-check: clean).
    out.push(Shape {
        name: "balance on the source between the pad and its balance".into(),
        source: format!(
            "{HEAD}{open}2024-01-03 pad Assets:A Equity:O\n\
             2024-01-05 balance Equity:O -100 USD\n2024-01-10 balance Assets:A 100 USD\n"
        ),
        padding: vec![("Assets:A", dec!(100))],
        failed: vec![],
        unused: vec![],
        cost_errors: 0,
    });
    // A pad that padded USD is no contender for EUR after a later pad: each
    // balance uses the latest pad (bean-check: clean).
    out.push(Shape {
        name: "a later pad for another currency".into(),
        source: format!(
            "{HEAD}{open}2024-01-02 pad Assets:A Equity:O\n2024-01-03 balance Assets:A 100 USD\n\
             2024-01-04 pad Assets:A Equity:O\n2024-01-05 balance Assets:A 10 EUR\n\
             2024-01-06 balance Assets:A 50 USD\n"
        ),
        padding: vec![
            ("Assets:A", dec!(100)),
            ("Assets:A", dec!(10)),
            ("Assets:A", dec!(-50)),
        ],
        failed: vec![],
        unused: vec![],
        cost_errors: 0,
    });
    // The ordinary case, as a control.
    out.push(Shape {
        name: "ordinary pad".into(),
        source: format!(
            "{HEAD}{open}2024-01-02 pad Assets:A Equity:O\n{}2024-01-05 balance Assets:A 100 USD\n\
             2024-01-06 balance Assets:A 100 USD\n",
            txn(-30)
        ),
        padding: vec![("Assets:A", dec!(130))],
        failed: vec![],
        unused: vec![],
        cost_errors: 0,
    });
    out
}

/// The #2901 shapes, each a whole ledger, with what bean-check / bean-query
/// 3.2.3 report for it.
fn shapes_2901() -> Vec<Shape> {
    let opens = |accounts: &[&str]| -> String {
        accounts.iter().fold(String::new(), |mut out, a| {
            out.push_str("2024-01-01 open ");
            out.push_str(a);
            out.push('\n');
            out
        })
    };
    let shape = |name: &str,
                 source: String,
                 padding: Vec<(&'static str, Decimal)>,
                 failed: Vec<&'static str>,
                 unused: Vec<&'static str>,
                 cost_errors: usize| Shape {
        name: name.into(),
        source,
        padding,
        failed,
        unused,
        cost_errors,
    };
    let buy = |lots: &str| format!("2024-01-02 * \"buy\"\n{lots}  Assets:Cash  -100 USD\n");
    vec![
        // A pad on a sub-account, a balance on its parent between the pad and
        // the sub-account's balance: the padding, dated at the pad, reaches
        // the parent (clean).
        shape(
            "pad on a sub-account, balance on the parent in between",
            format!(
                "{}2024-01-03 pad Assets:A:Sub Equity:O\n2024-01-05 balance Assets:A 100 USD\n\
                 2024-01-10 balance Assets:A:Sub 100 USD\n",
                opens(&["Assets:A", "Assets:A:Sub", "Equity:O"])
            ),
            vec![("Assets:A:Sub", dec!(100))],
            vec![],
            vec![],
            0,
        ),
        // A pad on the parent, a balance on its sub-account: the parent is
        // padded to the sub-account's amount, measured over the parent and
        // all its sub-accounts (100 - 30), and the currency is used up, so the
        // parent's own balance is compared: both balances fail.
        shape(
            "pad on the parent, balance on a sub-account",
            format!(
                "{}2024-01-02 * \"x\"\n  Assets:A:Other  30 USD\n  Equity:O  -30 USD\n\
                 2024-01-03 pad Assets:A Equity:O\n2024-01-10 balance Assets:A:Sub 100 USD\n\
                 2024-01-15 balance Assets:A 200 USD\n",
                opens(&["Assets:A", "Assets:A:Sub", "Assets:A:Other", "Equity:O"])
            ),
            vec![("Assets:A", dec!(70))],
            vec!["2024-01-10", "2024-01-15"],
            vec![],
            0,
        ),
        // A balance on a sub-account that already holds uses up the parent's
        // pad: `Unused Pad entry`, and the parent's balance fails.
        shape(
            "a held sub-account balance uses up the parent's pad",
            format!(
                "{}2024-01-02 * \"x\"\n  Assets:A:B  30 USD\n  Equity:O  -30 USD\n\
                 2024-01-03 pad Assets:A Equity:O\n2024-01-04 balance Assets:A:B 30 USD\n\
                 2024-01-05 balance Assets:A 100 USD\n",
                opens(&["Assets:A", "Assets:A:B", "Equity:O"])
            ),
            vec![],
            vec!["2024-01-05"],
            vec!["2024-01-03"],
            0,
        ),
        // Pads on a parent and on its sub-account: each pad group counts its
        // own padding only, so both pad 40 and the parent's balance fails.
        shape(
            "pads on a parent and its sub-account",
            format!(
                "{}2024-01-03 pad Assets:A Equity:O\n2024-01-03 pad Assets:A:Sub Equity:O\n\
                 2024-01-10 balance Assets:A:Sub 40 USD\n2024-01-10 balance Assets:A 100 USD\n",
                opens(&["Assets:A", "Assets:A:Sub", "Equity:O"])
            ),
            vec![("Assets:A", dec!(40)), ("Assets:A:Sub", dec!(40))],
            vec!["2024-01-10"],
            vec![],
            0,
        ),
        // A sub-account's padding is not part of its parent's pad group:
        // the parent pads its full 150, and its balance sees 250.
        shape(
            "a sub-account's padding, then a pad on the parent",
            format!(
                "{}2024-01-02 pad Assets:A:B Equity:O\n2024-01-03 balance Assets:A:B 100 USD\n\
                 2024-01-04 pad Assets:A Equity:O\n2024-01-05 balance Assets:A 150 USD\n",
                opens(&["Assets:A", "Assets:A:B", "Equity:O"])
            ),
            vec![("Assets:A:B", dec!(100)), ("Assets:A", dec!(150))],
            vec!["2024-01-05"],
            vec![],
            0,
        ),
        // Padding taken out of an account as a pad source is not part of
        // that account's own pad group: its pad sees 0, held, and is unused,
        // and its balance fails at -100.
        shape(
            "a pad source's padding, then a pad on the source",
            format!(
                "{}2024-01-02 pad Assets:A Assets:B\n2024-01-03 balance Assets:A 100 USD\n\
                 2024-01-04 pad Assets:B Equity:O\n2024-01-05 balance Assets:B 0 USD\n",
                opens(&["Assets:A", "Assets:B", "Equity:O"])
            ),
            vec![("Assets:A", dec!(100))],
            vec!["2024-01-05"],
            vec!["2024-01-04"],
            0,
        ),
        // Padding a currency held at cost: the padding is inserted, and the
        // error is reported once per lot held at cost.
        shape(
            "padding a currency held at cost",
            format!(
                "{}{}2024-01-03 pad Assets:Inv Equity:O\n2024-01-10 balance Assets:Inv 15 STK\n",
                opens(&["Assets:Inv", "Assets:Cash", "Equity:O"]),
                buy("  Assets:Inv  10 STK {10 USD}\n")
            ),
            vec![("Assets:Inv", dec!(5))],
            vec![],
            vec![],
            1,
        ),
        shape(
            "padding a currency held at cost in two lots",
            format!(
                "{}{}2024-01-03 pad Assets:Inv Equity:O\n2024-01-10 balance Assets:Inv 15 STK\n\
                 2024-01-11 balance Assets:Inv 15 STK\n",
                opens(&["Assets:Inv", "Assets:Cash", "Equity:O"]),
                buy("  Assets:Inv  5 STK {10 USD}\n  Assets:Inv  5 STK {10 USD, \"b\"}\n")
            ),
            vec![("Assets:Inv", dec!(5))],
            vec![],
            vec![],
            2,
        ),
        // Held at cost and already balanced: nothing is padded, so nothing
        // is reported but the unused pad.
        shape(
            "a balanced currency held at cost",
            format!(
                "{}{}2024-01-03 pad Assets:Inv Equity:O\n2024-01-10 balance Assets:Inv 10 STK\n",
                opens(&["Assets:Inv", "Assets:Cash", "Equity:O"]),
                buy("  Assets:Inv  10 STK {10 USD}\n")
            ),
            vec![],
            vec![],
            vec!["2024-01-03"],
            0,
        ),
        // A difference within the balance's inferred tolerance (0.005 for
        // `100.00`) is not padded: `Unused Pad entry`, and the currency is
        // used up, so the account keeps its 100.004.
        shape(
            "a difference within the inferred tolerance",
            format!(
                "{}2024-01-02 * \"x\"\n  Assets:A  100.004 USD\n  Equity:O  -100.004 USD\n\
                 2024-01-03 pad Assets:A Equity:O\n2024-01-10 balance Assets:A 100.00 USD\n\
                 2024-01-15 balance Assets:A 100.004 USD\n",
                opens(&["Assets:A", "Equity:O"])
            ),
            vec![],
            vec![],
            vec!["2024-01-03"],
            0,
        ),
        // Within an explicit tolerance: not padded, and the later exact
        // balance fails on the 99.5 the account still holds.
        shape(
            "a difference within an explicit tolerance",
            format!(
                "{}2024-01-02 * \"x\"\n  Assets:A  99.5 USD\n  Equity:O  -99.5 USD\n\
                 2024-01-03 pad Assets:A Equity:O\n2024-01-10 balance Assets:A 100 ~ 1 USD\n\
                 2024-01-15 balance Assets:A 100 USD\n",
                opens(&["Assets:A", "Equity:O"])
            ),
            vec![],
            vec!["2024-01-15"],
            vec!["2024-01-03"],
            0,
        ),
    ]
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
fn test_validator_padding_matches_process_pads_and_beancount() {
    for shape in shapes().into_iter().chain(shapes_2901()) {
        let name = &shape.name;
        let directives = parse(&shape.source);

        // The canonical padding.
        let pads = rustledger_booking::process_pads(
            &directives,
            rustledger_booking::DEFAULT_TOLERANCE_MULTIPLIER,
        );
        let padding: Vec<(&str, Decimal)> = pads
            .padding_transactions
            .iter()
            .map(|t| {
                let target = &t.postings[0];
                (
                    target.account.as_str(),
                    target.amount().expect("padding has units").number,
                )
            })
            .collect();
        assert_eq!(padding, shape.padding, "{name}: process_pads vs beancount");
        let canonical_unused = dates(
            pads.errors
                .iter()
                .filter(|e| e.message.contains("has no corresponding balance assertion"))
                .map(|e| e.date),
        );

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
        let cost_errors: Vec<_> = errors
            .iter()
            .filter(|e| e.code == ErrorCode::PadWithCost)
            .collect();
        assert_eq!(
            cost_errors.len(),
            shape.cost_errors,
            "{name}: `Attempt to pad an entry with cost` errors vs beancount: {cost_errors:?}"
        );
    }
}
