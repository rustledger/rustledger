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

use common::validate_with_options;
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use rustledger_core::{Directive, NaiveDate};
use rustledger_validate::{ErrorCode, ValidationOptions};

const DEFAULT: Decimal = rustledger_booking::DEFAULT_TOLERANCE_MULTIPLIER;

/// Two lots of the same cost, told apart by a label.
const LOTS_2: &str = "(5 STK {10 USD, 2024-01-02}, 5 STK {10 USD, 2024-01-02, \"b\"})";

/// The two lots of the first tie shape, in posting order.
const TIE_1: &str = "(10 STK {10 USD, 2024-01-02}, 10 STK {10 USD, 2024-01-03})";

/// A lot in `Assets:P:X`, then one transaction posting to `Assets:P:Y`
/// before `Assets:P:X`, a pad on the parent and its balance.
const RANK_BODY: &str = "2024-01-02 * \"lot\"\n  Assets:P:X  1 STK {10 USD}\n  Assets:Cash  -10 USD\n\
     2024-01-03 * \"g\"\n  Assets:P:Y  1 CCC\n  Assets:P:X  1 DDD\n  Equity:O  -1 CCC\n  Equity:O  -1 DDD\n\
     2024-01-04 pad Assets:P Equity:O\n2024-01-10 balance Assets:P 2 STK\n";

/// `Assets:A:C` opened before `Assets:A:D`, a lot in `Assets:A`, one
/// transaction posting to both, and a pad on the parent with its balance.
const REG_BASE: &str = "2024-01-01 open Assets:A\n2024-01-01 open Assets:A:C\n\
    2024-01-01 open Assets:A:D\n2024-01-01 open Assets:Z\n2024-01-01 open Assets:Cash\n\
    2024-01-01 open Equity:O\n2024-02-01 * \"lot\"\n  Assets:A  10 STK {10 USD}\n\
    \x20 Assets:Cash  -100 USD\n2024-02-02 * \"g\"\n  Assets:A:C  1 CCC\n  Assets:A:D  1 DDD\n\
    \x20 Equity:O  -1 CCC\n  Equity:O  -1 DDD\n2024-02-03 pad Assets:A Equity:O\n\
    2024-02-10 balance Assets:A 11 STK\n";

/// bean-check's message for [`REG_BASE`] with `Assets:A:C` met first.
const REG_C_FIRST: &str = "(1 CCC, 1 DDD, 10 STK {10 USD, 2024-02-01})";

/// The same with `Assets:A:D` met first.
const REG_D_FIRST: &str = "(1 DDD, 1 CCC, 10 STK {10 USD, 2024-02-01})";

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
    /// beancount's `Attempt to pad an entry with cost` errors, one per lot,
    /// word for word as bean-check prints them.
    cost_messages: Vec<&'static str>,
    /// The ledger's `tolerance_multiplier` option.
    tolerance_multiplier: Decimal,
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
            cost_messages: vec![],
            tolerance_multiplier: DEFAULT,
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
            cost_messages: vec![],
            tolerance_multiplier: DEFAULT,
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
            cost_messages: vec![],
            tolerance_multiplier: DEFAULT,
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
            cost_messages: vec![],
            tolerance_multiplier: DEFAULT,
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
        cost_messages: vec![],
        tolerance_multiplier: DEFAULT,
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
        cost_messages: vec![],
        tolerance_multiplier: DEFAULT,
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
        cost_messages: vec![],
        tolerance_multiplier: DEFAULT,
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
        cost_messages: vec![],
        tolerance_multiplier: DEFAULT,
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
                 cost_messages: Vec<&'static str>| Shape {
        name: name.into(),
        source,
        padding,
        failed,
        unused,
        cost_messages,
        tolerance_multiplier: DEFAULT,
    };
    let buy = |lots: &str| format!("2024-01-02 * \"buy\"\n{lots}  Assets:Cash  -100 USD\n");
    let mut out = vec![
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
            vec![],
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
            vec![],
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
            vec![],
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
            vec![],
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
            vec![],
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
            vec![],
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
            vec!["(10 STK {10 USD, 2024-01-02})"],
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
            vec![LOTS_2, LOTS_2],
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
            vec![],
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
            vec![],
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
            vec![],
        ),
        // The same lot held in two sub-accounts is one position: one error.
        shape(
            "the same lot in two sub-accounts",
            format!(
                "{}2024-01-02 * \"buy\"\n  Assets:A:B  10 STK {{10 USD}}\n  Assets:A:Sub  4 STK {{10 USD}}\n\
                 \x20 Assets:Cash  -140 USD\n2024-01-03 pad Assets:A Equity:O\n\
                 2024-01-10 balance Assets:A 20 STK\n",
                opens(&[
                    "Assets:A",
                    "Assets:A:B",
                    "Assets:A:Sub",
                    "Assets:Cash",
                    "Equity:O"
                ])
            ),
            vec![("Assets:A", dec!(6))],
            vec![],
            vec![],
            vec!["(14 STK {10 USD, 2024-01-02})"],
        ),
        // A lot held in a sub-account of the padded account.
        shape(
            "a lot held at cost in a sub-account",
            format!(
                "{}{}2024-01-03 pad Assets:A Equity:O\n2024-01-10 balance Assets:A 15 STK\n",
                opens(&["Assets:A", "Assets:A:B", "Assets:Cash", "Equity:O"]),
                buy("  Assets:A:B  10 STK {10 USD}\n")
            ),
            vec![("Assets:A", dec!(5))],
            vec![],
            vec![],
            vec!["(10 STK {10 USD, 2024-01-02})"],
        ),
        // Pads on a sub-account and then its parent, at cost: each group's
        // message shows what that group holds, not the other's padding.
        shape(
            "pads on a sub-account and its parent, at cost",
            format!(
                "{}{}2024-01-03 pad Assets:A:B Equity:O\n2024-01-04 balance Assets:A:B 12 STK\n\
                 2024-01-05 pad Assets:A Equity:O\n2024-01-10 balance Assets:A 15 STK\n",
                opens(&["Assets:A", "Assets:A:B", "Assets:Cash", "Equity:O"]),
                buy("  Assets:A:B  10 STK {10 USD}\n")
            ),
            vec![("Assets:A:B", dec!(2)), ("Assets:A", dec!(5))],
            vec!["2024-01-10"],
            vec![],
            vec![
                "(10 STK {10 USD, 2024-01-02})",
                "(10 STK {10 USD, 2024-01-02})",
            ],
        ),
        // The message lists the group's inventory as beancount sorts it:
        // USD first, then the rest, a position at cost after one without.
        shape(
            "the message sorts the inventory as beancount does",
            format!(
                "{}{}2024-01-02 * \"gift\"\n  Assets:A  5 STK\n  Assets:A  20 USD\n\
                 \x20 Equity:O  -5 STK\n  Equity:O  -20 USD\n\
                 2024-01-03 pad Assets:A Equity:O\n2024-01-10 balance Assets:A 20 STK\n",
                opens(&["Assets:A", "Assets:Cash", "Equity:O"]),
                buy("  Assets:A  10 STK {10 USD}\n")
            ),
            vec![("Assets:A", dec!(5))],
            vec![],
            vec![],
            vec!["(20 USD, 5 STK, 10 STK {10 USD, 2024-01-02})"],
        ),
        // Ties in beancount's sort key (`Position.sortkey` reads no currency
        // name and no lot date) keep the order the positions came in, as its
        // stable sort leaves them: lots, then plain positions, then both.
        shape(
            "tie: two lots of one cost, in posting order",
            format!(
                "{}2024-01-02 * \"z\"\n  Assets:A:Z  10 STK {{10 USD}}\n  Assets:Cash  -100 USD\n\
                 2024-01-03 * \"b\"\n  Assets:A:B  10 STK {{10 USD}}\n  Assets:Cash  -100 USD\n\
                 2024-01-04 pad Assets:A Equity:O\n2024-01-10 balance Assets:A 25 STK\n",
                opens(&[
                    "Assets:A",
                    "Assets:A:Z",
                    "Assets:A:B",
                    "Assets:Cash",
                    "Equity:O"
                ])
            ),
            vec![("Assets:A", dec!(5))],
            vec![],
            vec![],
            vec![TIE_1, TIE_1],
        ),
        shape(
            "tie: plain positions in posting order",
            format!(
                "{}2024-01-02 * \"g\"\n  Assets:A  5 XYZ\n  Assets:A  5 ABC\n  Assets:A  5 QQQ\n\
                 \x20 Assets:A  5 MMM\n  Equity:O  -5 XYZ\n  Equity:O  -5 ABC\n  Equity:O  -5 QQQ\n\
                 \x20 Equity:O  -5 MMM\n2024-01-03 * \"buy\"\n  Assets:A  10 STK {{10 USD}}\n\
                 \x20 Assets:Cash  -100 USD\n2024-01-04 pad Assets:A Equity:O\n\
                 2024-01-10 balance Assets:A 20 STK\n",
                opens(&["Assets:A", "Assets:Cash", "Equity:O"])
            ),
            vec![("Assets:A", dec!(10))],
            vec![],
            vec![],
            vec!["(5 XYZ, 5 ABC, 5 QQQ, 5 MMM, 10 STK {10 USD, 2024-01-03})"],
        ),
        shape(
            "tie: plain positions in the reverse posting order",
            format!(
                "{}2024-01-02 * \"g\"\n  Assets:A  5 MMM\n  Assets:A  5 QQQ\n  Assets:A  5 ABC\n\
                 \x20 Assets:A  5 XYZ\n  Equity:O  -5 MMM\n  Equity:O  -5 QQQ\n  Equity:O  -5 ABC\n\
                 \x20 Equity:O  -5 XYZ\n2024-01-03 * \"buy\"\n  Assets:A  10 STK {{10 USD}}\n\
                 \x20 Assets:Cash  -100 USD\n2024-01-04 pad Assets:A Equity:O\n\
                 2024-01-10 balance Assets:A 20 STK\n",
                opens(&["Assets:A", "Assets:Cash", "Equity:O"])
            ),
            vec![("Assets:A", dec!(10))],
            vec![],
            vec![],
            vec!["(5 MMM, 5 QQQ, 5 ABC, 5 XYZ, 10 STK {10 USD, 2024-01-03})"],
        ),
        shape(
            "tie: lots of several currencies in posting order",
            format!(
                "{}2024-01-02 * \"buy\"\n  Assets:A  1 BBB {{10 USD}}\n  Assets:A  1 AAA {{10 USD}}\n\
                 \x20 Assets:A  1 YYY {{10 USD}}\n  Assets:A  1 CCC {{10 USD}}\n\
                 \x20 Assets:Cash  -40 USD\n2024-01-04 pad Assets:A Equity:O\n\
                 2024-01-10 balance Assets:A 3 AAA\n",
                opens(&["Assets:A", "Assets:Cash", "Equity:O"])
            ),
            vec![("Assets:A", dec!(2))],
            vec![],
            vec![],
            vec![
                "(1 BBB {10 USD, 2024-01-02}, 1 AAA {10 USD, 2024-01-02}, \
                 1 YYY {10 USD, 2024-01-02}, 1 CCC {10 USD, 2024-01-02})",
            ],
        ),
        // One transaction's postings to several sub-accounts enter the
        // group in the order beancount first met each account (its
        // `postings_by_account` key order), not as written: it stable-sorts
        // the group's postings by date, type and line, which they share.
        shape(
            "rank: postings to sub-accounts in their open order",
            format!(
                "{}{RANK_BODY}",
                opens(&[
                    "Assets:P",
                    "Assets:Cash",
                    "Equity:O",
                    "Assets:P:X",
                    "Assets:P:Y"
                ])
            ),
            vec![("Assets:P", dec!(1))],
            vec![],
            vec![],
            vec!["(1 DDD, 1 CCC, 1 STK {10 USD, 2024-01-02})"],
        ),
        shape(
            "rank: the opens swapped",
            format!(
                "{}{RANK_BODY}",
                opens(&[
                    "Assets:P",
                    "Assets:Cash",
                    "Equity:O",
                    "Assets:P:Y",
                    "Assets:P:X"
                ])
            ),
            vec![("Assets:P", dec!(1))],
            vec![],
            vec![],
            vec!["(1 CCC, 1 DDD, 1 STK {10 USD, 2024-01-02})"],
        ),
        // Accounts with no `open` are met first through a posting, in the
        // order it writes them.
        shape(
            "rank: accounts first met through a posting",
            format!(
                "{}2024-01-02 * \"lot\"\n  Assets:P  1 STK {{10 USD}}\n  Assets:Cash  -10 USD\n\
                 2024-01-03 * \"g\"\n  Assets:P:Y  1 CCC\n  Assets:P:X  1 DDD\n  Equity:O  -1 CCC\n\
                 \x20 Equity:O  -1 DDD\n2024-01-04 * \"h\"\n  Assets:P:X  1 EEE\n  Assets:P:Y  1 FFF\n\
                 \x20 Equity:O  -1 EEE\n  Equity:O  -1 FFF\n2024-01-05 pad Assets:P Equity:O\n\
                 2024-01-10 balance Assets:P 2 STK\n",
                opens(&["Assets:P", "Assets:Cash", "Equity:O"])
            ),
            vec![("Assets:P", dec!(1))],
            vec![],
            vec![],
            vec!["(1 CCC, 1 DDD, 1 FFF, 1 EEE, 1 STK {10 USD, 2024-01-02})"],
        ),
        // A joined lot prints the cost it was last written with, as
        // beancount's `add_amount` rebuilds it with the incoming cost.
        shape(
            "a joined lot prints its latest cost",
            format!(
                "{}2024-01-02 * \"a\"\n  Assets:A  1 STK {{10 USD}}\n  Assets:Cash  -10 USD\n\
                 2024-01-02 * \"b\"\n  Assets:A  1 STK {{10.00 USD, 2024-01-02}}\n\
                 \x20 Assets:Cash  -10.00 USD\n2024-01-03 pad Assets:A Equity:O\n\
                 2024-01-10 balance Assets:A 3 STK\n",
                opens(&["Assets:A", "Assets:Cash", "Equity:O"])
            ),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec![],
            vec!["(2 STK {10.00 USD, 2024-01-02})"],
        ),
        // Every directive beancount's `realization.postings_by_account`
        // registers an account through ranks it, so one line dated before
        // the opens that names `Assets:A:D` puts its postings ahead of
        // `Assets:A:C`'s, whatever the opens say.
        shape(
            "registration: the opens alone",
            REG_BASE.to_string(),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec![],
            vec![REG_C_FIRST],
        ),
        shape(
            "registration: a note",
            format!("2023-12-31 note Assets:A:D \"n\"\n{REG_BASE}"),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec![],
            vec![REG_D_FIRST],
        ),
        shape(
            "registration: a document",
            format!("2023-12-31 document Assets:A:D \"/nonexistent/x.pdf\"\n{REG_BASE}"),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec![],
            vec![REG_D_FIRST],
        ),
        shape(
            "registration: a balance",
            format!("2023-12-31 balance Assets:A:D 0 DDD\n{REG_BASE}"),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec![],
            vec![REG_D_FIRST],
        ),
        shape(
            "registration: a pad's source",
            format!("2023-12-31 pad Assets:Z Assets:A:D\n{REG_BASE}"),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec!["2023-12-31"],
            vec![REG_D_FIRST],
        ),
        shape(
            "registration: a pad's account",
            format!("2023-12-31 pad Assets:A:D Equity:O\n{REG_BASE}"),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec!["2023-12-31"],
            vec![REG_D_FIRST],
        ),
        shape(
            "registration: a custom",
            format!("2023-12-31 custom \"x\" Assets:A:D\n{REG_BASE}"),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec![],
            vec![REG_D_FIRST],
        ),
        shape(
            "registration: a custom's account values in order",
            format!("2023-12-31 custom \"x\" \"s\" Assets:A:D 2 Assets:A:C\n{REG_BASE}"),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec![],
            vec![REG_D_FIRST],
        ),
        shape(
            "registration: a close",
            format!("2023-12-31 close Assets:A:D\n{REG_BASE}"),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec![],
            vec![REG_D_FIRST],
        ),
        shape(
            "registration: a posting",
            format!("2023-12-31 * \"e\"\n  Assets:A:D  1 EEEE\n  Equity:O  -1 EEEE\n{REG_BASE}"),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec![],
            vec!["(1 DDD, 1 CCC, 10 STK {10 USD, 2024-02-01}, 1 EEEE)"],
        ),
        // A same-date `pad` meets its accounts at its own line, as
        // beancount's entry order ranks it with the date's transactions,
        // notes and customs, not ahead of them as the booking order does.
        shape(
            "same date: a note before a pad",
            format!(
                "2023-12-31 note Assets:A:C \"n\"\n2023-12-31 pad Assets:Z Assets:A:D\n{REG_BASE}"
            ),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec!["2023-12-31"],
            vec![REG_C_FIRST],
        ),
        shape(
            "same date: a transaction before a pad",
            format!(
                "2023-12-31 * \"c\"\n  Assets:A:C  1 FFFF\n  Equity:O  -1 FFFF\n\
                 2023-12-31 pad Assets:Z Assets:A:D\n{REG_BASE}"
            ),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec!["2023-12-31"],
            vec!["(1 CCC, 1 DDD, 10 STK {10 USD, 2024-02-01}, 1 FFFF)"],
        ),
        shape(
            "same date: a custom before a pad",
            format!(
                "2023-12-31 custom \"x\" Assets:A:C\n2023-12-31 pad Assets:Z Assets:A:D\n{REG_BASE}"
            ),
            vec![("Assets:A", dec!(1))],
            vec![],
            vec!["2023-12-31"],
            vec![REG_C_FIRST],
        ),
        // A later balance just beyond the tolerance (0.016 against 0.01)
        // fails: pins the balance check's tolerance to the pad's.
        shape(
            "a later balance just beyond the tolerance",
            format!(
                "{}2024-01-02 * \"x\"\n  Assets:A  100.004 USD\n  Equity:O  -100.004 USD\n\
                 2024-01-03 pad Assets:A Equity:O\n2024-01-10 balance Assets:A 100.00 USD\n\
                 2024-01-15 balance Assets:A 100.02 USD\n",
                opens(&["Assets:A", "Equity:O"])
            ),
            vec![],
            vec!["2024-01-15"],
            vec!["2024-01-03"],
            vec![],
        ),
    ];
    // `option "tolerance_multiplier" "2"`: 99.97 against `balance 100.00` is
    // within 2 * 2 * 0.01, so nothing is padded and the pad is unused
    // (bean-check: `Unused Pad entry`). At the default it pads 0.03.
    let mut multiplier = shape(
        "a difference within a tolerance_multiplier of 2",
        format!(
            "{}2024-01-02 * \"x\"\n  Assets:A  99.97 USD\n  Equity:O  -99.97 USD\n\
             2024-01-03 pad Assets:A Equity:O\n2024-01-10 balance Assets:A 100.00 USD\n",
            opens(&["Assets:A", "Equity:O"])
        ),
        vec![],
        vec![],
        vec!["2024-01-03"],
        vec![],
    );
    multiplier.tolerance_multiplier = dec!(2);
    out.push(multiplier);
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
fn test_validator_padding_matches_process_pads_and_beancount() {
    for shape in shapes().into_iter().chain(shapes_2901()) {
        let name = &shape.name;
        let directives = parse(&shape.source);

        // The canonical padding.
        let pads = rustledger_booking::process_pads(&directives, shape.tolerance_multiplier);
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
        let options =
            ValidationOptions::default().with_tolerance_multiplier(shape.tolerance_multiplier);
        let errors = validate_with_options(&directives, options.clone());
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
        let canonical_failures = failures(&validate_with_options(&padded, options));

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
        let cost_messages: Vec<&str> = errors
            .iter()
            .filter(|e| e.code == ErrorCode::PadWithCost)
            .map(|e| {
                e.message
                    .strip_prefix("Attempt to pad an entry with cost for balance: ")
                    .unwrap_or(&e.message)
            })
            .collect();
        assert_eq!(
            cost_messages, shape.cost_messages,
            "{name}: `Attempt to pad an entry with cost` errors vs beancount"
        );
    }
}

/// One balance, two pad groups: the parent's total cannot be represented
/// (#1863), and the sub-account pads a currency it holds at cost. The
/// validator reports the "pad an entry with cost" as `process_pads` does,
/// whatever the parent's group came to.
#[test]
fn test_validator_reports_padding_at_cost_beside_an_unrepresentable_group() {
    let big = "50000000000000000000000000000";
    let source = format!(
        "2024-01-01 open Assets:P\n2024-01-01 open Assets:P:X1\n2024-01-01 open Assets:P:X2\n\
         2024-01-01 open Assets:P:B\n2024-01-01 open Assets:Cash\n2024-01-01 open Equity:O\n\
         2024-01-02 * \"x1\"\n  Assets:P:X1  {big} STK\n  Equity:O  -{big} STK\n\
         2024-01-02 * \"x2\"\n  Assets:P:X2  {big} STK\n  Equity:O  -{big} STK\n\
         2024-01-02 * \"lot\"\n  Assets:P:B  1 STK {{10 USD}}\n  Assets:Cash  -10 USD\n\
         2024-01-03 pad Assets:P Equity:O\n2024-01-03 pad Assets:P:B Equity:O\n\
         2024-01-10 balance Assets:P:B 2 STK\n"
    );
    let directives = parse(&source);
    let pads = rustledger_booking::process_pads(&directives, DEFAULT);
    let canonical = pads
        .errors
        .iter()
        .filter(|e| e.message.starts_with("Attempt to pad an entry with cost"))
        .count();
    assert_eq!(canonical, 1, "{:?}", pads.errors);
    let errors = validate_with_options(&directives, ValidationOptions::default());
    let inline = errors
        .iter()
        .filter(|e| e.code == ErrorCode::PadWithCost)
        .count();
    assert_eq!(inline, canonical, "{errors:?}");
}
