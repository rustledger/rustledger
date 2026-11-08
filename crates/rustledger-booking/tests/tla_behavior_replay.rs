//! Behavior replay for `PadCorrect.tla` against the pad engine.
//!
//! Companion to `rustledger-core/tests/tla_behavior_replay.rs` (see its
//! module docs for the corpus format and regeneration workflow) — this suite
//! lives in the booking crate because the abstraction target is
//! [`rustledger_booking::process_pads`].
//!
//! The model (`spec/tla/PadCorrect.tla`): a pad directive arms a pending pad
//! on the account; the next balance assertion absorbs the difference by
//! synthesizing a padding transaction (`pad amount = asserted − actual`); a
//! newer pad replaces a pending one; assertions without a pad only occur
//! when they already hold. Single account, single currency — the
//! implementation's sub-account summing semantic is out of model scope
//! (pinned by integration tests instead).
//!
//! Conformance per behavior: `process_pads` synthesizes exactly the pads
//! the model resolved with exactly the model's amounts, and the final
//! account balance (original transactions + synthesized pads) equals the
//! model's final `actual`. Behaviors ending with an ARMED pad must produce
//! exactly the implementation's unused-pad error (beancount-aligned) and
//! nothing else; all other behaviors must be error-free.

use rust_decimal::Decimal;
use rustledger_booking::process_pads;
use rustledger_core::{
    Amount, Balance, Directive, IncompleteAmount, NaiveDate, Pad, Posting, Spanned, Transaction,
    naive_date,
};
use serde_json::Value;

const ACCOUNT: &str = "Assets:Cash";
const SOURCE: &str = "Equity:Opening-Balances";

fn load_corpus(spec: &str) -> Option<Value> {
    let path = match std::env::var("RUSTLEDGER_TLA_BEHAVIORS_DIR") {
        Ok(dir) => std::path::PathBuf::from(dir).join(format!("{spec}.json")),
        Err(_) => std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join(format!("../../spec/tla/behaviors/{spec}.json")),
    };
    // Graceful skip when spec/ is stripped (crane srcFilter, published crates).
    let raw = std::fs::read_to_string(path).ok()?;
    let corpus: Value = serde_json::from_str(&raw).expect("corpus is valid JSON");
    let behaviors = corpus["behaviors"]
        .as_array()
        .expect("behaviors array")
        .len() as u64;
    let declared = corpus["coverage"]["behaviors"]
        .as_u64()
        .expect("coverage.behaviors");
    assert!(
        behaviors > 0 && behaviors == declared,
        "{spec}: corpus has {behaviors} behaviors but declares {declared} — \
         regenerate with scripts/tla-behaviors.py"
    );
    Some(corpus)
}

fn day(step: usize) -> NaiveDate {
    naive_date(2024, 1, u32::try_from(step.min(27)).expect("small") + 1).expect("valid day")
}

fn txn(date: NaiveDate, amount: i64) -> Directive {
    let leg = |account: &str, number: i64| {
        Spanned::synthesized(Posting {
            account: account.into(),
            units: Some(IncompleteAmount::Complete(Amount::new(
                Decimal::from(number),
                "USD",
            ))),
            cost: None,
            price: None,
            flag: None,
            comments: Default::default(),
            trailing_comments: Default::default(),
            meta: Default::default(),
            booking: Default::default(),
        })
    };
    Directive::Transaction(Transaction {
        date,
        flag: '*',
        payee: None,
        narration: "replay".into(),
        tags: Default::default(),
        links: Default::default(),
        postings: vec![leg(ACCOUNT, amount), leg("Equity:Aux", -amount)],
        trailing_comments: Default::default(),
        meta: Default::default(),
    })
}

/// Sum a transaction's postings on ACCOUNT.
fn account_units(t: &Transaction) -> Decimal {
    t.postings
        .iter()
        .filter(|p| p.account.as_ref() == ACCOUNT)
        .filter_map(|p| p.amount())
        .map(|a| a.number)
        .sum()
}

#[test]
fn replay_every_pad_behavior() {
    let Some(corpus) = load_corpus("PadCorrect") else {
        eprintln!("skipping: PadCorrect corpus not available");
        return;
    };
    let behaviors = corpus["behaviors"].as_array().expect("behaviors");

    for (bi, behavior) in behaviors.iter().enumerate() {
        // Open every account first, as any real ledger would (process_pads
        // counts an unopened account's postings too, as beancount does; the
        // validator owns that error class).
        let mut directives: Vec<Directive> = [ACCOUNT, SOURCE, "Equity:Aux"]
            .iter()
            .map(|account| {
                Directive::Open(rustledger_core::Open {
                    date: naive_date(2023, 12, 31).expect("valid"),
                    account: (*account).into(),
                    currencies: vec![],
                    booking: None,
                    meta: Default::default(),
                })
            })
            .collect();
        // Model-side bookkeeping to derive the expected synthesized pads.
        let mut actual: i64 = 0;
        let mut pad_pending = false;
        // Pads that never insert padding, each an `Unused Pad entry` as in
        // beancount: one superseded by a later pad, one whose balance already
        // held (a zero difference), and one still armed at the end.
        let mut unused_pads = 0usize;
        let mut expected_pads: Vec<i64> = Vec::new();
        let mut txn_sum: i64 = 0;

        for (si, step) in behavior.as_array().expect("steps").iter().enumerate() {
            let (action, params, state) = (step[0].as_str().expect("action"), &step[1], &step[2]);
            let date = day(si + 1);
            match action {
                "AddTxn" => {
                    let amount = params["amount"].as_i64().expect("amount");
                    directives.push(txn(date, amount));
                    actual += amount;
                    txn_sum += amount;
                }
                "AddPad" => {
                    directives.push(Directive::Pad(Pad {
                        date,
                        account: ACCOUNT.into(),
                        source_account: SOURCE.into(),
                        meta: Default::default(),
                    }));
                    if pad_pending {
                        unused_pads += 1;
                    }
                    pad_pending = true;
                }
                "AddBalance" => {
                    let asserted = params["asserted"].as_i64().expect("asserted");
                    directives.push(Directive::Balance(Balance {
                        date,
                        account: ACCOUNT.into(),
                        amount: Amount::new(Decimal::from(asserted), "USD"),
                        tolerance: None,
                        meta: Default::default(),
                    }));
                    if pad_pending {
                        if asserted == actual {
                            unused_pads += 1;
                        }
                        expected_pads.push(asserted - actual);
                        actual = asserted;
                        pad_pending = false;
                    } else {
                        assert_eq!(asserted, actual, "model emitted an illegal balance");
                    }
                }
                other => panic!("PadCorrect: unknown action {other:?}"),
            }
            assert_eq!(
                actual,
                state["actual"].as_i64().expect("actual"),
                "PadCorrect behavior {bi} step {si}: bookkeeping drifted from the corpus"
            );
        }

        let result = process_pads(&directives);
        // The implementation (beancount-aligned) reports each pad that never
        // padded as an error. Assert EXACTLY those errors: any other error,
        // or a missing or extra unused-pad error, is a divergence.
        if pad_pending {
            unused_pads += 1;
        }
        assert!(
            result.errors.len() == unused_pads
                && result
                    .errors
                    .iter()
                    .all(|e| e.message.contains("no corresponding balance")),
            "PadCorrect behavior {bi}: expected exactly {unused_pads} unused-pad \
             errors, got: {:?}",
            result.errors
        );

        // Zero-difference pads may or may not synthesize a transaction; only
        // nonzero expected pads are structural.
        let synthesized: Vec<Decimal> = result
            .padding_transactions
            .iter()
            .map(account_units)
            .collect();
        let expected: Vec<Decimal> = expected_pads
            .iter()
            .filter(|p| **p != 0)
            .map(|p| Decimal::from(*p))
            .collect();
        assert_eq!(
            synthesized, expected,
            "PadCorrect behavior {bi}: synthesized pad amounts diverged"
        );

        let final_balance = Decimal::from(txn_sum) + synthesized.iter().sum::<Decimal>();
        assert_eq!(
            final_balance,
            Decimal::from(actual),
            "PadCorrect behavior {bi}: final balance diverged from the model"
        );
    }
    println!("PadCorrect: replayed {} behaviors", behaviors.len());
}
