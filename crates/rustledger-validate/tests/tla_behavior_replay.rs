//! Behavior replay for `AccountStateMachine.tla` against the validator.
//!
//! Companion to `rustledger-core/tests/tla_behavior_replay.rs` (see its
//! module docs for the corpus format and regeneration workflow) — this suite
//! lives in the validate crate because the abstraction target is the
//! validator's account lifecycle, which core cannot depend on.
//!
//! The model's actions are guarded (open only when unopened, close only when
//! open with zero balance, post/transfer only between open accounts), so
//! every behavior in the corpus is a LEGAL lifecycle. The conformance
//! obligation is enabledness: each behavior, converted to a directive
//! sequence, must validate with ZERO errors — a validator that wrongly
//! rejects a model-legal open/close/post/transfer sequence (the
//! E1001/E1002/E1003 state machine) fails here.
//!
//! Balances are carried in the corpus for transparency; per-account balance
//! equality holds by construction of the emitted postings (each model Post
//! and Transfer maps to exactly its amount), so the assertable content is
//! the validator's acceptance, not arithmetic.

mod common;

use rust_decimal::Decimal;
use rustledger_core::{
    Amount, Close, Directive, IncompleteAmount, NaiveDate, Open, Posting, Spanned, Transaction,
    naive_date,
};
use serde_json::Value;

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
    // Monotonically non-decreasing dates; duplicates are legal directives.
    naive_date(2024, 1, u32::try_from(step.min(27)).expect("small") + 1).expect("valid day")
}

/// Model accounts are root names; map to valid beancount accounts. The
/// auxiliary equity leg balances every Post (the model is single-entry).
fn acct(model: &str) -> String {
    format!("{model}:Model")
}

fn units(number: i64) -> Option<IncompleteAmount> {
    Some(IncompleteAmount::Complete(Amount::new(
        Decimal::from(number),
        "USD",
    )))
}

fn posting(account: &str, number: i64) -> Spanned<Posting> {
    Spanned::synthesized(Posting {
        account: account.into(),
        units: units(number),
        cost: None,
        price: None,
        flag: None,
        comments: Vec::new(),
        trailing_comments: Vec::new(),
        meta: Default::default(),
    })
}

fn transaction(date: NaiveDate, postings: Vec<Spanned<Posting>>) -> Directive {
    Directive::Transaction(Transaction {
        date,
        flag: '*',
        payee: None,
        narration: "replay".into(),
        tags: vec![],
        links: vec![],
        postings,
        trailing_comments: Vec::new(),
        meta: Default::default(),
    })
}

#[test]
fn replay_every_account_state_machine_behavior() {
    let Some(corpus) = load_corpus("AccountStateMachine") else {
        eprintln!("skipping: AccountStateMachine corpus not available");
        return;
    };
    let behaviors = corpus["behaviors"].as_array().expect("behaviors");

    for (bi, behavior) in behaviors.iter().enumerate() {
        // The auxiliary account absorbs Post's counter-leg; opened first.
        let mut directives = vec![Directive::Open(Open {
            date: naive_date(2024, 1, 1).expect("valid"),
            account: "Equity:Aux".into(),
            currencies: vec![],
            booking: None,
            meta: Default::default(),
        })];

        for (si, step) in behavior.as_array().expect("steps").iter().enumerate() {
            let action = step[0].as_str().expect("action");
            let params = &step[1];
            let date = day(si + 1);
            match action {
                "Open" => directives.push(Directive::Open(Open {
                    date,
                    account: acct(params["account"].as_str().expect("account")).into(),
                    currencies: vec![],
                    booking: None,
                    meta: Default::default(),
                })),
                "Close" => directives.push(Directive::Close(Close {
                    date,
                    account: acct(params["account"].as_str().expect("account")).into(),
                    meta: Default::default(),
                })),
                "Post" => {
                    let a = acct(params["account"].as_str().expect("account"));
                    let amt = params["amount"].as_i64().expect("amount");
                    directives.push(transaction(
                        date,
                        vec![posting(&a, amt), posting("Equity:Aux", -amt)],
                    ));
                }
                "Transfer" => {
                    let from = acct(params["from"].as_str().expect("from"));
                    let to = acct(params["to"].as_str().expect("to"));
                    let amt = params["amount"].as_i64().expect("amount");
                    directives.push(transaction(
                        date,
                        vec![posting(&from, -amt), posting(&to, amt)],
                    ));
                }
                other => panic!("AccountStateMachine: unknown action {other:?}"),
            }
        }

        // Enabledness: a model-legal lifecycle must validate cleanly.
        let errors = common::validate(&directives);
        assert!(
            errors.is_empty(),
            "AccountStateMachine behavior {bi}: model-legal lifecycle rejected \
             by the validator: {errors:?}\ndirectives: {directives:#?}"
        );
    }
    println!(
        "AccountStateMachine: replayed {} behaviors",
        behaviors.len()
    );
}
