//! Behavior replay for `PriceDB.tla` against `PriceDatabase`.
//!
//! Companion to `rustledger-core/tests/tla_behavior_replay.rs` (see its
//! module docs for the corpus format and regeneration workflow) — this suite
//! lives in the query crate because the abstraction target is
//! [`rustledger_query::PriceDatabase`].
//!
//! Mapping: each model `SetPrice(base, quote, price)` becomes an
//! `add_price` of a price directive at a strictly-later date, so the model's
//! overwrite semantics ("the price is the last one set") corresponds to
//! `get_latest_price`. Conformance is checked on every entry the MODEL has
//! set: `get_latest_price(base, quote) == prices[base][quote]`. Entries the
//! model has NOT set (0) are not asserted — the implementation legitimately
//! derives inverse rates the model doesn't track.

use rust_decimal::Decimal;
use rustledger_core::{Amount, NaiveDate, Price as PriceDirective, naive_date};
use rustledger_query::PriceDatabase;
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
    naive_date(2024, 1, u32::try_from(step.min(27)).expect("small") + 1).expect("valid day")
}

#[test]
fn replay_every_price_db_behavior() {
    let Some(corpus) = load_corpus("PriceDB") else {
        eprintln!("skipping: PriceDB corpus not available");
        return;
    };
    let behaviors = corpus["behaviors"].as_array().expect("behaviors");

    for (bi, behavior) in behaviors.iter().enumerate() {
        let mut db = PriceDatabase::new();
        for (si, step) in behavior.as_array().expect("steps").iter().enumerate() {
            let (action, params, state) = (step[0].as_str().expect("action"), &step[1], &step[2]);
            assert_eq!(action, "SetPrice", "PriceDB: unknown action {action:?}");
            let base = params["base"].as_str().expect("base");
            let quote = params["quote"].as_str().expect("quote");
            let price = params["price"].as_i64().expect("price");
            db.add_price(&PriceDirective {
                date: day(si + 1),
                currency: base.into(),
                amount: Amount::new(Decimal::from(price), quote),
                meta: Default::default(),
            });

            // Every model-set entry must read back as the latest price.
            for entry in state["prices"].as_array().expect("prices") {
                let (b, q, p) = (
                    entry[0].as_str().expect("base"),
                    entry[1].as_str().expect("quote"),
                    entry[2].as_i64().expect("price"),
                );
                assert_eq!(
                    db.get_latest_price(b, q),
                    Some(Decimal::from(p)),
                    "PriceDB behavior {bi} step {si}: latest {b}/{q} diverged"
                );
            }
        }
    }
    println!("PriceDB: replayed {} behaviors", behaviors.len());
}
