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
//! `get_latest_price`. The model clears the opposite direction on every set
//! (direction supersession, #1759 — a pair has ONE rate timeline, like
//! beancount's `build_price_map`), so conformance is checked both ways on
//! every entry the model holds: `get_latest_price(base, quote) ==
//! prices[base][quote]` AND `get_latest_price(quote, base)` is its
//! reciprocal (the implementation derives inverses; the model stores 0
//! there, which is why zero entries are never asserted as absent).

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
            // Finalize before reading — lookups go through the
            // conversion index, built by `sort_prices`.
            db.sort_prices();

            // Every model-held entry must read back as the latest
            // price, and its derived inverse as the reciprocal.
            // Compared at 20 decimal places: the build may invert a
            // swallowed rate twice (1/(1/r)), leaving a residue in
            // the 28th significant digit — Python beancount's
            // build_price_map performs the same double inversion
            // with its own last-digit artifacts, so exactness at
            // full precision is not part of the modeled contract.
            for entry in state["prices"].as_array().expect("prices") {
                let (b, q, p) = (
                    entry[0].as_str().expect("base"),
                    entry[1].as_str().expect("quote"),
                    entry[2].as_i64().expect("price"),
                );
                assert_eq!(
                    db.get_latest_price(b, q).map(|r| r.round_dp(20)),
                    Some(Decimal::from(p).round_dp(20)),
                    "PriceDB behavior {bi} step {si}: latest {b}/{q} diverged"
                );
                assert_eq!(
                    db.get_latest_price(q, b).map(|r| r.round_dp(20)),
                    Some((Decimal::ONE / Decimal::from(p)).round_dp(20)),
                    "PriceDB behavior {bi} step {si}: inverse {q}/{b} diverged"
                );
            }
        }
    }
    println!("PriceDB: replayed {} behaviors", behaviors.len());
}
