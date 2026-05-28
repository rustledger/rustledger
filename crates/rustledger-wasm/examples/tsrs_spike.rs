//! Spike for #1218 — prototype `ts-rs` against the wire-format DTOs
//! to see whether the emitted `.d.ts` preserves the load-bearing
//! shape details the hand-written declarations carry today.
//!
//! Run via:
//!
//! ```bash
//! cargo test --example tsrs_spike \
//!   -p rustledger-wasm --features ts-rs-spike
//! ```
//!
//! (ts-rs emits the `.d.ts` files from auto-generated unit tests, not
//! from `main()` — `cargo run` compiles but doesn't export.)
//!
//! The four DTOs below MIRROR the structs in `src/types.rs` exactly —
//! same fields, same serde attributes, same doc comments — but with
//! `#[derive(TS)]` added so ts-rs can introspect them. They're a copy
//! rather than a feature-gated derive on the production types because
//! the spike's goal is to compare what ts-rs emits against what we
//! ship by hand, without committing to the derive in the real DTOs
//! before the design decision is made.
//!
//! Output lands in `crates/rustledger-wasm/bindings/bindings/`
//! (ts-rs's `export_to = "bindings/"` puts files in a nested
//! `bindings/` under the crate root — the inner directory comes from
//! the attribute string, the outer from ts-rs's per-crate output
//! root). Eyeball:
//!
//! 1. Does the `DirectiveJson` discriminated union narrow correctly?
//! 2. Is the `TypedValueJson` payload's `MetaValueJson` substituted by
//!    the right TS shape, or does it become `any` / `unknown`?
//! 3. Do the doc comments translate to JSDoc?
//! 4. Do `skip_serializing_if = "Option::is_none"` fields become
//!    optional (`field?: T`)?
//! 5. How does `Vec<TypedValueJson>` render — `TypedValueJson[]` or
//!    `Array<TypedValueJson>`?

use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use ts_rs::TS;

// =============================================================================
// 1. MetaValueJson — untagged union, four shapes (string, bool, amount, null)
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, TS)]
#[serde(untagged)]
#[ts(export, export_to = "bindings/")]
pub enum MetaValueJson {
    String(String),
    Bool(bool),
    Amount { number: String, currency: String },
    Null,
}

// =============================================================================
// 2. TypedValueJson — tagged union for Custom.values (issue #1207)
// =============================================================================

#[derive(Debug, Clone, Serialize, Deserialize, TS)]
#[ts(export, export_to = "bindings/")]
pub struct TypedValueJson {
    #[serde(rename = "type")]
    pub value_type: String,
    pub value: MetaValueJson,
}

// =============================================================================
// 3. PostingJson — has skip_serializing_if optionals + flag (#1209)
// =============================================================================

#[derive(Debug, Clone, Serialize, Deserialize, TS)]
#[ts(export, export_to = "bindings/")]
pub struct AmountValue {
    pub number: String,
    pub currency: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, TS)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[ts(export, export_to = "bindings/")]
pub enum CostNumberJson {
    PerUnit { value: String },
    Total { value: String },
    PerUnitFromTotal { per_unit: String, total: String },
}

#[derive(Debug, Clone, Serialize, Deserialize, TS)]
#[ts(export, export_to = "bindings/")]
pub struct PostingCostJson {
    #[serde(skip_serializing_if = "Option::is_none")]
    #[ts(optional)]
    pub number: Option<CostNumberJson>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[ts(optional)]
    pub currency: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[ts(optional)]
    pub date: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[ts(optional)]
    pub label: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, TS)]
#[ts(export, export_to = "bindings/")]
pub struct PostingJson {
    pub account: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[ts(optional)]
    pub units: Option<AmountValue>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[ts(optional)]
    pub cost: Option<PostingCostJson>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[ts(optional)]
    pub price: Option<AmountValue>,
    /// Posting-level flag (e.g. `"!"` for pending). Mirrors
    /// `rustledger_core::Posting::flag`.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[ts(optional)]
    pub flag: Option<String>,
    /// Posting-level metadata (issue #1168). Empty when the posting
    /// has no explicit metadata.
    #[serde(skip_serializing_if = "HashMap::is_empty", default)]
    pub meta: HashMap<String, MetaValueJson>,
}

// =============================================================================
// 4. DirectiveJson — discriminated union with tag="type" (the big one)
// =============================================================================

#[derive(Debug, Clone, Serialize, Deserialize, TS)]
#[serde(tag = "type")]
#[ts(export, export_to = "bindings/")]
pub enum DirectiveJson {
    #[serde(rename = "transaction")]
    Transaction {
        date: String,
        flag: String,
        payee: Option<String>,
        narration: Option<String>,
        tags: Vec<String>,
        links: Vec<String>,
        postings: Vec<PostingJson>,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    #[serde(rename = "balance")]
    Balance {
        date: String,
        account: String,
        amount: AmountValue,
        #[serde(skip_serializing_if = "Option::is_none")]
        #[ts(optional)]
        tolerance: Option<String>,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    #[serde(rename = "document")]
    Document {
        date: String,
        account: String,
        path: String,
        #[serde(skip_serializing_if = "Vec::is_empty", default)]
        tags: Vec<String>,
        #[serde(skip_serializing_if = "Vec::is_empty", default)]
        links: Vec<String>,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
    #[serde(rename = "custom")]
    Custom {
        date: String,
        custom_type: String,
        #[serde(skip_serializing_if = "Vec::is_empty", default)]
        values: Vec<TypedValueJson>,
        #[serde(skip_serializing_if = "HashMap::is_empty", default)]
        meta: HashMap<String, MetaValueJson>,
    },
}

fn main() {
    // ts-rs writes one .d.ts per exported type into `bindings/`
    // when this binary runs. The `#[ts(export)]` attribute on each
    // struct/enum triggers the write — `main()` only has to exist so
    // the binary compiles.
    //
    // Confusingly, ts-rs's actual export mechanism is to write the
    // files when the `#[test]` it auto-generates runs — so running
    // `cargo test --example tsrs_spike --features ts-rs-spike` is
    // what actually produces the `.d.ts`. The `cargo run` path is a
    // no-op confirmation that the types compile.
    println!("ts-rs spike binary compiled cleanly.");
    println!(
        "Run `cargo test --example tsrs_spike --features ts-rs-spike` to emit \
         the .d.ts files into crates/rustledger-wasm/bindings/bindings/."
    );
}
