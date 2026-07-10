//! Cross-mirror wire parity for the `CostNumber` family (Phase-1 sweep W1).
//!
//! `CostNumber` crosses process boundaries through FIVE hand-written
//! mirrors, unified only by convention:
//!
//! 1. `rustledger_core::CostNumber` serde (`kind`-tagged `snake_case`)
//! 2. `rustledger_plugin_types::CostNumberData` (plugin wire + Python shim)
//! 3. `rustledger_wasm::types::CostNumberJson` (TypeScript clients)
//! 4. `rustledger_ffi_wasi::types::input::InputCostNumber` (builder ingress)
//! 5. the WIT `cost-number` variant (component model — positional, not
//!    JSON; its core→WIT / WIT→ingress mappings are pinned in
//!    `rustledger-ffi-component`'s own unit tests, which cross-reference
//!    this file)
//!
//! Before this test, each JSON mirror pinned its own shape against its own
//! literals — nothing asserted the shapes are THE SAME, and `compound` was
//! entirely unpinned in the core and wasm mirrors. Here every JSON mirror
//! is held to one canonical set of fixtures, for all four variants:
//! serialization must produce the canonical value (mirrors 1–3) and
//! deserialization must accept it (mirrors 2 and 4 — `InputCostNumber` is
//! ingress-only and has no `Serialize`).
//!
//! If this test fails, a mirror drifted: fix the mirror, do NOT re-pin the
//! fixture unless you are deliberately breaking the wire format for every
//! plugin, TypeScript, and FFI client at once.
#![cfg(not(target_arch = "wasm32"))]

use rustledger_core::{BookedCost, CostNumber, Decimal};
use rustledger_ffi_wasi::InputCostNumber;
use rustledger_plugin_types::CostNumberData;
use rustledger_wasm::types::CostNumberJson;

fn dec(s: &str) -> Decimal {
    Decimal::from_str_exact(s).unwrap()
}

/// The canonical wire shapes. Values are chosen to also pin scale
/// preservation ("5.00" must stay "5.00", not "5").
fn canonical() -> Vec<(&'static str, serde_json::Value)> {
    vec![
        (
            "per_unit",
            serde_json::json!({"kind": "per_unit", "value": "100"}),
        ),
        (
            "total",
            serde_json::json!({"kind": "total", "value": "1500"}),
        ),
        (
            "compound",
            serde_json::json!({"kind": "compound", "per_unit": "5.00", "total": "10.00"}),
        ),
        (
            "per_unit_from_total",
            serde_json::json!({"kind": "per_unit_from_total", "per_unit": "150", "total": "300"}),
        ),
    ]
}

fn core_variants() -> Vec<CostNumber> {
    vec![
        CostNumber::PerUnit { value: dec("100") },
        CostNumber::Total { value: dec("1500") },
        CostNumber::Compound {
            per_unit: dec("5.00"),
            total: dec("10.00"),
        },
        CostNumber::PerUnitFromTotal(BookedCost {
            per_unit: dec("150"),
            total: dec("300"),
        }),
    ]
}

fn data_variants() -> Vec<CostNumberData> {
    vec![
        CostNumberData::PerUnit {
            value: "100".into(),
        },
        CostNumberData::Total {
            value: "1500".into(),
        },
        CostNumberData::Compound {
            per_unit: "5.00".into(),
            total: "10.00".into(),
        },
        CostNumberData::PerUnitFromTotal {
            per_unit: "150".into(),
            total: "300".into(),
        },
    ]
}

fn json_variants() -> Vec<CostNumberJson> {
    vec![
        CostNumberJson::PerUnit {
            value: "100".into(),
        },
        CostNumberJson::Total {
            value: "1500".into(),
        },
        CostNumberJson::Compound {
            per_unit: "5.00".into(),
            total: "10.00".into(),
        },
        CostNumberJson::PerUnitFromTotal {
            per_unit: "150".into(),
            total: "300".into(),
        },
    ]
}

#[test]
fn all_serializing_mirrors_emit_the_canonical_shape() {
    // zip() truncates to the shortest iterator — assert the lengths first
    // so a variant accidentally dropped from any list fails the test
    // instead of silently shrinking the parity guarantee (review catch).
    assert_eq!(canonical().len(), 4);
    assert_eq!(core_variants().len(), 4);
    assert_eq!(data_variants().len(), 4);
    assert_eq!(json_variants().len(), 4);
    for (((kind, expected), core), (data, json)) in canonical()
        .into_iter()
        .zip(core_variants())
        .zip(data_variants().into_iter().zip(json_variants()))
    {
        assert_eq!(
            serde_json::to_value(core).unwrap(),
            expected,
            "core CostNumber diverged from canonical wire shape for {kind}"
        );
        assert_eq!(
            serde_json::to_value(&data).unwrap(),
            expected,
            "plugin CostNumberData diverged from canonical wire shape for {kind}"
        );
        assert_eq!(
            serde_json::to_value(&json).unwrap(),
            expected,
            "wasm CostNumberJson diverged from canonical wire shape for {kind}"
        );
    }
}

#[test]
fn deserializing_mirrors_accept_the_canonical_shape() {
    for (kind, expected) in canonical() {
        // Plugin DTO round-trips.
        let data: CostNumberData = serde_json::from_value(expected.clone())
            .unwrap_or_else(|e| panic!("CostNumberData rejected canonical {kind}: {e}"));
        assert_eq!(serde_json::to_value(&data).unwrap(), expected, "{kind}");

        // FFI builder ingress (Deserialize-only) accepts the same shape.
        let input: InputCostNumber = serde_json::from_value(expected.clone())
            .unwrap_or_else(|e| panic!("InputCostNumber rejected canonical {kind}: {e}"));
        let (got_kind, fields) = match &input {
            InputCostNumber::PerUnit { value } => ("per_unit", vec![("value", value.clone())]),
            InputCostNumber::Total { value } => ("total", vec![("value", value.clone())]),
            InputCostNumber::Compound { per_unit, total } => (
                "compound",
                vec![("per_unit", per_unit.clone()), ("total", total.clone())],
            ),
            InputCostNumber::PerUnitFromTotal { per_unit, total } => (
                "per_unit_from_total",
                vec![("per_unit", per_unit.clone()), ("total", total.clone())],
            ),
        };
        assert_eq!(got_kind, kind, "InputCostNumber picked the wrong variant");
        for (field, value) in fields {
            assert_eq!(
                expected[field].as_str().unwrap(),
                value,
                "InputCostNumber field {field} diverged for {kind}"
            );
        }

        // Core CostNumber also accepts the canonical shape (it serializes
        // it, so it must read it back).
        let core: CostNumber = serde_json::from_value(expected.clone())
            .unwrap_or_else(|e| panic!("core CostNumber rejected canonical {kind}: {e}"));
        assert_eq!(serde_json::to_value(core).unwrap(), expected, "{kind}");
    }
}
