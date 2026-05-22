//! Wire-format round-trip tests for `CostNumberData` (#1164).
//!
//! These tests pin the JSON shape that plugins and the Python compat
//! shim depend on. Any change in serde representation here is a wire-
//! format break for every plugin language binding.

use rustledger_plugin_types::CostNumberData;

#[test]
fn per_unit_serializes_with_kind_tag() {
    let cn = CostNumberData::PerUnit {
        value: "100".to_string(),
    };
    let json = serde_json::to_value(&cn).unwrap();
    assert_eq!(
        json,
        serde_json::json!({"kind": "per_unit", "value": "100"})
    );
}

#[test]
fn total_serializes_with_kind_tag() {
    let cn = CostNumberData::Total {
        value: "1500".to_string(),
    };
    let json = serde_json::to_value(&cn).unwrap();
    assert_eq!(json, serde_json::json!({"kind": "total", "value": "1500"}));
}

#[test]
fn per_unit_from_total_serializes_with_kind_tag_and_both_fields() {
    let cn = CostNumberData::PerUnitFromTotal {
        per_unit: "150".to_string(),
        total: "300".to_string(),
    };
    let json = serde_json::to_value(&cn).unwrap();
    assert_eq!(
        json,
        serde_json::json!({
            "kind": "per_unit_from_total",
            "per_unit": "150",
            "total": "300",
        })
    );
}

#[test]
fn unified_wire_shape_matches_ffi_wasi_and_wasm() {
    // Load-bearing regression guard: plugin-types, FFI-WASI, WASM,
    // and Python compat all emit the same `kind`-tagged shape. If
    // serde defaults ever drift here, downstream clients written
    // against the unified shape silently break — this assertion
    // catches it. The `kind` value uses snake_case to match the
    // FFI-WASI/WASM convention.
    let cn = CostNumberData::PerUnit {
        value: "1".to_string(),
    };
    let json = serde_json::to_value(&cn).unwrap();
    assert_eq!(json["kind"], "per_unit", "kind must be snake_case");
    assert!(json.get("value").is_some(), "value field must be present");
    assert!(
        json.get("PerUnit").is_none(),
        "must NOT use external-tag (pre-PR shape)"
    );
}

#[test]
fn per_unit_round_trip() {
    let cn = CostNumberData::PerUnit {
        value: "100".to_string(),
    };
    let json = serde_json::to_string(&cn).unwrap();
    let back: CostNumberData = serde_json::from_str(&json).unwrap();
    assert_eq!(back.per_unit(), Some("100"));
    assert_eq!(back.total(), None);
}

#[test]
fn total_round_trip() {
    let cn = CostNumberData::Total {
        value: "1500".to_string(),
    };
    let json = serde_json::to_string(&cn).unwrap();
    let back: CostNumberData = serde_json::from_str(&json).unwrap();
    assert_eq!(back.per_unit(), None);
    assert_eq!(back.total(), Some("1500"));
}

#[test]
fn per_unit_from_total_round_trip() {
    let cn = CostNumberData::PerUnitFromTotal {
        per_unit: "150".to_string(),
        total: "300".to_string(),
    };
    let json = serde_json::to_string(&cn).unwrap();
    let back: CostNumberData = serde_json::from_str(&json).unwrap();
    // Both accessors must return Some — this is the load-bearing
    // assertion that plugins like currency_accounts can access the
    // preserved total without losing it on the wire.
    assert_eq!(back.per_unit(), Some("150"));
    assert_eq!(back.total(), Some("300"));
}

// ===== MessagePack wire-format tests (review A-3.11 / A-4.3) =====
//
// The *actual* WASM plugin wire transport is MessagePack, not JSON
// (see `rmp_serde::to_vec` / `from_slice` at
// `rustledger-plugin/src/runtime.rs:230` and `:273`). The JSON
// tests above pin the human-readable shape; these pin the binary
// wire so a future change to msgpack serializer settings (e.g.
// switching to `to_vec_named` for self-describing maps, or
// `Serializer::new(buf).with_struct_map(false)` for compact
// positional encoding) doesn't silently break cross-language plugin
// compat.
//
// IMPORTANT: these tests use `rmp_serde::to_vec` and `from_slice`
// because that's what production uses. If runtime.rs ever changes
// to a different serializer call, update these tests to match —
// otherwise wire-shape drift passes here while real plugins break.

#[test]
fn per_unit_msgpack_round_trip() {
    let cn = CostNumberData::PerUnit {
        value: "100".to_string(),
    };
    let bytes = rmp_serde::to_vec(&cn).unwrap();
    let back: CostNumberData = rmp_serde::from_slice(&bytes).unwrap();
    assert_eq!(back.per_unit(), Some("100"));
    assert_eq!(back.total(), None);
}

#[test]
fn total_msgpack_round_trip() {
    let cn = CostNumberData::Total {
        value: "1500".to_string(),
    };
    let bytes = rmp_serde::to_vec(&cn).unwrap();
    let back: CostNumberData = rmp_serde::from_slice(&bytes).unwrap();
    assert_eq!(back.per_unit(), None);
    assert_eq!(back.total(), Some("1500"));
}

#[test]
fn per_unit_from_total_msgpack_round_trip() {
    // Load-bearing: post-booking PerUnitFromTotal must survive the
    // msgpack round-trip with both halves intact. If serializer
    // settings drop the discriminator, the variant degrades silently
    // to one half — exactly the silent-degradation pattern this PR
    // was designed to prevent.
    let cn = CostNumberData::PerUnitFromTotal {
        per_unit: "150".to_string(),
        total: "300".to_string(),
    };
    let bytes = rmp_serde::to_vec(&cn).unwrap();
    let back: CostNumberData = rmp_serde::from_slice(&bytes).unwrap();
    assert_eq!(back.per_unit(), Some("150"));
    assert_eq!(back.total(), Some("300"));
}

#[test]
fn cost_data_msgpack_round_trip_preserves_all_variants() {
    use rustledger_plugin_types::CostData;

    for number in [
        Some(CostNumberData::PerUnit { value: "1".into() }),
        Some(CostNumberData::Total { value: "10".into() }),
        Some(CostNumberData::PerUnitFromTotal {
            per_unit: "1".into(),
            total: "10".into(),
        }),
        None,
    ] {
        let cost = CostData {
            number,
            currency: Some("USD".into()),
            date: Some("2024-01-15".into()),
            label: Some("lot1".into()),
            merge: false,
        };
        let bytes = rmp_serde::to_vec(&cost).unwrap();
        let back: CostData = rmp_serde::from_slice(&bytes).unwrap();
        match (&cost.number, &back.number) {
            (None, None) => {}
            (Some(a), Some(b)) => {
                assert_eq!(a.per_unit(), b.per_unit());
                assert_eq!(a.total(), b.total());
            }
            _ => panic!("msgpack round trip mutated cost.number presence"),
        }
        assert_eq!(cost.currency, back.currency);
        assert_eq!(cost.date, back.date);
        assert_eq!(cost.label, back.label);
        assert_eq!(cost.merge, back.merge);
    }
}

#[test]
fn accessors_exhaustively_cover_variants() {
    // Regression guard: if a future variant is added without updating
    // the accessors, this test stays green only by accident. The
    // exhaustive match in the impl is what guarantees coverage; this
    // test is a behavioral spot-check.
    for cn in [
        CostNumberData::PerUnit { value: "1".into() },
        CostNumberData::Total { value: "2".into() },
        CostNumberData::PerUnitFromTotal {
            per_unit: "3".into(),
            total: "30".into(),
        },
    ] {
        // At least one accessor returns Some for every variant.
        assert!(cn.per_unit().is_some() || cn.total().is_some());
    }
}
