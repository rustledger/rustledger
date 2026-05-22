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
