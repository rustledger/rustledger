//! Round-trip tests for the Python compat shim's `CostSpec`
//! parse/serialize functions (#1164 regression guard).
//!
//! These tests exec the host `python3` against the embedded
//! `BEANCOUNT_COMPAT_PY` source and verify that Rust's typed
//! `CostData` JSON shape survives the Python parse → re-serialize
//! → Python parse round-trip with values intact.
//!
//! Without this test the silent value-loss the agent reviewer flagged
//! (Rust serializes as `{"PerUnit": "100"}`, Python tries to read
//! `number_per` and gets `None`) returns the first time the wire
//! shape drifts again. The test is skipped when host `python3` isn't
//! available so it doesn't break developers on minimal systems. Gated
//! behind the `python-plugins` feature so it only runs when the
//! relevant code is compiled in.

#![cfg(feature = "python-plugins")]

use std::io::Write;
use std::process::{Command, Stdio};

use rustledger_plugin::python::BEANCOUNT_COMPAT_PY;

fn host_python_available() -> bool {
    Command::new("python3")
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

/// Execute a Python script that loads the compat shim and runs the
/// caller's test body, returning stdout. Panics with stderr on
/// failure so test output points at the actual Python error.
fn run_python(test_body: &str) -> String {
    let mut child = Command::new("python3")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn python3");

    let script = format!("{BEANCOUNT_COMPAT_PY}\n\n# ---- test body ----\n{test_body}");
    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(script.as_bytes())
        .expect("write script");

    let out = child.wait_with_output().expect("wait_with_output");
    assert!(
        out.status.success(),
        "python3 failed:\n--- stderr ---\n{}\n--- stdout ---\n{}",
        String::from_utf8_lossy(&out.stderr),
        String::from_utf8_lossy(&out.stdout),
    );
    String::from_utf8(out.stdout).expect("utf8 stdout")
}

#[test]
fn per_unit_round_trip_through_python() {
    if !host_python_available() {
        eprintln!("skipping: python3 not available");
        return;
    }

    // Rust serializes `CostNumber::PerUnit(100)` as
    // {"kind":"per_unit","value":"100.00"} via the unified `kind`-tag
    // shape. The Python `_parse_cost_spec` must read that shape and
    // populate `number_per`.
    let out = run_python(
        r"
import json
input_dict = {
    'number': {'kind': 'per_unit', 'value': '100.00'},
    'currency': 'USD',
    'date': '2024-01-15',
    'label': None,
    'merge': False,
}
spec = _parse_cost_spec(input_dict)
assert spec.number_per is not None, f'number_per is None — silent value loss! spec={spec!r}'
assert str(spec.number_per) == '100.00', f'expected 100.00, got {spec.number_per!r}'
assert spec.number_total is None, f'number_total should be None, got {spec.number_total!r}'
assert spec.currency == 'USD'

# Now re-serialize and check the wire shape Rust will read back
out_dict = _serialize_cost_spec(spec)
print(json.dumps(out_dict, sort_keys=True))
",
    );

    let parsed: serde_json::Value = serde_json::from_str(out.trim()).expect("json");
    assert_eq!(
        parsed["number"],
        serde_json::json!({"kind": "per_unit", "value": "100.00"}),
        "Python re-serialization lost the unified `kind`-tag shape"
    );
}

#[test]
fn total_round_trip_through_python() {
    if !host_python_available() {
        eprintln!("skipping: python3 not available");
        return;
    }

    let out = run_python(
        r"
import json
spec = _parse_cost_spec({
    'number': {'kind': 'total', 'value': '1500.00'},
    'currency': 'USD',
    'date': None,
    'label': None,
    'merge': False,
})
assert spec.number_per is None
assert str(spec.number_total) == '1500.00', f'expected 1500.00, got {spec.number_total!r}'
print(json.dumps(_serialize_cost_spec(spec), sort_keys=True))
",
    );

    let parsed: serde_json::Value = serde_json::from_str(out.trim()).expect("json");
    assert_eq!(
        parsed["number"],
        serde_json::json!({"kind": "total", "value": "1500.00"})
    );
}

#[test]
fn per_unit_from_total_round_trip_through_python() {
    if !host_python_available() {
        eprintln!("skipping: python3 not available");
        return;
    }

    // The post-booking variant: Python flattens to two fields
    // (number_per + number_total) for upstream beancount API
    // compatibility, but the re-serialize must reconstruct the
    // PerUnitFromTotal variant so the preserved total survives the
    // round trip.
    let out = run_python(
        r"
import json
spec = _parse_cost_spec({
    'number': {
        'kind': 'per_unit_from_total',
        'per_unit': '150.00',
        'total': '300.00',
    },
    'currency': 'USD',
    'date': None,
    'label': None,
    'merge': False,
})
# Both fields populated on the Python side
assert spec.number_per is not None and str(spec.number_per) == '150.00'
assert spec.number_total is not None and str(spec.number_total) == '300.00'
# Re-serialize preserves the variant
print(json.dumps(_serialize_cost_spec(spec), sort_keys=True))
",
    );

    let parsed: serde_json::Value = serde_json::from_str(out.trim()).expect("json");
    assert_eq!(
        parsed["number"],
        serde_json::json!({
            "kind": "per_unit_from_total",
            "per_unit": "150.00",
            "total": "300.00",
        }),
        "round-trip lost the preserved total — currency_accounts and friends would silently regress"
    );
}

#[test]
fn bare_brace_round_trip_through_python() {
    if !host_python_available() {
        eprintln!("skipping: python3 not available");
        return;
    }

    // Bare `{}` cost: number is None on the Python side and stays
    // None on re-serialize. Distinct from a currency-only spec.
    let out = run_python(
        r"
import json
spec = _parse_cost_spec({
    'number': None,
    'currency': 'USD',
    'date': None,
    'label': None,
    'merge': False,
})
assert spec.number_per is None and spec.number_total is None
print(json.dumps(_serialize_cost_spec(spec), sort_keys=True))
",
    );

    let parsed: serde_json::Value = serde_json::from_str(out.trim()).expect("json");
    assert!(
        parsed["number"].is_null(),
        "bare-brace re-serialize must emit null number, got {parsed:?}"
    );
}

#[test]
fn python_emits_kind_tagged_shape_matching_ffi_wasi_and_wasm() {
    // Pins the unification invariant: Python compat emits exactly the
    // same shape as FFI-WASI / WASM / plugin-types. If serde defaults
    // ever drift on the Rust side, this test catches the cross-
    // boundary mismatch from the Python side directly.
    if !host_python_available() {
        eprintln!("skipping: python3 not available");
        return;
    }
    let out = run_python(
        r"
import json
# Construct a CostSpec namedtuple via parse, then re-serialize and
# verify the wire shape matches what every other binding emits.
spec = _parse_cost_spec({
    'number': {'kind': 'per_unit', 'value': '42'},
    'currency': 'USD', 'date': None, 'label': None, 'merge': False,
})
print(json.dumps(_serialize_cost_spec(spec)['number'], sort_keys=True))
",
    );
    let parsed: serde_json::Value = serde_json::from_str(out.trim()).expect("json");
    assert_eq!(parsed["kind"], "per_unit");
    assert_eq!(parsed["value"], "42");
    assert!(
        parsed.get("PerUnit").is_none(),
        "Python must NOT emit the pre-unification external-tag shape"
    );
}

#[test]
fn legacy_flat_shape_no_longer_silently_works() {
    if !host_python_available() {
        eprintln!("skipping: python3 not available");
        return;
    }

    // The pre-#1164 wire shape had `number_per` / `number_total` at
    // the top level. Sending it should NOT silently populate the
    // Python CostSpec (which is what was happening — and how the
    // silent value-loss regression hid). Both fields stay None.
    let out = run_python(
        r"
import json
spec = _parse_cost_spec({
    'number_per': '100',
    'number_total': None,
    'currency': 'USD',
    'date': None,
    'label': None,
    'merge': False,
})
# The new parser only reads from `number`. Legacy keys are ignored.
result = {
    'per_was_read': spec.number_per is not None,
    'total_was_read': spec.number_total is not None,
}
print(json.dumps(result))
",
    );

    let parsed: serde_json::Value = serde_json::from_str(out.trim()).expect("json");
    assert_eq!(
        parsed["per_was_read"], false,
        "Python compat must NOT silently accept legacy `number_per`; it's the regression vector"
    );
}
