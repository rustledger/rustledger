#!/usr/bin/env python3
"""
TLA+ Trace to Rust Test Generator

Converts JSON traces (from tla_trace_to_json.py) into Rust test cases.

Usage:
    python trace_to_rust_test.py trace.json > test_from_trace.rs
    python trace_to_rust_test.py --module booking traces/*.json > generated_tests.rs
"""

import json
import sys
import argparse
from pathlib import Path
from typing import Any


# Maps TLA+ spec names to Rust module templates
SPEC_TEMPLATES = {
    "BookingMethods": {
        "imports": """
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use rustledger_core::{Amount, Inventory, Position, Cost, CostSpec};
use rustledger_core::inventory::BookingMethod;
use chrono::NaiveDate;
""",
        "setup": """
fn setup_inventory() -> Inventory {
    Inventory::new()
}

fn make_date(days: i32) -> NaiveDate {
    NaiveDate::from_ymd_opt(2024, 1, 1).unwrap() + chrono::Duration::days(days as i64)
}

fn make_cost(units: i64, currency: &str, date: i32) -> Cost {
    Cost {
        amount: Some(Amount::new(Decimal::new(units, 0), currency.into())),
        date: Some(make_date(date)),
        label: None,
    }
}
""",
    },
    "ValidationErrors": {
        "imports": """
use rustledger_validate::{Validator, ValidationError};
use rustledger_core::*;
use chrono::NaiveDate;
""",
        "setup": """
fn make_date(days: i32) -> NaiveDate {
    NaiveDate::from_ymd_opt(2024, 1, 1).unwrap() + chrono::Duration::days(days as i64)
}
""",
    },
    "Inventory": {
        "imports": """
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use rustledger_core::{Amount, Inventory, Position, Cost, CostSpec};
use chrono::NaiveDate;
""",
        "setup": """
fn setup_inventory() -> Inventory {
    Inventory::new()
}

fn make_date(days: i32) -> NaiveDate {
    NaiveDate::from_ymd_opt(2024, 1, 1).unwrap() + chrono::Duration::days(days as i64)
}
""",
    },
    "AccountLifecycle": {
        "imports": """
use rustledger_validate::{Validator, ValidationError};
use rustledger_core::*;
use chrono::NaiveDate;
use std::collections::HashMap;
""",
        "setup": """
fn make_date(days: i32) -> NaiveDate {
    NaiveDate::from_ymd_opt(2024, 1, 1).unwrap() + chrono::Duration::days(days as i64)
}
""",
    },
    "PriceDatabase": {
        "imports": """
use rust_decimal::Decimal;
use rust_decimal_macros::dec;
use rustledger_core::PriceMap;
use chrono::NaiveDate;
""",
        "setup": """
fn make_date(days: i32) -> NaiveDate {
    NaiveDate::from_ymd_opt(2024, 1, 1).unwrap() + chrono::Duration::days(days as i64)
}
""",
    },
}


def tla_to_rust_value(value: Any, indent: int = 0) -> str:
    """Convert a TLA+ value (parsed as Python) to Rust code."""
    ind = "    " * indent

    if value is None:
        return "None"

    if isinstance(value, bool):
        return "true" if value else "false"

    if isinstance(value, int):
        return str(value)

    if isinstance(value, str):
        return f'"{value}"'

    if isinstance(value, dict):
        if value.get("type") == "set":
            elements = value.get("elements", [])
            if not elements:
                return "HashSet::new()"
            els = ", ".join(tla_to_rust_value(e, indent) for e in elements)
            return f"HashSet::from([{els}])"

        if value.get("type") == "sequence":
            elements = value.get("elements", [])
            if not elements:
                return "vec![]"
            els = ", ".join(tla_to_rust_value(e, indent) for e in elements)
            return f"vec![{els}]"

        if value.get("type") == "record":
            fields = value.get("fields", {})
            if not fields:
                return "/* empty record */"
            # This is context-dependent - generate a struct literal comment
            field_strs = []
            for k, v in fields.items():
                field_strs.append(f"{k}: {tla_to_rust_value(v, indent + 1)}")
            return "{\n" + ind + "    " + (",\n" + ind + "    ").join(field_strs) + "\n" + ind + "}"

        if value.get("type") == "function":
            mapping = value.get("mapping", {})
            if not mapping:
                return "HashMap::new()"
            entries = []
            for k, v in mapping.items():
                entries.append(f"({tla_to_rust_value(k)}, {tla_to_rust_value(v)})")
            return f"HashMap::from([{', '.join(entries)}])"

    return f"/* unknown: {value} */"


def generate_booking_test(trace: dict, test_name: str) -> str:
    """Generate a Rust test for a BookingMethods trace."""
    states = trace.get("states", [])
    invariant = trace.get("invariant_violated", "Unknown")

    lines = [
        f"/// Generated from TLA+ counterexample",
        f"/// Invariant violated: {invariant}",
        f"#[test]",
        f"fn {test_name}() {{",
        f"    let mut inventory = setup_inventory();",
        f"",
    ]

    for state in states:
        action = state.get("action", "Unknown")
        vars = state.get("variables", {})

        if action == "Init":
            lines.append(f"    // Initial state")
            continue

        if action in ("AddLot", "Add"):
            # Extract lot info from variables
            currency = vars.get("currency", "USD")
            if isinstance(currency, dict):
                currency = list(currency.get("elements", ["USD"]))[0] if currency.get("elements") else "USD"

            lines.append(f"    // Action: {action}")
            lines.append(f"    // TODO: Extract lot details from trace")
            lines.append(f"    // inventory.add_position(position);")

        elif action in ("ReduceFIFO", "ReduceLIFO", "ReduceHIFO", "ReduceSTRICT", "ReduceAVERAGE"):
            method = action.replace("Reduce", "").upper()
            lines.append(f"    // Action: {action}")
            lines.append(f"    // TODO: Extract reduction details from trace")
            lines.append(f"    // inventory.reduce(BookingMethod::{method}, units, &spec);")

    lines.append(f"")
    lines.append(f"    // Verify invariant would have been violated")
    lines.append(f"    // assert!(...);")
    lines.append(f"}}")

    return "\n".join(lines)


def generate_validation_test(trace: dict, test_name: str) -> str:
    """Generate a Rust test for a ValidationErrors trace."""
    states = trace.get("states", [])
    invariant = trace.get("invariant_violated", "Unknown")

    lines = [
        f"/// Generated from TLA+ counterexample",
        f"/// Invariant violated: {invariant}",
        f"#[test]",
        f"fn {test_name}() {{",
        f"    let mut validator = Validator::new();",
        f"",
    ]

    for state in states:
        action = state.get("action", "Unknown")
        vars = state.get("variables", {})

        if action == "Init":
            lines.append(f"    // Initial state")
            continue

        if "Error" in action or "Add" in action:
            lines.append(f"    // Action: {action}")
            if "errors" in vars:
                errors = vars["errors"]
                if isinstance(errors, dict) and errors.get("type") == "set":
                    for err in errors.get("elements", []):
                        if isinstance(err, dict) and err.get("type") == "record":
                            fields = err.get("fields", {})
                            code = fields.get("code", "E1001")
                            lines.append(f"    // Error: {code}")

    lines.append(f"")
    lines.append(f"    // Verify expected errors")
    lines.append(f"    // let errors = validator.validate(&ledger);")
    lines.append(f"    // assert!(...);")
    lines.append(f"}}")

    return "\n".join(lines)


def generate_test_from_trace(trace: dict, test_num: int = 1) -> str:
    """Generate a Rust test from a TLA+ trace."""
    spec_name = trace.get("spec_name", "Unknown")
    invariant = trace.get("invariant_violated", "unknown")
    test_name = f"tla_trace_{spec_name.lower()}_{invariant.lower()}_{test_num}"
    # Sanitize test name
    test_name = "".join(c if c.isalnum() or c == "_" else "_" for c in test_name)

    if spec_name == "BookingMethods":
        return generate_booking_test(trace, test_name)
    elif spec_name == "ValidationErrors":
        return generate_validation_test(trace, test_name)
    else:
        # Generic test template
        return generate_generic_test(trace, test_name)


def generate_generic_test(trace: dict, test_name: str) -> str:
    """Generate a generic Rust test from a TLA+ trace."""
    states = trace.get("states", [])
    invariant = trace.get("invariant_violated", "Unknown")
    property_violated = trace.get("property_violated")

    lines = [
        f"/// Generated from TLA+ counterexample",
        f"/// Spec: {trace.get('spec_name', 'Unknown')}",
    ]

    if invariant:
        lines.append(f"/// Invariant violated: {invariant}")
    if property_violated:
        lines.append(f"/// Property violated: {property_violated}")

    lines.extend([
        f"#[test]",
        f"fn {test_name}() {{",
    ])

    for i, state in enumerate(states):
        action = state.get("action", "Unknown")
        state_num = state.get("state_num", i)

        lines.append(f"")
        lines.append(f"    // State {state_num}: {action}")

        for var_name, var_value in state.get("variables", {}).items():
            rust_value = tla_to_rust_value(var_value, 1)
            lines.append(f"    // {var_name} = {rust_value}")

    lines.extend([
        f"",
        f"    // TODO: Implement test based on trace",
        f"    todo!(\"Implement test from TLA+ trace\");",
        f"}}",
    ])

    return "\n".join(lines)


def generate_test_module(traces: list[dict], module_name: str = "tla_traces") -> str:
    """Generate a complete Rust test module from multiple traces."""
    # Collect all spec names
    spec_names = set(t.get("spec_name", "Unknown") for t in traces)

    # Build imports
    imports = set()
    setups = []

    for spec_name in spec_names:
        if spec_name in SPEC_TEMPLATES:
            imports.add(SPEC_TEMPLATES[spec_name]["imports"])
            setups.append(SPEC_TEMPLATES[spec_name]["setup"])

    lines = [
        f"//! Auto-generated tests from TLA+ counterexample traces",
        f"//! ",
        f"//! Generated by: scripts/trace_to_rust_test.py",
        f"//! ",
        f"//! DO NOT EDIT MANUALLY",
        f"",
        f"#![allow(dead_code)]",
        f"#![allow(unused_imports)]",
        f"#![allow(unused_variables)]",
        f"",
    ]

    for imp in imports:
        lines.append(imp.strip())

    lines.append("")

    for setup in setups:
        lines.append(setup.strip())
        lines.append("")

    # Generate tests
    for i, trace in enumerate(traces, 1):
        test_code = generate_test_from_trace(trace, i)
        lines.append("")
        lines.append(test_code)

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Generate Rust tests from TLA+ traces"
    )
    parser.add_argument(
        "traces",
        nargs="+",
        type=Path,
        help="JSON trace files"
    )
    parser.add_argument(
        "--module", "-m",
        default="tla_traces",
        help="Rust module name"
    )
    parser.add_argument(
        "--output", "-o",
        type=Path,
        help="Output Rust file (default: stdout)"
    )

    args = parser.parse_args()

    # Load all traces
    traces = []
    for trace_path in args.traces:
        with open(trace_path) as f:
            trace = json.load(f)
            traces.append(trace)

    # Generate module
    rust_code = generate_test_module(traces, args.module)

    if args.output:
        args.output.write_text(rust_code)
        print(f"Generated {args.output}", file=sys.stderr)
    else:
        print(rust_code)


if __name__ == "__main__":
    main()
