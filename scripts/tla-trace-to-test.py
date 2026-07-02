#!/usr/bin/env python3
"""TLC counterexample → Rust regression-test converter.

Restores the counterexample-driven workflow from the formal-verification
roadmap ("every counterexample TLC finds becomes a pinned Rust regression
test" — the workflow that once produced
`crates/rustledger-core/tests/tla_fifo_bug_test.rs`).

Parses TLC model-checker output; when it contains an error trace, emits a
Rust `#[test]` skeleton:

- For the inventory/booking spec family (state variables like `inventory`,
  `lots`, `totalAdded`), consecutive states are diffed to infer Add/Reduce
  actions and concrete `Inventory` calls are generated.
- For any other spec, the full trace is embedded as comments around an
  `#[ignore]`d skeleton, so the counterexample is pinned verbatim and a human
  finishes the translation.

Usage:
    java -jar tla2tools.jar ... spec/tla/Foo.tla | tee foo.log
    python3 scripts/tla-trace-to-test.py --spec Foo < foo.log > foo_bug_test.rs

    python3 scripts/tla-trace-to-test.py --self-test
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field

# ---------------------------------------------------------------------------
# TLA+ value parsing (ported from the retired scripts/tla_trace_to_json.py)
# ---------------------------------------------------------------------------


def split_tla_list(s: str) -> list[str]:
    """Split a TLA+ comma-separated list, respecting nested structures."""
    elements: list[str] = []
    current: list[str] = []
    depth = 0
    in_string = False
    for i, c in enumerate(s):
        if c == '"' and (i == 0 or s[i - 1] != "\\"):
            in_string = not in_string
            current.append(c)
        elif in_string:
            current.append(c)
        elif c in "{[(<":
            depth += 1
            current.append(c)
        elif c in "}])>":
            depth -= 1
            current.append(c)
        elif c == "," and depth == 0:
            elements.append("".join(current).strip())
            current = []
        else:
            current.append(c)
    if current:
        elements.append("".join(current).strip())
    return elements


def parse_tla_value(value_str: str):
    """Parse a TLA+ value string into a Python value."""
    value_str = value_str.strip()
    if value_str == "TRUE":
        return True
    if value_str == "FALSE":
        return False
    if re.match(r"^-?\d+$", value_str):
        return int(value_str)
    if value_str.startswith('"') and value_str.endswith('"'):
        return value_str[1:-1]
    if value_str.startswith("{") and value_str.endswith("}"):
        inner = value_str[1:-1].strip()
        return [parse_tla_value(e) for e in split_tla_list(inner)] if inner else []
    if value_str.startswith("<<") and value_str.endswith(">>"):
        inner = value_str[2:-2].strip()
        return [parse_tla_value(e) for e in split_tla_list(inner)] if inner else []
    if value_str.startswith("[") and value_str.endswith("]"):
        inner = value_str[1:-1].strip()
        fields: dict = {}
        for part in split_tla_list(inner):
            if " |-> " in part:
                k, v = part.split(" |-> ", 1)
                fields[k.strip()] = parse_tla_value(v.strip())
        return fields
    if value_str.startswith("(") and value_str.endswith(")") and ":>" in value_str:
        inner = value_str[1:-1].strip()
        mapping: dict = {}
        for part in inner.split("@@"):
            if ":>" in part:
                k, v = part.split(":>", 1)
                mapping[str(parse_tla_value(k.strip()))] = parse_tla_value(v.strip())
        return mapping
    return value_str


# ---------------------------------------------------------------------------
# Trace parsing
# ---------------------------------------------------------------------------

STATE_HEADER = re.compile(r"^State (\d+): <?([^>\n]*)>?")
VAR_LINE = re.compile(r"^/\\ (\w+) = (.*)$")
ERROR_LINE = re.compile(r"^Error: (.*)$")


@dataclass
class TraceState:
    num: int
    action: str
    variables: dict = field(default_factory=dict)


@dataclass
class Trace:
    spec: str
    errors: list[str] = field(default_factory=list)
    states: list[TraceState] = field(default_factory=list)


def parse_tlc_output(text: str, spec: str) -> Trace:
    """Extract the error(s) and behavior trace from TLC stdout."""
    trace = Trace(spec=spec)
    current: TraceState | None = None
    pending_value: list[str] = []
    pending_var: str | None = None

    def flush_var():
        nonlocal pending_var, pending_value
        if current is not None and pending_var is not None:
            current.variables[pending_var] = parse_tla_value(" ".join(pending_value))
        pending_var, pending_value = None, []

    for line in text.splitlines():
        stripped = line.strip()
        m = ERROR_LINE.match(stripped)
        if m:
            trace.errors.append(m.group(1).strip())
            continue
        m = STATE_HEADER.match(stripped)
        if m:
            flush_var()
            current = TraceState(num=int(m.group(1)), action=m.group(2).strip())
            trace.states.append(current)
            continue
        m = VAR_LINE.match(stripped)
        if m:
            flush_var()
            pending_var = m.group(1)
            pending_value = [m.group(2).strip()]
            continue
        # Continuation of a multi-line value.
        if pending_var is not None and stripped and current is not None:
            if stripped.startswith("/\\"):
                continue  # defensive; matched above normally
            pending_value.append(stripped)
    flush_var()
    return trace


# ---------------------------------------------------------------------------
# Rust emission
# ---------------------------------------------------------------------------

INVENTORY_FAMILY_VARS = {"inventory", "lots", "totalAdded", "totalReduced"}


def is_inventory_family(trace: Trace) -> bool:
    if not trace.states:
        return False
    return bool(INVENTORY_FAMILY_VARS & set(trace.states[0].variables))


def snake(name: str) -> str:
    s = re.sub(r"[^A-Za-z0-9]+", "_", name)
    s = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "_", s)
    return s.lower().strip("_")


def emit_header(trace: Trace) -> list[str]:
    out = [
        f"//! Regression test derived from a TLC counterexample in {trace.spec}.tla",
        "//!",
        "//! Generated by `scripts/tla-trace-to-test.py`. The trace below is the",
        "//! exact behavior TLC reported; keep it in sync with any edits.",
        "//!",
    ]
    for err in trace.errors:
        out.append(f"//! TLC error: {err}")
    return out


def emit_trace_comment(state: TraceState, indent: str = "    ") -> list[str]:
    out = [f"{indent}// State {state.num}: {state.action or '<unnamed action>'}"]
    for k, v in state.variables.items():
        out.append(f"{indent}//   {k} = {v!r}")
    return out


def emit_inventory_test(trace: Trace) -> str:
    """Diff consecutive inventory-family states into Inventory calls."""
    lines = emit_header(trace)
    lines += [
        "",
        "use rust_decimal::Decimal;",
        "use rustledger_core::{Amount, BookingMethod, Cost, CostSpec, Inventory, Position};",
        "",
        "#[test]",
        f"fn tla_{snake(trace.spec)}_counterexample() {{",
        "    let mut inv = Inventory::new();",
    ]
    prev_inventory = None
    for state in trace.states:
        lines.append("")
        lines += emit_trace_comment(state)
        inv_val = state.variables.get("inventory")
        if isinstance(inv_val, int) and isinstance(prev_inventory, int):
            delta = inv_val - prev_inventory
            if delta > 0:
                lines += [
                    "    inv.add(Position::with_cost(",
                    f'        Amount::new(Decimal::from({delta}), "AAPL"),',
                    f'        Cost::new(Decimal::from(1), "USD"),',
                    "    ));",
                ]
            elif delta < 0:
                lines += [
                    "    inv.reduce(",
                    f'        &Amount::new(Decimal::from({delta}), "AAPL"),',
                    "        Some(&CostSpec::default()),",
                    "        BookingMethod::Fifo,",
                    '    ).expect("reduction from the TLC trace must book");',
                ]
        if isinstance(inv_val, int):
            prev_inventory = inv_val
    lines += [
        "",
        "    // Final-state invariant from the TLC error above — translate the",
        "    // violated invariant into a concrete assertion, then fix the code",
        "    // until it passes.",
    ]
    if prev_inventory is not None:
        lines.append(
            f'    assert_eq!(inv.units("AAPL"), Decimal::from({prev_inventory}), "final trace state");'
        )
    lines += ["    todo!(\"assert the violated invariant\");", "}", ""]
    return "\n".join(lines)


def emit_generic_test(trace: Trace) -> str:
    lines = emit_header(trace)
    lines += [
        "",
        "#[test]",
        '#[ignore = "translate the pinned TLC trace into executable steps"]',
        f"fn tla_{snake(trace.spec)}_counterexample() {{",
    ]
    for state in trace.states:
        lines += emit_trace_comment(state)
        lines.append("")
    lines += ["    todo!(\"drive the implementation through the states above\");", "}", ""]
    return "\n".join(lines)


def convert(text: str, spec: str) -> str | None:
    trace = parse_tlc_output(text, spec)
    if not trace.errors or not trace.states:
        return None
    if is_inventory_family(trace):
        return emit_inventory_test(trace)
    return emit_generic_test(trace)


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------

SELF_TEST_TRACE = """\
TLC2 Version 2.18
Error: Invariant ConservationInvariant is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\\ inventory = 0
/\\ totalAdded = 0
/\\ totalReduced = 0

State 2: <AddAmount line 30, col 5 to line 34, col 40 of module Conservation>
/\\ inventory = 3
/\\ totalAdded = 3
/\\ totalReduced = 0

State 3: <ReduceAmount line 36, col 5 to line 41, col 44 of module Conservation>
/\\ inventory = 1
/\\ totalAdded = 3
/\\ totalReduced = 1
"""

SELF_TEST_GENERIC = """\
Error: Invariant PadServed is violated.
State 1: <Initial predicate>
/\\ pads = <<>>
/\\ balances = {}

State 2: <AddPad>
/\\ pads = <<[account |-> "A", date |-> 1]>>
/\\ balances = {}
"""


def self_test() -> int:
    inv_out = convert(SELF_TEST_TRACE, "Conservation")
    assert inv_out is not None, "inventory-family trace must convert"
    for needle in [
        "tla_conservation_counterexample",
        "Invariant ConservationInvariant is violated",
        "inv.add(",
        "inv.reduce(",
        "State 3",
    ]:
        assert needle in inv_out, f"missing {needle!r} in inventory emission"

    gen_out = convert(SELF_TEST_GENERIC, "PadSpec")
    assert gen_out is not None, "generic trace must convert"
    for needle in ["#[ignore", "tla_pad_spec_counterexample", "AddPad", "pads ="]:
        assert needle in gen_out, f"missing {needle!r} in generic emission"

    clean = convert("TLC2 finished. No error.", "Conservation")
    assert clean is None, "clean run must produce no test"

    print("self-test: OK")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--spec", default="Spec", help="spec name for the generated test")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    out = convert(sys.stdin.read(), args.spec)
    if out is None:
        print("no TLC error trace found; nothing to convert", file=sys.stderr)
        return 1
    print(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
