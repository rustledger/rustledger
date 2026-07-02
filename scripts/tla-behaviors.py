#!/usr/bin/env python3
"""TLC state-graph dump → exhaustive behavior corpus (model-based testing).

The TLA+ specs use tiny bounds (e.g. Conservation.cfg: MaxUnits=3,
MaxOperations=6 → 207 states / 678 transitions), so TLC can enumerate the
COMPLETE state graph. This script turns that graph into an *edge-coverage*
behavior corpus: one behavior per transition, each = (shortest path from Init
to the source state) + the transition. Replaying every behavior against the
real implementation and checking the abstraction of the implementation state
against the spec state at every step gives exhaustive conformance up to the
model bound — strictly stronger than sampled property tests, one notch below
a full refinement proof.

Corpora are committed (spec/tla/behaviors/<Spec>.json) so the Rust replay
test (`crates/rustledger-core/tests/tla_behavior_replay.rs`) is hermetic — it
runs in plain `cargo test` with no Java/TLC. CI keeps spec and corpus in
lockstep: the TLA+ workflow regenerates each corpus from its spec and fails
on drift.

Output is CANONICAL: node ids never appear; adjacency, path tie-breaks, and
behavior order derive from sorted state/action content, and action semantics
derive from STATE DELTAS (never from dot edge labels, whose syntax varies
across TLC versions). Stutter self-loops are skipped.

Supported specs (see SPECS): Conservation (legacy compact int steps) and the
booking-method family — FIFOCorrect, LIFOCorrect, HIFOCorrect, STRICTCorrect,
AVERAGECorrect, NONECorrect — whose steps are `[action, params, state]`.

Usage:
    tlc -config spec/tla/FIFOCorrect.cfg -deadlock \\
        -dump dot,actionlabels states spec/tla/FIFOCorrect.tla
    python3 scripts/tla-behaviors.py --spec FIFOCorrect < states.dot \\
        > spec/tla/behaviors/FIFOCorrect.json

    python3 scripts/tla-behaviors.py --self-test
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import deque

NODE_RE = re.compile(r'^(-?\d+)\s+\[label="(.*)"(,style = filled)?\]')
EDGE_RE = re.compile(r"^(-?\d+)\s*->\s*(-?\d+)")


# ---------------------------------------------------------------------------
# TLA+ value parsing (records, sequences, sets, ints, strings)
# ---------------------------------------------------------------------------


def split_tla_list(s: str) -> list[str]:
    """Split a TLA+ comma-separated list, respecting nested structures.

    Angle brackets count only as the two-character sequence tokens `<<`/`>>`
    — a bare `>` appears inside the record-field arrow `|->` and must NOT
    affect nesting depth.
    """
    elements: list[str] = []
    current: list[str] = []
    depth = 0
    in_string = False
    i = 0
    while i < len(s):
        c = s[i]
        if c == '"' and (i == 0 or s[i - 1] != "\\"):
            in_string = not in_string
            current.append(c)
        elif in_string:
            current.append(c)
        elif s[i : i + 2] == "<<":
            depth += 1
            current.append("<<")
            i += 2
            continue
        elif s[i : i + 2] == ">>":
            depth -= 1
            current.append(">>")
            i += 2
            continue
        elif c in "{[(":
            depth += 1
            current.append(c)
        elif c in "}])":
            depth -= 1
            current.append(c)
        elif c == "," and depth == 0:
            elements.append("".join(current).strip())
            current = []
        else:
            current.append(c)
        i += 1
    if current:
        elements.append("".join(current).strip())
    return elements


def parse_tla_value(value_str: str):
    """Parse a TLA+ value: int, string, record → dict, sequence/set → list.

    Sets are unordered, so their elements are canonically sorted; sequences
    keep their order.
    """
    value_str = value_str.strip()
    if re.match(r"^-?\d+$", value_str):
        return int(value_str)
    if value_str.startswith('"') and value_str.endswith('"'):
        return value_str[1:-1]
    # Dot labels escape string quotes: \"none\".
    if value_str.startswith('\\"') and value_str.endswith('\\"'):
        return value_str[2:-2]
    if value_str.startswith("<<") and value_str.endswith(">>"):
        inner = value_str[2:-2].strip()
        return [parse_tla_value(e) for e in split_tla_list(inner)] if inner else []
    if value_str.startswith("{") and value_str.endswith("}"):
        inner = value_str[1:-1].strip()
        elems = [parse_tla_value(e) for e in split_tla_list(inner)] if inner else []
        return sorted(elems, key=lambda e: json.dumps(e, sort_keys=True))
    if value_str.startswith("[") and value_str.endswith("]"):
        fields: dict = {}
        for part in split_tla_list(value_str[1:-1].strip()):
            if " |-> " in part:
                k, v = part.split(" |-> ", 1)
                fields[k.strip()] = parse_tla_value(v.strip())
        return fields
    return value_str


def parse_label(label: str) -> dict:
    """Parse a node label: `/\\ var = value` conjuncts joined by literal \\n.

    TLC pretty-prints long VALUES with embedded `\\n` + indentation, so a
    segment that does not start with `/\\` is a continuation of the previous
    conjunct's value and is rejoined before parsing.
    """
    conjuncts: list[str] = []
    for segment in label.split("\\n"):
        stripped = segment.strip()
        if stripped.startswith("/\\\\ "):
            conjuncts.append(stripped[4:])
        elif stripped.startswith("/\\ "):
            conjuncts.append(stripped[3:])
        elif conjuncts:
            conjuncts[-1] += " " + stripped
    variables: dict = {}
    for conjunct in conjuncts:
        if " = " in conjunct:
            k, v = conjunct.split(" = ", 1)
            variables[k.strip()] = parse_tla_value(v.strip())
    return variables


NODE_START_RE = re.compile(r'^-?\d+\s+\[label="')


def parse_dot(text: str):
    """Return (states: id → variables dict, init_ids, edges: [(src, dst)]).

    TLC wraps long node labels across PHYSICAL newlines (the conjunct
    separator inside a label is the two-character escape `\\n`), so a node
    definition is accumulated until its closing `"]` before parsing.
    """
    states: dict[str, dict] = {}
    init_ids: set[str] = set()
    edges: list[tuple[str, str]] = []
    pending: list[str] = []

    def try_node(line: str) -> bool:
        m = NODE_RE.match(line)
        if not m:
            return False
        variables = parse_label(m.group(2))
        if variables:
            states[m.group(1)] = variables
            if m.group(3):
                init_ids.add(m.group(1))
        return True

    for raw in text.splitlines():
        line = raw.strip()
        if pending:
            pending.append(line)
            joined = " ".join(pending)
            if try_node(joined):
                pending = []
            continue
        if "->" in line:
            m = EDGE_RE.match(line)
            if m:
                if m.group(1) != m.group(2):  # skip stutter self-loops
                    edges.append((m.group(1), m.group(2)))
                continue
        if try_node(line):
            continue
        if NODE_START_RE.match(line):
            pending = [line]  # label wrapped across physical lines
    return states, init_ids, edges


# ---------------------------------------------------------------------------
# Spec registry: per spec, the required state variables and a `derive`
# function turning a (src, dst) state pair into a replayable step. Semantics
# always come from the state delta, never from edge labels.
# ---------------------------------------------------------------------------


def canon(v) -> str:
    return json.dumps(v, sort_keys=True, separators=(",", ":"))


def _totals(lots: list, key: str) -> list:
    """Per-key unit totals over a lot sequence: sorted [[key, units], ...].

    The abstraction deliberately collapses the spec's lot SEQUENCE to per-key
    totals: the implementation merges identical (cost, date) lots on add, so
    lot count is not preserved — but per-key unit totals are.
    """
    acc: dict = {}
    for lot in lots:
        acc[lot[key]] = acc.get(lot[key], 0) + lot["units"]
    return [[k, acc[k]] for k in sorted(acc)]


def _derive_conservation(src: dict, dst: dict) -> list:
    add = dst["totalAdded"] - src["totalAdded"]
    red = dst["totalReduced"] - src["totalReduced"]
    post = [dst["inventory"], dst["totalAdded"], dst["totalReduced"]]
    if add > 0 and red == 0:
        return ["Add", add, *post]
    if red > 0 and add == 0:
        return ["Reduce", red, *post]
    raise SystemExit(f"Conservation: underivable delta {src} -> {dst}")


def _derive_lot_selection(key: str):
    """FIFO/LIFO (key='date') and HIFO (key='cost'): AddLot / Reduce-one-lot."""

    def derive(src: dict, dst: dict) -> list:
        lots_s, lots_d = src["lots"], dst["lots"]
        state = {
            "totals": _totals(lots_d, key),
            "selected": dst["lastSelected"][key],
        }
        if len(lots_d) == len(lots_s) + 1:
            new = lots_d[-1]
            return ["AddLot", {"units": new["units"], key: new[key]}, state]
        if len(lots_d) == len(lots_s) - 1:
            units = sum(l["units"] for l in lots_s) - sum(l["units"] for l in lots_d)
            return ["Reduce", {"units": units, key: dst["lastSelected"][key]}, state]
        raise SystemExit(f"lot-selection({key}): underivable delta {src} -> {dst}")

    return derive


def _currency_lot_count(lots: list, currency) -> int:
    return sum(1 for l in lots if l["currency"] == currency)


def _derive_strict(src: dict, dst: dict) -> list:
    lots_s, lots_d = src["lots"], dst["lots"]
    state = {"totals": _totals(lots_d, "currency"), "result": dst["lastResult"]}
    if len(lots_d) == len(lots_s) + 1:
        new = lots_d[-1]
        return ["AddLot", {"units": new["units"], "currency": new["currency"]}, state]
    result = dst["lastResult"]
    if len(lots_d) == len(lots_s) - 1 and result == "success":
        removed = [
            c
            for c in {l["currency"] for l in lots_s}
            if _currency_lot_count(lots_s, c) == _currency_lot_count(lots_d, c) + 1
        ]
        return ["Reduce", {"currency": removed[0], "expect": "success"}, state]
    if lots_d == lots_s and result in ("no_match", "ambiguous"):
        # The attempted currency is not recorded in the state; any qualifying
        # currency replays identically (0 matching lots for no_match, >1 for
        # ambiguous). Domain is 1..MaxCurrency=2; smallest picked for
        # determinism.
        qualifying = [
            c
            for c in (1, 2)
            if (
                _currency_lot_count(lots_s, c) == 0
                if result == "no_match"
                else _currency_lot_count(lots_s, c) > 1
            )
        ]
        if qualifying:
            return ["Reduce", {"currency": qualifying[0], "expect": result}, state]
    raise SystemExit(f"STRICT: underivable delta {src} -> {dst}")


def _derive_average(src: dict, dst: dict) -> list:
    du = dst["totalUnits"] - src["totalUnits"]
    dc = dst["totalCostValue"] - src["totalCostValue"]
    # NOTE: the model computes the average cost with INTEGER division
    # (`\\div`), while the implementation divides exactly — the replay
    # therefore checks the units abstraction only; cost values are carried
    # for transparency, not asserted.
    state = {"units": dst["totalUnits"], "cost_value": dst["totalCostValue"]}
    if du > 0:
        if dc % du != 0:
            raise SystemExit(f"AVERAGE: non-integral add cost {src} -> {dst}")
        return ["AddUnits", {"units": du, "cost": dc // du}, state]
    if du < 0:
        return ["Reduce", {"units": -du}, state]
    raise SystemExit(f"AVERAGE: underivable delta {src} -> {dst}")


def _derive_none(src: dict, dst: dict) -> list:
    add = dst["totalAdded"] - src["totalAdded"]
    red = dst["totalReduced"] - src["totalReduced"]
    state = {
        "balance": dst["balance"],
        "added": dst["totalAdded"],
        "reduced": dst["totalReduced"],
    }
    if add > 0 and red == 0:
        return ["AddUnits", {"units": add}, state]
    if red > 0 and add == 0:
        return ["Reduce", {"units": red}, state]
    raise SystemExit(f"NONE: underivable delta {src} -> {dst}")


SPECS = {
    "Conservation": {
        "required": ("inventory", "totalAdded", "totalReduced"),
        "derive": _derive_conservation,
        "step_format": ["action", "units", "inventory", "totalAdded", "totalReduced"],
    },
    "FIFOCorrect": {
        "required": ("lots", "lastSelected"),
        "derive": _derive_lot_selection("date"),
        "step_format": ["action", "params", "state"],
    },
    "LIFOCorrect": {
        "required": ("lots", "lastSelected"),
        "derive": _derive_lot_selection("date"),
        "step_format": ["action", "params", "state"],
    },
    "HIFOCorrect": {
        "required": ("lots", "lastSelected"),
        "derive": _derive_lot_selection("cost"),
        "step_format": ["action", "params", "state"],
    },
    "STRICTCorrect": {
        "required": ("lots", "lastResult"),
        "derive": _derive_strict,
        "step_format": ["action", "params", "state"],
    },
    "AVERAGECorrect": {
        "required": ("totalUnits", "totalCostValue"),
        "derive": _derive_average,
        "step_format": ["action", "params", "state"],
    },
    "NONECorrect": {
        "required": ("balance", "totalAdded", "totalReduced"),
        "derive": _derive_none,
        "step_format": ["action", "params", "state"],
    },
}


# ---------------------------------------------------------------------------
# Behavior construction (edge coverage)
# ---------------------------------------------------------------------------


def build_behaviors(states: dict, init_ids: set, edges: list, derive) -> list:
    """One behavior per transition: shortest canonical path to src + the edge."""
    adjacency: dict[str, list[str]] = {}
    for src, dst in edges:
        if src in states and dst in states:
            adjacency.setdefault(src, []).append(dst)
    for src in adjacency:
        # Canonical order by derived step content — node ids never used.
        adjacency[src].sort(key=lambda d: canon(derive(states[src], states[d])))

    parent: dict[str, str | None] = {}
    queue: deque[str] = deque()
    for init in sorted(init_ids, key=lambda i: canon(states[i])):
        parent[init] = None
        queue.append(init)
    while queue:
        node = queue.popleft()
        for dst in adjacency.get(node, []):
            if dst not in parent:
                parent[dst] = node
                queue.append(dst)

    def path_to(node: str) -> list:
        rev = []
        cur = node
        while parent[cur] is not None:
            prev = parent[cur]
            rev.append(derive(states[prev], states[cur]))
            cur = prev
        rev.reverse()
        return rev

    behaviors = []
    for src, dst in edges:
        if src not in parent or dst not in states:
            continue  # unreachable or unparsed
        behaviors.append(path_to(src) + [derive(states[src], states[dst])])
    # Canonical order + dedup (distinct graph edges can yield identical
    # semantic step sequences).
    unique = sorted({canon(b) for b in behaviors})
    return [json.loads(b) for b in unique]


def generate(text: str, spec: str) -> dict:
    if spec not in SPECS:
        raise SystemExit(f"unknown spec {spec!r}; known: {', '.join(sorted(SPECS))}")
    config = SPECS[spec]
    all_states, init_ids, edges = parse_dot(text)
    states = {
        i: v for i, v in all_states.items() if all(r in v for r in config["required"])
    }
    init_ids &= set(states)
    if not states or not init_ids:
        raise SystemExit("no states / no initial state found in the dot dump")
    behaviors = build_behaviors(states, init_ids, edges, config["derive"])
    if len(states) > 1 and not behaviors:
        raise SystemExit(
            "parsed states but ZERO transitions/behaviors — the dot edge "
            "syntax of this TLC version doesn't match the parser; refusing "
            "to emit a vacuous corpus"
        )
    transitions = sum(1 for src, dst in edges if src in states and dst in states)
    return {
        "spec": spec,
        "state_vars": list(config["required"]),
        "step_format": config["step_format"],
        "coverage": {
            "states": len(states),
            "transitions": transitions,
            "behaviors": len(behaviors),
        },
        "behaviors": behaviors,
    }


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------

SELF_TEST_DOT = """\
strict digraph DiskGraph {
10 [label="/\\\\ inventory = 0\\n/\\\\ opCount = 0\\n/\\\\ totalAdded = 0\\n/\\\\ totalReduced = 0",style = filled]
10 -> 20 [label="Add",color="black",fontcolor="black"];
20 [label="/\\\\ inventory = 2\\n/\\\\ opCount = 1\\n/\\\\ totalAdded = 2\\n/\\\\ totalReduced = 0"];
20 -> 30 [label="Reduce",color="black",fontcolor="black"];
30 [label="/\\\\ inventory = 1\\n/\\\\ opCount = 2\\n/\\\\ totalAdded = 2\\n/\\\\ totalReduced = 1"];
20 -> 40 [label="Add",color="black",fontcolor="black"];
40 [label="/\\\\ inventory = 3\\n/\\\\ opCount = 2\\n/\\\\ totalAdded = 3\\n/\\\\ totalReduced = 0"];
}
"""

SELF_TEST_FIFO_DOT = """\
strict digraph DiskGraph {
1 [label="/\\\\ lots = <<>>\\n/\\\\ lastSelected = [date |-> 0, allDates |-> {}]",style = filled]
1 -> 2;
2 [label="/\\\\ lots = <<[units |-> 1, date |-> 2]>>\\n/\\\\ lastSelected = [date |-> 0, allDates |-> {}]"];
2 -> 3;
3 [label="/\\\\ lots = <<[units |-> 1, date |-> 2], [units |-> 1, date |-> 1]>>\\n/\\\\ lastSelected = [date |-> 0, allDates |-> {}]"];
3 -> 4;
4 [label="/\\\\ lots = <<[units |-> 1, date |-> 2]>>\\n/\\\\ lastSelected = [date |-> 1, allDates |-> {1, 2}]"];
}
"""

SELF_TEST_STRICT_DOT = """\
strict digraph DiskGraph {
1 [label="/\\\\ lots = <<>>\\n/\\\\ lastResult = \\"none\\"",style = filled]
1 -> 2;
2 [label="/\\\\ lots = <<[units |-> 1, currency |-> 1]>>\\n/\\\\ lastResult = \\"none\\""];
2 -> 3;
3 [label="/\\\\ lots = <<[units |-> 1, currency |-> 1]>>\\n/\\\\ lastResult = \\"no_match\\""];
2 -> 4;
4 [label="/\\\\ lots = <<>>\\n/\\\\ lastResult = \\"success\\""];
}
"""


def self_test() -> int:
    out = generate(SELF_TEST_DOT, "Conservation")
    assert out["coverage"] == {"states": 4, "transitions": 3, "behaviors": 3}
    assert [["Add", 2, 2, 2, 0], ["Reduce", 1, 1, 2, 1]] in out["behaviors"]
    # Canonical under dump reordering.
    lines = SELF_TEST_DOT.splitlines()
    reordered = "\n".join([lines[0]] + list(reversed(lines[1:-1])) + [lines[-1]])
    assert canon(generate(reordered, "Conservation")) == canon(out)
    # Label-stripping invariance (semantics derive from deltas).
    unlabeled = re.sub(r'\[label="\w+",?', "[", SELF_TEST_DOT)
    assert canon(generate(unlabeled, "Conservation")) == canon(out)

    fifo = generate(SELF_TEST_FIFO_DOT, "FIFOCorrect")
    assert fifo["coverage"]["behaviors"] == 3
    reduce_behavior = [
        ["AddLot", {"units": 1, "date": 2}, {"totals": [[2, 1]], "selected": 0}],
        ["AddLot", {"units": 1, "date": 1}, {"totals": [[1, 1], [2, 1]], "selected": 0}],
        ["Reduce", {"units": 1, "date": 1}, {"totals": [[2, 1]], "selected": 1}],
    ]
    assert reduce_behavior in fifo["behaviors"], fifo["behaviors"]

    strict = generate(SELF_TEST_STRICT_DOT, "STRICTCorrect")
    steps = [s for b in strict["behaviors"] for s in b]
    assert ["Reduce", {"currency": 2, "expect": "no_match"},
            {"totals": [[1, 1]], "result": "no_match"}] in steps, steps
    assert ["Reduce", {"currency": 1, "expect": "success"},
            {"totals": [], "result": "success"}] in steps, steps

    print("self-test: OK")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--spec", default="Conservation")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    out = generate(sys.stdin.read(), args.spec)
    json.dump(out, sys.stdout, indent=1)
    sys.stdout.write("\n")
    print(
        f"{args.spec}: {out['coverage']['states']} states, "
        f"{out['coverage']['transitions']} transitions, "
        f"{out['coverage']['behaviors']} behaviors",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
