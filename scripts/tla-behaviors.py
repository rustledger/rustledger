#!/usr/bin/env python3
"""TLC state-graph dump → exhaustive behavior corpus (model-based testing).

The TLA+ specs use tiny bounds (Conservation.cfg: MaxUnits=3, MaxOperations=6
→ 207 states / 678 transitions), so TLC can enumerate the COMPLETE state
graph. This script turns that graph into an *edge-coverage* behavior corpus:
one behavior per transition, each = (shortest path from Init to the source
state) + the transition. Replaying every behavior against the real
implementation and checking the abstraction of the implementation state
against the spec state at every step gives exhaustive conformance up to the
model bound — strictly stronger than sampled property tests, one notch below
a full refinement proof.

The corpus is committed (spec/tla/behaviors/<Spec>.json) so the Rust replay
test (`crates/rustledger-core/tests/tla_behavior_replay.rs`) is hermetic — it
runs in plain `cargo test` with no Java/TLC. CI keeps spec and corpus in
lockstep: the TLA+ workflow regenerates the corpus from the spec and fails on
drift.

Output is CANONICAL: node ids never appear; adjacency, path tie-breaks, and
behavior order are all derived from sorted state/action content, so
regeneration is byte-stable regardless of TLC's dump order or fingerprint
seed.

Usage:
    tlc -config spec/tla/Conservation.cfg -deadlock \\
        -dump dot,actionlabels states spec/tla/Conservation.tla
    python3 scripts/tla-behaviors.py --spec Conservation < states.dot \\
        > spec/tla/behaviors/Conservation.json

    python3 scripts/tla-behaviors.py --self-test
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import deque

NODE_RE = re.compile(r'^(-?\d+)\s+\[label="(.*)"(,style = filled)?\]')
EDGE_RE = re.compile(r'^(-?\d+)\s*->\s*(-?\d+)\s*(?:\[label="(\w+)")?')
VAR_RE = re.compile(r"/\\\\ (\w+) = (-?\d+)")

# The state variables that define a spec state, in canonical order. opCount is
# bookkeeping (the step index) and is excluded from the abstraction.
STATE_VARS = ("inventory", "totalAdded", "totalReduced")


def parse_dot(text: str):
    """Parse TLC's `-dump dot,actionlabels` output.

    Returns (states, init_ids, edges): states maps node id → state tuple,
    init_ids is the set of initial-state node ids, edges is a list of
    (src id, dst id, action name).
    """
    states: dict[str, tuple] = {}
    init_ids: set[str] = set()
    edges: list[tuple[str, str, str]] = []
    for line in text.splitlines():
        line = line.strip()
        m = EDGE_RE.match(line)
        if m:
            edges.append((m.group(1), m.group(2), m.group(3)))
            continue
        m = NODE_RE.match(line)
        if m:
            node_id, label, filled = m.group(1), m.group(2), m.group(3)
            variables = {k: int(v) for k, v in VAR_RE.findall(label)}
            if all(v in variables for v in STATE_VARS):
                states[node_id] = tuple(variables[v] for v in STATE_VARS)
                if filled:
                    init_ids.add(node_id)
    return states, init_ids, edges


def derive_action(src: tuple, dst: tuple) -> tuple[str, int]:
    """Derive (action, units) from the state delta.

    TLC's dot edge syntax and action labelling vary across versions (the CI
    jar emitted edges the 1.7.4-tuned label regex didn't match, yielding an
    empty corpus), so semantics NEVER depend on the label: totalAdded grew →
    Add, totalReduced grew → Reduce.
    """
    _, add_s, red_s = src
    _, add_d, red_d = dst
    if add_d > add_s and red_d == red_s:
        return "Add", add_d - add_s
    if red_d > red_s and add_d == add_s:
        return "Reduce", red_d - red_s
    raise SystemExit(f"cannot derive action for delta {src} -> {dst}")


def step(src: tuple, dst: tuple) -> list:
    """Compact step encoding: [action, units, inventory', totalAdded', totalReduced']."""
    action, units = derive_action(src, dst)
    return [action, units, *dst]


def build_behaviors(states, init_ids, edges):
    """One behavior per transition: shortest canonical path to src, then the edge."""
    # Canonical adjacency: successors sorted by derived (action, units, dst).
    # Self-loops are stutter steps (some TLC versions emit them) — no-ops by
    # definition, skipped rather than fed to derive_action.
    adjacency: dict[str, list[str]] = {}
    for src, dst, _label in edges:
        if src != dst and src in states and dst in states:
            adjacency.setdefault(src, []).append(dst)
    for src in adjacency:
        adjacency[src].sort(key=lambda d: (*derive_action(states[src], states[d]), states[d]))

    # BFS shortest paths from the initial state(s), canonical tie-break by
    # visiting successors in the sorted adjacency order.
    parent: dict[str, str | None] = {}
    queue: deque[str] = deque()
    for init in sorted(init_ids, key=lambda i: states[i]):
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
            rev.append(step(states[prev], states[cur]))
            cur = prev
        rev.reverse()
        return rev

    behaviors = []
    for src, dst, _label in edges:
        if src == dst or src not in parent or dst not in states:
            continue  # stutter self-loop, unreachable, or unparsed
        behaviors.append(path_to(src) + [step(states[src], states[dst])])
    # Canonical order + dedup (distinct edges can yield identical behaviors
    # when several graph edges share the same semantic step sequence).
    unique = sorted({json.dumps(b, separators=(",", ":")) for b in behaviors})
    return [json.loads(b) for b in unique]


def generate(text: str, spec: str) -> dict:
    states, init_ids, edges = parse_dot(text)
    if not states or not init_ids:
        raise SystemExit("no states / no initial state found in the dot dump")
    behaviors = build_behaviors(states, init_ids, edges)
    if len(states) > 1 and not behaviors:
        raise SystemExit(
            "parsed states but ZERO transitions/behaviors — the dot edge "
            "syntax of this TLC version doesn't match the parser; refusing "
            "to emit a vacuous corpus"
        )
    # Count only semantic transitions (no stutter self-loops, both endpoints
    # parsed) so the byte-diff lockstep check is stable across TLC versions
    # that do/don't emit self-loop edges.
    transitions = sum(
        1 for src, dst, _label in edges if src != dst and src in states and dst in states
    )
    return {
        "spec": spec,
        "state_vars": list(STATE_VARS),
        "step_format": ["action", "units", *STATE_VARS],
        "coverage": {
            "states": len(states),
            "transitions": transitions,
            "behaviors": len(behaviors),
        },
        "behaviors": behaviors,
    }


# ---------------------------------------------------------------------------
# Self-test: a hand-checked 4-state mini graph.
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


def self_test() -> int:
    out = generate(SELF_TEST_DOT, "Mini")
    assert out["coverage"]["states"] == 4, out["coverage"]
    assert out["coverage"]["transitions"] == 3
    assert out["coverage"]["behaviors"] == 3
    # The Reduce edge's behavior: Add 2, then Reduce 1.
    assert ["Add", 2, 2, 2, 0] in [b[0] for b in out["behaviors"]]
    assert [["Add", 2, 2, 2, 0], ["Reduce", 1, 1, 2, 1]] in out["behaviors"]
    # Canonical: regenerating from a reordered dump is byte-identical.
    lines = SELF_TEST_DOT.splitlines()
    reordered = "\n".join([lines[0]] + list(reversed(lines[1:-1])) + [lines[-1]])
    assert json.dumps(generate(reordered, "Mini"), sort_keys=True) == json.dumps(
        out, sort_keys=True
    ), "output must be canonical under dump reordering"
    # Version-agnosticism: stripping the action labels entirely (as other
    # TLC versions' dot dumps do) must yield the identical corpus, because
    # semantics are derived from state deltas, never from labels.
    import re as _re
    unlabeled = _re.sub(r'\[label="\w+",?', "[", SELF_TEST_DOT)
    assert json.dumps(generate(unlabeled, "Mini"), sort_keys=True) == json.dumps(
        out, sort_keys=True
    ), "unlabeled edges must produce the identical corpus"

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
