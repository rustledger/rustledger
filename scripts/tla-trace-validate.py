#!/usr/bin/env python3
"""Validate implementation traces against a TLA+ spec (dual-direction MBT).

The behavior-replay suite checks model → implementation: every model behavior
is implemented correctly. This tool checks the DUAL, implementation → model:
traces produced by driving the REAL `Inventory` (see
`crates/rustledger-core/examples/conservation_trace_gen.rs`) are checked by
TLC against `Conservation.tla`'s transition relation — each recorded step must
satisfy `[][Conservation!Next]_vars`. An implementation transition the model
forbids fails the property. Together the two directions give two-sided
refinement checking (exhaustive model-side, sampled implementation-side).

Input (stdin or --traces FILE): one trace per line — a JSON array of
`[inventory, totalAdded, totalReduced, opCount]` states.

For each trace this script writes a small trace-following spec that drives
the spec variables through the recorded states and asserts the conformance
property, then runs TLC on it.

Usage:
    cargo run -q -p rustledger-core --example conservation_trace_gen -- \\
        --count 24 --seed 7 | python3 scripts/tla-trace-validate.py

    python3 scripts/tla-trace-validate.py --self-test   # incl. a negative check

TLC discovery: $TLC_CMD if set, else `tlc` on PATH, else
`java -jar ~/tla2tools.jar`.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC = REPO_ROOT / "spec" / "tla" / "Conservation.tla"

MODULE_TEMPLATE = """---- MODULE {name} ----
EXTENDS Integers, Sequences
CONSTANTS MaxUnits, MaxOperations
VARIABLES inventory, totalAdded, totalReduced, opCount, idx

specVars == <<inventory, totalAdded, totalReduced, opCount>>
vars == <<inventory, totalAdded, totalReduced, opCount, idx>>

C == INSTANCE Conservation

Trace == <<{trace}>>

Init ==
    /\\ idx = 1
    /\\ inventory = Trace[1].inventory
    /\\ totalAdded = Trace[1].totalAdded
    /\\ totalReduced = Trace[1].totalReduced
    /\\ opCount = Trace[1].opCount

Next ==
    /\\ idx < Len(Trace)
    /\\ idx' = idx + 1
    /\\ inventory' = Trace[idx'].inventory
    /\\ totalAdded' = Trace[idx'].totalAdded
    /\\ totalReduced' = Trace[idx'].totalReduced
    /\\ opCount' = Trace[idx'].opCount

Spec == Init /\\ [][Next]_vars

(* Every recorded implementation transition must be a legal step of the
   Conservation model (or a stutter on its variables). *)
ConformsToConservation == [][C!Next]_specVars
====
"""

CFG_TEMPLATE = """CONSTANTS
    MaxUnits = {max_units}
    MaxOperations = {max_ops}
SPECIFICATION Spec
PROPERTY ConformsToConservation
"""


def tlc_command() -> list[str]:
    if os.environ.get("TLC_CMD"):
        return os.environ["TLC_CMD"].split()
    if shutil.which("tlc"):
        return ["tlc"]
    jar = Path.home() / "tla2tools.jar"
    if jar.exists():
        return ["java", "-XX:+UseParallelGC", "-Xmx2g", "-jar", str(jar)]
    raise SystemExit("no TLC found: set TLC_CMD, or provide `tlc` / ~/tla2tools.jar")


def state_record(s: list[int]) -> str:
    return (
        f"[inventory |-> {s[0]}, totalAdded |-> {s[1]}, "
        f"totalReduced |-> {s[2]}, opCount |-> {s[3]}]"
    )


def validate_trace(states: list[list[int]], workdir: Path, name: str) -> bool:
    """Write the trace spec + cfg and TLC-check it. True = conforms."""
    deltas = [1]
    for prev, cur in zip(states, states[1:]):
        deltas.append(cur[1] - prev[1])
        deltas.append(cur[2] - prev[2])
    max_units = max(deltas)
    max_ops = max(1, states[-1][3])

    trace = ", ".join(state_record(s) for s in states)
    (workdir / f"{name}.tla").write_text(
        MODULE_TEMPLATE.format(name=name, trace=trace)
    )
    (workdir / f"{name}.cfg").write_text(
        CFG_TEMPLATE.format(max_units=max_units, max_ops=max_ops)
    )
    proc = subprocess.run(
        [*tlc_command(), "-deadlock", "-config", f"{name}.cfg", f"{name}.tla"],
        cwd=workdir,
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )
    ok = proc.returncode == 0 and "Error:" not in proc.stdout
    if not ok:
        print(f"--- {name}: NON-CONFORMING trace ---", file=sys.stderr)
        print(json.dumps(states), file=sys.stderr)
        for line in proc.stdout.splitlines():
            if "Error" in line or "violated" in line or line.startswith("State"):
                print(f"  {line}", file=sys.stderr)
    return ok


def run(traces: list[list[list[int]]]) -> int:
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        workdir = Path(tmp)
        shutil.copy(SPEC, workdir / "Conservation.tla")
        for i, states in enumerate(traces):
            if not validate_trace(states, workdir, f"Trace{i}"):
                failures += 1
    print(
        f"trace validation: {len(traces) - failures}/{len(traces)} traces conform",
        file=sys.stderr,
    )
    return 1 if failures else 0


# A hand-checked legal trace: Add 2, Reduce 1.
SELF_TEST_LEGAL = [[0, 0, 0, 0], [2, 2, 0, 1], [1, 2, 1, 2]]
# Conservation broken in the final state (inventory 2 ≠ 3 added − 1 reduced
# ... actually inventory jumps without a matching total change).
SELF_TEST_ILLEGAL = [[0, 0, 0, 0], [2, 2, 0, 1], [2, 2, 1, 2]]


def self_test() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        workdir = Path(tmp)
        shutil.copy(SPEC, workdir / "Conservation.tla")
        assert validate_trace(SELF_TEST_LEGAL, workdir, "SelfLegal"), (
            "a legal implementation trace must conform"
        )
        assert not validate_trace(SELF_TEST_ILLEGAL, workdir, "SelfIllegal"), (
            "TLC must REJECT a trace whose step violates the model — the "
            "harness would otherwise pass vacuously"
        )
    print("self-test: OK (legal trace accepted, illegal trace rejected)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--traces", help="file of trace lines (default: stdin)")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    text = Path(args.traces).read_text() if args.traces else sys.stdin.read()
    traces = [json.loads(line) for line in text.splitlines() if line.strip()]
    if not traces:
        raise SystemExit("no traces on input")
    return run(traces)


if __name__ == "__main__":
    sys.exit(main())
