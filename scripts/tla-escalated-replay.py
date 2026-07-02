#!/usr/bin/env python3
"""Regenerate behavior corpora at ESCALATED model bounds (depth beyond CI).

The committed corpora (`spec/tla/behaviors/*.json`) use each spec's small CI
bounds — exhaustive but shallow. This tool regenerates every corpus at larger
bounds into a scratch directory so the replay suite can be run against
orders-of-magnitude more behaviors without committing the (large) files:

    python3 scripts/tla-escalated-replay.py --out /tmp/escalated
    RUSTLEDGER_TLA_BEHAVIORS_DIR=/tmp/escalated \\
        cargo test -p rustledger-core --test tla_behavior_replay

Run weekly by `.github/workflows/tla-escalated.yml` — catches bound-sensitive
conformance issues the committed corpora can't reach.

Escalated bounds respect the replay/derive assumptions:
- STRICTCorrect keeps MaxUnits=1 (the replay reduces exactly one unit) and
  MaxCurrency=2 (the derive's currency domain);
- everything else scales units/lots/costs/dates/operations.

TLC discovery: $TLC_CMD, else `tlc`, else `java -jar ~/tla2tools.jar`.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
TLA_DIR = REPO / "spec" / "tla"
GENERATOR = REPO / "scripts" / "tla-behaviors.py"

# Per-spec escalated constants (only the named ones are overridden; the rest
# keep their committed .cfg values).
ESCALATED: dict[str, dict[str, int]] = {
    "Conservation": {"MaxUnits": 5, "MaxOperations": 8},
    "NONECorrect": {"MaxUnits": 5, "MaxOperations": 7},
    "FIFOCorrect": {"MaxLots": 4, "MaxUnits": 2, "MaxDate": 5},
    "LIFOCorrect": {"MaxLots": 4, "MaxUnits": 2, "MaxDate": 5},
    "HIFOCorrect": {"MaxLots": 4, "MaxUnits": 2, "MaxCost": 5},
    # MaxUnits/MaxCurrency deliberately NOT escalated (see module docs).
    "STRICTCorrect": {"MaxLots": 5},
    "AVERAGECorrect": {"MaxLots": 4, "MaxUnits": 3, "MaxCost": 4, "MaxOperations": 7},
}


def tlc_command() -> list[str]:
    if os.environ.get("TLC_CMD"):
        return os.environ["TLC_CMD"].split()
    if shutil.which("tlc"):
        return ["tlc"]
    jar = Path.home() / "tla2tools.jar"
    if jar.exists():
        return ["java", "-XX:+UseParallelGC", "-Xmx4g", "-jar", str(jar)]
    raise SystemExit("no TLC found: set TLC_CMD, or provide `tlc` / ~/tla2tools.jar")


def escalate_cfg(cfg_text: str, overrides: dict[str, int]) -> str:
    for name, value in overrides.items():
        cfg_text, n = re.subn(
            rf"^(\s*{name} = )\d+$", rf"\g<1>{value}", cfg_text, flags=re.M
        )
        if n != 1:
            raise SystemExit(f"constant {name} not found exactly once in cfg")
    return cfg_text


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", required=True, help="directory for escalated corpora")
    ap.add_argument("--only", help="escalate a single spec (default: all)")
    args = ap.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)

    # Drift guard: every committed corpus must have an escalation entry, so a
    # newly added spec cannot silently skip escalated coverage (the replay
    # gracefully skips missing corpora, which would otherwise turn a gap into
    # a vacuous green).
    committed = {p.stem for p in (TLA_DIR / "behaviors").glob("*.json")}
    missing = sorted(committed - set(ESCALATED))
    if missing:
        raise SystemExit(
            f"specs with committed corpora but no ESCALATED entry: {missing}"
        )

    specs = [args.only] if args.only else sorted(ESCALATED)
    for spec in specs:
        overrides = ESCALATED[spec]
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            shutil.copy(TLA_DIR / f"{spec}.tla", work / f"{spec}.tla")
            (work / f"{spec}.cfg").write_text(
                escalate_cfg((TLA_DIR / f"{spec}.cfg").read_text(), overrides)
            )
            print(f"=== {spec} @ {overrides} ===", file=sys.stderr)
            subprocess.run(
                [
                    *tlc_command(),
                    "-deadlock",
                    "-config",
                    f"{spec}.cfg",
                    "-dump",
                    "dot,actionlabels",
                    "states",
                    f"{spec}.tla",
                ],
                cwd=work,
                check=True,
                stdout=subprocess.DEVNULL,
                timeout=1200,
            )
            with (work / "states.dot").open() as dot, (out / f"{spec}.json").open(
                "w"
            ) as corpus:
                subprocess.run(
                    [sys.executable, str(GENERATOR), "--spec", spec],
                    stdin=dot,
                    stdout=corpus,
                    check=True,
                )
    print(f"escalated corpora written to {out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
