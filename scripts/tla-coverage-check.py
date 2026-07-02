#!/usr/bin/env python3
"""TLA+ coverage lint — spec ↔ CI ↔ corpus ↔ docs must not drift.

The formal-verification stack has four layers that reference each other by
name: the specs (`spec/tla/*.tla` + `.cfg`), the CI model-check loop
(`.github/workflows/tla.yml`), the behavior corpora
(`spec/tla/behaviors/*.json` + their replay interpreters in
`crates/*/tests/tla_behavior_replay.rs`), and the mapping doc
(`spec/tla/RUST_MAPPING.md`). History shows the links rot silently: the
counterexample converter vanished in a cleanup leaving a dead workflow step,
`InductiveInvariants.cfg` outlived its module, and a stale trigger path
stopped the models running on inventory changes at all.

Checks:
  1. every `.cfg` has a matching `.tla` (no orphans);
  2. every `.tla` (with a `.cfg`) is model-checked by the tla.yml loop;
  3. every spec in the tla.yml loop exists on disk;
  4. every behavior corpus has a matching spec, an entry in the generator's
     SPECS registry, a mention in the replay test, and a row in
     RUST_MAPPING.md;
  5. every generator SPECS entry has a committed corpus.

Run: python3 scripts/tla-coverage-check.py   (exits non-zero on drift)
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
TLA_DIR = REPO / "spec" / "tla"
BEHAVIORS = TLA_DIR / "behaviors"
WORKFLOW = REPO / ".github" / "workflows" / "tla.yml"
# Replay interpreters are distributed by abstraction target (core inventory,
# validator lifecycle, query price DB) — a corpus counts as replayed if ANY
# of these loads it.
REPLAY_FILES = [
    REPO / "crates" / "rustledger-core" / "tests" / "tla_behavior_replay.rs",
    REPO / "crates" / "rustledger-validate" / "tests" / "tla_behavior_replay.rs",
    REPO / "crates" / "rustledger-query" / "tests" / "tla_behavior_replay.rs",
    REPO / "crates" / "rustledger-booking" / "tests" / "tla_behavior_replay.rs",
]
MAPPING = TLA_DIR / "RUST_MAPPING.md"
GENERATOR = REPO / "scripts" / "tla-behaviors.py"


# Specs deliberately NOT model-checked in CI — each needs a reason. A spec
# here that gains a passing role should move into the tla.yml loop instead.
KNOWN_UNCHECKED = {
    "BuggyInventory": "teaching spec with a deliberate bug — TLC fails it by design",
    "FIFOCheck": "historical: modeled the pre-fix FIFO insertion-order bug and "
    "produced the tla_fifo_bug_test.rs counterexample; superseded by FIFOCorrect",
    "SimpleInventory": "tutorial spec with an UNBOUNDED state space "
    "(totalAdded/totalReduced grow without limit) — TLC does not terminate on it",
}


def main() -> int:
    problems: list[str] = []

    tla_specs = {p.stem for p in TLA_DIR.glob("*.tla")}
    cfg_specs = {p.stem for p in TLA_DIR.glob("*.cfg")}
    workflow_text = WORKFLOW.read_text()
    replay_text = "\n".join(f.read_text() for f in REPLAY_FILES if f.exists())
    mapping_text = MAPPING.read_text()
    generator_text = GENERATOR.read_text()

    # The model-check loop's spec list (SPECS="A B C ..." possibly wrapped).
    m = re.search(r'SPECS="([^"]+)"', workflow_text)
    ci_specs = set(m.group(1).replace("\\", " ").split()) if m else set()
    if not ci_specs:
        problems.append("tla.yml: could not find the SPECS list in the model-check loop")

    # The generator's registry keys.
    registry_specs = set(re.findall(r'^    "(\w+)": \{', generator_text, re.M))

    # 1. Orphan configs.
    for orphan in sorted(cfg_specs - tla_specs):
        problems.append(f"orphan config: spec/tla/{orphan}.cfg has no matching .tla module")

    # 2 + 3. CI loop ↔ specs on disk.
    for spec in sorted((tla_specs & cfg_specs) - ci_specs - set(KNOWN_UNCHECKED)):
        problems.append(f"not model-checked: {spec}.tla/.cfg exist but {spec} is missing from tla.yml's SPECS loop")
    for spec in sorted(set(KNOWN_UNCHECKED) & ci_specs):
        problems.append(f"stale allowlist: {spec} is in KNOWN_UNCHECKED but IS model-checked — remove the entry")
    for spec in sorted(set(KNOWN_UNCHECKED) - tla_specs):
        problems.append(f"stale allowlist: {spec} is in KNOWN_UNCHECKED but has no spec on disk")
    for spec in sorted(ci_specs - tla_specs):
        problems.append(f"ghost CI entry: tla.yml model-checks {spec} but spec/tla/{spec}.tla does not exist")

    # 4. Corpora ↔ spec / registry / replay / mapping.
    for corpus in sorted(p.stem for p in BEHAVIORS.glob("*.json")):
        if corpus not in tla_specs:
            problems.append(f"corpus without spec: behaviors/{corpus}.json has no spec/tla/{corpus}.tla")
        if corpus not in registry_specs:
            problems.append(f"corpus without generator entry: {corpus} missing from tla-behaviors.py SPECS")
        if f'"{corpus}"' not in replay_text:
            problems.append(f"corpus without replay: {corpus} never loaded in tla_behavior_replay.rs")
        if corpus not in mapping_text:
            problems.append(f"corpus undocumented: {corpus} not mentioned in RUST_MAPPING.md")

    # 5. Registry entries without committed corpora.
    for spec in sorted(registry_specs - {p.stem for p in BEHAVIORS.glob("*.json")}):
        problems.append(f"generator entry without corpus: {spec} in SPECS but behaviors/{spec}.json not committed")

    if problems:
        print("TLA+ coverage drift detected:", file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        return 1
    print(
        f"tla-coverage-check: OK — {len(tla_specs)} specs, {len(ci_specs)} CI-checked, "
        f"{len(list(BEHAVIORS.glob('*.json')))} corpora, all cross-references intact"
    )
    for spec, reason in KNOWN_UNCHECKED.items():
        print(f"  (unchecked by design: {spec} — {reason})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
