#!/usr/bin/env python3
"""Guardrail: keep the crates.io publish list in sync with the workspace.

`release-publish.yml` publishes a hand-maintained `CRATES=( ... )` array to
crates.io. If a new publishable crate is added to the workspace but not to that
array, the release silently skips it — and any crate that depends on it then
fails to publish ("failed to select a version for <crate>"). That is exactly
what broke the v0.16.0 release (rustledger-completion was missing).

Fails (exit 1) if the set of publishable workspace crates does not match the
CRATES array. Pure stdlib so it runs identically in CI and locally.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys

WORKFLOW = ".github/workflows/release-publish.yml"


def publishable_crates() -> set[str]:
    out = subprocess.check_output(
        ["cargo", "metadata", "--format-version", "1", "--no-deps"]
    )
    meta = json.loads(out)
    # `publish == []` means `publish = false`; anything else is publishable.
    return {p["name"] for p in meta["packages"] if p.get("publish") != []}


def listed_crates() -> set[str]:
    text = open(WORKFLOW, encoding="utf-8").read()
    m = re.search(r"CRATES=\((.*?)\)", text, re.DOTALL)
    if not m:
        sys.exit(f"::error::could not find a CRATES=( ... ) array in {WORKFLOW}")
    return set(m.group(1).split())


def main() -> int:
    publishable = publishable_crates()
    listed = listed_crates()

    status = 0
    missing = sorted(publishable - listed)
    extra = sorted(listed - publishable)

    if missing:
        print(f"::error::Publishable crate(s) missing from the CRATES array in {WORKFLOW}:")
        for c in missing:
            print(f"  - {c}")
        print()
        print("Add each one to the array IN DEPENDENCY ORDER (dependencies before dependents).")
        print("If a crate is brand-new to crates.io, its FIRST publish must be done MANUALLY")
        print("  cargo login <token> && cargo publish -p <crate>")
        print("and trusted publishing must be configured at")
        print("  https://crates.io/crates/<crate>/settings")
        print("OIDC cannot create a crate or push to one without trusted publishing set up.")
        status = 1

    if extra:
        print(f"::error::CRATES array lists name(s) that are not publishable workspace crates:")
        for c in extra:
            print(f"  - {c}")
        print("Remove them, or fix the crate's publish setting.")
        status = 1

    if status == 0:
        print(f"✓ crates.io publish list matches all {len(publishable)} publishable crates")
    return status


if __name__ == "__main__":
    raise SystemExit(main())
