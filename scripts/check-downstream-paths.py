#!/usr/bin/env python3
"""Fail if `Downstream (rustfava)` cannot see a change the embedder would feel.

`.github/workflows/downstream.yml` is path-filtered: it builds the wasip2
component and runs rustfava's suite against it only when a listed path changed.
The list was written by hand and fell behind the code. When this check was
added the component depended on 14 workspace crates and the filter named 8, so
a change to `rustledger-plugin`, `rustledger-ops`, `rustledger-importer`,
`rustledger-budget`, `rustledger-returns` or `rustledger-plugin-types` could
break the embedder with nothing to say so (#2332).

A missing row is worse than a red one. The workflow header invites the reader
to treat a green run as evidence the embedder is fine, and a PR that never ran
the job looks exactly like one that passed it.

The fix is not a longer hand-written list -- that is the thing that drifted --
but deriving the requirement from cargo and asserting agreement, per the
canonical-function discipline in CLAUDE.md.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

COMPONENT = "rustledger-ffi-component"
WORKFLOW = Path(".github/workflows/downstream.yml")


def workspace_closure(root: str) -> set[str]:
    """Workspace crates `root` is built from, including itself.

    Walks `cargo metadata --no-deps`, which lists each workspace member's
    dependencies without resolving the external graph: no network, no lockfile
    work, ~100ms. Dev-dependencies are excluded -- they are not compiled into
    the component -- while build-dependencies are kept, since a build script
    that changes can change the artifact.

    Verified against `cargo tree -p rustledger-ffi-component` when written:
    both report the same 14 crates.
    """
    meta = json.loads(
        subprocess.run(
            ["cargo", "metadata", "--format-version", "1", "--no-deps"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout
    )
    members = {p["name"]: p for p in meta["packages"]}
    if root not in members:
        sys.exit(f"{root} is not a workspace member; has it been renamed?")

    seen: set[str] = set()
    queue = [root]
    while queue:
        name = queue.pop()
        if name in seen or name not in members:
            continue
        seen.add(name)
        queue.extend(
            d["name"]
            for d in members[name]["dependencies"]
            if d["kind"] != "dev" and d["name"] in members
        )
    return seen


def filtered_paths(workflow: Path) -> list[str]:
    """The `paths:` entries of the workflow's `pull_request` trigger.

    Read with a line scan rather than a YAML parser so the check needs no
    dependency beyond the standard library, matching the other `check-*`
    scripts. The shape it reads is a flat list of quoted strings under
    `paths:`, which is what the file has; anything else ends the list and is
    reported rather than silently skipped.
    """
    lines = workflow.read_text(encoding="utf-8").splitlines()
    try:
        start = next(i for i, ln in enumerate(lines) if ln.strip() == "paths:")
    except StopIteration:
        sys.exit(f"no `paths:` block in {workflow}; has the trigger changed?")

    entries: list[str] = []
    for ln in lines[start + 1 :]:
        stripped = ln.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if not stripped.startswith("- "):
            break
        entries.append(stripped[2:].strip().strip('"').strip("'"))
    if not entries:
        sys.exit(f"`paths:` in {workflow} is empty")
    return entries


def main() -> int:
    closure = workspace_closure(COMPONENT)
    entries = filtered_paths(WORKFLOW)

    covered = {
        m.group(1)
        for m in (re.fullmatch(r"crates/([a-z0-9-]+)/\*\*", e) for e in entries)
        if m
    }
    missing = sorted(closure - covered)
    stale = sorted(covered - closure)

    for crate in stale:
        print(
            f"note: {WORKFLOW} lists crates/{crate}/** but {COMPONENT} no longer "
            f"depends on it; the job runs more often than it needs to"
        )

    if missing:
        print(
            f"error: {COMPONENT} is built from {len(closure)} workspace crates and "
            f"{WORKFLOW} covers {len(closure) - len(missing)} of them.\n"
            f"A change to one of these would not run Downstream (rustfava), and the "
            f"PR would show no row at all rather than a failing one:\n"
            + "".join(f"    crates/{c}/**\n" for c in missing)
            + "Add them to the `paths:` list, or drop the dependency."
        )
        return 1

    print(
        f"ok: {WORKFLOW} covers all {len(closure)} workspace crates "
        f"{COMPONENT} is built from"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
