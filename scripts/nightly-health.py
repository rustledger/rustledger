#!/usr/bin/env python3
"""Report scheduled workflows that are failing or have stopped running.

Miri failed every week from 2026-06-07 to 2026-07-26 and nobody noticed:
four genuine failures, then four six-hour timeouts reported as `cancelled`,
which reads like an infrastructure hiccup. Nothing in the repository turned
that into a signal a human would see. This does.

Two distinct failure modes, and the second is the one that hides:

  FAILING  the last scheduled run did not succeed.
  STALE    no scheduled run within its cadence. A cron that stops firing
           produces no failure at all — GitHub disables schedules on
           inactive repos, a bad `cron:` silently never matches, and a
           renamed workflow leaves the old one simply gone. Looking only
           at conclusions cannot see any of these.

The workflow list is DERIVED from `.github/workflows/*.yml`, never
hardcoded: a hardcoded list would omit whatever gets added next, which is
the same drift that let this go unnoticed.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

REPO = "rustledger/rustledger"
ISSUE_TITLE = "Scheduled workflow health"
MARKER = "<!-- nightly-health -->"

# Multiples of the nominal period before a workflow counts as stale. Generous
# on purpose: a single skipped run is noise (runner outages, a quiet repo),
# a fortnight of silence on a daily job is not.
STALENESS = {"daily": timedelta(days=3), "weekly": timedelta(days=17), "monthly": timedelta(days=70)}


def gh(*args: str) -> str:
    return subprocess.run(["gh", *args], capture_output=True, text=True, check=False).stdout


def cadence(cron: str) -> str:
    """Classify a cron into daily / weekly / monthly.

    Only the coarse period matters; the exact hour is irrelevant to whether a
    workflow has stopped running.
    """
    parts = cron.split()
    if len(parts) != 5:
        return "daily"
    _minute, _hour, dom, _month, dow = parts
    if dom != "*":
        return "monthly"
    if dow != "*":
        return "weekly"
    return "daily"


def scheduled_workflows() -> dict[str, str]:
    """Map workflow filename -> cadence, for every workflow with a `schedule:`."""
    out: dict[str, str] = {}
    for path in sorted(Path(".github/workflows").glob("*.yml")):
        text = path.read_text()
        # Deliberately a regex rather than a YAML parse: `on:` parses as the
        # boolean True in YAML 1.1, which has bitten this repo's own tooling.
        crons = re.findall(r"^\s*-\s*cron:\s*['\"]([^'\"]+)['\"]", text, re.M)
        if crons:
            out[path.name] = cadence(crons[0])
    return out


def latest_scheduled_run(workflow: str) -> dict | None:
    raw = gh(
        "run", "list", "--repo", REPO, "--workflow", workflow,
        "--event", "schedule", "--limit", "1",
        "--json", "conclusion,status,createdAt,databaseId,url",
    )
    try:
        runs = json.loads(raw)
    except json.JSONDecodeError:
        return None
    return runs[0] if runs else None


def main() -> int:
    now = datetime.now(timezone.utc)
    failing: list[str] = []
    stale: list[str] = []
    ok: list[str] = []

    workflows = scheduled_workflows()
    if not workflows:
        # An empty list would otherwise report a clean bill of health while
        # checking nothing — the exact shape of vacuous pass this exists to
        # prevent.
        print("::error::found no scheduled workflows; the derivation is broken")
        return 1

    for wf, period in sorted(workflows.items()):
        run = latest_scheduled_run(wf)
        if run is None:
            stale.append(f"- `{wf}` ({period}) — no scheduled run found at all")
            continue
        created = datetime.fromisoformat(run["createdAt"].replace("Z", "+00:00"))
        age = now - created
        concl = run["conclusion"] or run["status"]

        # A run still in flight is not a failure. `mutation.yml` starts at
        # 06:00 with a 180-minute cap, so at 08:00 it can legitimately still
        # be going — reading its `in_progress` status as a conclusion would
        # raise a false alarm every month, and an alarm that cries wolf gets
        # muted, which is how the original problem persisted.
        if run["status"] != "completed":
            ok.append(f"`{wf}` (still running)")
            print(f"{wf:24} {period:8} {'in flight':12} {age.days}d ago")
            continue

        if age > STALENESS[period]:
            stale.append(
                f"- `{wf}` ({period}) — last scheduled run {age.days}d ago "
                f"([{concl}]({run['url']}))"
            )
        elif concl != "success":
            failing.append(f"- `{wf}` ({period}) — last run **{concl}** ([log]({run['url']}))")
        else:
            ok.append(f"`{wf}`")
        print(f"{wf:24} {period:8} {concl:12} {age.days}d ago")

    problems = failing + stale
    body = [MARKER, ""]
    if problems:
        body.append(f"{len(problems)} scheduled workflow(s) need attention, as of {now:%Y-%m-%d %H:%M} UTC.")
        if failing:
            body += ["", "### Failing", *failing]
        if stale:
            body += [
                "", "### Stale (no recent scheduled run)",
                "",
                "A cron that stops firing produces no failure, so these are the ones that hide.",
                *stale,
            ]
        body += ["", "### Healthy", "", ", ".join(ok) if ok else "_none_"]
    body += [
        "", "---",
        "",
        "Maintained by `.github/workflows/nightly-health.yml`. Closes itself when everything is green.",
    ]
    text = "\n".join(body)

    existing = gh(
        "issue", "list", "--repo", REPO, "--state", "open",
        "--search", ISSUE_TITLE, "--json", "number,title,body", "--limit", "20",
    )
    try:
        issues = [i for i in json.loads(existing) if MARKER in (i.get("body") or "")]
    except json.JSONDecodeError:
        issues = []

    if problems:
        if issues:
            num = str(issues[0]["number"])
            gh("issue", "edit", num, "--repo", REPO, "--body", text)
            print(f"\nupdated issue #{num}: {len(problems)} problem(s)")
        else:
            url = gh("issue", "create", "--repo", REPO, "--title", ISSUE_TITLE, "--body", text).strip()
            print(f"\nopened {url}: {len(problems)} problem(s)")
    elif issues:
        num = str(issues[0]["number"])
        gh("issue", "comment", num, "--repo", REPO, "--body",
           "All scheduled workflows are green again. Closing automatically.")
        gh("issue", "close", num, "--repo", REPO)
        print(f"\nall green; closed issue #{num}")
    else:
        print("\nall scheduled workflows healthy")

    # Always exit 0: this reports, it does not gate. A red X here would be one
    # more failing scheduled workflow for nobody to notice.
    return 0


if __name__ == "__main__":
    sys.exit(main())
