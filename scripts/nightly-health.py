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


# Set when any `gh` invocation fails, so a broken token or a rate limit is
# reported as a tooling problem rather than silently read as "no runs found" —
# which would mark every workflow stale and replace a real report with a wrong
# one. Louder than raising: a partial answer plus a visible error still tells
# a human more than a stack trace in a job nobody watches.
_GH_FAILED: list[str] = []


def gh(*args: str, tolerate_missing: bool = False) -> str:
    proc = subprocess.run(["gh", *args], capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        detail = (proc.stderr or "").strip().splitlines()
        summary = detail[-1] if detail else f"exit {proc.returncode}"
        # A workflow present in the tree but not yet on the default branch has
        # no run history and 404s. That is "has not run yet", which the stale
        # path already reports correctly — not a broken token. Recording it as
        # a tooling failure would make every newly added scheduled workflow
        # raise a spurious alarm on its first night.
        if tolerate_missing and "not found" in summary.lower():
            return ""
        _GH_FAILED.append(f"gh {' '.join(args[:3])}: {summary}")
        print(f"::error::gh {' '.join(args[:3])} failed: {summary}")
    return proc.stdout


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
        # Accepts quoted AND unquoted crons, and strips a trailing comment.
        # Actions allows `cron: 0 8 * * *` bare, so a quoted-only regex would
        # silently omit a future workflow — the same drift the derivation
        # exists to prevent.
        crons = [
            m.strip().strip("'\"").strip()
            for m in re.findall(r"^\s*-\s*cron:\s*([^#\n]+)", text, re.M)
        ]
        crons = [c for c in crons if c]
        if crons:
            out[path.name] = cadence(crons[0])
    return out


def latest_scheduled_run(workflow: str) -> dict | None:
    raw = gh(
        "run", "list", "--repo", REPO, "--workflow", workflow,
        "--event", "schedule", "--limit", "1",
        "--json", "conclusion,status,createdAt,databaseId,url",
        tolerate_missing=True,
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
    broken: list[str] = []
    if not workflows:
        # An empty list would otherwise report a clean bill of health while
        # checking nothing — the exact shape of vacuous pass this exists to
        # prevent. Reported through the issue rather than as a job failure:
        # exiting non-zero here would make the alarm one more failing
        # scheduled workflow for nobody to notice, which is the problem it
        # exists to solve.
        print("::error::found no scheduled workflows; the derivation is broken")
        broken.append(
            "- **the workflow derivation returned nothing** — "
            "`scripts/nightly-health.py` found no `cron:` in `.github/workflows/*.yml`, "
            "so nothing below was actually checked"
        )

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

    problems = broken + failing + stale + [f"- tooling: {e}" for e in _GH_FAILED]
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
