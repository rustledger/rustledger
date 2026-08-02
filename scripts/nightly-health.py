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
DEFAULT_BRANCH = "main"
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


def later_successful_manual_run(workflow: str, after: datetime) -> dict | None:
    """A `workflow_dispatch` run of `workflow` that succeeded after `after`.

    A scheduled workflow whose fix has already been verified by hand is a
    different state from one nobody has touched, and only reading
    `--event schedule` cannot tell them apart. Miri is the case that prompted
    this: its fix (#1901, #1904) was confirmed by dispatch on 2026-08-01 and
    finished in 3 minutes where it had been running to the 60-minute cap, but
    the report went on naming it a plain failure against a scheduled run from
    six days earlier. An alarm that keeps flagging something already fixed is
    one people learn to skim, which is the failure mode this whole script
    exists to prevent.

    Deliberately does NOT clear the entry. A green manual run says the code is
    fixed; it says nothing about whether the cron still fires, which is the
    other half of what this watches (see STALE). So it annotates and the
    workflow stays listed until a SCHEDULED run proves it.
    """
    raw = gh(
        "run", "list", "--repo", REPO, "--workflow", workflow,
        "--event", "workflow_dispatch", "--status", "success",
        # DEFAULT BRANCH ONLY. A dispatch on a feature branch proves nothing
        # about the scheduled run, which fires against `main`, so counting one
        # would produce exactly the false reassurance this annotation exists to
        # avoid: "a fix is likely already in" while `main` is still broken.
        "--branch", DEFAULT_BRANCH,
        "--limit", "1",
        "--json", "conclusion,createdAt,url",
        tolerate_missing=True,
    )
    try:
        runs = json.loads(raw)
    except json.JSONDecodeError:
        return None
    if not runs:
        return None
    created = datetime.fromisoformat(runs[0]["createdAt"].replace("Z", "+00:00"))
    return runs[0] if created > after else None


def self_test() -> int:
    """Prove the manual-run annotation fires when it should and not otherwise.

    This script is only useful if it is trusted, and the one thing that
    destroys trust is a wrong entry. The date guard in
    `later_successful_manual_run` is the part that can silently invert: get the
    comparison backwards and every long-fixed workflow grows a reassuring
    "already fixed" note that is not true. Nothing else in CI exercises this
    file, so it checks itself.
    """
    global gh
    real_gh = gh
    sched = datetime(2026, 7, 26, 6, 0, tzinfo=timezone.utc)

    # Records the argv so the test can assert the QUERY, not just the answer.
    # Stubbing only the return value would let a regression that drops
    # `--event`, `--status` or `--branch` keep this green while the live
    # annotation silently went wrong.
    seen_args: list[tuple[str, ...]] = []

    def stub(payload: str):
        def fake(*args, **kwargs):
            seen_args.append(args)
            return payload
        return fake

    cases = [
        ("newer manual success annotates",
         '[{"conclusion":"success","createdAt":"2026-08-01T01:53:00Z","url":"u"}]', True),
        ("older manual success does NOT annotate",
         '[{"conclusion":"success","createdAt":"2026-07-20T01:00:00Z","url":"u"}]', False),
        ("same instant does NOT annotate",
         '[{"conclusion":"success","createdAt":"2026-07-26T06:00:00Z","url":"u"}]', False),
        ("no manual runs at all", "[]", False),
        ("unparsable response", "not json", False),
    ]

    failures = 0
    for label, payload, expected in cases:
        gh = stub(payload)
        got = later_successful_manual_run("miri.yml", sched) is not None
        ok = got == expected
        failures += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} {label}: annotated={got} expected={expected}")

    # The query shape itself: these four flags are what make the answer mean
    # "a later manual run on the branch the cron uses".
    required = [
        ("--event", "workflow_dispatch"),
        ("--status", "success"),
        ("--branch", DEFAULT_BRANCH),
        ("--workflow", "miri.yml"),
    ]
    argv = seen_args[-1] if seen_args else ()
    for flag, value in required:
        ok = flag in argv and argv[argv.index(flag) + 1] == value
        failures += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} query passes {flag} {value}")

    gh = real_gh
    if failures:
        print(f"::error::nightly-health self-test: {failures} case(s) failed")
        return 1
    print("nightly-health self-test: all cases passed")
    return 0


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
            entry = f"- `{wf}` ({period}) — last scheduled run **{concl}** ([log]({run['url']}))"
            manual = later_successful_manual_run(wf, created)
            if manual:
                since = (now - datetime.fromisoformat(
                    manual["createdAt"].replace("Z", "+00:00")
                )).days
                entry += (
                    f", but a [manual run]({manual['url']}) has succeeded since "
                    f"({since}d ago) — a fix is likely already in; still listed "
                    "until a SCHEDULED run confirms the cron itself"
                )
            failing.append(entry)
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
    if "--self-test" in sys.argv:
        raise SystemExit(self_test())
    sys.exit(main())
