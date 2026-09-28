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

import contextlib
import io
import json
import re
import os
import subprocess
import tempfile
import sys
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path

REPO = "rustledger/rustledger"
DEFAULT_BRANCH = "main"
ISSUE_TITLE = "Scheduled workflow health"
MARKER = "<!-- nightly-health -->"
# Machine-readable list of workflows that looked stale on the PREVIOUS run.
#
# Every false alarm so far was transient: reported stale, correct again by hand
# minutes later. Nothing transient survives a night, so a stale claim has to be
# seen twice, a day apart, before it is stated as fact. The first sighting is
# published as a SUSPICION, which is both honest and self-clearing -- if the
# next run disagrees the entry simply disappears.
#
# This is the part that does not depend on knowing the mechanism. Asking for
# the runs in a `created>=` window (see `latest_scheduled_run`) defeats the one
# way the old listing was seen to lie; this defeats any way it can lie briefly.
SUSPECT_MARKER = "<!-- suspect:"

# Multiples of the nominal period before a workflow counts as stale. Generous
# on purpose: a single skipped run is noise (runner outages, a quiet repo),
# a fortnight of silence on a daily job is not.
STALENESS = {"daily": timedelta(days=3), "weekly": timedelta(days=17), "monthly": timedelta(days=70)}


class GhError(RuntimeError):
    """A `gh` invocation failed for a reason other than a missing workflow."""


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
        print(f"::error::gh {' '.join(args[:3])} failed: {summary}")
        # Raise rather than fall through. A failed call's stdout is empty, and
        # callers read empty as "no runs", which this reporter renders as
        # "stale" -- the exact claim it exists to make trustworthy. A transient
        # API error was therefore indistinguishable from a dead cron.
        raise GhError(summary)
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
    # Both extensions. Actions accepts `.yaml`, and a `*.yml`-only glob does not
    # report a `.yaml` workflow as unchecked — it never learns the file exists,
    # so the workflow is absent from every section including "Healthy". A
    # scheduled job silently outside the monitor is the worst outcome this
    # script has, and the repo happening to use `.yml` today is not a guarantee.
    paths = sorted(
        [*Path(".github/workflows").glob("*.yml"), *Path(".github/workflows").glob("*.yaml")]
    )
    for path in paths:
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
            # The TIGHTEST cadence among all of them, not the first one written.
            # A workflow with both a weekly and a daily cron was classified by
            # whichever came first in the file: a daily job read as weekly gets a
            # 17-day threshold, so its daily cron can die and keep firing weekly
            # for a fortnight before anything is said. Taking the shortest window
            # also makes that partial death detectable — runs arriving weekly do
            # not satisfy a daily schedule, and now the report can say so.
            out[path.name] = min(
                (cadence(c) for c in crons), key=lambda period: STALENESS[period]
            )
    return out


# Pause before re-asking whether a workflow has run. Long enough to outlast a
# momentary blip, short enough not to matter in a nightly job.
_REQUERY_DELAY_S = 5


def latest_scheduled_run(workflow: str, since: datetime) -> dict | None:
    """The newest scheduled run of `workflow` created since `since`, or None.

    Asks for EVERY scheduled run in the window (`created>=`, paginated) and
    picks the newest by timestamp. That one answer settles both questions the
    report asks: whether the cron fired within its cadence (any run at all),
    and whether it passed (the newest run's conclusion).

    It used to ask `gh run list --workflow W --event schedule --limit 10` for
    the newest runs instead, and that listing returns an arbitrary set of
    scheduled runs, not the newest ten. Three calls in a row on 2026-09-28 for
    `bench.yml`, a DAILY job, returned pages whose newest run was 09-25, 09-25
    and 09-28 (the right one), spanning up to two and a half months (#2462).
    Every false stale alarm this reporter filed came from such a page
    (#2232, #2281, #2301, #2356, #2448), and taking the max of the page or
    asking twice could not help: a max over the wrong rows is still wrong. The
    same page also decided the conclusion, so a newest run that FAILED could be
    left off it and an older success reported in its place -- a failure hidden,
    with nothing checking a success.

    The windowed query was right on every try of the same test, and it is what
    the stale verdict's second opinion already used. Asking it directly removes
    that second opinion: there is no longer a listing for it to contradict.

    The filter is date-granular, so the window is up to a day wider than asked.
    That errs toward NOT claiming staleness, the right direction for a report
    whose credibility is the thing being protected. It does not defeat a
    lagged view of the runs table, which is why a stale claim must also survive
    a night; see `SUSPECT_MARKER`.
    """
    day = since.strftime("%Y-%m-%d")

    def query() -> list[dict]:
        raw = gh(
            "api", "--paginate",
            f"repos/{REPO}/actions/workflows/{workflow}/runs"
            f"?event=schedule&created=%3E%3D{day}&per_page=100",
            "--jq",
            "{total: .total_count, runs: [.workflow_runs[] | {conclusion, status, "
            "createdAt: .created_at, databaseId: .id, url: .html_url}]}",
            tolerate_missing=True,
        )
        # One JSON object per PAGE, each carrying the query's `total_count`.
        # A tolerated 404 returns "", which genuinely means "has not run yet":
        # the stale path reports that correctly, so it is an empty list rather
        # than an error.
        runs: list[dict] = []
        total = 0
        for line in raw.splitlines():
            if not line.strip():
                continue
            # Output that will not parse is a different thing entirely. Reading
            # it as "no runs" would put an invalid response through the same
            # path as a dead cron.
            try:
                page = json.loads(line)
                runs.extend(page["runs"])
                total = max(total, int(page["total"]))
            except (json.JSONDecodeError, KeyError, TypeError, ValueError) as e:
                raise GhError(f"unparsable scheduled-run output: {line[:120]!r}") from e
        # The answer checks itself. Fewer rows than the API says exist is the
        # old listing's failure -- runs left out -- and the rows it did return
        # would decide both verdicts: a missing newest run is a false stale
        # claim or a hidden failure. So an incomplete answer is not an answer.
        # (More rows than `total` is a run created mid-pagination, and harmless.)
        if len(runs) < total:
            raise GhError(f"incomplete answer: {len(runs)} of {total} scheduled run(s)")
        return runs

    # Ask twice before concluding anything. An empty first answer is the input
    # to the report's most serious claim, and a second call costs one round
    # trip where a false alarm costs the report its credibility. A failed or
    # unparsable answer is retried on the same reasoning, and raised only if it
    # persists, so it lands in "could not be checked" rather than in a claim
    # about the workflow.
    runs: list[dict] = []
    error: GhError | None = None
    for attempt in (1, 2):
        if attempt == 2:
            time.sleep(_REQUERY_DELAY_S)
        try:
            runs, error = query(), None
        except GhError as e:
            runs, error = [], e
        if runs:
            break
    if error is not None:
        raise error
    if not runs:
        return None
    return max(runs, key=lambda r: r["createdAt"])


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

    # Fixtures that `main()` reads are timestamped RELATIVE TO NOW, because the
    # staleness rule they exercise is relative to now. An absolute date here
    # rots: the "going green clears the marker" case was written with a fresh
    # run at 2026-09-11T06:42Z, which passed the 3-day daily threshold on
    # 2026-09-14 and failed every night after, having tested nothing that
    # changed (#2334). `sched` above and the ordering fixtures below are
    # different -- they are compared against each other, never against now, so
    # they do not rot and are left as written.
    def ago(**kw: float) -> str:
        return f"{datetime.now(timezone.utc) - timedelta(**kw):%Y-%m-%dT%H:%M:%SZ}"

    fresh_run = ago(hours=1)
    stale_run = ago(days=21)

    # The re-query delay is real time, and two cases below drive an empty first
    # answer. `.github/workflows/nightly-health.yml` runs `--self-test` every
    # night, so leaving it in spends 10s a night waiting for nothing.
    real_sleep = time.sleep
    time.sleep = lambda _s: None  # type: ignore[assignment]

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

    # `latest_scheduled_run` reads one JSON object per PAGE, `{total, runs}`,
    # which is what its `gh api --paginate --jq` prints.
    def run(created: str, url: str, concl: str = "success",
            status: str = "completed") -> dict:
        return {"conclusion": concl, "status": status,
                "createdAt": created, "databaseId": 1, "url": url}

    def page(*runs: dict, total: int | None = None) -> str:
        return json.dumps({"total": len(runs) if total is None else total,
                           "runs": list(runs)})

    def run_line(created: str, url: str, concl: str = "success") -> str:
        return page(run(created, url, concl))

    since_t = datetime(2026, 9, 8, tzinfo=timezone.utc)

    # It must pick by TIMESTAMP, not by position: nothing promises the order,
    # so a fixture in the right order could not tell the two apart.
    # Two pages, the newest on neither's first row.
    gh = stub("\n".join([
        page(run("2026-09-08T02:52:42Z", "old"), run("2026-09-10T06:34:44Z", "new"),
             total=3),
        page(run("2026-09-09T02:00:00Z", "middle"), total=3),
    ]))
    picked = latest_scheduled_run("bench.yml", since_t)
    ok = picked is not None and picked["url"] == "new"
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} newest scheduled run wins regardless of order")

    gh = stub(page())
    ok = latest_scheduled_run("bench.yml", since_t) is None
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} no scheduled run in the window reports None")

    # The answer checks itself: fewer rows than `total_count` is the old
    # listing's failure, runs left out, so it must not become a verdict --
    # not "stale" when the page is empty, not "healthy" off an older row.
    for label, answer in [
        ("rows missing from a non-empty answer", page(run("2026-09-09T02:00:00Z", "old"),
                                                       total=4)),
        ("an empty answer that says runs exist", page(total=3)),
    ]:
        gh = stub(answer)
        try:
            latest_scheduled_run("bench.yml", since_t)
            ok = False
        except GhError:
            ok = True
        failures += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} an incomplete answer raises: {label}")

    # The query's SHAPE is what makes the answer trustworthy (#2462): the
    # windowed endpoint, every page of it, scheduled runs only. `gh run list
    # --event schedule` is the query that returned arbitrary pages; a
    # regression back to it, or one dropping the window or `--paginate`, must
    # fail here rather than resurface as a false alarm a week later.
    seen_args.clear()
    gh = stub(run_line("2026-09-10T06:34:44Z", "u"))
    latest_scheduled_run("bench.yml", since_t)
    argv = seen_args[-1] if seen_args else ()
    url = next((a for a in argv if "actions/workflows" in a), "")
    for ok, label in [
        (bool(argv) and argv[0] == "api", "asks the API, not `gh run list`"),
        ("--paginate" in argv, "reads every page of the window"),
        ("workflows/bench.yml/runs" in url, "names the workflow it was asked about"),
        ("event=schedule" in url, "counts scheduled runs only"),
        ("created=%3E%3D2026-09-08" in url, "limits to the staleness window"),
    ]:
        failures += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} scheduled-run query {label}")

    # An empty first answer must be re-asked before concluding a cron stopped.
    calls = {"n": 0}

    def flaky(*_args: str, **_kw: object) -> str:
        calls["n"] += 1
        return page() if calls["n"] == 1 else run_line("2026-09-10T06:37:00Z", "real")

    gh = flaky
    picked = latest_scheduled_run("bench.yml", since_t)
    ok = calls["n"] == 2 and picked is not None and picked["url"] == "real"
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} an empty answer is re-queried before reporting stale")

    # A failed query must not masquerade as "no runs", which the report renders
    # as stale -- the claim this whole script exists to make trustworthy.
    #
    # This drives the REAL `gh` through a failing subprocess rather than a stub
    # that raises. A stub raising GhError would only prove the exception
    # propagates, which is true whether or not `gh` raises it: the first draft
    # of this case passed with the fix reverted.
    gh = real_gh
    real_run = subprocess.run

    def failing_run(*_a: object, **_k: object) -> subprocess.CompletedProcess:
        return subprocess.CompletedProcess(
            args=["gh"], returncode=1, stdout="", stderr="HTTP 503: upstream is sad"
        )

    subprocess.run = failing_run  # type: ignore[assignment]
    # `gh` prints a `::error::` annotation on failure, which is right in a real
    # run and wrong here: it would paint a red annotation on the nightly job
    # every night for a PASSING test. A health reporter that cries wolf about
    # itself has the same credibility problem as one that cries wolf about a
    # workflow.
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            gh("run", "list", "--repo", "x/y")
        ok = False
    except GhError:
        ok = True
    finally:
        subprocess.run = real_run  # type: ignore[assignment]
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} a failed gh call raises rather than returning empty")

    # Output that will not parse is not evidence that a cron stopped. `gh` can
    # exit 0 and hand back an error page, and reading that as "no runs" puts an
    # invalid response through the same path as a dead cron.
    gh = lambda *_a, **_k: "<!DOCTYPE html><html>upstream error page</html>"  # noqa: E731
    try:
        latest_scheduled_run("bench.yml", since_t)
        ok = False
    except GhError:
        ok = True
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} unparsable output raises rather than reporting stale")

    # ...but an EMPTY answer still means "has not run yet". A tolerated 404
    # returns "", and raising on that would file every newly added workflow as
    # "could not be checked" instead of reporting it correctly as stale.
    gh = lambda *_a, **_k: ""  # noqa: E731
    try:
        ok = latest_scheduled_run("brand-new.yml", since_t) is None
    except GhError:
        # Without the guard this raises. Catch it so the case reports FAIL
        # rather than aborting the whole self-test on the way past.
        ok = False
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} an empty answer still reports no runs, not a failed check")

    # --- the two ways the old listing lied, through main() (#2462) ---
    #
    # Both drive the real main() with `gh run list --event schedule` answering
    # the way it was observed to: an old page missing the newest runs. Each
    # fails on the code before #2462, which trusted that page.
    def drive(api_runs: dict[str, str], listed: str,
              unreachable: frozenset[str] = frozenset()) -> dict[str, str]:
        seen: dict[str, str] = {"ops": ""}

        def fake(*args: str, **_kw: object) -> str:
            a = list(args)
            if a[0] == "issue" and a[1] == "list":
                return "[]"
            if a[0] == "issue":
                seen["ops"] += a[1] + ","
                if "--body" in a:
                    seen["body"] = a[a.index("--body") + 1]
                return "https://example/1"
            if a[0] == "run" and a[1] == "list":
                event = a[a.index("--event") + 1] if "--event" in a else ""
                return listed if event == "schedule" else "[]"
            if a[0] == "api":
                url = next(x for x in a if "actions/workflows" in x)
                wf = url.split("/workflows/")[1].split("/")[0]
                if wf in unreachable:
                    raise GhError("HTTP 504")
                return api_runs.get(wf, run_line(fresh_run, "fresh"))
            return ""

        global gh
        gh = fake
        with contextlib.redirect_stdout(io.StringIO()):
            main()
        return seen

    old_page = json.dumps([{
        "conclusion": "success", "status": "completed",
        "createdAt": stale_run, "databaseId": 1, "url": "old",
    }])

    # 1. A cron that fired is healthy, whatever the listing says. Before #2462
    # this read the old page as stale, the second opinion contradicted it, and
    # the contradiction was filed under "could not be checked", which opened
    # the tracking issue (#2301, #2448).
    seen = drive({}, old_page)
    ok = "create" not in seen["ops"] and "body" not in seen
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} an old listing page does not raise a false alarm")

    # 2. A failed newest run is reported, though the listing shows an older
    # success. Before #2462 the page decided the conclusion, so this read as
    # healthy: a real failure hidden.
    seen = drive({"bench.yml": page(
        run(ago(days=2), "older-success"),
        run(ago(hours=6), "newest-failure", concl="failure"),
    )}, old_page)
    body = seen.get("body", "")
    ok = "### Failing" in body and "newest-failure" in body
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} a failed newest run is reported, not hidden by an older success")

    # 3. A query that cannot be answered claims nothing either way: it lands in
    # "Could not be checked", and is neither suspected stale nor healthy. The
    # 2026-09-28 review hit a live HTTP 504 on exactly this call.
    seen = drive({}, old_page, unreachable=frozenset({"bench.yml"}))
    body = seen.get("body", "")
    ok = (
        "### Could not be checked" in body and "`bench.yml`" in body
        and f"{SUSPECT_MARKER}  -->" in body and "### Suspected stale" not in body
    )
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} an unreachable query claims nothing about the workflow")

    # --- the suspicion round-trip ---
    #
    # A stale claim is only stated as fact if the PREVIOUS report already
    # suspected it, so the marker this report writes must be readable by the
    # next one. That is a round trip through an issue body, and if it breaks in
    # either direction the failure is silent: an unreadable marker means every
    # night is a first sighting and a real dead cron is never escalated.
    roundtrip = [
        ("two workflows", {"bench.yml", "fuzz.yml"}),
        ("one workflow", {"bench.yml"}),
        ("none, cleared", set()),
    ]
    for label, names in roundtrip:
        rendered = f"{SUSPECT_MARKER} {','.join(sorted(names))} -->"
        body = f"{MARKER}\n\nsome report text\n\n---\n\n{rendered}"
        got = previous_suspects(body)
        ok = got == names
        failures += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} suspicion marker round-trips ({label}): {got or '{}'}")

    # A body with no marker at all is the pre-upgrade issue, and every body
    # written before this change looks like that. It must read as "nothing
    # suspected yet", not crash and not invent names.
    ok = previous_suspects(f"{MARKER}\n\nold style report\n") == set()
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} a body with no marker reads as no suspicions")

    ok = previous_suspects("") == set()
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} an empty body reads as no suspicions")

    # A lost issue body must not promote a transient to a published fact. It
    # yields no suspects, so everything starts over as a first sighting.
    def boom(*_a: object, **_k: object) -> str:
        raise GhError("HTTP 500")

    gh = boom
    with contextlib.redirect_stdout(io.StringIO()):
        ok = tracking_issue() is None
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} an unreadable previous report yields no suspicions")

    gh = stub("not json")
    ok = tracking_issue() is None
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} an unparsable issue list yields no suspicions")

    # A marker must not outlive the condition it records. The issue keeps its
    # body when closed, so a reopened one carrying last month's suspicions would
    # let a single sighting escalate to a stated fact.
    kept = f"{MARKER}\n\nthe report text\n\n---\n\n{SUSPECT_MARKER} bench.yml -->"
    cleared = clear_suspects(kept)
    ok = previous_suspects(cleared) == set() and "the report text" in cleared
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} closing clears the marker but keeps the report")

    # --- escalation, end to end through main() ---
    #
    # The pieces above are each checked in isolation, and that is not the same
    # as checking the behavior: the round trip could work, the query could
    # work, and main() could still put every entry in the wrong section.
    # This drives the real main() over a stubbed API and reads the body it
    # would publish, which is the only thing a person ever sees.
    def report_body(prior_body: str) -> str:
        written: dict[str, str] = {}

        def fake(*args: str, **_kw: object) -> str:
            a = list(args)
            if a[0] == "issue" and a[1] == "list":
                return json.dumps(
                    [{"number": 1, "title": ISSUE_TITLE, "body": prior_body}]
                ) if prior_body else "[]"
            if a[0] == "issue":
                if "--body" in a:
                    written["body"] = a[a.index("--body") + 1]
                return "https://example/1"
            if a[0] == "api":
                # bench.yml has no scheduled run in its window, so the only
                # thing holding the stale claim back is the one-night rule.
                url = next(x for x in a if "actions/workflows" in x)
                return page() if "/bench.yml/" in url else run_line(fresh_run, "u")
            return ""

        global gh
        gh = fake
        with contextlib.redirect_stdout(io.StringIO()):
            main()
        return written.get("body", "")

    first = report_body("")
    ok = "### Suspected stale" in first and "### Stale (no recent" not in first
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} a first sighting publishes a suspicion, not a stale claim")

    ok = f"{SUSPECT_MARKER} bench.yml -->" in first
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} the first report records the suspicion for the next run")

    second = report_body(first)
    ok = "### Stale (no recent" in second and "### Suspected stale" not in second
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} a second sighting escalates to a stale claim")

    # The escalation must be driven by the RECORDED suspicion, not by anything
    # else in the body. Feeding back a report whose marker was cleared has to
    # start the count over, or a cleared suspicion would silently stay armed.
    ok = "### Suspected stale" in report_body(first.replace(
        f"{SUSPECT_MARKER} bench.yml -->", f"{SUSPECT_MARKER}  -->"))
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} a cleared marker starts the count over")

    # ...and the same thing through main(), because testing `clear_suspects` on
    # its own leaves the WIRING unpinned: drop the edit call before the close
    # and every isolated case above still passes.
    closed: dict[str, str] = {}

    def fake_green(*args: str, **_kw: object) -> str:
        a = list(args)
        if a[0] == "issue" and a[1] == "list":
            return json.dumps([{
                "number": 1, "title": ISSUE_TITLE,
                "body": f"{MARKER}\n\nthe report text\n\n---\n\n{SUSPECT_MARKER} bench.yml -->",
            }])
        if a[0] == "issue":
            closed.setdefault("ops", "")
            closed["ops"] += a[1] + ","
            if a[1] == "edit" and "--body" in a:
                closed["body"] = a[a.index("--body") + 1]
            return "u"
        if a[0] == "api":
            return run_line(fresh_run, "u")
        return ""

    gh = fake_green
    with contextlib.redirect_stdout(io.StringIO()):
        main()
    ok = (
        previous_suspects(closed.get("body", "")) == set()
        and "the report text" in closed.get("body", "")
        and "close" in closed.get("ops", "")
    )
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} going green clears the marker before closing the issue")

    # --- the derivation, which decides what is monitored AT ALL ---
    #
    # A workflow missing from here is not reported as unchecked; it is absent
    # from every section, "Healthy" included, so nothing says it stopped being
    # watched. That is the quietest failure this script has, and both cases
    # below were live until this change.
    cwd = os.getcwd()
    with tempfile.TemporaryDirectory() as tmp:
        wf_dir = Path(tmp) / ".github" / "workflows"
        wf_dir.mkdir(parents=True)
        (wf_dir / "daily.yml").write_text(
            "on:\n  schedule:\n    - cron: '0 2 * * *'\n"
        )
        # Actions accepts `.yaml`; a `*.yml`-only glob never learns it exists.
        (wf_dir / "other.yaml").write_text(
            "on:\n  schedule:\n    - cron: '0 4 * * *'\n"
        )
        # Weekly written first, daily second. Classified by the first cron, the
        # daily one gets a 17-day window and can die for a fortnight unremarked.
        (wf_dir / "both.yml").write_text(
            "on:\n  schedule:\n    - cron: '0 5 * * 1'\n    - cron: '0 6 * * *'\n"
        )
        try:
            os.chdir(tmp)
            found = scheduled_workflows()
        finally:
            os.chdir(cwd)

    ok = "other.yaml" in found
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} a .yaml workflow is monitored, not silently skipped")

    ok = found.get("both.yml") == "daily"
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} a multi-cron workflow takes its tightest cadence "
          f"(got {found.get('both.yml')})")

    ok = found.get("daily.yml") == "daily" and len(found) == 3
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} every scheduled file is found ({len(found)} of 3)")

    gh = real_gh
    time.sleep = real_sleep  # type: ignore[assignment]
    if failures:
        print(f"::error::nightly-health self-test: {failures} case(s) failed")
        return 1
    print("nightly-health self-test: all cases passed")
    return 0


def previous_suspects(body: str) -> set[str]:
    """Workflows the previous report already suspected of being stale.

    Parsed out of the tracking issue rather than kept in a state file: the issue
    is already the reporter's memory between runs, and a file would have to live
    somewhere a nightly job can write.

    An unreadable or missing body yields an empty set, which means every
    suspicion starts over. That direction is deliberate — it delays a true alarm
    by one night, where the opposite would let a lost body promote a transient
    straight to a published fact.
    """
    for line in body.splitlines():
        line = line.strip()
        if line.startswith(SUSPECT_MARKER):
            inner = line[len(SUSPECT_MARKER):].rstrip(">").rstrip("-").strip()
            return {w for w in (p.strip() for p in inner.split(",")) if w}
    return set()


def clear_suspects(body: str) -> str:
    """Blank the suspicion marker in `body`, leaving the rest of the report intact.

    Written when the report goes green and the issue is closed. Without it the
    marker outlives the condition it records: a closed issue keeps whatever was
    suspected weeks ago, and reopening it makes the NEXT first sighting escalate
    straight to a stated fact — the "seen twice, a day apart" rule defeated by a
    sighting seen once, a month apart.

    The report text is left alone. It is the record of what was wrong, and the
    closing comment is not a reason to erase it.
    """
    out = [
        f"{SUSPECT_MARKER}  -->" if line.strip().startswith(SUSPECT_MARKER) else line
        for line in body.splitlines()
    ]
    return "\n".join(out)


def tracking_issue() -> dict | None:
    """The open tracking issue, or None if there is none or it cannot be read.

    ONE lookup, used both to read the previous run's suspicions and to decide
    where this run's report goes. It used to be two identical queries at
    opposite ends of `main`, which is a drift hazard with a silent failure: if
    the two ever disagreed about which issue is the tracking issue, suspicions
    would be read from one and written to another, no suspicion would ever match
    the next night, and nothing would escalate again. That fails toward never
    stating a fact, which is the direction nobody notices.

    Deliberately swallows every failure. The caller treats None as "no prior
    suspicions", which costs one night's escalation; raising here would take
    down a report that is otherwise fine.
    """
    try:
        raw = gh(
            "issue", "list", "--repo", REPO, "--state", "open",
            "--search", ISSUE_TITLE, "--json", "number,title,body", "--limit", "20",
        )
        issues = [i for i in json.loads(raw) if MARKER in (i.get("body") or "")]
    except (GhError, json.JSONDecodeError):
        return None
    return issues[0] if issues else None


def main() -> int:
    now = datetime.now(timezone.utc)
    failing: list[str] = []
    stale: list[str] = []
    suspected: list[str] = []
    unchecked: list[str] = []
    ok: list[str] = []

    # Read BEFORE the loop: a stale verdict is only published as fact if the
    # previous run reached the same verdict.
    issue = tracking_issue()
    prior = previous_suspects((issue or {}).get("body") or "")
    suspects_now: list[str] = []

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
        window = STALENESS[period]
        try:
            run = latest_scheduled_run(wf, now - window)
        except GhError as e:
            # An unanswered query is not evidence that a cron stopped. Say the
            # check did not happen rather than assert something about the
            # workflow, and keep going so one bad call does not cost the whole
            # report.
            print(f"::error::could not check {wf}: {e}")
            unchecked.append(f"- `{wf}` ({period}) — could not be checked: {e}")
            continue
        if run is None:
            # No scheduled run in the window: the stale candidate. Published as
            # fact only if the previous report already suspected it.
            suspects_now.append(wf)
            entry = f"- `{wf}` ({period}) — no scheduled run in the last {window.days}d"
            (stale if wf in prior else suspected).append(entry)
            print(f"{wf:24} {period:8} {'none':12} in {window.days}d")
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

        # A run inside the window means the cron is firing; whether it is
        # healthy is now the newest run's conclusion, from the same answer.
        if concl != "success":
            entry = f"- `{wf}` ({period}) — last scheduled run **{concl}** ([log]({run['url']}))"
            try:
                manual = later_successful_manual_run(wf, created)
            except GhError as e:
                # The annotation is a nicety; the failure entry above is the
                # point. Losing the whole report over it would be the worse
                # trade, and this call sits inside the loop, so an unguarded
                # raise discards every workflow already checked.
                print(f"::error::could not check manual runs of {wf}: {e}")
                manual = None
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

    problems = broken + failing + stale + suspected + unchecked
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
        if suspected:
            body += [
                "", "### Suspected stale (unconfirmed — first sighting)",
                "",
                # Explicit `+` rather than adjacent literals: every element here
                # is its own markdown line, so a missing comma would silently
                # merge two of them instead of failing. Matches the `unchecked`
                # section below.
                "Seen once. Every false alarm this reporter has filed was transient, "
                + "so one sighting is not stated as fact: if the next run agrees these "
                + "move to **Stale**, and if it does not they disappear on their own. "
                + "Nothing needs doing about an entry here yet.",
                *suspected,
            ]
        if unchecked:
            # Previously these were counted in the total but had no section, so
            # the headline claimed more workflows needed attention than the body
            # listed, with nothing to explain the gap.
            body += [
                "", "### Could not be checked",
                "",
                "The query failed, so nothing is claimed about these either way. "
                + "An unanswered query looks exactly like a cron that stopped, and "
                + "reporting it as stale is how this report loses its credibility.",
                *unchecked,
            ]
        body += ["", "### Healthy", "", ", ".join(ok) if ok else "_none_"]
    body += [
        "", "---",
        "",
        "Maintained by `.github/workflows/nightly-health.yml`. Closes itself when everything is green.",
        "",
        # Read back by the next run to decide whether a suspicion has been seen
        # twice. Written even when empty, so a cleared suspicion is recorded as
        # cleared rather than as a body this reporter failed to parse.
        f"{SUSPECT_MARKER} {','.join(sorted(suspects_now))} -->",
    ]
    text = "\n".join(body)

    # `gh` raises now, and every call below is a write to the tracking issue.
    # Letting one escape would end the run in a traceback and a red X, which
    # contradicts the contract just below and would make this reporter one more
    # failing scheduled workflow for nobody to notice. The table has already
    # been printed at this point, so the diagnosis survives either way.
    try:
        if problems:
            if issue:
                num = str(issue["number"])
                gh("issue", "edit", num, "--repo", REPO, "--body", text)
                print(f"\nupdated issue #{num}: {len(problems)} problem(s)")
            else:
                url = gh("issue", "create", "--repo", REPO, "--title", ISSUE_TITLE, "--body", text).strip()
                print(f"\nopened {url}: {len(problems)} problem(s)")
        elif issue:
            num = str(issue["number"])
            # Clear the marker BEFORE closing. A closed issue keeps its body,
            # and a reopened one carrying last month's suspicions would let a
            # single sighting escalate to a stated fact.
            gh("issue", "edit", num, "--repo", REPO,
               "--body", clear_suspects(issue.get("body") or ""))
            gh("issue", "comment", num, "--repo", REPO, "--body",
               "All scheduled workflows are green again. Closing automatically.")
            gh("issue", "close", num, "--repo", REPO)
            print(f"\nall green; closed issue #{num}")
        else:
            print("\nall scheduled workflows healthy")
    except GhError as e:
        print(f"::error::could not update the tracking issue: {e}")

    # Always exit 0: this reports, it does not gate. A red X here would be one
    # more failing scheduled workflow for nobody to notice.
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        raise SystemExit(self_test())
    sys.exit(main())
