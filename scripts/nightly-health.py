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
import subprocess
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
# This is the part that does not depend on knowing the mechanism. The
# `created>=` count defeats one specific way the listing can lie; this defeats
# any way it can lie briefly, which is every way observed so far.
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


# How many recent scheduled runs to fetch before picking the newest.
#
# More than one because the newest is chosen by comparing timestamps rather
# than by trusting list order (see `latest_scheduled_run`).
_RUN_PAGE = 10

# Pause before re-asking whether a workflow has run. Long enough to outlast a
# momentary blip, short enough not to matter in a nightly job.
_REQUERY_DELAY_S = 5


def latest_scheduled_run(workflow: str) -> dict | None:
    """The most recent scheduled run of `workflow`, by `createdAt`.

    Fetches a page and takes the MAXIMUM rather than the first element. On
    2026-09-03 this reported `bench.yml` as ten days stale while it had in fact
    run six hours earlier, and the run it linked was a real but old one -- so
    the lookup returned a stale entry rather than failing. The cause was not
    reproducible afterwards (the same `gh run list --limit 1` returned the
    correct run by hand), so this does not claim to fix a diagnosed bug: it
    removes the dependence on list ORDER, which is the only assumption that
    could have produced that output.

    That matters more here than the code size suggests. A health reporter
    exists to be believed; one that cries wolf gets muted, which is the failure
    it was written to prevent.
    """
    def query() -> list[dict]:
        raw = gh(
            "run", "list", "--repo", REPO, "--workflow", workflow,
            "--event", "schedule", "--limit", str(_RUN_PAGE),
            "--json", "conclusion,status,createdAt,databaseId,url",
            tolerate_missing=True,
        )
        # A tolerated 404 returns "". That genuinely means "has not run yet",
        # which the stale path already reports correctly, so it is an empty
        # list rather than an error.
        if not raw.strip():
            return []
        # Non-empty output that will not parse is a different thing entirely.
        # Reading it as "no runs" would put an invalid response through the
        # same path as a dead cron, which is the confusion this whole change
        # is about.
        try:
            return json.loads(raw)
        except json.JSONDecodeError as e:
            raise GhError(f"unparsable `gh run list` output: {raw[:120]!r}") from e

    # Ask twice before concluding anything. An empty first answer is the input
    # to the report's most serious claim, and on 2026-09-03 and 2026-09-08 that
    # claim was wrong both times: `bench.yml` had run hours earlier and the same
    # query returned it correctly by hand afterwards. A second call costs one
    # API round trip; a false alarm costs the report its credibility.
    #
    # A failed or unparsable answer is retried on the same reasoning, and
    # raised only if it persists, so it lands in "could not be checked" rather
    # than in a claim about the workflow.
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


def scheduled_runs_since(workflow: str, since: datetime) -> int:
    """How many scheduled runs of `workflow` exist since `since`, counted server-side.

    This is the second opinion the stale verdict is checked against, and it is
    deliberately a DIFFERENT question than `latest_scheduled_run` asks. That one
    fetches a page and picks the newest from it, so it is only ever as good as
    the page it was handed; every false alarm so far (2026-09-03, -09-08, -09-11,
    all on `bench.yml`) came from a page whose newest entry was weeks old while
    the cron had in fact fired that morning. Taking the max instead of the first
    element, then asking twice, did not stop it — both retries can be handed the
    same lagged page, and a max over stale rows is still stale.

    `total_count` with a `created>=` filter has no such dependence: no ordering,
    no pagination, no "newest of what I was given". It answers "did it fire in
    the window" directly, which is the only thing the stale claim rests on.

    Be precise about how much that buys, because it is less than it looks.
    `gh run list --workflow F --event schedule` resolves F to an id and then
    GETs `/actions/workflows/<id>/runs?event=schedule`; this asks the SAME
    endpoint with different parameters, so it is not an independent source. It
    defeats a bad page — wrong order, wrong window, rows that should not be
    newest — which is the only mechanism anyone has actually named. It does NOT
    defeat a lagged view of the runs table, because a count computed against
    that same lagged view would agree with the wrong answer.

    That remaining hole is why the stale claim must also survive a night; see
    `SUSPECT_MARKER`.

    Note the filter is date-granular, so the window is up to a day wider than
    asked. That errs toward NOT claiming staleness, which is the right direction
    for a report whose credibility is the thing being protected.
    """
    day = since.strftime("%Y-%m-%d")
    raw = gh(
        "api",
        f"repos/{REPO}/actions/workflows/{workflow}/runs"
        f"?event=schedule&created=%3E%3D{day}&per_page=1",
        "--jq", ".total_count",
        tolerate_missing=True,
    )
    # A tolerated 404 is "no such workflow / never run", which is genuinely zero
    # runs in the window rather than a failed check.
    if not raw.strip():
        return 0
    try:
        return int(raw.strip())
    except ValueError as e:
        # Same reasoning as the run listing: an answer that will not parse must
        # not be read as "no runs", because that is the input to the stale claim.
        raise GhError(f"unparsable total_count: {raw.strip()[:80]!r}") from e


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

    # `latest_scheduled_run` must pick by TIMESTAMP, not by position. The
    # 2026-09-03 report called `bench.yml` ten days stale while it had run six
    # hours earlier, linking a real but older run -- consistent with taking
    # element zero of a list that was not newest-first. Fed deliberately
    # out-of-order here, since a correctly-ordered fixture cannot tell the two
    # implementations apart.
    out_of_order = (
        '[{"conclusion":"success","status":"completed",'
        '"createdAt":"2026-08-24T02:52:42Z","databaseId":1,"url":"old"},'
        '{"conclusion":"success","status":"completed",'
        '"createdAt":"2026-09-03T06:34:44Z","databaseId":2,"url":"new"}]'
    )
    gh = stub(out_of_order)
    picked = latest_scheduled_run("bench.yml")
    ok = picked is not None and picked["url"] == "new"
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} newest scheduled run wins regardless of list order")

    gh = stub("[]")
    ok = latest_scheduled_run("bench.yml") is None
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} no scheduled runs reports None")

    # An empty first answer must be re-asked before concluding a cron stopped.
    # This is the 2026-09-03 and 2026-09-08 `bench.yml` false alarm: the run
    # existed, the first query did not show it.
    calls = {"n": 0}

    def flaky(*_args: str, **_kw: object) -> str:
        calls["n"] += 1
        if calls["n"] == 1:
            return "[]"
        return (
            '[{"conclusion":"success","status":"completed",'
            '"createdAt":"2026-09-08T06:37:00Z","databaseId":9,"url":"real"}]'
        )

    gh = flaky
    picked = latest_scheduled_run("bench.yml")
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
        latest_scheduled_run("bench.yml")
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
        ok = latest_scheduled_run("brand-new.yml") is None
    except GhError:
        # Without the guard this raises. Catch it so the case reports FAIL
        # rather than aborting the whole self-test on the way past.
        ok = False
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} an empty answer still reports no runs, not a failed check")

    # --- the cross-check that decides whether a stale verdict is published ---
    #
    # This is the part that would have stopped all three `bench.yml` false
    # alarms, so it is checked in both directions: it must suppress a wrong
    # stale claim, and it must NOT suppress a right one.
    now_t = datetime(2026, 9, 11, 12, 30, tzinfo=timezone.utc)

    gh = stub("5")
    claim, note = confirm_stale("bench.yml", "daily", now_t, timedelta(days=16))
    ok = claim is False and "not claimed stale" in note
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} a contradicting count suppresses the stale claim")

    gh = stub("0")
    claim, _ = confirm_stale("dead.yml", "daily", now_t, timedelta(days=16))
    ok = claim is True
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} an agreeing count still reports a genuinely dead cron")

    # The count query is the whole second opinion, so its SHAPE is the thing
    # worth pinning: filtered to scheduled runs, and to the staleness window.
    # A regression dropping either flag would count every run ever and silence
    # the report permanently -- failing open, in the direction nobody notices.
    seen_args.clear()
    gh = stub("3")
    confirm_stale("bench.yml", "daily", now_t, timedelta(days=16))
    argv = seen_args[-1] if seen_args else ()
    url = next((a for a in argv if "actions/workflows" in a), "")
    for fragment, label in [
        ("bench.yml", "the workflow it was asked about"),
        ("event=schedule", "scheduled runs only"),
        ("created=%3E%3D2026-09-08", "the staleness window, not all time"),
    ]:
        ok = fragment in url
        failures += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} count query names {label}")

    # An unreachable cross-check must not become an assertion in either
    # direction: not a stale claim, and not a clean bill of health.
    def raiser(*_a: object, **_k: object) -> str:
        raise GhError("HTTP 502")

    gh = raiser
    with contextlib.redirect_stdout(io.StringIO()):
        claim, note = confirm_stale("bench.yml", "daily", now_t, timedelta(days=16))
    ok = claim is False and "could not be fetched" in note
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} an unreachable cross-check claims nothing")

    # A count that will not parse is the same hazard as an unparsable listing:
    # read as zero it would CONFIRM a false stale claim, which is worse than
    # not checking at all.
    gh = stub("<!DOCTYPE html>")
    try:
        scheduled_runs_since("bench.yml", now_t - timedelta(days=3))
        ok = False
    except GhError:
        ok = True
    failures += not ok
    print(f"  {'ok  ' if ok else 'FAIL'} an unparsable count raises rather than confirming stale")

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
    # as checking the behavior: the round trip could work, `confirm_stale`
    # could work, and main() could still put every entry in the wrong section.
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
            if a[0] == "run" and a[1] == "list":
                wf = a[a.index("--workflow") + 1]
                when = "2026-08-26T02:54:00Z" if wf == "bench.yml" else "2026-09-11T06:42:00Z"
                return json.dumps([{
                    "conclusion": "success", "status": "completed",
                    "createdAt": when, "databaseId": 1, "url": "u",
                }])
            if a[0] == "api":
                # The count AGREES that bench.yml really has not run, so the
                # only thing holding the claim back is the one-night rule.
                return "0" if "bench.yml" in a[1] else "4"
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
        if a[0] == "run" and a[1] == "list":
            return json.dumps([{
                "conclusion": "success", "status": "completed",
                "createdAt": "2026-09-11T06:42:00Z", "databaseId": 1, "url": "u",
            }])
        if a[0] == "api":
            return "4"
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


def confirm_stale(
    workflow: str, period: str, now: datetime, age: timedelta | None
) -> tuple[bool, str]:
    """Second-opinion a stale verdict. Returns (claim_it, note_if_not).

    The run listing has now produced three false stale reports, so its verdict
    alone is not enough to publish. A count that contradicts it means the cron
    is alive and the listing was wrong, which is the case actually observed; a
    count that agrees turns a single lookup into two independent ones.

    A cross-check that cannot be reached decides nothing either way, so it lands
    in "could not be checked" rather than becoming an assertion about the cron.
    That is the same call the surrounding code already makes for an unanswered
    listing, and it is the safer one: this report has three false alarms on
    record and no missed dead cron.
    """
    window = STALENESS[period]
    try:
        recent = scheduled_runs_since(workflow, now - window)
    except GhError as e:
        print(f"::error::could not confirm staleness of {workflow}: {e}")
        return False, (
            f"- `{workflow}` ({period}) — looks stale, but the confirming count "
            f"could not be fetched ({e}), so nothing is claimed"
        )

    if recent > 0:
        observed = (
            "no scheduled run at all" if age is None
            else f"its newest scheduled run {age.days}d old"
        )
        print(f"::warning::{workflow}: listing said stale, count says {recent} recent run(s)")
        return False, (
            f"- `{workflow}` ({period}) — **not claimed stale**: the run listing "
            f"reported {observed}, but {recent} scheduled run(s) exist in the last "
            f"{window.days}d. The listing was wrong, not the cron "
            f"(see `scheduled_runs_since`)"
        )
    return True, ""


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
        try:
            run = latest_scheduled_run(wf)
        except GhError as e:
            # An unanswered query is not evidence that a cron stopped. Say the
            # check did not happen rather than assert something about the
            # workflow, and keep going so one bad call does not cost the whole
            # report.
            print(f"::error::could not check {wf}: {e}")
            unchecked.append(f"- `{wf}` ({period}) — could not be checked: {e}")
            continue
        if run is None:
            confirmed, note = confirm_stale(wf, period, now, None)
            if not confirmed:
                unchecked.append(note)
                continue
            suspects_now.append(wf)
            entry = f"- `{wf}` ({period}) — no scheduled run found at all"
            (stale if wf in prior else suspected).append(entry)
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
            confirmed, note = confirm_stale(wf, period, now, age)
            if not confirmed:
                unchecked.append(note)
            else:
                suspects_now.append(wf)
                entry = (
                    f"- `{wf}` ({period}) — last scheduled run {age.days}d ago "
                    f"([{concl}]({run['url']}))"
                )
                (stale if wf in prior else suspected).append(entry)
        elif concl != "success":
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
