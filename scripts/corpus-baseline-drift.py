#!/usr/bin/env python3
"""Report parser-baseline drift that no PR would otherwise carry.

`tests/baselines/parser-corpus.manifest` pins the parser's output for every
file in the downloaded compatibility corpus. Two things keep it from staying
current on its own:

  * The baseline gate treats a downloaded corpus file with no manifest entry
    as a WARNING, not a failure, and deliberately so -- upstream can add a
    file at any moment and failing would fire on unrelated PRs. The warning
    goes to a CI log nobody reads, so such a file can sit with no baseline
    coverage indefinitely.

  * CI restores the corpus from a cache keyed on the FETCH SCRIPT, not on
    upstream state, so the fetch step is skipped on an exact key hit. CI's
    corpus is therefore frozen at whatever was fetched when that key was
    first created, while the upstream repositories it mirrors keep moving.
    Every PR sees the same stale corpus and reports no drift.

Together those mean drift accumulates silently until somebody changes the
parser, whose PR then has to carry and explain unrelated churn (#2186).

This runs on a schedule against a FRESHLY FETCHED corpus and turns the
result into an issue -- a signal a human sees. It reports; it does not gate.

The oracle is the repository's own regeneration path (`BASELINE_UPDATE=1`)
plus `git diff`, deliberately: reimplementing the fingerprint in Python
would be a second implementation of the thing under test, free to disagree
with the Rust one in exactly the cases that matter.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys

REPO = "rustledger/rustledger"
ISSUE_TITLE = "Parser corpus baseline has drifted"
MARKER = "<!-- corpus-baseline-drift -->"
MANIFEST = "tests/baselines/parser-corpus.manifest"

REGEN = [
    "cargo", "test", "-p", "rustledger-parser",
    "--test", "corpus_baseline", "parser_output_matches_baseline",
]


CORPUS_ROOT = "tests/compatibility/files"

# Same slack as the "Verify corpus is populated" step in
# `parser-baselines.yml`, and for the same reason: the fetch tolerates up to
# 15 best-effort clone failures, so a legitimately complete run can still come
# up a little short.
CORPUS_SLACK = 50


def corpus_size() -> int:
    """Count `.beancount` files the way the baseline test discovers them."""
    n = 0
    for _, _, files in os.walk(CORPUS_ROOT):
        n += sum(1 for f in files if f.endswith(".beancount"))
    return n


def manifest_entries() -> int:
    with open(MANIFEST, encoding="utf-8") as fh:
        return sum(1 for line in fh if line.strip() and not line.startswith("#"))


def fetch_is_complete(count: int, expected: int) -> bool:
    """Is this corpus whole enough to trust a "file disappeared" verdict?

    This matters here in a way it does not for the PR gate. That job restores
    a cached corpus, so it always has a complete one; this one fetches fresh
    into an empty checkout, so every tolerated clone failure is simply missing
    files. Regenerating against a partial corpus drops their manifest entries,
    and reporting that as "upstream deleted these" would be a confident lie --
    the more repositories failed, the longer and more alarming the list.

    A short corpus cannot manufacture a false "added" or "rehashed" either,
    but it does mean the run saw an unrepresentative corpus, so the honest
    answer is to report nothing and say why.

    This is deliberately stricter than the backstop inside the test itself,
    which refuses to write a manifest below `MIN_FULL_CORPUS_SIZE` (100). That
    one exists to stop a catastrophic fetch truncating the committed manifest
    to the three in-tree fixtures, and it fires as a panic. At a corpus of
    ~735 this check trips at ~685, so a merely partial fetch gets a sentence
    explaining itself rather than a cargo stack trace, and the test's assert
    stays what it was written to be: a last resort.
    """
    return count >= expected - CORPUS_SLACK


class GhError(RuntimeError):
    """A `gh` invocation failed.

    Raised rather than returning an empty string, which is what the first
    version did and is indistinguishable from a successful empty result. That
    conflation is not cosmetic here: a failed `issue list` would look like
    "no existing issue" and open a duplicate, and a failed `issue create`
    would print a blank URL and leave the workflow GREEN having reported
    nothing at all -- the exact silence this job exists to break.
    """


def gh(*args: str) -> str:
    proc = subprocess.run(["gh", *args], capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        raise GhError(f"gh {' '.join(args)} failed: {proc.stderr.strip()}")
    return proc.stdout


def regenerate() -> None:
    """Rewrite the manifest from the corpus currently on disk."""
    subprocess.run(REGEN, env={**os.environ, "BASELINE_UPDATE": "1"}, check=True)


def manifest_diff() -> str:
    """Unified diff of the manifest after regeneration, empty if unchanged."""
    return subprocess.run(
        ["git", "diff", "--unified=0", "--", MANIFEST],
        capture_output=True, text=True, check=True,
    ).stdout


def classify(diff: str) -> dict[str, list[str]]:
    """Split a manifest diff into added / removed / rehashed paths.

    A manifest line is `path<TAB>source_hash<TAB>output_hash`. A path on both
    sides of the diff had a hash change; a path on one side only was added or
    removed from the corpus.
    """
    added, removed = {}, {}
    for line in diff.splitlines():
        if line.startswith(("+++", "---")):
            continue
        if line.startswith("+"):
            body = line[1:]
        elif line.startswith("-"):
            body = line[1:]
        else:
            continue
        if not body or body.startswith("#"):
            continue
        path = body.split("\t")[0]
        (added if line.startswith("+") else removed)[path] = body
    # A path on both sides had a hash change, and WHICH hash moved is the
    # whole question. A changed source hash is upstream churn and expected. A
    # changed output hash with an UNCHANGED source hash means this repository
    # produces different output for identical input than the committed
    # baseline says -- a parser change that reached main without regenerating.
    # The body used to promise "the diff says which" and then print only
    # paths, which told the reader to go find something it already knew.
    upstream, unregenerated = [], []
    for path in sorted(set(added) & set(removed)):
        before = removed[path].split("\t")
        after = added[path].split("\t")
        if len(before) >= 2 and len(after) >= 2 and before[1] != after[1]:
            upstream.append(path)
        else:
            unregenerated.append(path)
    return {
        "unregenerated": unregenerated,
        "added": sorted(set(added) - set(removed)),
        "upstream": upstream,
        "removed": sorted(set(removed) - set(added)),
    }


def _summary(n: int) -> str:
    """Lead paragraph. Built here rather than as adjacent literals in the body
    list, where two strings on consecutive lines read as a missing comma
    (CodeQL `py/implicit-string-concatenation-in-list`)."""
    plural = "y" if n == 1 else "ies"
    return (
        f"A fresh fetch of the compatibility corpus moves **{n}** manifest"
        + f" entr{plural}. Nothing on a pull request would report this: the"
        + " baseline gate treats an unmanifested downloaded file as a warning,"
        + " and CI restores the corpus from a cache keyed on the fetch script"
        + " rather than on upstream state, so every PR sees the same frozen"
        + " corpus."
    )


def render(groups: dict[str, list[str]]) -> str:
    n = sum(len(v) for v in groups.values())
    body = [
        MARKER,
        "",
        _summary(n),
        "",
    ]

    def section(key: str, title: str, why: str) -> None:
        paths = groups[key]
        if not paths:
            return
        body.extend([f"### {title} ({len(paths)})", "", why, ""])
        body.extend(f"- `{p}`" for p in paths[:40])
        if len(paths) > 40:
            body.append(f"- _...and {len(paths) - 40} more_")
        body.append("")

    section(
        "added", "New corpus files with no baseline",
        "These have had **no parser-output coverage at all** since they "
        + "appeared upstream.",
    )
    section(
        "unregenerated", "Parser output changed on UNCHANGED input",
        "The source hash is identical and the output hash is not: this "
        + "repository now produces different output for the same bytes than "
        + "the committed baseline records. A parser change reached main without "
        + "regenerating. **This is the group to look at first.**",
    )
    section(
        "upstream", "Upstream source changed",
        "The file's own contents moved upstream, so a different output hash "
        + "is expected. Routine churn; regenerate when convenient.",
    )
    section(
        "removed", "Manifest entries whose file is gone",
        "Upstream deleted or renamed these; the entries are dead weight.",
    )

    body += [
        "---",
        "",
        "To resolve, on a clean checkout:",
        "",
        "```sh",
        "./scripts/fetch-compat-test-files.sh   # refresh the corpus",
        "./scripts/regen-corpus-baselines.sh",
        "git diff tests/baselines/              # review",
        "```",
        "",
        (
            "Maintained by `.github/workflows/corpus-baseline-drift.yml`."
            + " Closes itself when the manifest matches a fresh corpus again."
        ),
    ]
    return "\n".join(body)


def _empty() -> dict[str, list[str]]:
    return {"unregenerated": [], "added": [], "upstream": [], "removed": []}


def self_test() -> int:
    """Prove the classifier can report drift, and can report its absence.

    A drift reporter that always says "clean" is worse than none: it is the
    same silence it exists to break, wearing a green check.
    """
    failures = []

    clean = classify("")
    if any(clean.values()):
        failures.append(f"empty diff must be clean, got {clean}")

    sample = (
        "--- a/tests/baselines/parser-corpus.manifest\n"
        + "+++ b/tests/baselines/parser-corpus.manifest\n"
        + "-tests/compatibility/files/a/x.beancount\tAAA\tBBB\n"
        + "+tests/compatibility/files/a/x.beancount\tAAA\tCCC\n"
        + "+tests/compatibility/files/a/new.beancount\tDDD\tEEE\n"
        + "-tests/compatibility/files/a/gone.beancount\tFFF\tGGG\n"
    )
    got = classify(sample)
    want = {
        # x.beancount keeps source hash AAA and changes output BBB -> CCC:
        # same input, different output, which is the serious case.
        "unregenerated": ["tests/compatibility/files/a/x.beancount"],
        "added": ["tests/compatibility/files/a/new.beancount"],
        "upstream": [],
        "removed": ["tests/compatibility/files/a/gone.beancount"],
    }
    if got != want:
        failures.append(f"classify mismatch:\n  got  {got}\n  want {want}")

    text = render(got)
    for needle in ("new.beancount", "x.beancount", "gone.beancount", MARKER):
        if needle not in text:
            failures.append(f"rendered body omits {needle}")
    if "**3**" not in text:
        failures.append("rendered body does not count all three entries")

    # The split is the point of the section: an upstream content change and a
    # parser change that skipped regeneration look identical in a path list
    # and mean entirely different things.
    upstream_only = classify(
        "-tests/compatibility/files/a/y.beancount\tAAA\tBBB\n"
        + "+tests/compatibility/files/a/y.beancount\tZZZ\tCCC\n"
    )
    if upstream_only["upstream"] != ["tests/compatibility/files/a/y.beancount"]:
        failures.append(f"changed source hash must read as upstream: {upstream_only}")
    if upstream_only["unregenerated"]:
        failures.append("a changed source hash must NOT read as unregenerated")

    # A comment-only diff is not drift.
    if any(classify("+# regenerated\n").values()):
        failures.append("comment lines must not count as drift")

    # The partial-fetch guard, which is the difference between reporting
    # drift and inventing it. Fresh-fetching into an empty checkout means a
    # tolerated clone failure looks exactly like an upstream deletion.
    if not fetch_is_complete(735, 735):
        failures.append("a complete corpus must be accepted")
    if not fetch_is_complete(735 - CORPUS_SLACK, 735):
        failures.append("a corpus short by exactly the slack must be accepted")
    if fetch_is_complete(735 - CORPUS_SLACK - 1, 735):
        failures.append("a corpus short by more than the slack must be refused")
    if fetch_is_complete(0, 735):
        failures.append("an empty corpus must be refused")

    # A failing `gh` must raise, not return "". The first version returned an
    # empty string, which reads as "no issues exist" to the dedupe check and
    # as a blank URL to the create path -- a green run that reported nothing.
    real_run = subprocess.run

    def failing_run(*a, **kw):
        class P:
            returncode = 1
            stdout = ""
            stderr = "gh: HTTP 403"
        return P()

    try:
        subprocess.run = failing_run
        try:
            gh("issue", "list")
            failures.append("gh must raise GhError when the command fails")
        except GhError:
            # Raising IS the expected outcome, so there is nothing to record:
            # the `except` arm reaching at all is what the check asserts, and
            # the `failures.append` above it is what runs when it does not.
            pass
    finally:
        subprocess.run = real_run

    # ...and must NOT raise on a successful empty result, which is a real and
    # different answer.
    def empty_run(*a, **kw):
        class P:
            returncode = 0
            stdout = ""
            stderr = ""
        return P()

    try:
        subprocess.run = empty_run
        try:
            if gh("issue", "list") != "":
                failures.append("gh must pass through an empty success")
        except GhError:
            failures.append("gh must not raise on a successful empty result")
    finally:
        subprocess.run = real_run

    # `_report` is the only code that does anything: it decides between
    # opening, updating and closing. `--dry-run` returns before reaching it,
    # and a scheduled run exercises exactly one branch per week, so without
    # this the working part of the script ships unexecuted.
    calls: list[tuple[str, ...]] = []

    def recording_gh(*args: str) -> str:
        calls.append(args)
        return "https://github.com/x/y/issues/1\n"

    real_gh = globals()["gh"]
    drift = {"unregenerated": ["a"], "added": [], "upstream": [], "removed": []}
    # `_report` narrates to stdout. Left alone it prints "opened
    # https://github.com/x/y/issues/1" into a self-test log, which is exactly
    # the sort of line someone skims and believes.
    import contextlib
    import io

    try:
        globals()["gh"] = recording_gh
        sink = contextlib.redirect_stdout(io.StringIO())
        sink.__enter__()

        calls.clear()
        _report(True, drift, [])
        verbs = [c[1] for c in calls]
        if verbs != ["create"]:
            failures.append(f"drift with no open issue must create one, got {verbs}")

        calls.clear()
        _report(True, drift, [{"number": 7}])
        verbs = [c[1] for c in calls]
        if verbs != ["edit"]:
            failures.append(f"drift with an open issue must edit it, got {verbs}")
        if calls and "7" not in calls[0]:
            failures.append("edit must target the existing issue number")

        calls.clear()
        _report(False, _empty(), [{"number": 7}])
        verbs = [c[1] for c in calls]
        if verbs != ["comment", "close"]:
            failures.append(f"clean with an open issue must comment then close, got {verbs}")

        calls.clear()
        _report(False, _empty(), [])
        if calls:
            failures.append(f"clean with no issue must touch nothing, got {calls}")
    finally:
        sink.__exit__(None, None, None)
        globals()["gh"] = real_gh

    for f in failures:
        print(f"self-test FAIL: {f}", file=sys.stderr)
    print("self-test: ok" if not failures else f"self-test: {len(failures)} failure(s)")
    return 1 if failures else 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true", help="print, do not touch issues")
    args = ap.parse_args()

    # Every path here is repo-relative, and so is the `git checkout --` that
    # --dry-run uses to put the manifest back. Run from anywhere else and that
    # either fails confusingly or, worse, resolves somewhere unintended.
    if not os.path.isfile(MANIFEST):
        print(
            f"{MANIFEST} not found: run this from the repository root.",
            file=sys.stderr,
        )
        return 2

    # Whether the manifest was already modified before we touched it. If it
    # was, --dry-run must NOT restore it: `git checkout --` would throw away
    # edits the caller made, and a reporting script has no business deleting
    # someone's work to keep its own promise about not leaving a diff.
    dirty_before = bool(
        subprocess.run(
            ["git", "diff", "--name-only", "--", MANIFEST],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
    )

    expected = manifest_entries()
    count = corpus_size()
    if not fetch_is_complete(count, expected):
        print(
            f"corpus has {count} files, manifest expects ~{expected} "
            + f"(slack {CORPUS_SLACK}): the fetch came up short, so a "
            + "regeneration here would report its own missing files as "
            + "upstream deletions. Reporting nothing this run.",
            file=sys.stderr,
        )
        return 0

    regenerate()
    groups = classify(manifest_diff())
    drifted = any(groups.values())

    if args.dry_run:
        # Regenerating rewrote the manifest in the working tree. On CI that is
        # a throwaway checkout, but --dry-run is for humans, and a flag named
        # dry-run must not leave a modified file behind for someone to commit
        # by accident. Unless it was already modified when we arrived, in
        # which case restoring it would delete their edits instead.
        if dirty_before:
            print(
                f"note: {MANIFEST} had uncommitted changes before this ran, "
                + "so it was regenerated in place and NOT restored.",
                file=sys.stderr,
            )
        else:
            subprocess.run(["git", "checkout", "--", MANIFEST], check=True)
        print(render(groups) if drifted else "no drift")
        return 0

    try:
        existing = gh(
            "issue", "list", "--repo", REPO, "--state", "open",
            "--search", ISSUE_TITLE, "--json", "number,body", "--limit", "20",
        )
    except GhError as e:
        # Cannot dedupe without this, and guessing "none exist" opens a
        # duplicate every week. Fail the step instead.
        print(e, file=sys.stderr)
        return 1
    try:
        issues = [i for i in json.loads(existing or "[]") if MARKER in (i.get("body") or "")]
    except json.JSONDecodeError:
        issues = []

    try:
        return _report(drifted, groups, issues)
    except GhError as e:
        print(e, file=sys.stderr)
        return 1


def _report(drifted: bool, groups: dict[str, list[str]], issues: list) -> int:
    if drifted:
        text = render(groups)
        if issues:
            num = str(issues[0]["number"])
            gh("issue", "edit", num, "--repo", REPO, "--body", text)
            print(f"updated issue #{num}")
        else:
            url = gh("issue", "create", "--repo", REPO,
                     "--title", ISSUE_TITLE, "--body", text).strip()
            print(f"opened {url}")
    elif issues:
        num = str(issues[0]["number"])
        gh("issue", "comment", num, "--repo", REPO, "--body",
           "The manifest matches a freshly fetched corpus again. Closing automatically.")
        gh("issue", "close", num, "--repo", REPO)
        print(f"no drift; closed issue #{num}")
    else:
        print("no drift")

    # 0 for what this measures: drift is reported, not gated, and a red X for
    # finding drift would be one more failing scheduled workflow for nobody to
    # notice.
    #
    # Failing to REPORT is the opposite case and returns non-zero, as does
    # `regenerate()` running under `check=True` when a corpus file panics the
    # parser or the build will not compile. Those are real problems on main,
    # and `nightly-health.yml` picks them up from there. A job that cannot say
    # what it found must not look like a job that found nothing.
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        raise SystemExit(self_test())
    sys.exit(main())
