#!/usr/bin/env python3
"""BQL compatibility harness — diff bean-query vs rledger output row-by-row.

Loads a query corpus from a TOML file (default
`tests/compatibility/bql-queries.toml`), runs each query against every
test file that both tools could parse, and reports per-query/per-file
matches and mismatches.

The README in `tests/compatibility/` documents how to add queries and
why the corpus is biased toward semantic-divergence cases.

Usage (CI; `--github-output` writes summary lines into $GITHUB_OUTPUT):

    python3 scripts/compat-bql-test.py \\
        --corpus tests/compatibility/bql-queries.toml \\
        --files-from compat-check-results.jsonl \\
        --rledger ./target/release/rledger \\
        --output compat-bql-results.jsonl \\
        --github-output

Usage (local, with paths and tools auto-detected):

    python3 scripts/compat-bql-test.py
"""

from __future__ import annotations

import argparse
import json
import multiprocessing
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from pathlib import Path

try:
    import tomllib  # Python 3.11+
except ImportError:
    import tomli as tomllib  # type: ignore[no-redef]


# ---------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_CORPUS = REPO_ROOT / "tests" / "compatibility" / "bql-queries.toml"
DEFAULT_TEST_DIRS = [
    REPO_ROOT / "tests" / "compatibility" / "files",
    REPO_ROOT / "tests" / "compatibility" / "synthetic",
    REPO_ROOT / "tests" / "regressions",
]

# Hard floor — guards against accidental corpus shrinkage. Bump
# whenever the actual corpus grows. CI fails if the loaded corpus has
# fewer queries than this.
MIN_CORPUS_SIZE = 15

# Files queried per run, unless --max-files says otherwise.
#
# Raised from 30 after measuring the real cost: the BQL step ran 510 runs in
# about 30 seconds (~17 runs/sec), so the old cap was saving seconds while
# exercising 4% of the eligible corpus. 150 costs roughly two minutes and
# covers ~22%; the nightly passes a cap high enough to take everything (see
# compat.yml), which is the same gate-on-PR / full-sweep-nightly split the
# fuzz workflow uses.
MAX_FILES = 150

# beancount emits these on stderr and still exits 0, leaving the ledger short
# of directives the fixture expects. Same expression as the one in
# `verify-first-balance-divergence.py`, which documents the failure mode.
_LOAD_ERROR = re.compile(r"Error importing|error importing|<load>:")

# A query that returns 0 rows on more than this fraction of files isn't
# really being tested by the corpus — flag it loudly so we know to add
# data that exercises it.
EMPTY_RESULT_WARNING_FRACTION = 0.5

# Known cases where Python beanquery has a bug rather than rledger.
# These don't count against compat percentage. See referenced beanquery
# issues for context.
#
# Keyed by `(repo_relative_path, query_name)`. A bare filename used to be
# enough, but with a 13-query corpus a single broken file would silently mask
# up to 12 unrelated regressions on that same file. The query_name pin
# makes the allowlist surgical: only the specific query that's known to
# diverge is excused.
#
# The key is a PATH, not a basename: four basenames collide in the corpus, so a
# name-keyed mask would excuse every twin sharing that name (#2016). Entries are
# stale/dangling-checked at runtime, so a mistyped path surfaces as a dangling
# warning rather than a silent no-op mask.
#
# Use `("path", "*")` to allowlist ALL queries on a file (e.g., when
# the divergence is in a column projection that every query touches).
KNOWN_PYTHON_DIVERGENCES: set[tuple[str, str]] = {
    # beancount/beanquery#275: position display truncates precision in
    # the ledger's display context. Affects any query that projects
    # `position` or sums it.
    ("tests/compatibility/files/beancount-import/testdata_source_generic_importer_test_invalid_journal.beancount", "*"),
    # DisplayContext common vs max precision (#724)
    ("tests/compatibility/files/beancount-import/testdata_source_ofx_test_fidelity_journal.beancount", "*"),
    # beancount/beanquery#279 used to be pinned here, 56 fixtures of it. It is
    # not masked any more because it is no longer a divergence: the corpus query
    # now selects `LAST(balance)` alongside `FIRST(balance)`, which forces
    # beanquery to evaluate the stateful `balance` accumulator on every row, and
    # the two tools then agree exactly. See the rationale on
    # `first-balance-by-month` in tests/compatibility/bql-queries.toml.
    #
    # Pinning could never have finished the job. 499 of the 513 unpinned
    # occurrences were `synthetic_*` fixtures, which the nightly generator
    # recreates every run — a `(filename, query)` entry cannot mask a file that
    # will not exist tomorrow, so the registry lost ground every night no matter
    # how many entries were added.
}


# Known cases where **rledger** is the side that diverges from bean-query.
# Kept SEPARATE from `KNOWN_PYTHON_DIVERGENCES` on purpose: conflating the
# two lists would let an rledger bug masquerade as a Python quirk, and a
# future rledger regression on these file/query pairs would be silently
# absorbed by the same allowlist. Reported separately in the per-CI
# summary so the count of Rust-side divergences is visible at a glance.
#
# Both lists are stale-checked at runtime (`stale_divergence_entries`): an entry
# whose pair now MATCHES bean-query fails the run, so a mask can't outlive the
# divergence it documents and then absorb a real regression on the same pair.
#
# Keyed by `(repo_relative_path, query_name)` with the same surgical-pin
# semantics as `KNOWN_PYTHON_DIVERGENCES`. Counted as "known" for the effective
# match percentage (the values are correct — only display scale differs),
# but tracked as a distinct category so future bookkeeping stays honest.
KNOWN_RUST_DIVERGENCES: set[tuple[str, str]] = {
    # `sum-number-by-currency` display-scale mismatch on cost-spec
    # interpolation fixtures: Python beanquery preserves arithmetic
    # scale through SUM (`-1966.700` at scale 3); rledger's booking
    # layer normalizes residuals to the input minimum scale and lands
    # at scale 2 (`-1966.70`). The values are numerically equal — the
    # difference is *display scale only*, surfaced as a textual diff
    # because both tools intentionally preserve scale on `Value::Number`
    # output (#1103 / #1106 / #1113).
    #
    # Root cause: cost-spec interpolation against `{}` lot-match against
    # a `{{total}}` lot produces a residual whose scale depends on which
    # intermediate value drives it. Python's intermediate stays at the
    # buy-side scale 3; rledger's #1108 fix dropped intermediate scale
    # to the input minimum (2) to stop 26-digit contamination — that
    # fix was correct for the over-precision case but over-applies on
    # these fixtures.
    #
    # Deep fix is continuation of #1108's pipeline scale-propagation
    # work. Tracked under #1112 (kept open as the tracker — do not
    # auto-close from this PR). Surgical pin (not "*") so any
    # non-scale divergence on these fixtures stays surfaced.
    ("tests/compatibility/files/beancount-import/testdata_source_healthequity_test_invalid_journal.beancount", "sum-number-by-currency"),
    ("tests/compatibility/files/beancount-import/testdata_source_healthequity_test_matching_journal.beancount", "sum-number-by-currency"),
    ("tests/compatibility/files/beancount-import/testdata_source_ofx_test_non_default_capital_gains_journal.beancount", "sum-number-by-currency"),
}


# Queries whose "empty source" case is divergent because beanquery
# returns 0 rows for `SELECT COUNT(*) FROM <empty_source>` (and
# similar pure-aggregate, no-GROUP-BY shapes) where standard SQL —
# and rledger — returns 1 row with the aggregate identity (e.g., 0
# for COUNT). Non-standard beanquery behavior; see #1055.
#
# Maps query_name -> the rs row content that constitutes the
# canonical quirk shape. Checking the row content (not just the row
# count) is what makes the predicate safe against future regressions:
# a fixture where bean-query sees 0 prices but rledger over-emits
# `N>0` would also produce `py_rows=0 rs_rows=1`, but the rs row
# would be `"N"`, not `"0"` — so we wouldn't mask the bug.
#
# Add a sibling no-GROUP-BY aggregate query by appending one entry,
# keyed on the corpus query name and mapped to its aggregate identity
# (e.g. SUM → "0", or "0.00" if the column carries a tracked
# precision; check what bean-query renders empirically).
_BEANQUERY_EMPTY_AGGREGATE_IDENTITY: dict[str, str] = {
    # SELECT COUNT(*) AS n FROM #prices  →  identity is integer 0
    "count-prices-from-plugin": "0",
}


def _is_beanquery_empty_aggregate_quirk(run: "QueryRun") -> bool:
    """True if this run's mismatch is the beanquery empty-aggregate quirk.

    Beanquery returns 0 rows from a pure-aggregate query (no GROUP BY)
    when the source table is empty; standard SQL (and rledger) returns
    1 row with the aggregate identity. We treat this as a known
    divergence ONLY when:

    1. Both tools ran successfully (`*_failed` false). A bean-query
       timeout or non-zero exit produces empty stdout, so `py_rows ==
       0`, and could otherwise be misclassified as the quirk.
    2. The row-count fingerprint matches: `py_rows == 0` and
       `rs_rows == 1`.
    3. Rledger's row content equals the aggregate identity for this
       query (`_BEANQUERY_EMPTY_AGGREGATE_IDENTITY`). Without this
       check, a fixture where bean-query sees 0 prices but rledger
       over-emits would fingerprint identically and be silently
       masked — defeating the purpose of the predicate set vs. a
       blanket allowlist.
    """
    expected_identity = _BEANQUERY_EMPTY_AGGREGATE_IDENTITY.get(run.query_name)
    return (
        expected_identity is not None
        and not run.py_failed
        and not run.rs_failed
        and run.py_rows == 0
        and run.rs_rows == 1
        and run.rs_first_row == expected_identity
    )


def _is_known_python_divergence(run: "QueryRun") -> bool:
    if (run.file, run.query_name) in KNOWN_PYTHON_DIVERGENCES or (
        run.file,
        "*",
    ) in KNOWN_PYTHON_DIVERGENCES:
        return True
    return _is_beanquery_empty_aggregate_quirk(run)


def _is_known_rust_divergence(run: "QueryRun") -> bool:
    """True if this mismatch is on the rledger-side allowlist.

    See `KNOWN_RUST_DIVERGENCES` for context. Wildcard `"*"` is honored
    for symmetry with the Python allowlist, though no entry currently
    uses it.
    """
    return (run.file, run.query_name) in KNOWN_RUST_DIVERGENCES or (
        run.file,
        "*",
    ) in KNOWN_RUST_DIVERGENCES


def _is_known_divergence(run: "QueryRun") -> bool:
    """True if the mismatch is in either allowlist (Python or Rust).

    Used by reporting paths that just want the "known vs real" split
    without caring which side has the bug.
    """
    return _is_known_python_divergence(run) or _is_known_rust_divergence(run)


def _index_runs(
    results: "list[QueryRun]",
) -> "tuple[dict[tuple[str, str], list[QueryRun]], dict[str, list[QueryRun]]]":
    """Index runs by `(file, query)` and by `file` for the stale-mask check."""
    by_pair: dict[tuple[str, str], list] = {}
    by_file: dict[str, list] = {}
    for r in results:
        by_pair.setdefault((r.file, r.query_name), []).append(r)
        by_file.setdefault(r.file, []).append(r)
    return by_pair, by_file


def _stale_registry_entries(
    registry: "set[tuple[str, str]]",
    registry_name: str,
    by_pair: "dict[tuple[str, str], list[QueryRun]]",
    by_file: "dict[str, list[QueryRun]]",
) -> "tuple[list[tuple[str, tuple[str, str]]], list[tuple[str, tuple[str, str]]]]":
    """Split one registry's entries into (stale, dangling).

    * STALE: the masked pair (or, for `(file, "*")`, every query on the file)
      now MATCHES bean-query, so the divergence is gone.
    * DANGLING: no run exercises the entry — the fixture or query was renamed
      or removed.

    Pure (takes the registry + the pre-built run indices) so it is unit-testable
    without a live corpus; see `--self-test`.
    """
    stale: list = []
    dangling: list = []
    for file, query in registry:
        runs = (by_file.get(file) if query == "*" else by_pair.get((file, query))) or []
        if not runs:
            dangling.append((registry_name, (file, query)))
            continue
        # Only runs where BOTH tools ran successfully are conclusive evidence. A
        # timeout or non-zero exit yields `match == False` without proving a real
        # divergence, so a failed run must NOT keep a stale mask alive (nor count
        # as still-diverging). If every run for the entry was a tool failure the
        # result is inconclusive — leave the mask in place rather than guess.
        conclusive = [r for r in runs if not r.py_failed and not r.rs_failed]
        if conclusive and all(r.match for r in conclusive):
            stale.append((registry_name, (file, query)))
    return stale, dangling


def bare_name_registry_entries(
    registries: list[tuple[str, set[tuple[str, str]]]] | None = None,
) -> list[tuple[str, str]]:
    r"""Registry keys written as a bare filename instead of a repo-relative path.

    Since #2016 a fixture's identity is its path. A bare name is not merely
    unidiomatic here — it silently NEVER MATCHES any run, so the mask it was
    meant to apply quietly does nothing and the divergence it documents shows
    up as a mismatch (or, worse, a mask intended for one file gets written in a
    form that could only ever have excused a twin).

    The check is purely syntactic (`"/" in key`) on purpose: it needs no corpus
    on disk, so it cannot silently skip on a machine where the fixtures were
    never downloaded — which is exactly how the stale/dangling check degrades.
    Typo'd *paths* are a different failure and are caught by the dangling check.

    `/` is the only separator accepted, deliberately. Run keys are POSIX
    (`str(file_path)` on a Linux runner), so a key written with `\` separators
    could never match one either, and flagging it here is the correct outcome —
    treating `\` as a separator would make this guard go SILENT on exactly the
    kind of unmatchable key it exists to catch.
    """
    if registries is None:
        registries = [
            ("KNOWN_PYTHON_DIVERGENCES", KNOWN_PYTHON_DIVERGENCES),
            ("KNOWN_RUST_DIVERGENCES", KNOWN_RUST_DIVERGENCES),
        ]
    bare: list[tuple[str, str]] = []
    for name, registry in registries:
        for file, _query in registry:
            if "/" not in file:
                bare.append((name, file))
    return sorted(bare)


def stale_divergence_entries(
    results: "list[QueryRun]",
) -> "tuple[list[tuple[str, tuple[str, str]]], list[tuple[str, tuple[str, str]]]]":
    """Stale and dangling entries across both static deliberate-divergence lists.

    The `KNOWN_*_DIVERGENCES` allowlists have no runtime check that the pair they
    mask still actually diverges — a stale mask silently absorbs a future
    regression that lands on the same pair. This applies the runtime
    divergence-fingerprint defense that `_is_beanquery_empty_aggregate_quirk`
    gives the one empty-aggregate quirk to the static lists too.
    """
    by_pair, by_file = _index_runs(results)
    stale: list = []
    dangling: list = []
    for name, registry in (
        ("KNOWN_PYTHON_DIVERGENCES", KNOWN_PYTHON_DIVERGENCES),
        ("KNOWN_RUST_DIVERGENCES", KNOWN_RUST_DIVERGENCES),
    ):
        s, d = _stale_registry_entries(registry, name, by_pair, by_file)
        stale += s
        dangling += d
    return stale, dangling


def _run_self_test() -> int:
    """Validate the stale-mask detection logic without a corpus or the tools.

    Builds synthetic runs + registries and asserts `_stale_registry_entries`
    flags exactly the now-matching (stale) and never-run (dangling) entries.
    """

    # Explicit checks rather than `assert` so the guard still fires under
    # `python -O` / PYTHONOPTIMIZE (which strips assert statements).
    failures: list[str] = []

    def check(cond: bool, msg: str) -> None:
        if not cond:
            failures.append(msg)

    def run(
        file: str,
        query: str,
        match: bool,
        py_failed: bool = False,
        rs_failed: bool = False,
    ) -> "QueryRun":
        return QueryRun(
            file=file,
            query_name=query,
            query="",
            match=match,
            py_failed=py_failed,
            rs_failed=rs_failed,
        )

    runs = [
        run("a.beancount", "q1", match=True),  # registered + matches -> STALE
        run("a.beancount", "q2", match=False),  # registered + diverges -> OK
        run("b.beancount", "q1", match=True),  # wildcard file, all match -> STALE
        run("b.beancount", "q2", match=True),
        run("c.beancount", "q1", match=False),  # wildcard file, one diverges -> OK
        run("c.beancount", "q2", match=True),
        # Only run for this pair is a tool failure: inconclusive, must NOT be
        # treated as stale (its match==False is a timeout, not a real divergence).
        run("d.beancount", "q1", match=False, rs_failed=True),
    ]
    by_pair, by_file = _index_runs(runs)

    surgical = {
        ("a.beancount", "q1"),
        ("a.beancount", "q2"),
        ("gone.beancount", "q9"),
        ("d.beancount", "q1"),
    }
    stale, dangling = _stale_registry_entries(surgical, "T", by_pair, by_file)
    check(("T", ("a.beancount", "q1")) in stale, "matching pair must be flagged stale")
    check(
        ("T", ("a.beancount", "q2")) not in stale,
        "diverging pair must NOT be flagged",
    )
    check(
        ("T", ("gone.beancount", "q9")) in dangling,
        "never-run pair must be dangling",
    )
    check(
        ("T", ("d.beancount", "q1")) not in stale,
        "tool-failure-only pair must NOT be stale (inconclusive)",
    )
    check(
        ("T", ("d.beancount", "q1")) not in dangling,
        "tool-failure pair WAS exercised, so it is not dangling",
    )

    wildcard = {("b.beancount", "*"), ("c.beancount", "*")}
    stale_w, _ = _stale_registry_entries(wildcard, "T", by_pair, by_file)
    check(
        ("T", ("b.beancount", "*")) in stale_w,
        "all-matching file must make its wildcard stale",
    )
    check(
        ("T", ("c.beancount", "*")) not in stale_w,
        "a file with one diverging query keeps its wildcard live",
    )

    # --- bare-name registry guard (#2016) ---
    # Both directions, because a guard only ever shown reporting "clean" is
    # indistinguishable from one that is wired up wrong and always says clean.
    dirty = bare_name_registry_entries(
        [("T", {("bare.beancount", "q1"), ("tests/x/ok.beancount", "q2")})]
    )
    check(dirty == [("T", "bare.beancount")], f"bare-name key must be flagged, got {dirty}")
    clean = bare_name_registry_entries([("T", {("tests/x/ok.beancount", "q2")})])
    check(clean == [], f"path-keyed registry must be clean, got {clean}")
    # A `\`-separated key can't match a POSIX run key either, so it must be
    # flagged, not excused. Pins the reasoning in the docstring against a
    # future "portability" edit that would silently disarm the guard.
    backslash = bare_name_registry_entries(
        [("T", {(r"tests\x\a.beancount", "q1")})]
    )
    check(
        backslash == [("T", r"tests\x\a.beancount")],
        f"backslash-separated key must be flagged, got {backslash}",
    )
    # And the real registries this script ships with must be path-keyed.
    live = bare_name_registry_entries()
    check(live == [], f"shipped registries must be path-keyed, got {live}")

    # --- find_file must not escape the corpus root (#2019 review) ---
    for escape in ("/etc/passwd", "../outside.beancount", "tests/../../outside.beancount"):
        check(
            find_file(escape, DEFAULT_TEST_DIRS) is None,
            f"find_file must reject {escape!r} rather than resolve outside REPO_ROOT",
        )

    if failures:
        for m in failures:
            print(f"self-test FAIL: {m}", file=sys.stderr)
        return 1
    print("self-test OK: stale/dangling divergence detection behaves correctly")
    return 0


# ---------------------------------------------------------------------
# Types
# ---------------------------------------------------------------------


@dataclass
class Query:
    """A single corpus entry."""

    name: str
    query: str
    notes: str | None = None
    # When True, the row order in the result is part of the contract —
    # don't sort before comparing. Auto-detected from `ORDER BY` if not
    # set explicitly.
    preserve_order: bool = False


@dataclass
class QueryRun:
    """Result of running one query against one file."""

    file: str
    query_name: str
    query: str
    match: bool
    py_rows: int = 0
    rs_rows: int = 0
    diff_samples: list[dict] = field(default_factory=list)
    # Populated when one of the tools failed (timeout, non-zero exit, etc).
    # Surfaces in the mismatch report instead of being silently swallowed
    # into an empty-result match.
    py_failure: str = ""
    rs_failure: str = ""
    # Explicit failure flags. Mirrors `ToolOutput.failed`. Lets predicates
    # gate cleanly on "the tool ran successfully" without relying on the
    # implicit invariant that `*_failure` is non-empty iff `*_failed` is
    # true. Use these in any new known-divergence fingerprint check.
    py_failed: bool = False
    rs_failed: bool = False
    # First row of rledger's output, normalized via `extract_data` (so
    # whitespace is collapsed). Used by quirk fingerprints that need to
    # distinguish "rs returned the aggregate identity (e.g. `0`)" from
    # "rs returned a real value", since `rs_rows == 1` alone can't tell
    # those apart. None when rledger returned no rows.
    rs_first_row: str | None = None


# ---------------------------------------------------------------------
# Corpus loading
# ---------------------------------------------------------------------


_ORDER_BY_RE = re.compile(r"\bORDER\s+BY\b", re.IGNORECASE)


def load_corpus(path: Path) -> list[Query]:
    """Parse the TOML corpus and validate."""
    if not path.exists():
        sys.exit(f"corpus file not found: {path}")
    with open(path, "rb") as f:
        data = tomllib.load(f)
    raw = data.get("query") or []
    if not raw:
        sys.exit(f"corpus is empty: {path}")
    queries = []
    seen_names: set[str] = set()
    for entry in raw:
        name = entry["name"]
        if name in seen_names:
            sys.exit(f"duplicate query name in corpus: {name}")
        seen_names.add(name)
        q = Query(
            name=name,
            query=entry["query"],
            notes=entry.get("notes"),
            preserve_order=entry.get("preserve_order", False),
        )
        # Auto-detect ORDER BY (only meaningful for SELECT, but BALANCES /
        # JOURNAL queries shouldn't legitimately have one anyway).
        if not q.preserve_order and _ORDER_BY_RE.search(q.query):
            q.preserve_order = True
        queries.append(q)
    if len(queries) < MIN_CORPUS_SIZE:
        sys.exit(
            f"corpus has {len(queries)} queries; minimum is {MIN_CORPUS_SIZE}. "
            "If you intentionally removed queries, lower MIN_CORPUS_SIZE."
        )
    return queries


# ---------------------------------------------------------------------
# Result extraction & comparison
# ---------------------------------------------------------------------


# A separator line in BQL tabular output is composed entirely of dashes
# and whitespace, with at least one dash. Used to find where the header
# ends and data begins, instead of slicing a fixed-size header off — the
# old approach broke whenever a tool emitted a deprecation banner ahead
# of the table.
_SEPARATOR_RE = re.compile(r"^[-\s]+$")


def extract_data(output: str, preserve_order: bool) -> list[str]:
    """Pull data rows out of bean-query / rledger tabular output.

    Detects the dashed separator line precisely (instead of slicing the
    first two lines as header) so that error banners or extra blank
    lines don't shift real rows out of view, and so a result row whose
    first column happens to be a negative number doesn't get mistaken
    for a separator.

    For ``preserve_order=False``, sort the result so the comparison is
    order-independent (correct when the query has no ``ORDER BY``). For
    ``preserve_order=True``, leave rows in iteration order — the
    ordering is part of what's being tested.
    """
    if not output or not output.strip():
        return []

    found_sep = False
    rows: list[str] = []
    for line in output.split("\n"):
        stripped = line.strip()
        if not found_sep:
            if stripped and "-" in stripped and _SEPARATOR_RE.fullmatch(stripped):
                found_sep = True
            continue
        if not stripped:
            continue
        if "row(s)" in stripped:
            break
        rows.append(" ".join(stripped.split()))

    return rows if preserve_order else sorted(rows)


@dataclass
class ToolOutput:
    """Result of invoking a query tool."""

    stdout: str
    failed: bool = False
    reason: str = ""


def run_query(
    bin_path: list[str], file_path: Path, query: str, timeout: int = 30
) -> ToolOutput:
    """Invoke a query tool, capture stdout, and surface failures.

    Returning an opaque ``"ERROR"`` string used to make every failure
    look like an empty-result match in the diff. We now distinguish
    timeouts, non-zero exits, and exceptions, and stash a short reason
    string for the mismatch report so the cause shows up in CI logs
    instead of being silently swallowed.
    """
    try:
        proc = subprocess.run(
            [*bin_path, str(file_path), query],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return ToolOutput(stdout="", failed=True, reason=f"timeout (>{timeout}s)")
    except Exception as e:  # pragma: no cover — narrow safety net
        return ToolOutput(stdout="", failed=True, reason=f"exception: {e}")
    if proc.returncode != 0:
        first_err = (proc.stderr or "").strip().splitlines()
        head = first_err[0] if first_err else "non-zero exit"
        return ToolOutput(
            stdout=proc.stdout, failed=True, reason=f"rc={proc.returncode}: {head[:120]}"
        )
    # Exit status alone is NOT enough for bean-query. beancount reports a
    # failed plugin import as a load error on stderr and then exits 0 with a
    # PARTIALLY LOADED ledger, so the comparison silently degrades to
    # rledger-full against beancount-partial. That is not evidence of
    # anything: every divergence it produces is an artifact of the missing
    # plugin, and a fixture where both sides happen to come back empty is
    # recorded as a match on no basis at all.
    #
    # This is not hypothetical. The corpus installs two third-party plugin
    # sets (`beancount_reds_plugins`, `beancount-lazy-plugins`, see
    # compat.yml), and running without them turns the four
    # `beancount-lazy-plugins` valuation fixtures into ~58 confident
    # mismatches that vanish once the plugins are present.
    #
    # `scripts/verify-first-balance-divergence.py` has guarded this since it
    # was written; the harness that produces the published number did not.
    for line in (proc.stderr or "").splitlines():
        if _LOAD_ERROR.search(line):
            return ToolOutput(
                stdout=proc.stdout, failed=True, reason=f"load error: {line.strip()[:120]}"
            )
    return ToolOutput(stdout=proc.stdout)


def diff_rows(py: list[str], rs: list[str], max_samples: int = 3) -> list[dict]:
    """Return up to max_samples differing-row records.

    Even when row counts match exactly, a single bug like #929 produces a
    fully-divergent result; printing only the first differing line makes
    that look like a small mismatch. Surface a few rows from each side so
    the actual scale of the divergence is visible.
    """
    samples = []
    if len(py) != len(rs):
        samples.append(
            {
                "kind": "row_count",
                "py_rows": len(py),
                "rs_rows": len(rs),
            }
        )
    for i, (p, r) in enumerate(zip(py, rs)):
        if p != r:
            samples.append(
                {
                    "kind": "row_diff",
                    "row": i,
                    "py": p[:120],
                    "rs": r[:120],
                }
            )
            if len(samples) >= max_samples:
                break
    return samples


# ---------------------------------------------------------------------
# Per-file test
# ---------------------------------------------------------------------


def test_one(
    file_path: Path,
    filename: str,
    query: Query,
    bean_query_bin: list[str],
    rledger_bin: list[str],
) -> QueryRun:
    py_out = run_query(bean_query_bin, file_path, query.query)
    rs_out = run_query(rledger_bin, file_path, query.query)
    py = extract_data(py_out.stdout, query.preserve_order)
    rs = extract_data(rs_out.stdout, query.preserve_order)
    # If either tool failed (non-zero exit, timeout, etc.) we never want
    # to claim a match, even if both happen to produce zero rows.
    match = (
        py == rs
        and not py_out.failed
        and not rs_out.failed
    )
    return QueryRun(
        file=filename,
        query_name=query.name,
        query=query.query,
        match=match,
        py_rows=len(py),
        rs_rows=len(rs),
        diff_samples=[] if match else diff_rows(py, rs),
        py_failure=py_out.reason,
        rs_failure=rs_out.reason,
        py_failed=py_out.failed,
        rs_failed=rs_out.failed,
        rs_first_row=rs[0] if rs else None,
    )


# ---------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------


def load_valid_files(check_results: Path) -> list[str]:
    """Pick files where both tools parsed successfully and there are postings.

    BQL diffs against an empty postings table aren't meaningful — both
    tools return zero rows trivially. Only test files with real data.

    Returns repo-relative paths (the check step records `file` as a path since
    #2016). Order is preserved, and paths are unique by construction, so the
    caller's `--max-files` budget now counts files rather than names.
    """
    files: list[str] = []
    if not check_results.exists():
        return files
    with open(check_results) as f:
        for line in f:
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            if (
                r.get("python_ok")
                and r.get("rust_ok")
                and r.get("python_posting_count", 0) > 0
            ):
                files.append(r["file"])
    return files


def find_file(name_or_path: str, test_dirs: list[Path]) -> Path | None:
    """Resolve a check-results `file` entry to a path on disk.

    `file` is a repo-relative PATH (see the `FileResult` rationale in
    `.github/workflows/compat.yml`), so the common case is a direct hit and
    involves no globbing at all. That directness is the point: the previous
    `rglob(name) -> matches[0]` made identity filesystem-order dependent, and
    four basenames collide in the corpus (#2016).

    The glob is kept only as a fallback for a BARE name, which is what a
    baseline artifact published before #2016 contains. It is deliberately
    `sorted()` (not `matches[0]` on an arbitrary walk order) so that even the
    legacy path is reproducible across machines and runs.
    """
    # Reject absolute paths and `..` before touching the filesystem.
    # `REPO_ROOT / "/etc/passwd"` is `/etc/passwd` — pathlib lets an absolute
    # operand replace the base entirely — and `..` walks out the same way. The
    # entries we generate are always relative and clean, but `--files-from` also
    # accepts a downloaded baseline artifact, and silently querying a file
    # outside the corpus is the same "this is not the file it claims to be"
    # failure this function exists to remove.
    if os.path.isabs(name_or_path) or ".." in name_or_path.split("/"):
        return None

    direct = REPO_ROOT / name_or_path
    if direct.is_file():
        return direct
    if "/" in name_or_path:
        # A path that does not exist is a genuine miss; do not fall back to
        # globbing its basename, which would resolve to a DIFFERENT file that
        # merely shares the name — exactly the bug this function stopped having.
        return None
    for d in test_dirs:
        if d.exists():
            matches = sorted(d.rglob(name_or_path))
            if matches:
                return matches[0]
    return None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    ap.add_argument(
        "--files-from",
        type=Path,
        default=Path("compat-check-results.jsonl"),
        help="JSONL of compat-check results; we pick files that passed both tools",
    )
    ap.add_argument(
        "--rledger",
        default=str(REPO_ROOT / "target" / "release" / "rledger"),
        help="Path to the rledger binary",
    )
    ap.add_argument("--bean-query", default="bean-query", help="bean-query command")
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("compat-bql-results.jsonl"),
        help="Where to write the per-run JSONL",
    )
    ap.add_argument(
        "--github-output",
        action="store_true",
        help="Append summary lines to $GITHUB_OUTPUT",
    )
    ap.add_argument(
        "--max-files",
        type=int,
        default=MAX_FILES,
        help="Test against at most this many files",
    )
    ap.add_argument(
        "--baseline",
        type=Path,
        default=None,
        help=(
            "Baseline JSONL (a previous run's --output) to gate against. "
            "Exit non-zero if any (file, query) pair that matched in the "
            "baseline now fails — i.e. a regression."
        ),
    )
    ap.add_argument(
        "--self-test",
        action="store_true",
        help=(
            "Validate the stale-divergence detection logic on synthetic data "
            "and exit (no corpus or tools required)."
        ),
    )
    args = ap.parse_args()

    if args.self_test:
        return _run_self_test()

    # Static gate, before any work: a bare-name registry key can never match a
    # run, so it is a mask that does nothing. Fail fast rather than let the run
    # report the divergence it was supposed to excuse.
    bare = bare_name_registry_entries()
    if bare:
        print(
            f"::error::{len(bare)} deliberate-divergence registry "
            f"entr{'y' if len(bare) == 1 else 'ies'} keyed by bare filename. "
            "Fixtures are identified by repo-relative path since #2016; a bare "
            "name never matches a run, so the mask silently does nothing."
        )
        for name, file in bare:
            print(f"  NOT A PATH [{name}]: {file!r} — use a repo-relative path "
                  f"with '/' separators, e.g. "
                  f"'tests/compatibility/files/<project>/{Path(file).name}'")
        return 1

    queries = load_corpus(args.corpus)
    print(f"Corpus: {len(queries)} queries from {args.corpus.name}")

    valid = load_valid_files(args.files_from)
    if not valid:
        sys.exit(
            f"no valid files found in {args.files_from}. Run the check "
            "phase first or pass --files-from."
        )

    test_dirs = DEFAULT_TEST_DIRS

    # Resolve to real paths BEFORE prioritization: `is_plugin_fixture` below
    # needs the path's directory segments, which the entry alone doesn't
    # guarantee is on disk. Since #2016 the `--files-from` JSONL stores a
    # repo-relative path (see `FileResult` in `.github/workflows/compat.yml`),
    # so this is a direct existence check rather than a basename glob.
    resolved: list[tuple[str, Path]] = []
    unresolved: list[str] = []
    for filename in valid:
        path = find_file(filename, test_dirs)
        if path is None:
            unresolved.append(filename)
        else:
            resolved.append((filename, path))

    # Prioritize plugin-fixture files so they always make the MAX_FILES
    # cut. These exercise specific plugin code paths (Phase 2 of the
    # plugin-testing-quality plan, see #992) — losing them to random
    # truncation defeats the purpose of having them. Identification is
    # by resolved path: any fixture whose path includes a `plugins`
    # directory segment counts (matches the `get_category` convention
    # in `.github/workflows/compat.yml`).
    def is_plugin_fixture(path: Path) -> bool:
        return "plugins" in path.parts

    plugin_pairs = [(fn, p) for (fn, p) in resolved if is_plugin_fixture(p)]
    other_pairs = [(fn, p) for (fn, p) in resolved if not is_plugin_fixture(p)]
    remaining_budget = max(0, args.max_files - len(plugin_pairs))
    selected_pairs = plugin_pairs + other_pairs[:remaining_budget]

    if plugin_pairs:
        print(
            f"Testing against {len(selected_pairs)} files "
            f"({len(plugin_pairs)} plugin fixtures + "
            f"{len(selected_pairs) - len(plugin_pairs)} other)"
        )
    else:
        print(f"Testing against {len(selected_pairs)} files")

    rledger_bin = [args.rledger, "query"]
    bean_query_bin = [args.bean_query]

    # Build (file, filename, query) cases
    cases = []
    for filename, path in selected_pairs:
        for q in queries:
            cases.append((path, filename, q))

    if not cases:
        # An empty case list used to silently produce a 0-runs/0-mismatches
        # green result, which is exactly the failure mode that hid #929 for
        # so long. Bail with an actionable message instead.
        sys.exit(
            f"no test cases generated. Checked {len(valid)} files "
            f"against {len(queries)} queries; "
            f"{len(unresolved)} files could not be located on disk: "
            f"{unresolved[:5]}{'...' if len(unresolved) > 5 else ''}"
        )

    workers = min(multiprocessing.cpu_count(), 8)
    print(f"Running {len(cases)} pairs across {workers} workers...")

    results: list[QueryRun] = []
    with ThreadPoolExecutor(max_workers=workers) as ex:
        futures = [
            ex.submit(test_one, p, fn, q, bean_query_bin, rledger_bin)
            for (p, fn, q) in cases
        ]
        for fut in as_completed(futures):
            try:
                results.append(fut.result())
            except Exception as e:
                print(f"error in worker: {e}", file=sys.stderr)

    # Tally. `total` counts file×query *runs*, not distinct corpus
    # queries; we expose both to make the CI summary unambiguous.
    # A run where either tool failed proves nothing, so it must not be
    # averaged into the match rate. Counting it as a mismatch (which is what
    # `match=False` does) quietly converts an environment problem — a missing
    # third-party plugin, a timeout — into a lower compatibility number, and
    # the number is the thing people read.
    #
    # Excluding them silently would trade one blind spot for another, so
    # they are also surfaced as a CI annotation. Deliberately a warning and
    # not a hard failure: in CI the corpus plugins ARE installed (compat.yml),
    # so a load error there means the install broke and is worth shouting
    # about — but a timeout lands in this same bucket, and failing the suite
    # on a slow runner would make it flaky for a reason unrelated to
    # compatibility.
    inconclusive = [r for r in results if r.py_failed or r.rs_failed]
    conclusive = [r for r in results if not (r.py_failed or r.rs_failed)]
    total = len(conclusive)
    matching = sum(1 for r in conclusive if r.match)
    known_py = sum(
        1 for r in conclusive
        if not r.match and _is_known_python_divergence(r)
    )
    known_rs = sum(
        1 for r in conclusive
        if not r.match and _is_known_rust_divergence(r)
    )
    known_div = known_py + known_rs
    real_mismatches = total - matching - known_div
    effective_match = matching + known_div
    pct = effective_match * 100 // total if total > 0 else 0
    # The RAW rate: what matched with nothing masked. `pct` is the number that
    # gets quoted (release notes, badge, the job summary), and quoting it alone
    # invites exactly the doubt #1902 raised - is the headline real, or is it
    # the registry doing the work? Printing both makes the masking's size
    # visible instead of inferable, and it moves: #1927 pinned 51 more pairs
    # (all proven upstream bugs), which widened the gap between these two by
    # about 2 points in a single PR. A reader who sees only the effective
    # figure cannot tell that happened.
    raw_pct = matching * 100 // total if total > 0 else 0

    # Per-query empty-result rate. A query that returns 0 rows on >50%
    # of files isn't actually being tested by the corpus and should
    # either be reformulated or paired with data that exercises it.
    #
    # Over `conclusive`, not `results`: a failed run has empty stdout, so it
    # scores as `py_rows == 0 and rs_rows == 0` and would be indistinguishable
    # from a query the corpus genuinely fails to exercise. A missing plugin or
    # a timeout would then be reported as poor corpus coverage — the same
    # mistake as folding those runs into the match rate, one metric over.
    empties_by_query: dict[str, int] = {}
    runs_by_query: dict[str, int] = {}
    for r in conclusive:
        runs_by_query[r.query_name] = runs_by_query.get(r.query_name, 0) + 1
        if r.py_rows == 0 and r.rs_rows == 0:
            empties_by_query[r.query_name] = empties_by_query.get(r.query_name, 0) + 1

    # Use "Runs" rather than "Queries" so the count of file×query pairs
    # isn't mistaken for the corpus size. Keep the GitHub Output keys
    # (bql_total / bql_match) the same — the workflow's chart-generation
    # step downstream consumes those names.
    print()
    print(f"Corpus queries:      {len(queries)}")
    # `valid` is every file BOTH tools parse with postings; `selected_pairs` is
    # what this run actually queried, capped by --max-files. Reporting the
    # former as "Files tested" overstated coverage by 22x at the old default
    # (673 eligible, 30 queried) — and it is the one number a reader quotes.
    _covered = 100 * len(selected_pairs) / len(valid) if valid else 0.0
    print(f"Corpus files eligible: {len(valid)}")
    print(
        f"Files queried:       {len(selected_pairs)} "
        f"({_covered:.0f}% of eligible; --max-files={args.max_files})"
    )
    print(f"Runs tested:         {total}  (file × query)")
    print(f"Runs matching:       {matching}")
    if inconclusive:
        print(
            f"Inconclusive:        {len(inconclusive)} run(s) where a tool failed "
            f"— EXCLUDED from the rates below"
        )
        for r in inconclusive[:5]:
            reason = r.py_failure or r.rs_failure or "?"
            print(f"    {r.file} | {r.query_name}: {reason[:96]}")
        load_errs = [r for r in inconclusive
                     if "load error" in (r.py_failure or r.rs_failure or "")]
        if load_errs:
            files = sorted({r.file for r in load_errs})
            print(
                f"::warning::{len(load_errs)} run(s) across {len(files)} fixture(s) "
                f"could not be compared because a tool reported a load error and "
                f"still exited 0 — usually a missing third-party corpus plugin. "
                f"Those runs are excluded from the match rates. Files: "
                f"{', '.join(files[:5])}"
            )
    print(f"Raw match:           {matching}/{total} ({raw_pct}%)  [nothing masked]")
    print(f"Known Python diffs:  {known_py}")
    print(f"Known Rust diffs:    {known_rs}")
    print(f"Real mismatches:     {real_mismatches}")
    print(
        f"Effective match:     {effective_match}/{total} ({pct}%)"
        f"  [+{known_div} masked, {pct - raw_pct} pts over raw]"
    )

    # Empty-result warnings — corpus signal, not a test failure
    print()
    print("=== Per-query coverage ===")
    for q in queries:
        runs = runs_by_query.get(q.name, 0)
        empties = empties_by_query.get(q.name, 0)
        empty_frac = empties / runs if runs else 0.0
        flag = "⚠️ " if empty_frac > EMPTY_RESULT_WARNING_FRACTION else "  "
        print(
            f"  {flag}{q.name}: {runs - empties}/{runs} non-empty"
            f" ({100 * (1 - empty_frac):.0f}%)"
        )
    weak = [
        q
        for q in queries
        if empties_by_query.get(q.name, 0) / max(runs_by_query.get(q.name, 1), 1)
        > EMPTY_RESULT_WARNING_FRACTION
    ]
    if weak:
        print()
        print(
            f"WARN: {len(weak)} queries return 0 rows on >50% of files — "
            "the corpus needs data that exercises them, or the query needs "
            "reformulation. Names: " + ", ".join(q.name for q in weak)
        )

    # Mismatch detail (up to 3 differing rows per case, with row counts)
    bad = [r for r in results if not r.match]
    if bad:
        print()
        print(f"=== {len(bad)} mismatches ===")
        for r in bad:
            if _is_known_python_divergence(r):
                label = "KNOWN-PY"
            elif _is_known_rust_divergence(r):
                label = "KNOWN-RS"
            else:
                label = "MISMATCH"
            print(f"  {label}: {r.file} | {r.query_name}")
            if r.py_failure:
                print(f"    py FAILED: {r.py_failure}")
            if r.rs_failure:
                print(f"    rs FAILED: {r.rs_failure}")
            for s in r.diff_samples:
                if s["kind"] == "row_count":
                    print(f"    row count: py={s['py_rows']} rs={s['rs_rows']}")
                else:
                    print(f"    row {s['row']}:")
                    print(f"      py: {s['py']}")
                    print(f"      rs: {s['rs']}")

    # JSONL output
    with open(args.output, "w") as f:
        for r in results:
            row = {
                "file": r.file,
                "query_name": r.query_name,
                "query": r.query[:80],
                "match": r.match,
                "py_rows": r.py_rows,
                "rs_rows": r.rs_rows,
                "diff_samples": r.diff_samples,
            }
            if r.py_failure:
                row["py_failure"] = r.py_failure
            if r.rs_failure:
                row["rs_failure"] = r.rs_failure
            f.write(json.dumps(row) + "\n")

    if args.github_output:
        out_path = os.environ.get("GITHUB_OUTPUT")
        if out_path:
            with open(out_path, "a") as f:
                f.write(f"bql_total={total}\n")
                f.write(f"bql_match={matching}\n")
                f.write(f"bql_known_divergences={known_div}\n")
                f.write(f"bql_known_python={known_py}\n")
                f.write(f"bql_known_rust={known_rs}\n")
                f.write(f"bql_pct={pct}\n")
                f.write(f"bql_raw_pct={raw_pct}\n")
                f.write(f"bql_weak_queries={len(weak)}\n")

    # Stale-mask gate. A KNOWN_*_DIVERGENCE entry whose pair now MATCHES
    # bean-query is a stale mask — it would silently absorb a future regression
    # on that pair (the failure mode the registry rationale warns about), so fail
    # and force its removal. Dangling entries (no run exercises them) are warned
    # but not failed: a partially-fetched corpus can transiently drop a file, and
    # a warning is enough to prompt a cleanup.
    stale, dangling = stale_divergence_entries(results)
    for name, (file, query) in sorted(dangling):
        print(
            f"::warning::deliberate-divergence registry {name}: entry "
            f"({file!r}, {query!r}) is dangling — no run exercises it "
            "(fixture or query renamed/removed?)."
        )
    if stale:
        print()
        print(
            f"::error::{len(stale)} deliberate-divergence registry "
            f"entr{'y' if len(stale) == 1 else 'ies'} no longer diverge — the "
            "mask is stale and would silently absorb a future regression on the "
            "same pair."
        )
        for name, (file, query) in sorted(stale):
            print(
                f"  STALE [{name}]: ({file!r}, {query!r}) now matches bean-query."
                " Remove the entry (and its code comment / tracking-issue note)."
            )
        return 1

    # Regression gate. Compare against a baseline run (e.g. main's results from
    # the `compatibility` branch) and FAIL if any (file, query) pair that
    # *matched* in the baseline now fails. Comparing per-pair — not the overall
    # percentage — is robust to corpus/coverage changes: a pair that simply drops
    # out of the run (its file no longer qualifies) is NOT counted, only a real
    # true→false flip is. This is the gate that would have caught the JOURNAL
    # regression (90→12 matches) that previously merged unblocked.
    #
    # The pair key's file component became a repo-relative path in #2016. The
    # first run after that change compares against a name-keyed baseline, so no
    # pair matches and nothing is gated — by the same "dropped pairs don't
    # count" rule above. One cycle of reduced sensitivity, then the published
    # baseline is path-keyed too.
    if args.baseline and args.baseline.exists():
        baseline_passing = set()
        with open(args.baseline) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    b = json.loads(line)
                except json.JSONDecodeError:
                    # Tolerate a truncated/corrupt baseline line rather than
                    # crashing with a traceback that obscures the real result.
                    # A wholly unparsable baseline yields an empty set → no gate
                    # this run (safer than a spurious block).
                    continue
                if b.get("match"):
                    baseline_passing.add((b.get("file"), b.get("query_name")))

        # A run where a tool failed is NOT a regression — it is an absence of
        # evidence, the same reasoning `stale_divergence_entries` already
        # applies. Without this, making load errors visible would itself fire
        # the gate: a pair that "matched" only because beancount loaded a
        # partial ledger and both sides came back empty is a FALSE match, and
        # honestly reclassifying it as inconclusive would be reported as a
        # regression it never was.
        regressed = [
            r
            for r in results
            if not r.match
            and not (r.py_failed or r.rs_failed)
            and (r.file, r.query_name) in baseline_passing
        ]
        if regressed:
            print()
            print(
                f"::error::BQL compat regression: {len(regressed)} (file, query) "
                f"pair(s) that matched on the baseline now fail"
            )
            for r in sorted(regressed, key=lambda r: (r.query_name, r.file))[:30]:
                print(f"  REGRESSED: {r.query_name} | {r.file}")
            if len(regressed) > 30:
                print(f"  ... and {len(regressed) - 30} more")
            return 1
        print(
            f"\nNo BQL regressions vs baseline "
            f"({len(baseline_passing)} baseline-passing pairs checked)."
        )

    return 0


if __name__ == "__main__":
    sys.exit(main())
