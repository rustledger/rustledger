#!/usr/bin/env python3
"""BQL compatibility harness — diff bean-query vs rledger output row-by-row.

Loads a query corpus from a TOML file (default
`tests/compatibility/bql-queries.toml`), runs each query against every
test file that both tools could parse, and reports per-query/per-file
matches and mismatches.

The README in `tests/compatibility/` documents how to add queries and
why the corpus is biased toward semantic-divergence cases.

Usage (CI):

    python3 scripts/compat-bql-test.py \\
        --corpus tests/compatibility/bql-queries.toml \\
        --files-from compat-check-results.jsonl \\
        --rledger ./target/release/rledger \\
        --output compat-bql-results.jsonl \\
        --github-output >> "$GITHUB_OUTPUT"

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
from typing import Any

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
MIN_CORPUS_SIZE = 13

# Files we test against. 30 is enough breadth for representative coverage
# without being slow; tune up if the corpus grows substantially.
MAX_FILES = 30

# A query that returns 0 rows on more than this fraction of files isn't
# really being tested by the corpus — flag it loudly so we know to add
# data that exercises it.
EMPTY_RESULT_WARNING_FRACTION = 0.5

# Known cases where Python beanquery has a bug rather than rledger.
# These don't count against compat percentage. See referenced beanquery
# issues for context.
KNOWN_PYTHON_DIVERGENCES = {
    # beancount/beanquery#275: position display truncates precision
    "testdata_source_generic_importer_test_invalid_journal.beancount",
    # Interpolation quantization: Python rounds residual to zero
    "testdata_source_ofx_test_non_default_capital_gains_journal.beancount",
    # DisplayContext common vs max precision (#724)
    "testdata_source_ofx_test_fidelity_journal.beancount",
}


# ---------------------------------------------------------------------
# Types
# ---------------------------------------------------------------------


@dataclass
class Query:
    """A single corpus entry."""

    name: str
    query: str
    form: str = "select"  # "select" | "balances" | "journal"
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
            form=entry.get("form", "select"),
            notes=entry.get("notes"),
            preserve_order=entry.get("preserve_order", False),
        )
        # Auto-detect ORDER BY for SELECT queries that didn't set it.
        if not q.preserve_order and q.form == "select" and _ORDER_BY_RE.search(q.query):
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


def extract_data(output: str, preserve_order: bool) -> list[str]:
    """Strip headers, separators, and row counts; normalize whitespace.

    For preserve_order=False, sort the result so the comparison is
    order-independent (correct for queries without ORDER BY). For
    preserve_order=True, leave rows in iteration order — the ordering
    is part of what's being tested.
    """
    lines = []
    for line in output.strip().split("\n")[2:]:
        line = line.strip()
        if line and not line.startswith("-") and "row(s)" not in line:
            lines.append(" ".join(line.split()))
    return lines if preserve_order else sorted(lines)


def run_query(
    bin_path: list[str], file_path: Path, query: str, timeout: int = 30
) -> str:
    """Invoke a query tool and return stdout. Returns 'ERROR' on failure."""
    try:
        proc = subprocess.run(
            [*bin_path, str(file_path), query],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return proc.stdout
    except Exception:
        return "ERROR"


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
    py = extract_data(py_out, query.preserve_order)
    rs = extract_data(rs_out, query.preserve_order)
    match = py == rs
    return QueryRun(
        file=filename,
        query_name=query.name,
        query=query.query,
        match=match,
        py_rows=len(py),
        rs_rows=len(rs),
        diff_samples=[] if match else diff_rows(py, rs),
    )


# ---------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------


def load_valid_files(check_results: Path) -> list[str]:
    """Pick files where both tools parsed successfully and there are postings.

    BQL diffs against an empty postings table aren't meaningful — both
    tools return zero rows trivially. Only test files with real data.
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


def find_file(filename: str, test_dirs: list[Path]) -> Path | None:
    for d in test_dirs:
        if d.exists():
            matches = list(d.rglob(filename))
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
    args = ap.parse_args()

    queries = load_corpus(args.corpus)
    print(f"Corpus: {len(queries)} queries from {args.corpus.name}")

    valid = load_valid_files(args.files_from)
    if not valid:
        sys.exit(
            f"no valid files found in {args.files_from}. Run the check "
            "phase first or pass --files-from."
        )
    valid = valid[: args.max_files]
    print(f"Testing against {len(valid)} files")

    test_dirs = DEFAULT_TEST_DIRS

    rledger_bin = [args.rledger, "query"]
    bean_query_bin = [args.bean_query]

    # Build (file, filename, query) cases
    cases = []
    for filename in valid:
        path = find_file(filename, test_dirs)
        if not path:
            continue
        for q in queries:
            cases.append((path, filename, q))

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

    # Tally
    total = len(results)
    matching = sum(1 for r in results if r.match)
    known_div = sum(
        1 for r in results if not r.match and r.file in KNOWN_PYTHON_DIVERGENCES
    )
    real_mismatches = total - matching - known_div
    effective_match = matching + known_div
    pct = effective_match * 100 // total if total > 0 else 0

    # Per-query empty-result rate. A query that returns 0 rows on >50%
    # of files isn't actually being tested by the corpus and should
    # either be reformulated or paired with data that exercises it.
    empties_by_query: dict[str, int] = {}
    runs_by_query: dict[str, int] = {}
    for r in results:
        runs_by_query[r.query_name] = runs_by_query.get(r.query_name, 0) + 1
        if r.py_rows == 0 and r.rs_rows == 0:
            empties_by_query[r.query_name] = empties_by_query.get(r.query_name, 0) + 1

    print()
    print(f"Queries tested: {total}")
    print(f"Queries matching: {matching}")
    print(f"Known Python divergences: {known_div}")
    print(f"Real mismatches: {real_mismatches}")
    print(f"Effective match: {effective_match}/{total} ({pct}%)")

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
            label = "KNOWN" if r.file in KNOWN_PYTHON_DIVERGENCES else "MISMATCH"
            print(f"  {label}: {r.file} | {r.query_name}")
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
            f.write(
                json.dumps(
                    {
                        "file": r.file,
                        "query_name": r.query_name,
                        "query": r.query[:80],
                        "match": r.match,
                        "py_rows": r.py_rows,
                        "rs_rows": r.rs_rows,
                        "diff_samples": r.diff_samples,
                    }
                )
                + "\n"
            )

    if args.github_output:
        out_path = os.environ.get("GITHUB_OUTPUT")
        if out_path:
            with open(out_path, "a") as f:
                f.write(f"bql_total={total}\n")
                f.write(f"bql_match={matching}\n")
                f.write(f"bql_known_divergences={known_div}\n")
                f.write(f"bql_pct={pct}\n")
                f.write(f"bql_weak_queries={len(weak)}\n")

    return 0


if __name__ == "__main__":
    sys.exit(main())
