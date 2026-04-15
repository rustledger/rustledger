#!/usr/bin/env python3
"""
Analyze Compatibility Test Results

Generates a detailed root cause analysis of mismatches between
Python beancount and rustledger.

Usage:
    python scripts/analyze-compat-results.py [results_dir]
"""

import json
import sys
from collections import Counter, defaultdict
from pathlib import Path


def load_jsonl(path: Path) -> list[dict]:
    """Load a JSONL file, skipping malformed lines."""
    results = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                try:
                    results.append(json.loads(line))
                except json.JSONDecodeError:
                    # Skip malformed JSON lines (may occur from truncated output or encoding issues)
                    continue
    return results


def analyze_check_results(results: list[dict]) -> dict:
    """Analyze bean-check vs rledger check results."""
    analysis = {
        "total": len(results),
        "matching": 0,
        "mismatching": 0,
        "categories": Counter(),
        "mismatch_patterns": defaultdict(list),
    }

    for r in results:
        if r.get("match"):
            analysis["matching"] += 1
        else:
            analysis["mismatching"] += 1

            # Categorize the mismatch
            py = r.get("python", {})
            rs = r.get("rust", {})
            py_exit = py.get("exit", -1)
            rs_exit = rs.get("exit", -1)
            py_parse_err = py.get("parse_error", False)
            rs_parse_err = rs.get("parse_error", False)

            if py_exit == 0 and rs_exit != 0:
                category = "python_pass_rust_fail"
            elif py_exit != 0 and rs_exit == 0:
                category = "python_fail_rust_pass"
            elif py_parse_err and not rs_parse_err:
                category = "python_parse_error_only"
            elif rs_parse_err and not py_parse_err:
                category = "rust_parse_error_only"
            else:
                category = "different_errors"

            analysis["categories"][category] += 1
            analysis["mismatch_patterns"][category].append(r.get("file", "unknown"))

    return analysis


def analyze_bql_results(results: list[dict]) -> dict:
    """Analyze BQL query results."""
    analysis = {
        "total": len(results),
        "matching": 0,
        "mismatching": 0,
        "categories": Counter(),
        "by_query": defaultdict(lambda: {"match": 0, "mismatch": 0}),
        "sample_failures": defaultdict(list),
    }

    for r in results:
        query = r.get("query", "unknown")[:40]  # Truncate for display
        category = r.get("category", "unknown")

        if r.get("match"):
            analysis["matching"] += 1
            analysis["by_query"][query]["match"] += 1
        else:
            analysis["mismatching"] += 1
            analysis["by_query"][query]["mismatch"] += 1
            analysis["categories"][category] += 1

            if len(analysis["sample_failures"][category]) < 3:
                analysis["sample_failures"][category].append({
                    "file": r.get("file", "unknown"),
                    "query": query,
                    "py_rows": r.get("py_rows", "?"),
                    "rs_rows": r.get("rs_rows", "?"),
                })

    return analysis


def analyze_ast_results(results: list[dict]) -> dict:
    """Analyze AST/directive comparison results."""
    analysis = {
        "total": len(results),
        "full_match": 0,
        "partial_match": 0,
        "mismatch": 0,
        "issues": Counter(),
        "sample_issues": [],
    }

    for r in results:
        if r.get("full_match"):
            analysis["full_match"] += 1
        else:
            if r.get("accounts_match") and r.get("posting_count_match"):
                analysis["partial_match"] += 1
            else:
                analysis["mismatch"] += 1

            # Track specific issues
            if not r.get("accounts_match"):
                analysis["issues"]["accounts_differ"] += 1
            if not r.get("posting_count_match"):
                analysis["issues"]["posting_count_differs"] += 1
            if not r.get("error_count_match"):
                analysis["issues"]["error_presence_differs"] += 1

            # Sample issues
            if len(analysis["sample_issues"]) < 5:
                sample = {"file": r.get("file", "unknown")}
                if r.get("accounts_only_python"):
                    sample["py_only_accounts"] = r["accounts_only_python"][:3]
                if r.get("accounts_only_rust"):
                    sample["rs_only_accounts"] = r["accounts_only_rust"][:3]
                if r.get("posting_count_diff"):
                    sample["posting_diff"] = r["posting_count_diff"]
                analysis["sample_issues"].append(sample)

    return analysis


def print_report(results_dir: Path):
    """Print a comprehensive analysis report."""
    print("=" * 70)
    print("COMPATIBILITY ROOT CAUSE ANALYSIS")
    print("=" * 70)
    print()

    # Find most recent results
    check_files = sorted(results_dir.glob("results_*.jsonl"), reverse=True)
    bql_files = sorted(results_dir.glob("bql_results_*.jsonl"), reverse=True)
    ast_files = sorted(results_dir.glob("ast_results_*.jsonl"), reverse=True)

    # Analyze check results
    if check_files:
        print("## Check Results (bean-check vs rledger check)")
        print("-" * 50)
        data = load_jsonl(check_files[0])
        analysis = analyze_check_results(data)

        match_pct = analysis["matching"] * 100 // analysis["total"] if analysis["total"] else 0
        print(f"Files tested:  {analysis['total']}")
        print(f"Matching:      {analysis['matching']} ({match_pct}%)")
        print(f"Mismatching:   {analysis['mismatching']}")
        print()

        if analysis["categories"]:
            print("Mismatch breakdown:")
            for cat, count in analysis["categories"].most_common():
                print(f"  {cat}: {count}")
                # Show sample files
                samples = analysis["mismatch_patterns"][cat][:3]
                for f in samples:
                    print(f"    - {f}")
        print()

    # Analyze BQL results
    if bql_files:
        print("## BQL Query Results")
        print("-" * 50)
        data = load_jsonl(bql_files[0])
        analysis = analyze_bql_results(data)

        match_pct = analysis["matching"] * 100 // analysis["total"] if analysis["total"] else 0
        print(f"Queries tested: {analysis['total']}")
        print(f"Matching:       {analysis['matching']} ({match_pct}%)")
        print(f"Mismatching:    {analysis['mismatching']}")
        print()

        if analysis["categories"]:
            print("Mismatch categories:")
            for cat, count in analysis["categories"].most_common():
                print(f"  {cat}: {count}")

            print()
            print("Sample failures by category:")
            for cat, samples in analysis["sample_failures"].items():
                print(f"  [{cat}]")
                for s in samples:
                    print(f"    {s['file']}: {s['query']} (py={s['py_rows']}, rs={s['rs_rows']})")
        print()

        print("Match rate by query type:")
        for query, stats in sorted(analysis["by_query"].items()):
            total = stats["match"] + stats["mismatch"]
            pct = stats["match"] * 100 // total if total else 0
            status = "OK" if pct >= 80 else "WARN" if pct >= 50 else "FAIL"
            print(f"  [{status}] {query}... {stats['match']}/{total} ({pct}%)")
        print()

    # Analyze AST results
    if ast_files:
        print("## AST/Directive Results")
        print("-" * 50)
        data = load_jsonl(ast_files[0])
        analysis = analyze_ast_results(data)

        match_pct = analysis["full_match"] * 100 // analysis["total"] if analysis["total"] else 0
        print(f"Files tested:  {analysis['total']}")
        print(f"Full match:    {analysis['full_match']} ({match_pct}%)")
        print(f"Partial match: {analysis['partial_match']}")
        print(f"Mismatch:      {analysis['mismatch']}")
        print()

        if analysis["issues"]:
            print("Issue types:")
            for issue, count in analysis["issues"].most_common():
                print(f"  {issue}: {count}")

        if analysis["sample_issues"]:
            print()
            print("Sample issues:")
            for s in analysis["sample_issues"]:
                print(f"  {s['file']}:")
                if "py_only_accounts" in s:
                    print(f"    Python-only accounts: {s['py_only_accounts']}")
                if "rs_only_accounts" in s:
                    print(f"    Rust-only accounts: {s['rs_only_accounts']}")
                if "posting_diff" in s:
                    print(f"    Posting count diff: {s['posting_diff']:+d}")
        print()

    # Summary recommendations
    print("=" * 70)
    print("RECOMMENDATIONS")
    print("=" * 70)
    print()
    print("1. rust_empty issues: Investigate why Rust returns no data for some queries")
    print("   - Check if certain directives are not being parsed")
    print("   - Verify BQL FROM clause is processing all entries")
    print()
    print("2. python_empty issues: May indicate Rust parsing additional entries")
    print("   - Could be auto-generated entries (prices, opens)")
    print("   - Check plugin behavior differences")
    print()
    print("3. data_diff issues: Row counts match but values differ")
    print("   - Check sorting/ordering differences")
    print("   - Verify numeric formatting (decimal places)")
    print()
    print("4. accounts_differ: Account extraction differences")
    print("   - Check implicit account generation (auto_accounts plugin)")
    print("   - Verify Open directive parsing")
    print()


def main():
    if len(sys.argv) > 1:
        results_dir = Path(sys.argv[1])
    else:
        results_dir = Path("tests/compatibility-results")

    if not results_dir.exists():
        print(f"Error: Results directory not found: {results_dir}")
        sys.exit(1)

    print_report(results_dir)


if __name__ == "__main__":
    main()
