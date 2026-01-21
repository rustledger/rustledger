#!/usr/bin/env python3
"""
Benchmark comparison and regression detection tool.

This script compares benchmark results from hyperfine JSON output against
historical baselines stored in the benchmarks branch.

Usage:
    # Compare latest local benchmark against history
    ./scripts/bench-compare.py bench-validation.json

    # Compare against specific baseline
    ./scripts/bench-compare.py bench-validation.json --baseline 30.0

    # Check for regressions (exit 1 if regression detected)
    ./scripts/bench-compare.py bench-validation.json --fail-on-regression
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Optional


# Default regression threshold (percentage)
DEFAULT_THRESHOLD = 15.0


def load_hyperfine_results(filepath: Path) -> dict[str, float]:
    """Load results from hyperfine JSON output."""
    with open(filepath) as f:
        data = json.load(f)

    results = {}
    for r in data.get("results", []):
        name = r.get("command", "unknown")
        mean_ms = r.get("mean", 0) * 1000  # Convert to milliseconds
        results[name] = round(mean_ms, 2)

    return results


def load_baseline_from_history(history_file: Path) -> Optional[float]:
    """Load the most recent rustledger result from history."""
    if not history_file.exists():
        return None

    try:
        with open(history_file) as f:
            history = json.load(f)
        if history:
            return history[-1].get("rustledger_ms")
    except (json.JSONDecodeError, KeyError):
        # History file may be malformed or missing expected fields - safe to ignore
        # and fall through to return None (no baseline available)
        pass

    return None


def compare_results(
    current: float,
    baseline: float,
    threshold: float = DEFAULT_THRESHOLD,
) -> tuple[float, str]:
    """Compare current vs baseline, return (change_percent, status)."""
    if baseline <= 0:
        return 0.0, "no_baseline"

    change = ((current - baseline) / baseline) * 100

    if change > threshold:
        status = "regression"
    elif change > 5:
        status = "warning"
    elif change < -5:
        status = "improvement"
    else:
        status = "stable"

    return change, status


def main():
    parser = argparse.ArgumentParser(
        description="Compare benchmark results and detect regressions"
    )
    parser.add_argument(
        "results_file",
        type=Path,
        help="Hyperfine JSON results file",
    )
    parser.add_argument(
        "--baseline",
        type=float,
        default=None,
        help="Baseline time in ms (overrides history lookup)",
    )
    parser.add_argument(
        "--history",
        type=Path,
        default=None,
        help="Path to history JSON file for baseline lookup",
    )
    parser.add_argument(
        "--threshold",
        type=float,
        default=DEFAULT_THRESHOLD,
        help=f"Regression threshold percentage (default: {DEFAULT_THRESHOLD}%%)",
    )
    parser.add_argument(
        "--fail-on-regression",
        action="store_true",
        help="Exit with code 1 if regression detected",
    )
    parser.add_argument(
        "--tool",
        default="rustledger",
        help="Tool name to check for regression (default: rustledger)",
    )

    args = parser.parse_args()

    # Load current results
    if not args.results_file.exists():
        print(f"Error: Results file not found: {args.results_file}")
        sys.exit(1)

    results = load_hyperfine_results(args.results_file)

    if args.tool not in results:
        print(f"Error: Tool '{args.tool}' not found in results")
        print(f"Available tools: {list(results.keys())}")
        sys.exit(1)

    current = results[args.tool]

    # Get baseline
    baseline = args.baseline
    if baseline is None and args.history:
        baseline = load_baseline_from_history(args.history)

    # Print all results
    print("=" * 60)
    print("Benchmark Results")
    print("=" * 60)
    for tool, time_ms in sorted(results.items(), key=lambda x: x[1]):
        marker = " <--" if tool == args.tool else ""
        print(f"  {tool:20} {time_ms:8.1f} ms{marker}")
    print()

    # Compare against baseline if available
    if baseline is not None:
        change, status = compare_results(current, baseline, args.threshold)

        print("=" * 60)
        print("Regression Check")
        print("=" * 60)
        print(f"  Tool:      {args.tool}")
        print(f"  Current:   {current:.1f} ms")
        print(f"  Baseline:  {baseline:.1f} ms")
        print(f"  Change:    {change:+.1f}%")
        print(f"  Threshold: {args.threshold}%")
        print(f"  Status:    {status.upper()}")
        print()

        # Status symbols
        status_symbols = {
            "regression": "[FAIL] Regression detected",
            "warning": "[WARN] Performance degradation",
            "improvement": "[GOOD] Performance improved",
            "stable": "[OK] Stable performance",
            "no_baseline": "[SKIP] No baseline available",
        }
        print(status_symbols.get(status, status))

        if status == "regression" and args.fail_on_regression:
            sys.exit(1)
    else:
        print("No baseline available for comparison.")
        print("Run benchmarks with --history to compare against historical data.")


if __name__ == "__main__":
    main()
