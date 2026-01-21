#!/usr/bin/env python3
"""
AST/Directive Comparison Test (Parallel)

Compares the parsed output between Python beancount and rustledger,
going beyond exit codes to compare:
- Directive counts by type
- Extracted accounts
- Transaction counts
- Error counts

Usage:
    python scripts/compat-ast-test.py [directory]
    python scripts/compat-ast-test.py tests/compat/files

Environment variables:
    PARALLEL_JOBS: Number of parallel workers (default: CPU count, max 8)
"""

import json
import subprocess
import sys
import os
import multiprocessing
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

# Try to import beancount
try:
    from beancount import loader
    from beancount.core import data
    BEANCOUNT_AVAILABLE = True
except ImportError:
    BEANCOUNT_AVAILABLE = False
    print("Warning: beancount not installed, Python comparison disabled")

# Parallel settings
MAX_WORKERS = min(int(os.environ.get('PARALLEL_JOBS', multiprocessing.cpu_count())), 16)


@dataclass
class ParseResult:
    """Result of parsing a beancount file."""
    accounts: set = field(default_factory=set)
    directive_counts: dict = field(default_factory=dict)
    total_directives: int = 0
    error_count: int = 0
    transaction_count: int = 0
    posting_count: int = 0  # COUNT(*) in BQL counts postings
    balance_count: int = 0
    open_count: int = 0
    price_count: int = 0
    raw_errors: list = field(default_factory=list)


@dataclass
class ComparisonResult:
    """Result of comparing Python vs Rust parsing."""
    file: str
    python: Optional[ParseResult]
    rust: Optional[ParseResult]

    # Comparison flags
    accounts_match: bool = False
    posting_count_match: bool = False
    error_count_match: bool = False

    # Differences
    accounts_only_python: set = field(default_factory=set)
    accounts_only_rust: set = field(default_factory=set)
    posting_count_diff: int = 0  # rust - python

    @property
    def full_match(self) -> bool:
        return (self.accounts_match and
                self.posting_count_match and
                self.error_count_match)


def parse_with_python(file_path: Path) -> Optional[ParseResult]:
    """Parse a file with Python beancount and extract structured data."""
    if not BEANCOUNT_AVAILABLE:
        return None

    try:
        entries, errors, options = loader.load_file(str(file_path))
    except Exception as e:
        return ParseResult(error_count=1, raw_errors=[str(e)])

    result = ParseResult()
    result.error_count = len(errors)
    result.raw_errors = [str(e) for e in errors[:5]]  # Keep first 5
    result.total_directives = len(entries)

    type_counts = Counter()
    for entry in entries:
        type_name = type(entry).__name__
        type_counts[type_name] += 1

        if isinstance(entry, data.Open):
            result.accounts.add(entry.account)
            result.open_count += 1
        elif isinstance(entry, data.Transaction):
            result.transaction_count += 1
            result.posting_count += len(entry.postings)
            # Also extract accounts from postings
            for posting in entry.postings:
                result.accounts.add(posting.account)
        elif isinstance(entry, data.Balance):
            result.balance_count += 1
            result.accounts.add(entry.account)
        elif isinstance(entry, data.Price):
            result.price_count += 1

    result.directive_counts = dict(type_counts)
    return result


def parse_with_rust(file_path: Path, rledger_check: str, rledger_query: str) -> Optional[ParseResult]:
    """Parse a file with rustledger and extract structured data."""
    result = ParseResult()

    # Get error count from rledger-check --format json
    try:
        proc = subprocess.run(
            [rledger_check, "--format", "json", str(file_path)],
            capture_output=True,
            text=True,
            timeout=30
        )
        if proc.stdout.strip():
            data = json.loads(proc.stdout)
            result.error_count = data.get("error_count", 0)
            result.raw_errors = [d.get("message", "") for d in data.get("diagnostics", [])[:5]]
    except (subprocess.TimeoutExpired, json.JSONDecodeError, Exception) as e:
        result.raw_errors = [str(e)]
        return result

    # Get accounts via BQL
    try:
        proc = subprocess.run(
            [rledger_query, str(file_path), "SELECT DISTINCT account ORDER BY account"],
            capture_output=True,
            text=True,
            timeout=30
        )
        if proc.returncode == 0:
            # Parse the table output
            lines = proc.stdout.strip().split('\n')
            for line in lines[2:]:  # Skip header and separator
                if line.strip() and not line.startswith('-') and 'row(s)' not in line:
                    result.accounts.add(line.strip())
    except Exception as e:
        # BQL query failure is non-fatal; record error and continue with empty accounts set
        result.raw_errors.append(f"accounts query: {e}")

    # Get posting count via BQL (COUNT(*) counts postings)
    try:
        proc = subprocess.run(
            [rledger_query, str(file_path), "SELECT COUNT(*)"],
            capture_output=True,
            text=True,
            timeout=30
        )
        if proc.returncode == 0:
            lines = proc.stdout.strip().split('\n')
            for line in lines[2:]:  # Skip header and separator
                line = line.strip()
                if line and not line.startswith('-') and 'row(s)' not in line:
                    try:
                        result.posting_count = int(line)
                    except ValueError:
                        # Non-integer lines (headers/footers) are expected; ignore them
                        pass
                    break
    except Exception as e:
        # BQL query failure is non-fatal; record error and continue with posting_count=0
        result.raw_errors.append(f"posting count query: {e}")

    return result


def compare_results(file_path: str, python: Optional[ParseResult], rust: Optional[ParseResult]) -> ComparisonResult:
    """Compare Python and Rust parsing results."""
    result = ComparisonResult(file=file_path, python=python, rust=rust)

    if python is None or rust is None:
        return result

    # Compare accounts
    result.accounts_only_python = python.accounts - rust.accounts
    result.accounts_only_rust = rust.accounts - python.accounts
    result.accounts_match = (python.accounts == rust.accounts)

    # Compare posting counts (what BQL COUNT(*) returns)
    result.posting_count_diff = rust.posting_count - python.posting_count
    result.posting_count_match = (python.posting_count == rust.posting_count)

    # Compare error counts (both have errors or both don't)
    result.error_count_match = (
        (python.error_count > 0) == (rust.error_count > 0)
    )

    return result


def test_single_file(args) -> ComparisonResult:
    """Test a single file - designed to run in parallel."""
    file_path, rledger_check, rledger_query = args
    python_result = parse_with_python(file_path)
    rust_result = parse_with_rust(file_path, rledger_check, rledger_query)
    return compare_results(str(file_path), python_result, rust_result)


def run_comparison(directory: Path, rledger_check: str, rledger_query: str) -> list[ComparisonResult]:
    """Run comparison on all beancount files in directory (parallel)."""
    files = list(directory.rglob("*.beancount"))

    print(f"Comparing {len(files)} files with {MAX_WORKERS} parallel workers...")
    print()

    results = []
    completed = 0

    # Build args for parallel execution
    test_args = [(f, rledger_check, rledger_query) for f in files]

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = [executor.submit(test_single_file, args) for args in test_args]
        for future in as_completed(futures):
            try:
                result = future.result()
                results.append(result)
                completed += 1
                if completed % 20 == 0:
                    print(f"  Progress: {completed}/{len(files)}", end='\r')
            except Exception as e:
                print(f"Error: {e}")

    print(f"  Completed: {len(results)}/{len(files)}    ")
    print()
    return results


def print_summary(results: list[ComparisonResult]):
    """Print summary of comparison results."""
    total = len(results)
    accounts_match = sum(1 for r in results if r.accounts_match)
    posting_match = sum(1 for r in results if r.posting_count_match)
    error_match = sum(1 for r in results if r.error_count_match)
    full_match = sum(1 for r in results if r.full_match)

    print("=" * 60)
    print("AST/Directive Comparison Results")
    print("=" * 60)
    print()
    print(f"Files tested:           {total}")
    print()
    print("Match Rates:")
    print(f"  Accounts match:       {accounts_match}/{total} ({100*accounts_match//total}%)")
    print(f"  Posting count:        {posting_match}/{total} ({100*posting_match//total}%)")
    print(f"  Error presence:       {error_match}/{total} ({100*error_match//total}%)")
    print(f"  Full match:           {full_match}/{total} ({100*full_match//total}%)")
    print()

    # Show mismatches
    mismatches = [r for r in results if not r.full_match]
    if mismatches:
        print("=" * 60)
        print(f"Mismatches ({len(mismatches)} files)")
        print("=" * 60)

        # Group by type
        account_mismatches = [r for r in mismatches if not r.accounts_match]
        posting_mismatches = [r for r in mismatches if not r.posting_count_match]
        error_mismatches = [r for r in mismatches if not r.error_count_match]

        if account_mismatches:
            print()
            print(f"Account Mismatches ({len(account_mismatches)}):")
            for r in account_mismatches[:5]:
                print(f"  {Path(r.file).name}")
                if r.accounts_only_python:
                    print(f"    Python only: {', '.join(sorted(r.accounts_only_python)[:3])}")
                if r.accounts_only_rust:
                    print(f"    Rust only:   {', '.join(sorted(r.accounts_only_rust)[:3])}")
            if len(account_mismatches) > 5:
                print(f"  ... and {len(account_mismatches) - 5} more")

        if posting_mismatches:
            print()
            print(f"Posting Count Mismatches ({len(posting_mismatches)}):")
            for r in posting_mismatches[:5]:
                py_count = r.python.posting_count if r.python else "?"
                rs_count = r.rust.posting_count if r.rust else "?"
                diff = r.posting_count_diff
                print(f"  {Path(r.file).name}: Python={py_count}, Rust={rs_count} (diff={diff:+d})")
            if len(posting_mismatches) > 5:
                print(f"  ... and {len(posting_mismatches) - 5} more")

        if error_mismatches:
            print()
            print(f"Error Presence Mismatches ({len(error_mismatches)}):")
            for r in error_mismatches[:5]:
                py_err = r.python.error_count if r.python else "?"
                rs_err = r.rust.error_count if r.rust else "?"
                print(f"  {Path(r.file).name}: Python errors={py_err}, Rust errors={rs_err}")
            if len(error_mismatches) > 5:
                print(f"  ... and {len(error_mismatches) - 5} more")


def save_results(results: list[ComparisonResult], output_file: Path):
    """Save results to JSON file."""
    data = []
    for r in results:
        entry = {
            "file": r.file,
            "accounts_match": r.accounts_match,
            "posting_count_match": r.posting_count_match,
            "error_count_match": r.error_count_match,
            "full_match": r.full_match,
        }
        if r.python:
            entry["python"] = {
                "accounts": sorted(r.python.accounts),
                "posting_count": r.python.posting_count,
                "transaction_count": r.python.transaction_count,
                "error_count": r.python.error_count,
            }
        if r.rust:
            entry["rust"] = {
                "accounts": sorted(r.rust.accounts),
                "posting_count": r.rust.posting_count,
                "error_count": r.rust.error_count,
            }
        if r.accounts_only_python:
            entry["accounts_only_python"] = sorted(r.accounts_only_python)
        if r.accounts_only_rust:
            entry["accounts_only_rust"] = sorted(r.accounts_only_rust)
        if r.posting_count_diff != 0:
            entry["posting_count_diff"] = r.posting_count_diff
        data.append(entry)

    with open(output_file, 'w') as f:
        for entry in data:
            f.write(json.dumps(entry) + '\n')

    print(f"\nResults saved to: {output_file}")


def main():
    # Determine directory to test
    if len(sys.argv) > 1:
        test_dir = Path(sys.argv[1])
    else:
        # Default to curated files, then full suite
        test_dir = Path("tests/compat/files")
        if not test_dir.exists():
            test_dir = Path("tests/compat-full")

    if not test_dir.exists():
        print(f"Error: Directory not found: {test_dir}")
        sys.exit(1)

    # Find rustledger binaries
    rledger_check = "./target/release/rledger-check"
    rledger_query = "./target/release/rledger-query"

    if not Path(rledger_check).exists():
        print("Building rustledger...")
        subprocess.run(["cargo", "build", "--release", "-p", "rustledger"], check=True)

    print(f"Testing directory: {test_dir}")
    print()

    # Run comparison
    results = run_comparison(test_dir, rledger_check, rledger_query)

    # Print summary
    print_summary(results)

    # Save results
    output_dir = Path("tests/compat-results")
    output_dir.mkdir(exist_ok=True)

    from datetime import datetime
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_file = output_dir / f"ast_results_{timestamp}.jsonl"
    save_results(results, output_file)


if __name__ == "__main__":
    main()
