#!/usr/bin/env python3
"""
Error Message Quality Testing

Compares error messages between bean-check (Python) and rledger check (Rust)
to ensure Rust provides equally helpful diagnostics.

This script tests:
1. Error message presence for known-bad inputs
2. Error location accuracy (line/column)
3. Error type consistency
4. Helpfulness of error messages

Usage:
    python scripts/compat-error-quality.py [--verbose]
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Optional


@dataclass
class ErrorInfo:
    """Parsed error information from compiler output."""
    line: Optional[int]
    column: Optional[int]
    error_type: str
    message: str
    raw: str


@dataclass
class TestCase:
    """A test case with known-bad input."""
    name: str
    content: str
    expected_error_pattern: str
    description: str


# Known-bad inputs that should produce helpful errors
TEST_CASES = [
    TestCase(
        name="invalid_date",
        content='2024-13-01 open Assets:Bank\n',
        expected_error_pattern=r"(invalid|date|month)",
        description="Invalid month in date",
    ),
    TestCase(
        name="invalid_date_day",
        content='2024-02-30 open Assets:Bank\n',
        expected_error_pattern=r"(invalid|date|day)",
        description="Invalid day in date",
    ),
    TestCase(
        name="unclosed_string",
        content='2024-01-01 * "Unclosed string\n  Assets:Bank  100 USD\n',
        expected_error_pattern=r"(unterminated|unclosed|string|quote)",
        description="Unterminated string literal",
    ),
    TestCase(
        name="invalid_account_segment",
        content='2024-01-01 open Assets:123Invalid\n',
        expected_error_pattern=r"(invalid|account|segment|name)",
        description="Account segment starting with number",
    ),
    TestCase(
        name="missing_account_type",
        content='2024-01-01 open MyAccount:Bank\n',
        expected_error_pattern=r"(invalid|account|type|root)",
        description="Account without valid root type",
    ),
    TestCase(
        name="duplicate_open",
        content='2024-01-01 open Assets:Bank\n2024-01-02 open Assets:Bank\n',
        expected_error_pattern=r"(duplicate|already|open)",
        description="Opening an already open account",
    ),
    TestCase(
        name="unbalanced_transaction",
        content='2024-01-01 open Assets:Bank\n2024-01-01 open Expenses:Food\n2024-01-02 * "Test"\n  Assets:Bank  -100 USD\n  Expenses:Food  50 USD\n',
        expected_error_pattern=r"(balance|unbalanced|sum|residual)",
        description="Transaction that doesn't balance",
    ),
    TestCase(
        name="invalid_currency",
        content='2024-01-01 open Assets:Bank\n2024-01-02 * "Test"\n  Assets:Bank  100 123\n',
        expected_error_pattern=r"(invalid|currency|symbol)",
        description="Invalid currency symbol",
    ),
    TestCase(
        name="posting_without_account",
        content='2024-01-01 * "Test"\n  100 USD\n',
        expected_error_pattern=r"(account|expected|syntax|posting)",
        description="Posting without account name",
    ),
    TestCase(
        name="invalid_metadata_key",
        content='2024-01-01 open Assets:Bank\n  123key: "value"\n',
        expected_error_pattern=r"(metadata|key|invalid|syntax)",
        description="Metadata key starting with number",
    ),
    TestCase(
        name="balance_wrong_currency",
        content='2024-01-01 open Assets:Bank USD\n2024-01-02 balance Assets:Bank  100 EUR\n',
        expected_error_pattern=r"(currency|mismatch|constraint)",
        description="Balance assertion with wrong currency",
    ),
    TestCase(
        name="close_unopened",
        content='2024-01-01 close Assets:Bank\n',
        expected_error_pattern=r"(close|unopened|not open|never)",
        description="Closing an account that was never opened",
    ),
    TestCase(
        name="use_before_open",
        content='2024-01-01 * "Test"\n  Assets:Bank  100 USD\n  Expenses:Food  -100 USD\n2024-01-02 open Assets:Bank\n2024-01-02 open Expenses:Food\n',
        expected_error_pattern=r"(open|before|used|not open)",
        description="Using account before it's opened",
    ),
    TestCase(
        name="use_after_close",
        content='2024-01-01 open Assets:Bank\n2024-01-02 close Assets:Bank\n2024-01-03 * "Test"\n  Assets:Bank  100 USD\n  Equity:Opening  -100 USD\n2024-01-01 open Equity:Opening\n',
        expected_error_pattern=r"(close|after|closed)",
        description="Using account after it's closed",
    ),
    TestCase(
        name="invalid_flag",
        content='2024-01-01 X "Invalid flag"\n  Assets:Bank  100 USD\n',
        expected_error_pattern=r"(flag|invalid|syntax|expected)",
        description="Invalid transaction flag",
    ),
]


def parse_python_error(stderr: str) -> list[ErrorInfo]:
    """Parse error information from bean-check output."""
    errors = []
    # Python beancount format: "file:line: message" or "file:line:col: message"
    pattern = r'(?:.*?):(\d+)(?::(\d+))?:\s*(.+)'

    for line in stderr.split('\n'):
        line = line.strip()
        if not line:
            continue
        match = re.match(pattern, line)
        if match:
            line_no = int(match.group(1)) if match.group(1) else None
            col_no = int(match.group(2)) if match.group(2) else None
            message = match.group(3)

            # Try to extract error type
            error_type = "unknown"
            if "syntax" in message.lower():
                error_type = "syntax"
            elif "balance" in message.lower():
                error_type = "balance"
            elif "invalid" in message.lower():
                error_type = "invalid"
            elif "duplicate" in message.lower():
                error_type = "duplicate"

            errors.append(ErrorInfo(
                line=line_no,
                column=col_no,
                error_type=error_type,
                message=message,
                raw=line,
            ))
        elif line and not line.startswith(' '):
            # Capture lines that might be errors but don't match pattern
            errors.append(ErrorInfo(
                line=None,
                column=None,
                error_type="unknown",
                message=line,
                raw=line,
            ))

    return errors


def parse_rust_error(stderr: str) -> list[ErrorInfo]:
    """Parse error information from rledger check output."""
    errors = []
    # Rust format varies, try common patterns
    # Format 1: "error[E001]: message\n  --> file:line:col"
    # Format 2: "file:line:col: error: message"

    current_message = None
    current_line = None
    current_col = None

    for line in stderr.split('\n'):
        line_stripped = line.strip()
        if not line_stripped:
            continue

        # Check for error line
        if line_stripped.startswith('error'):
            if current_message:
                errors.append(ErrorInfo(
                    line=current_line,
                    column=current_col,
                    error_type="error",
                    message=current_message,
                    raw=current_message,
                ))
            current_message = line_stripped
            current_line = None
            current_col = None

        # Check for location line
        elif '-->' in line_stripped:
            match = re.search(r':(\d+):(\d+)', line_stripped)
            if match:
                current_line = int(match.group(1))
                current_col = int(match.group(2))

        # Alternative format: "file:line:col: error: message"
        elif ':' in line_stripped:
            match = re.match(r'.*?:(\d+):(\d+):\s*(?:error:\s*)?(.+)', line_stripped)
            if match:
                errors.append(ErrorInfo(
                    line=int(match.group(1)),
                    column=int(match.group(2)),
                    error_type="error",
                    message=match.group(3),
                    raw=line_stripped,
                ))

    # Don't forget the last error
    if current_message:
        errors.append(ErrorInfo(
            line=current_line,
            column=current_col,
            error_type="error",
            message=current_message,
            raw=current_message,
        ))

    return errors


def run_checker(cmd: list[str], input_file: str) -> tuple[int, str, str]:
    """Run a checker command and return exit code, stdout, stderr."""
    try:
        result = subprocess.run(
            cmd + [input_file],
            capture_output=True,
            text=True,
            timeout=30,
        )
        return result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        return -1, "", "timeout"
    except Exception as e:
        return -1, "", str(e)


def test_error_quality(test: TestCase, verbose: bool = False) -> dict:
    """Run a single error quality test."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.beancount', delete=False) as f:
        f.write(test.content)
        temp_file = f.name

    try:
        # Run Python bean-check
        py_exit, py_stdout, py_stderr = run_checker(['bean-check'], temp_file)
        py_errors = parse_python_error(py_stderr + py_stdout)

        # Run Rust rledger check
        rs_exit, rs_stdout, rs_stderr = run_checker(['./target/release/rledger', 'check'], temp_file)
        rs_errors = parse_rust_error(rs_stderr + rs_stdout)

        # Check if expected error pattern is found
        py_has_expected = any(
            re.search(test.expected_error_pattern, e.message, re.IGNORECASE)
            for e in py_errors
        )
        rs_has_expected = any(
            re.search(test.expected_error_pattern, e.message, re.IGNORECASE)
            for e in rs_errors
        )

        # Check location accuracy (if Python provides location, Rust should too)
        py_has_location = any(e.line is not None for e in py_errors)
        rs_has_location = any(e.line is not None for e in rs_errors)

        # Determine overall result
        if py_exit != 0 and rs_exit == 0:
            status = "rust_missed"
        elif py_exit == 0 and rs_exit != 0:
            status = "rust_extra"
        elif py_exit == 0:
            # Both pass (rs_exit == 0 implied by previous conditions)
            status = "both_pass"  # Unexpected - test case should fail
        elif not rs_has_expected and py_has_expected:
            status = "rust_unhelpful"
        elif py_has_location and not rs_has_location:
            status = "rust_no_location"
        else:
            status = "pass"

        result = {
            "name": test.name,
            "description": test.description,
            "status": status,
            "python": {
                "exit": py_exit,
                "error_count": len(py_errors),
                "has_expected_pattern": py_has_expected,
                "has_location": py_has_location,
                "errors": [e.raw for e in py_errors[:3]],
            },
            "rust": {
                "exit": rs_exit,
                "error_count": len(rs_errors),
                "has_expected_pattern": rs_has_expected,
                "has_location": rs_has_location,
                "errors": [e.raw for e in rs_errors[:3]],
            },
        }

        if verbose:
            print(f"\n{'='*60}")
            print(f"Test: {test.name}")
            print(f"Description: {test.description}")
            print(f"Status: {status}")
            print(f"\nPython errors ({len(py_errors)}):")
            for e in py_errors[:3]:
                print(f"  {e.raw}")
            print(f"\nRust errors ({len(rs_errors)}):")
            for e in rs_errors[:3]:
                print(f"  {e.raw}")

        return result

    finally:
        os.unlink(temp_file)


def main():
    parser = argparse.ArgumentParser(description="Error message quality testing")
    parser.add_argument('--verbose', '-v', action='store_true', help="Show detailed output")
    parser.add_argument('--json', action='store_true', help="Output JSON results")
    args = parser.parse_args()

    # Build rustledger first
    print("Building rustledger...")
    result = subprocess.run(
        ['cargo', 'build', '--release', '--quiet'],
        capture_output=True,
    )
    if result.returncode != 0:
        print("Failed to build rustledger")
        sys.exit(1)

    # Check bean-check is available
    try:
        subprocess.run(['bean-check', '--version'], capture_output=True, check=True)
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("bean-check not found. Run inside nix develop.")
        sys.exit(1)

    print(f"\nRunning {len(TEST_CASES)} error quality tests...\n")

    results = []
    for test in TEST_CASES:
        result = test_error_quality(test, verbose=args.verbose)
        results.append(result)

        if not args.verbose:
            status_icon = "✓" if result["status"] == "pass" else "✗"
            print(f"  {status_icon} {test.name}: {result['status']}")

    # Summary
    print(f"\n{'='*60}")
    print("SUMMARY")
    print('='*60)

    passed = sum(1 for r in results if r["status"] == "pass")
    rust_missed = sum(1 for r in results if r["status"] == "rust_missed")
    rust_unhelpful = sum(1 for r in results if r["status"] == "rust_unhelpful")
    rust_no_location = sum(1 for r in results if r["status"] == "rust_no_location")
    rust_extra = sum(1 for r in results if r["status"] == "rust_extra")
    both_pass = sum(1 for r in results if r["status"] == "both_pass")

    print(f"Total tests:        {len(results)}")
    print(f"Passed:             {passed}")
    print(f"Rust missed error:  {rust_missed}")
    print(f"Rust unhelpful:     {rust_unhelpful}")
    print(f"Rust no location:   {rust_no_location}")
    print(f"Rust extra error:   {rust_extra}")
    print(f"Both pass (bad):    {both_pass}")

    if args.json:
        print(f"\n{json.dumps(results, indent=2)}")

    # Save results
    results_dir = Path("tests/compatibility-results")
    results_dir.mkdir(parents=True, exist_ok=True)

    from datetime import datetime
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    results_file = results_dir / f"error_quality_{timestamp}.json"

    with open(results_file, 'w') as f:
        json.dump(results, f, indent=2)

    print(f"\nResults saved to: {results_file}")

    # Exit with error if any tests failed
    if passed < len(results):
        sys.exit(1)


if __name__ == "__main__":
    main()
