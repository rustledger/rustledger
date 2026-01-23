#!/usr/bin/env python3
"""
Example: Using rustledger-wasi from Python via subprocess.

This demonstrates the integration pattern. For production use, you can either:
1. Use wasmtime-py for direct WASM execution (faster, no subprocess overhead)
2. Use this subprocess approach (simpler, works anywhere wasmtime is installed)

Usage:
    # Using subprocess (this script)
    python python_integration.py

    # Or with wasmtime-py:
    pip install wasmtime
    # Then use the wasmtime API directly
"""

import json
import subprocess
from pathlib import Path
from typing import Any

# Path to the WASI module (adjust for your setup)
WASM_PATH = Path(__file__).parent.parent.parent.parent / "target/wasm32-wasip1/release/rustledger-wasi.wasm"


class RustledgerWasi:
    """Python wrapper for rustledger-wasi module."""

    def __init__(self, wasm_path: Path = WASM_PATH):
        self.wasm_path = wasm_path
        if not self.wasm_path.exists():
            raise FileNotFoundError(f"WASM module not found: {wasm_path}")

    def _run(self, command: str, source: str, *args: str) -> dict[str, Any]:
        """Run a rustledger-wasi command."""
        cmd = ["wasmtime", str(self.wasm_path), command, *args]
        result = subprocess.run(
            cmd,
            input=source,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            raise RuntimeError(f"wasmtime error: {result.stderr}")
        return json.loads(result.stdout)

    def parse(self, source: str) -> dict[str, Any]:
        """Parse beancount source."""
        return self._run("parse", source)

    def validate(self, source: str) -> dict[str, Any]:
        """Validate beancount source."""
        return self._run("validate", source)

    def query(self, source: str, bql: str) -> dict[str, Any]:
        """Run a BQL query."""
        return self._run("query", source, bql)

    def balances(self, source: str) -> dict[str, Any]:
        """Get account balances (shorthand for BALANCES query)."""
        return self._run("balances", source)

    def version(self) -> str:
        """Get version string."""
        result = self._run("version", "")
        return result["version"]


def main():
    """Demo the integration."""
    ledger = RustledgerWasi()

    print(f"rustledger-wasi version: {ledger.version()}")
    print()

    source = """
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD
2024-01-01 open Expenses:Coffee USD

2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Coffee  5.00 USD
  Assets:Bank     -5.00 USD

2024-01-20 * "Grocery Store" "Weekly groceries"
  Expenses:Food   50.00 USD
  Assets:Bank    -50.00 USD
"""

    # Parse
    print("=== Parse ===")
    result = ledger.parse(source)
    print(f"Directives: {result['directive_count']}")
    print(f"Errors: {len(result['errors'])}")
    print()

    # Validate
    print("=== Validate ===")
    result = ledger.validate(source)
    print(f"Valid: {result['valid']}")
    if result['errors']:
        for err in result['errors']:
            print(f"  Error: {err['message']}")
    print()

    # Query
    print("=== Query: Account Balances ===")
    result = ledger.query(source, "SELECT account, sum(position) WHERE account ~ 'Expenses' GROUP BY 1")
    print(f"Columns: {result['columns']}")
    for row in result['rows']:
        account = row[0]
        balance = row[1]
        if 'positions' in balance:
            for pos in balance['positions']:
                print(f"  {account}: {pos['units']['number']} {pos['units']['currency']}")
    print()

    # Balances shorthand
    print("=== Balances ===")
    result = ledger.balances(source)
    for row in result['rows']:
        account = row[0]
        balance = row[1]
        if 'positions' in balance:
            for pos in balance['positions']:
                amt = f"{pos['units']['number']} {pos['units']['currency']}"
                print(f"  {account}: {amt}")


if __name__ == "__main__":
    main()
