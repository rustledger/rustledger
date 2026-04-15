#!/usr/bin/env python3
"""
Generate Vega benchmark charts from history JSON files.

This script loads the Vega spec template from .github/badges/validation-spec.json
and populates it with benchmark data.

Usage:
    # Generate specs from history files
    ./scripts/generate-bench-charts.py

    # Generate with custom values (for testing)
    ./scripts/generate-bench-charts.py --rustledger 32 --ledger 65 --hledger 540 --beancount 880

    # Render to SVG (requires: npm install -g vega vega-cli)
    vg2svg .github/badges/validation-chart.vega.json validation-chart.svg
"""

import argparse
import json
import subprocess
import sys
from datetime import datetime
from pathlib import Path


def load_spec_template(template_path: Path) -> dict:
    """Load a Vega spec template from file."""
    if not template_path.exists():
        raise FileNotFoundError(f"Template not found: {template_path}")
    return json.loads(template_path.read_text())


def populate_spec(
    spec: dict,
    title: str,
    subtitle: str,
    rustledger_ms: float,
    ledger_ms: float,
    hledger_ms: float,
    beancount_ms: float,
    bench_date: str,
) -> dict:
    """Populate a Vega spec template with benchmark data."""
    max_ms = max(rustledger_ms, ledger_ms, hledger_ms, beancount_ms)

    # Update signals
    signal_updates = {
        "rustledger_ms": rustledger_ms,
        "max_ms": max_ms,
        "bench_date": bench_date,
    }
    for signal in spec.get("signals", []):
        if signal["name"] in signal_updates:
            signal["value"] = signal_updates[signal["name"]]

    # Update data values
    benchmark_values = [
        {"tool": "rustledger", "label": "rustledger", "time_ms": rustledger_ms, "baseline_ms": beancount_ms, "color": "#00d4aa"},
        {"tool": "ledger", "label": "ledger (C++)", "time_ms": ledger_ms, "baseline_ms": beancount_ms, "color": "#9b59b6"},
        {"tool": "hledger", "label": "hledger (Haskell)", "time_ms": hledger_ms, "baseline_ms": beancount_ms, "color": "#e74c3c"},
        {"tool": "beancount", "label": "beancount (Python)", "time_ms": beancount_ms, "baseline_ms": beancount_ms, "color": "#f4b942"},
    ]
    for data_item in spec.get("data", []):
        if data_item.get("name") == "benchmarks":
            data_item["values"] = benchmark_values

    # Update title
    if "title" in spec:
        spec["title"]["text"] = title
        spec["title"]["subtitle"] = subtitle

    return spec


def main():
    parser = argparse.ArgumentParser(description="Generate Vega benchmark charts")
    parser.add_argument("--rustledger", type=float, help="rustledger time in ms")
    parser.add_argument("--ledger", type=float, help="ledger time in ms")
    parser.add_argument("--hledger", type=float, help="hledger time in ms")
    parser.add_argument("--beancount", type=float, help="beancount time in ms")
    parser.add_argument("--output-dir", type=Path, default=Path(".github/badges"))
    parser.add_argument("--render", action="store_true", help="Render to SVG using vg2svg")

    args = parser.parse_args()

    # Determine script location to find templates
    script_dir = Path(__file__).parent
    repo_root = script_dir.parent
    template_dir = repo_root / ".github" / "badges"

    # Use provided values or load from history
    if all([args.rustledger, args.ledger, args.hledger, args.beancount]):
        val_data = {
            "rustledger_ms": args.rustledger,
            "ledger_ms": args.ledger,
            "hledger_ms": args.hledger,
            "beancount_ms": args.beancount,
        }
        bal_data = val_data.copy()
        bench_date = datetime.now().strftime("%Y-%m-%d")
    else:
        # Load from history files
        val_history_file = args.output_dir / "validation-history.json"
        bal_history_file = args.output_dir / "balance-history.json"

        if not val_history_file.exists():
            print(f"Error: {val_history_file} not found")
            print("Provide values with --rustledger, --ledger, --hledger, --beancount")
            sys.exit(1)

        val_history = json.loads(val_history_file.read_text())
        bal_history = json.loads(bal_history_file.read_text())

        if not val_history:
            print("Error: validation history is empty")
            sys.exit(1)

        val_data = val_history[-1]
        bal_data = bal_history[-1] if bal_history else val_data
        bench_date = val_data.get("date", datetime.now().strftime("%Y-%m-%d"))

    # Load spec template
    template_path = template_dir / "validation-spec.json"
    try:
        spec_template = load_spec_template(template_path)
    except FileNotFoundError as e:
        print(f"Error: {e}")
        sys.exit(1)

    # Generate validation chart
    import copy
    val_spec = populate_spec(
        copy.deepcopy(spec_template),
        title="Validation: Parse + Check (10K transactions)",
        subtitle="rustledger vs other plain-text accounting tools",
        rustledger_ms=val_data["rustledger_ms"],
        ledger_ms=val_data["ledger_ms"],
        hledger_ms=val_data["hledger_ms"],
        beancount_ms=val_data["beancount_ms"],
        bench_date=bench_date,
    )

    args.output_dir.mkdir(parents=True, exist_ok=True)
    val_spec_path = args.output_dir / "validation-chart.vega.json"
    val_spec_path.write_text(json.dumps(val_spec, indent=2))
    print(f"Generated: {val_spec_path}")

    # Generate balance chart
    bal_spec = populate_spec(
        copy.deepcopy(spec_template),
        title="Balance Report: Parse + Compute (10K transactions)",
        subtitle="rustledger vs other plain-text accounting tools",
        rustledger_ms=bal_data.get("rustledger_ms", val_data["rustledger_ms"]),
        ledger_ms=bal_data.get("ledger_ms", val_data["ledger_ms"]),
        hledger_ms=bal_data.get("hledger_ms", val_data["hledger_ms"]),
        beancount_ms=bal_data.get("beancount_ms", val_data["beancount_ms"]),
        bench_date=bench_date,
    )

    bal_spec_path = args.output_dir / "balance-chart.vega.json"
    bal_spec_path.write_text(json.dumps(bal_spec, indent=2))
    print(f"Generated: {bal_spec_path}")

    # Render to SVG if requested
    if args.render:
        try:
            for name in ["validation-chart", "balance-chart"]:
                spec_path = args.output_dir / f"{name}.vega.json"
                svg_path = args.output_dir / f"{name}.svg"
                subprocess.run(["vg2svg", str(spec_path), str(svg_path)], check=True)
                print(f"Rendered: {svg_path}")
        except FileNotFoundError:
            print("\nError: vg2svg not found. Install with: npm install -g vega vega-cli")
            sys.exit(1)
        except subprocess.CalledProcessError as e:
            print(f"\nError rendering: {e}")
            sys.exit(1)


if __name__ == "__main__":
    main()
