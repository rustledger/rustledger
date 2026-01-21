#!/usr/bin/env python3
"""
Generate Vega benchmark charts from history JSON files.

This script reads benchmark history and generates Vega specs that can be
rendered to SVG using the vega-cli tools.

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


def generate_vega_bar_spec(
    title: str,
    subtitle: str,
    rustledger_ms: float,
    ledger_ms: float,
    hledger_ms: float,
    beancount_ms: float,
    bench_date: str,
) -> dict:
    """Generate a Vega bar chart spec for benchmark comparison."""
    max_ms = max(rustledger_ms, ledger_ms, hledger_ms, beancount_ms)

    return {
        "$schema": "https://vega.github.io/schema/vega/v5.json",
        "width": 550,
        "height": 150,
        "padding": {"left": 10, "right": 10, "top": 10, "bottom": 10},
        "background": "#0d1117",
        "config": {"text": {"font": "JetBrains Mono, Fira Code, SF Mono, Menlo, monospace"}},
        "signals": [
            {"name": "rustledger_ms", "value": rustledger_ms},
            {"name": "max_ms", "value": max_ms},
            {"name": "bench_date", "value": bench_date},
            {"name": "smallBarThreshold", "value": 200},
        ],
        "data": [
            {
                "name": "benchmarks",
                "values": [
                    {"tool": tool, "label": label, "time_ms": time_ms, "baseline_ms": beancount_ms, "color": color}
                    for tool, label, time_ms, color in [
                        ("rustledger", "rustledger", rustledger_ms, "#00d4aa"),
                        ("ledger", "ledger (C++)", ledger_ms, "#9b59b6"),
                        ("hledger", "hledger (Haskell)", hledger_ms, "#e74c3c"),
                        ("beancount", "beancount (Python)", beancount_ms, "#f4b942"),
                    ]
                ],
                "transform": [
                    {"type": "formula", "as": "slower_factor", "expr": "datum.time_ms / rustledger_ms"},
                    {"type": "formula", "as": "faster_factor", "expr": "datum.baseline_ms / datum.time_ms"},
                    {"type": "formula", "as": "bar_px", "expr": "datum.time_ms / max_ms * width"},
                    {"type": "formula", "as": "is_small", "expr": "datum.bar_px < smallBarThreshold"},
                ],
            }
        ],
        "scales": [
            {
                "name": "y",
                "type": "band",
                "domain": {"data": "benchmarks", "field": "label"},
                "range": "height",
                "padding": 0.3,
            },
            {
                "name": "x",
                "type": "linear",
                "domain": [0, {"signal": "max_ms"}],
                "range": [0, {"signal": "width"}],
            },
        ],
        "marks": [
            # Main bars
            {
                "type": "rect",
                "from": {"data": "benchmarks"},
                "encode": {
                    "enter": {
                        "y": {"scale": "y", "field": "label"},
                        "height": {"scale": "y", "band": 1},
                        "x": {"value": 0},
                        "x2": {"scale": "x", "field": "time_ms"},
                        "cornerRadiusTopRight": {"value": 5},
                        "cornerRadiusBottomRight": {"value": 5},
                        "fill": {"field": "color"},
                        "fillOpacity": {"signal": "datum.tool == 'rustledger' ? 1 : 0.85"},
                    }
                },
            },
            # Highlight glow for rustledger
            {
                "type": "rect",
                "from": {"data": "benchmarks"},
                "encode": {
                    "enter": {
                        "y": {"scale": "y", "field": "label", "offset": -2},
                        "height": {"scale": "y", "band": 1, "offset": 4},
                        "x": {"value": -2},
                        "x2": {"scale": "x", "field": "time_ms", "offset": 2},
                        "cornerRadius": {"value": 6},
                        "fill": {"signal": "datum.tool == 'rustledger' ? datum.color : 'transparent'"},
                        "fillOpacity": {"value": 0.12},
                    }
                },
            },
            # Labels for non-rustledger tools
            {
                "type": "text",
                "from": {"data": "benchmarks"},
                "encode": {
                    "enter": {
                        "y": {"scale": "y", "field": "label", "band": 0.5},
                        "x": {"value": -14},
                        "text": {"signal": "datum.tool == 'rustledger' ? '' : datum.label"},
                        "fill": {"value": "#e6edf3"},
                        "fontSize": {"value": 14},
                        "fontWeight": {"value": 600},
                        "baseline": {"value": "middle"},
                        "align": {"value": "right"},
                    }
                },
            },
            # "ledger" part of rustledger label
            {
                "type": "text",
                "from": {"data": "benchmarks"},
                "encode": {
                    "enter": {
                        "y": {"scale": "y", "field": "label", "band": 0.5},
                        "x": {"value": -18},
                        "text": {"signal": "datum.tool == 'rustledger' ? 'ledger' : ''"},
                        "fill": {"value": "#e6edf3"},
                        "fontSize": {"value": 14},
                        "fontWeight": {"value": 600},
                        "baseline": {"value": "middle"},
                        "align": {"value": "right"},
                    }
                },
            },
            # "rust" part of rustledger label (orange)
            {
                "type": "text",
                "from": {"data": "benchmarks"},
                "encode": {
                    "enter": {
                        "y": {"scale": "y", "field": "label", "band": 0.5},
                        "x": {"value": -72},
                        "text": {"signal": "datum.tool == 'rustledger' ? 'rust' : ''"},
                        "fill": {"value": "#f74c00"},
                        "fontSize": {"value": 14},
                        "fontWeight": {"value": 600},
                        "baseline": {"value": "middle"},
                        "align": {"value": "right"},
                    }
                },
            },
            # Comparison text (inside or outside bar depending on size)
            {
                "type": "text",
                "from": {"data": "benchmarks"},
                "encode": {
                    "enter": {
                        "y": {"scale": "y", "field": "label", "band": 0.5},
                        "x": {"signal": "datum.is_small ? scale('x', datum.time_ms) + 10 : 8"},
                        "text": {
                            "signal": "datum.is_small ? (datum.tool == 'rustledger' ? format(datum.faster_factor, '.0f') + 'x vs beancount · ' + format(datum.time_ms, '.0f') + ' ms' : format(datum.slower_factor, '.1f') + 'x slower · ' + format(datum.time_ms, '.0f') + ' ms') : (datum.tool == 'rustledger' ? format(datum.faster_factor, '.0f') + 'x vs beancount' : format(datum.slower_factor, '.1f') + 'x slower')"
                        },
                        "fill": {
                            "signal": "datum.is_small ? (datum.tool == 'rustledger' ? '#f74c00' : '#e6edf3') : '#000000'"
                        },
                        "fontSize": {"value": 18},
                        "fontWeight": {"value": 700},
                        "baseline": {"value": "middle"},
                        "align": {"value": "left"},
                    }
                },
            },
            # Time label inside large bars
            {
                "type": "text",
                "from": {"data": "benchmarks"},
                "encode": {
                    "enter": {
                        "y": {"scale": "y", "field": "label", "band": 0.5},
                        "x": {"signal": "scale('x', datum.time_ms) - 8"},
                        "text": {"signal": "datum.is_small ? '' : format(datum.time_ms, '.0f') + ' ms'"},
                        "fill": {"value": "#000000"},
                        "fontSize": {"value": 18},
                        "fontWeight": {"value": 700},
                        "baseline": {"value": "middle"},
                        "align": {"value": "right"},
                    }
                },
            },
            # Footer with date
            {
                "type": "text",
                "encode": {
                    "enter": {
                        "x": {"signal": "width"},
                        "y": {"signal": "height + 2"},
                        "text": {"signal": "'measured ' + bench_date + ' · hyperfine'"},
                        "fill": {"value": "#6e7681"},
                        "fontSize": {"value": 12},
                        "baseline": {"value": "top"},
                        "align": {"value": "right"},
                    }
                },
            },
        ],
        "title": {
            "text": title,
            "subtitle": subtitle,
            "font": "JetBrains Mono, Fira Code, SF Mono, Menlo, monospace",
            "color": "#e6edf3",
            "subtitleColor": "#6e7681",
            "fontSize": 16,
            "subtitleFontSize": 16,
            "fontWeight": 600,
            "subtitleFontWeight": "normal",
            "subtitlePadding": 4,
        },
    }


def main():
    parser = argparse.ArgumentParser(description="Generate Vega benchmark charts")
    parser.add_argument("--rustledger", type=float, help="rustledger time in ms")
    parser.add_argument("--ledger", type=float, help="ledger time in ms")
    parser.add_argument("--hledger", type=float, help="hledger time in ms")
    parser.add_argument("--beancount", type=float, help="beancount time in ms")
    parser.add_argument("--output-dir", type=Path, default=Path(".github/badges"))
    parser.add_argument("--render", action="store_true", help="Render to SVG using vg2svg")

    args = parser.parse_args()

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

    # Generate validation chart
    val_spec = generate_vega_bar_spec(
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
    bal_spec = generate_vega_bar_spec(
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
