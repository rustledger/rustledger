#!/usr/bin/env python3
"""
TLA+ State Space Coverage Analysis Tool

Analyzes TLC output to determine which states and transitions are covered
by Rust tests, identifying potential gaps in test coverage.

Usage:
    python tla_coverage.py --tlc-output tlc.log --rust-traces traces/*.json --report coverage.html
"""

import json
import re
import sys
import argparse
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any
from collections import defaultdict


@dataclass
class TLAState:
    """Represents a TLA+ state."""
    state_num: int
    variables: dict[str, Any]
    fingerprint: str = ""

    def __post_init__(self):
        # Create a fingerprint for state comparison
        self.fingerprint = self._compute_fingerprint()

    def _compute_fingerprint(self) -> str:
        """Compute a hashable fingerprint of the state."""
        def normalize(v):
            if isinstance(v, dict):
                return tuple(sorted((k, normalize(vv)) for k, vv in v.items()))
            elif isinstance(v, (list, tuple)):
                return tuple(normalize(x) for x in v)
            elif isinstance(v, set):
                return frozenset(normalize(x) for x in v)
            return v
        return str(normalize(self.variables))


@dataclass
class TLATransition:
    """Represents a TLA+ state transition."""
    from_state: int
    to_state: int
    action: str

    @property
    def key(self) -> str:
        return f"{self.from_state}->{self.to_state}:{self.action}"


@dataclass
class CoverageReport:
    """Coverage analysis report."""
    spec_name: str
    total_states: int = 0
    covered_states: int = 0
    total_transitions: int = 0
    covered_transitions: int = 0
    uncovered_states: list = field(default_factory=list)
    uncovered_transitions: list = field(default_factory=list)
    state_coverage_by_var: dict = field(default_factory=dict)
    action_coverage: dict = field(default_factory=dict)

    @property
    def state_coverage_pct(self) -> float:
        return (self.covered_states / self.total_states * 100) if self.total_states else 0

    @property
    def transition_coverage_pct(self) -> float:
        return (self.covered_transitions / self.total_transitions * 100) if self.total_transitions else 0


def parse_tlc_states(tlc_output: str) -> tuple[list[TLAState], list[TLATransition]]:
    """Parse TLC output to extract states and transitions."""
    states = []
    transitions = []

    # Pattern for state output
    state_pattern = re.compile(r'^State (\d+):.*$', re.MULTILINE)
    var_pattern = re.compile(r'^/\\ (\w+) = (.+)$', re.MULTILINE)

    current_state_num = None
    current_vars = {}

    for line in tlc_output.split('\n'):
        state_match = state_pattern.match(line)
        if state_match:
            # Save previous state
            if current_state_num is not None:
                states.append(TLAState(current_state_num, current_vars))
            current_state_num = int(state_match.group(1))
            current_vars = {}

            # Extract action if present
            action_match = re.search(r'<(\w+)', line)
            if action_match and len(states) > 0:
                transitions.append(TLATransition(
                    from_state=len(states),
                    to_state=len(states) + 1,
                    action=action_match.group(1)
                ))
            continue

        var_match = var_pattern.match(line)
        if var_match and current_state_num is not None:
            var_name = var_match.group(1)
            var_value = var_match.group(2)
            current_vars[var_name] = var_value

    # Save last state
    if current_state_num is not None:
        states.append(TLAState(current_state_num, current_vars))

    return states, transitions


def parse_rust_traces(trace_files: list[Path]) -> set[str]:
    """Parse Rust test traces and extract covered state fingerprints."""
    covered_fingerprints = set()

    for trace_file in trace_files:
        try:
            with open(trace_file) as f:
                trace = json.load(f)

            for state in trace.get("states", []):
                # Create fingerprint from Rust trace state
                vars = state.get("variables", {})
                fp = str(sorted(vars.items()))
                covered_fingerprints.add(fp)

        except (json.JSONDecodeError, KeyError) as e:
            print(f"Warning: Could not parse {trace_file}: {e}", file=sys.stderr)

    return covered_fingerprints


def analyze_coverage(
    states: list[TLAState],
    transitions: list[TLATransition],
    covered_fingerprints: set[str],
    spec_name: str
) -> CoverageReport:
    """Analyze coverage of TLA+ states by Rust tests."""
    report = CoverageReport(spec_name=spec_name)
    report.total_states = len(states)
    report.total_transitions = len(transitions)

    # Analyze state coverage
    for state in states:
        if state.fingerprint in covered_fingerprints:
            report.covered_states += 1
        else:
            report.uncovered_states.append(state)

    # Analyze transition coverage
    transition_actions = defaultdict(int)
    covered_actions = defaultdict(int)

    for trans in transitions:
        transition_actions[trans.action] += 1
        # Check if both states are covered
        from_covered = any(s.state_num == trans.from_state and s.fingerprint in covered_fingerprints
                          for s in states)
        to_covered = any(s.state_num == trans.to_state and s.fingerprint in covered_fingerprints
                        for s in states)

        if from_covered and to_covered:
            report.covered_transitions += 1
            covered_actions[trans.action] += 1
        else:
            report.uncovered_transitions.append(trans)

    # Calculate per-action coverage
    for action, total in transition_actions.items():
        covered = covered_actions.get(action, 0)
        report.action_coverage[action] = {
            "total": total,
            "covered": covered,
            "percentage": (covered / total * 100) if total else 0
        }

    # Analyze per-variable coverage
    var_values = defaultdict(set)
    covered_var_values = defaultdict(set)

    for state in states:
        for var_name, var_value in state.variables.items():
            var_values[var_name].add(str(var_value))
            if state.fingerprint in covered_fingerprints:
                covered_var_values[var_name].add(str(var_value))

    for var_name, values in var_values.items():
        covered = covered_var_values.get(var_name, set())
        report.state_coverage_by_var[var_name] = {
            "total_values": len(values),
            "covered_values": len(covered),
            "percentage": (len(covered) / len(values) * 100) if values else 0,
            "uncovered": list(values - covered)[:5]  # First 5 uncovered values
        }

    return report


def generate_html_report(report: CoverageReport) -> str:
    """Generate an HTML coverage report."""
    html = f"""<!DOCTYPE html>
<html>
<head>
    <title>TLA+ Coverage Report: {report.spec_name}</title>
    <style>
        body {{ font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; margin: 40px; }}
        h1 {{ color: #333; }}
        .summary {{ background: #f5f5f5; padding: 20px; border-radius: 8px; margin: 20px 0; }}
        .metric {{ display: inline-block; margin-right: 40px; }}
        .metric-value {{ font-size: 2em; font-weight: bold; }}
        .metric-label {{ color: #666; }}
        .good {{ color: #28a745; }}
        .medium {{ color: #ffc107; }}
        .poor {{ color: #dc3545; }}
        table {{ border-collapse: collapse; width: 100%; margin: 20px 0; }}
        th, td {{ border: 1px solid #ddd; padding: 12px; text-align: left; }}
        th {{ background: #f8f9fa; }}
        .progress {{ background: #e9ecef; border-radius: 4px; overflow: hidden; }}
        .progress-bar {{ height: 20px; background: #28a745; }}
    </style>
</head>
<body>
    <h1>TLA+ Coverage Report: {report.spec_name}</h1>

    <div class="summary">
        <div class="metric">
            <div class="metric-value {_coverage_class(report.state_coverage_pct)}">{report.state_coverage_pct:.1f}%</div>
            <div class="metric-label">State Coverage ({report.covered_states}/{report.total_states})</div>
        </div>
        <div class="metric">
            <div class="metric-value {_coverage_class(report.transition_coverage_pct)}">{report.transition_coverage_pct:.1f}%</div>
            <div class="metric-label">Transition Coverage ({report.covered_transitions}/{report.total_transitions})</div>
        </div>
    </div>

    <h2>Action Coverage</h2>
    <table>
        <tr><th>Action</th><th>Coverage</th><th>Covered/Total</th></tr>
        {"".join(f'''
        <tr>
            <td>{action}</td>
            <td>
                <div class="progress">
                    <div class="progress-bar" style="width: {data['percentage']:.0f}%"></div>
                </div>
            </td>
            <td>{data['covered']}/{data['total']} ({data['percentage']:.1f}%)</td>
        </tr>''' for action, data in sorted(report.action_coverage.items()))}
    </table>

    <h2>Variable Coverage</h2>
    <table>
        <tr><th>Variable</th><th>Coverage</th><th>Uncovered Values</th></tr>
        {"".join(f'''
        <tr>
            <td>{var}</td>
            <td>{data['covered_values']}/{data['total_values']} ({data['percentage']:.1f}%)</td>
            <td>{', '.join(data['uncovered'][:3]) if data['uncovered'] else '✓ All covered'}</td>
        </tr>''' for var, data in sorted(report.state_coverage_by_var.items()))}
    </table>

    <h2>Uncovered States ({len(report.uncovered_states)})</h2>
    <table>
        <tr><th>State #</th><th>Variables (sample)</th></tr>
        {"".join(f'''
        <tr>
            <td>{state.state_num}</td>
            <td><code>{str(state.variables)[:200]}...</code></td>
        </tr>''' for state in report.uncovered_states[:10])}
    </table>
    {f'<p>... and {len(report.uncovered_states) - 10} more</p>' if len(report.uncovered_states) > 10 else ''}

</body>
</html>"""
    return html


def _coverage_class(pct: float) -> str:
    """Return CSS class based on coverage percentage."""
    if pct >= 80:
        return "good"
    elif pct >= 50:
        return "medium"
    return "poor"


def generate_json_report(report: CoverageReport) -> str:
    """Generate a JSON coverage report."""
    return json.dumps({
        "spec_name": report.spec_name,
        "state_coverage": {
            "total": report.total_states,
            "covered": report.covered_states,
            "percentage": report.state_coverage_pct
        },
        "transition_coverage": {
            "total": report.total_transitions,
            "covered": report.covered_transitions,
            "percentage": report.transition_coverage_pct
        },
        "action_coverage": report.action_coverage,
        "variable_coverage": report.state_coverage_by_var,
        "uncovered_state_count": len(report.uncovered_states),
        "uncovered_transition_count": len(report.uncovered_transitions)
    }, indent=2)


def main():
    parser = argparse.ArgumentParser(
        description="Analyze TLA+ state space coverage by Rust tests"
    )
    parser.add_argument(
        "--tlc-output", "-t",
        type=Path,
        required=True,
        help="TLC output file with state enumeration"
    )
    parser.add_argument(
        "--rust-traces", "-r",
        type=Path,
        nargs="*",
        default=[],
        help="Rust test trace JSON files"
    )
    parser.add_argument(
        "--spec-name", "-s",
        default="Unknown",
        help="Name of the TLA+ specification"
    )
    parser.add_argument(
        "--report", "-o",
        type=Path,
        help="Output report file (HTML or JSON based on extension)"
    )
    parser.add_argument(
        "--format", "-f",
        choices=["html", "json", "text"],
        default="text",
        help="Output format"
    )

    args = parser.parse_args()

    # Parse TLC output
    tlc_output = args.tlc_output.read_text()
    states, transitions = parse_tlc_states(tlc_output)

    # Parse Rust traces
    covered = parse_rust_traces(args.rust_traces) if args.rust_traces else set()

    # Analyze coverage
    report = analyze_coverage(states, transitions, covered, args.spec_name)

    # Generate output
    if args.format == "html" or (args.report and args.report.suffix == ".html"):
        output = generate_html_report(report)
    elif args.format == "json" or (args.report and args.report.suffix == ".json"):
        output = generate_json_report(report)
    else:
        output = f"""TLA+ Coverage Report: {report.spec_name}
{'=' * 50}

State Coverage:      {report.covered_states}/{report.total_states} ({report.state_coverage_pct:.1f}%)
Transition Coverage: {report.covered_transitions}/{report.total_transitions} ({report.transition_coverage_pct:.1f}%)

Action Coverage:
{chr(10).join(f"  {action}: {data['covered']}/{data['total']} ({data['percentage']:.1f}%)"
              for action, data in sorted(report.action_coverage.items()))}

Uncovered States: {len(report.uncovered_states)}
Uncovered Transitions: {len(report.uncovered_transitions)}
"""

    if args.report:
        args.report.write_text(output)
        print(f"Report written to {args.report}", file=sys.stderr)
    else:
        print(output)


if __name__ == "__main__":
    main()
