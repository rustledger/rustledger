#!/usr/bin/env python3
"""
TLA+ Trace to JSON Converter

Parses TLC model checker output and extracts counterexample traces as JSON.
These can then be converted to Rust test cases.

Usage:
    python tla_trace_to_json.py < tlc_output.txt > trace.json
    python tla_trace_to_json.py --spec BookingMethods < tlc_output.txt > trace.json
"""

import json
import re
import sys
import argparse
from dataclasses import dataclass, asdict
from typing import Any


@dataclass
class TLAValue:
    """Represents a TLA+ value that can be converted to Rust."""
    tla_type: str
    value: Any

    def to_dict(self) -> dict:
        return {"type": self.tla_type, "value": self.value}


@dataclass
class TraceState:
    """A single state in a TLA+ counterexample trace."""
    state_num: int
    action: str | None
    variables: dict[str, Any]


@dataclass
class Trace:
    """A complete TLA+ counterexample trace."""
    spec_name: str
    invariant_violated: str | None
    property_violated: str | None
    states: list[TraceState]

    def to_dict(self) -> dict:
        return {
            "spec_name": self.spec_name,
            "invariant_violated": self.invariant_violated,
            "property_violated": self.property_violated,
            "states": [
                {
                    "state_num": s.state_num,
                    "action": s.action,
                    "variables": s.variables
                }
                for s in self.states
            ]
        }


def parse_tla_value(value_str: str) -> Any:
    """Parse a TLA+ value string into a Python value."""
    value_str = value_str.strip()

    # Boolean
    if value_str == "TRUE":
        return True
    if value_str == "FALSE":
        return False

    # Number (integer)
    if re.match(r'^-?\d+$', value_str):
        return int(value_str)

    # String
    if value_str.startswith('"') and value_str.endswith('"'):
        return value_str[1:-1]

    # Set: {a, b, c}
    if value_str.startswith('{') and value_str.endswith('}'):
        inner = value_str[1:-1].strip()
        if not inner:
            return {"type": "set", "elements": []}
        # Handle nested structures by tracking depth
        elements = split_tla_list(inner)
        return {"type": "set", "elements": [parse_tla_value(e) for e in elements]}

    # Sequence: <<a, b, c>>
    if value_str.startswith('<<') and value_str.endswith('>>'):
        inner = value_str[2:-2].strip()
        if not inner:
            return {"type": "sequence", "elements": []}
        elements = split_tla_list(inner)
        return {"type": "sequence", "elements": [parse_tla_value(e) for e in elements]}

    # Record: [field1 |-> val1, field2 |-> val2]
    if value_str.startswith('[') and value_str.endswith(']'):
        inner = value_str[1:-1].strip()
        if not inner:
            return {"type": "record", "fields": {}}

        fields = {}
        # Parse field |-> value pairs
        parts = split_tla_list(inner)
        for part in parts:
            if ' |-> ' in part:
                field, val = part.split(' |-> ', 1)
                fields[field.strip()] = parse_tla_value(val.strip())

        return {"type": "record", "fields": fields}

    # Function: (arg1 :> val1 @@ arg2 :> val2)
    if value_str.startswith('(') and value_str.endswith(')') and ':>' in value_str:
        inner = value_str[1:-1].strip()
        mapping = {}
        parts = inner.split('@@')
        for part in parts:
            part = part.strip()
            if ':>' in part:
                key, val = part.split(':>', 1)
                mapping[parse_tla_value(key.strip())] = parse_tla_value(val.strip())
        return {"type": "function", "mapping": mapping}

    # Null/None
    if value_str == "NULL" or value_str == "null":
        return None

    # Default: return as string
    return value_str


def split_tla_list(s: str) -> list[str]:
    """Split a TLA+ comma-separated list, respecting nested structures."""
    elements = []
    current = []
    depth = 0
    in_string = False

    i = 0
    while i < len(s):
        c = s[i]

        if c == '"' and (i == 0 or s[i-1] != '\\'):
            in_string = not in_string
            current.append(c)
        elif in_string:
            current.append(c)
        elif c in '{[(<':
            depth += 1
            current.append(c)
        elif c in '}])>':
            depth -= 1
            current.append(c)
        elif c == ',' and depth == 0:
            elements.append(''.join(current).strip())
            current = []
        else:
            current.append(c)
        i += 1

    if current:
        elements.append(''.join(current).strip())

    return [e for e in elements if e]


def parse_tlc_output(lines: list[str], spec_name: str = "Unknown") -> Trace | None:
    """Parse TLC model checker output and extract counterexample trace."""
    states = []
    invariant_violated = None
    property_violated = None
    current_state_num = None
    current_action = None
    current_vars = {}
    in_trace = False

    for line in lines:
        line = line.rstrip()

        # Check for invariant violation
        if "Invariant" in line and "is violated" in line:
            match = re.search(r'Invariant (\w+) is violated', line)
            if match:
                invariant_violated = match.group(1)

        # Check for property violation
        if "Property" in line and "is violated" in line:
            match = re.search(r'Property (\w+) is violated', line)
            if match:
                property_violated = match.group(1)

        # Start of trace
        if "Error: The behavior up to this point is:" in line:
            in_trace = True
            continue

        # State line: "State 1: <Init line 50, col 1 to line 55, col 20 of module Foo>"
        state_match = re.match(r'^State (\d+):', line)
        if state_match:
            # Save previous state if exists
            if current_state_num is not None:
                states.append(TraceState(
                    state_num=current_state_num,
                    action=current_action,
                    variables=current_vars
                ))

            current_state_num = int(state_match.group(1))
            # Try to extract action name
            action_match = re.search(r'<(\w+)', line)
            current_action = action_match.group(1) if action_match else None
            current_vars = {}
            in_trace = True
            continue

        # Variable assignment: "/\ varname = value"
        if in_trace and line.startswith('/\\'):
            var_match = re.match(r'^/\\ (\w+) = (.+)$', line)
            if var_match:
                var_name = var_match.group(1)
                var_value = var_match.group(2)
                current_vars[var_name] = parse_tla_value(var_value)

        # Continuation of multi-line value
        elif in_trace and current_vars and not line.startswith('State'):
            # Could be continuation - skip for now (complex multi-line parsing)
            pass

    # Save last state
    if current_state_num is not None:
        states.append(TraceState(
            state_num=current_state_num,
            action=current_action,
            variables=current_vars
        ))

    if not states:
        return None

    return Trace(
        spec_name=spec_name,
        invariant_violated=invariant_violated,
        property_violated=property_violated,
        states=states
    )


def main():
    parser = argparse.ArgumentParser(
        description="Convert TLC counterexample traces to JSON"
    )
    parser.add_argument(
        "--spec", "-s",
        default="Unknown",
        help="Name of the TLA+ specification"
    )
    parser.add_argument(
        "input",
        nargs="?",
        type=argparse.FileType('r'),
        default=sys.stdin,
        help="TLC output file (default: stdin)"
    )
    parser.add_argument(
        "--output", "-o",
        type=argparse.FileType('w'),
        default=sys.stdout,
        help="Output JSON file (default: stdout)"
    )

    args = parser.parse_args()

    lines = args.input.readlines()
    trace = parse_tlc_output(lines, args.spec)

    if trace:
        json.dump(trace.to_dict(), args.output, indent=2)
        args.output.write('\n')
    else:
        print("No counterexample trace found in input", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
