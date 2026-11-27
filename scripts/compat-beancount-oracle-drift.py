#!/usr/bin/env python3
"""Drift check: rledger's beancount reference oracle against beancount 3.2.3.

rledger reconciles its parse errors with a model of beancount's parser
(`crates/rustledger-parser/src/cst/oracle/beancount/`): a reference lexer
written from pta-standards' clean-room `LEXICAL.md`, and an LR driver
replaying the LALR tables of its clean-room `beancount.y`. This script feeds
both that model and beancount itself every input of the parse-error parity
harness (the stray-character matrix, the tracked ledgers and fuzz
regressions, the compat corpus, the pinned fuzz corpus; collected by
`scripts/compat-parse-error-parity.py`, not copied) and requires them to
agree, before any of rledger's deliberate differences is applied:

  * tokens: beancount's `lex_iter_string` against the model's lexer, per
    token, its name, its line and its text;
  * errors: beancount's `parse_string` syntax errors (line and exact
    message) and lexer errors (line), against the model's;
  * the gate: rledger skips the oracle on an input its own parse reports no
    error on, so the oracle (with rledger's deliberate differences applied)
    must find no syntax error on any such input. A lexer error it finds
    there is a known gap, counted: rledger reads a few lone capitals
    beancount's lexer rejects (`2229-4/3G`), and lexing every clean file to
    catch them would cost every parse far more than they are worth.

beancount is called as a black box, in ptadiff's forked workers (its C
parser can crash); ptadiff is loaded as the parity harness loads it (the
installed package, or `--ptadiff DIR`). An input it crashes or raises on has no verdict and is counted
apart, as is one where a division by zero makes it replace a token with a
lexer error of its own (`SystemError`), which its token stream does not show.

Usage (build the model's side first with `cargo build --release -p
rustledger-loader --no-default-features --example beancount_reference`):

    python3 -I scripts/compat-beancount-oracle-drift.py \\
        --reference target/release/examples/beancount_reference \\
        --fuzz-dir DIR --compat-dir tests/compatibility/files

Exits non-zero on any disagreement, and prints the first few.
"""

import argparse
import collections
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
PARITY_SCRIPT = REPO / "scripts/compat-parse-error-parity.py"


def load_parity():
    spec = importlib.util.spec_from_file_location("parity", PARITY_SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _as_bytes(text):
    if isinstance(text, bytes):
        return text
    return str(text).encode("utf-8", "surrogateescape")


def beancount_side(text):
    """beancount's tokens `[name, line, text-hex]` and errors `[line, message]`."""
    from beancount.parser import lexer, parser

    tokens = [[t[0], t[1], _as_bytes(t[2]).hex()] for t in lexer.lex_iter_string(text)]
    _, errors, _ = parser.parse_string(text)
    out = []
    for e in errors:
        line = int((e.source or {}).get("lineno") or 0)
        message = str(e.message)
        if type(e).__name__ == "LexerError":
            if "SystemError" in message:
                return {"crash": "division by zero (beancount garbles its token stream)"}
            out.append([line, "LexerError"])
        elif message.startswith("syntax error"):
            out.append([line, message])
    return {"tokens": tokens, "errors": sorted(out)}


def run_reference(binary, items):
    with tempfile.TemporaryDirectory() as td:
        frames = Path(td) / "frames"
        with open(frames, "wb") as f:
            for cid, text in items:
                data = text.encode("utf-8")
                f.write(f"{cid}\n{len(data)}\n".encode())
                f.write(data)
        with open(frames, "rb") as f:
            out = subprocess.run([binary], stdin=f, capture_output=True, check=True).stdout
    results = {}
    for line in out.decode("utf-8").splitlines():
        r = json.loads(line)
        results[r["id"]] = r
    return results


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--reference", required=True, help="the beancount_reference example binary")
    ap.add_argument("--fuzz-dir", help="extracted fuzz-corpus commit")
    ap.add_argument("--compat-dir", help="downloaded compat corpus")
    ap.add_argument("--min-compat", type=int, default=100)
    ap.add_argument("--ptadiff", help="a pta-standards tooling/differential checkout")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--show", type=int, default=5, help="disagreements to print")
    args = ap.parse_args()

    parity = load_parity()
    ptadiff = parity.load_ptadiff(args.ptadiff)
    inputs = parity.collect(args)
    items = [(cid, text) for cid, (_, _, text) in sorted(inputs.items.items())]
    parity.log(f"{len(items)} inputs; running beancount and the reference model")
    # Imported before the workers fork, so each one inherits it.
    from beancount.parser import lexer, parser  # noqa: F401

    raw = ptadiff.run_forked(items, beancount_side, jobs=args.jobs, timeout=20)
    bc = {
        cid: {"crash": r.why} if isinstance(r, ptadiff.Crash) else r
        for cid, r in raw.items()
    }
    rl = run_reference(args.reference, items)

    stats = collections.Counter()
    shown = 0
    for cid, text in items:
        b = bc[cid]
        if "crash" in b:
            stats["no verdict (beancount crashed or raised)"] += 1
            continue
        r = rl[cid]
        data = text.encode("utf-8")
        tokens = [[n, line, data[s:e].hex()] for n, line, s, e in r["tokens"]]
        errors = sorted([line, m] for line, m in r["errors"])
        ok_tokens = tokens == b["tokens"]
        ok_errors = errors == b["errors"]
        gated = r["gated_slots"]
        ok_gate = not any(kind != "lexical" for _, kind in gated)
        stats["compared"] += 1
        stats["tokens agree"] += ok_tokens
        stats["errors agree"] += ok_errors
        stats["gated off (rledger reports no error)"] += r["gate_skips_grammar"]
        if not ok_gate:
            stats["GATE MISSES A BEANCOUNT SYNTAX ERROR"] += 1
        elif gated:
            stats["gated off, beancount's lexer rejects a token (known gap)"] += 1
        if not (ok_tokens and ok_errors and ok_gate):
            stats["DISAGREE"] += 1
            if shown < args.show:
                shown += 1
                label = inputs.items[cid][1]
                print(f"--- {label}: {text[:200]!r}")
                if not ok_tokens:
                    at = next(
                        (i for i, (x, y) in enumerate(zip(tokens, b["tokens"])) if x != y),
                        min(len(tokens), len(b["tokens"])),
                    )
                    print(f"    token {at}: model {tokens[at:at + 2]} beancount {b['tokens'][at:at + 2]}")
                if not ok_errors:
                    print(f"    errors: model {errors[:6]} beancount {b['errors'][:6]}")
                if not ok_gate:
                    print(f"    the gate skips the oracle, which holds {gated[:6]}")
    for k, v in sorted(stats.items()):
        print(f"{k}: {v}")
    if stats["DISAGREE"] or not stats["compared"]:
        sys.exit(1)


if __name__ == "__main__":
    main()
