#!/usr/bin/env python3
"""Compare BOOKED VALUES against Python beancount, not just shapes.

The existing comprehensive compat test compares `check_match`,
`accounts_match`, `posting_count_match` and `error_presence_match` — whether
the two tools agree on how MANY postings there are and WHETHER there was an
error. It never compares an amount. A booking or interpolation bug that
produces the right number of postings with the wrong numbers in them passes
silently, which for an accounting tool is the failure that matters most.

This compares the sum of booked units per (account, currency) over a whole
file. That is sensitive to interpolation (an elided amount filled wrongly),
booking (a reduction matched against the wrong lot), and sign handling, while
being insensitive to directive ORDER and to display scale — which is a known,
documented divergence and not what this is hunting.
"""
from __future__ import annotations

import argparse, csv, io, subprocess, sys
from collections import defaultdict
from decimal import Decimal
from pathlib import Path

QUERY = ("SELECT account, currency, sum(number) AS n "
         "GROUP BY account, currency ORDER BY account, currency")


# Error classes that do NOT stop beancount booking the transactions it parsed.
# A file missing an `open` directive still books its postings correctly, and its
# amounts are just as comparable as a clean file's. Anything lexer/parser/load
# shaped is different: the entry stream is then incomplete, and comparing it
# would be comparing two different ledgers rather than two readings of one.
#
# This distinction is what the comparison lives or dies by. Skipping every file
# with any error at all left 499 of 758 unexamined, and 302 of those are fully
# booked — more files than were being compared.
NON_FATAL_ERRORS = {"ValidationError", "BalanceError", "DocumentError", "PadError"}


def beancount_totals(path: Path):
    """(account, currency) -> summed units, per Python beancount."""
    from beancount import loader
    entries, errors, _ = loader.load_file(str(path))
    if errors and not {type(e).__name__ for e in errors} <= NON_FATAL_ERRORS:
        return None
    from beancount.core import data
    totals = defaultdict(Decimal)
    for e in entries:
        if not isinstance(e, data.Transaction):
            continue
        for p in e.postings:
            if p.units is None or p.units.number is None:
                return None          # unbooked; nothing meaningful to compare
            totals[(p.account, p.units.currency)] += p.units.number
    return dict(totals)


def rledger_totals(binary: str, path: Path):
    try:
        proc = subprocess.run(
            [binary, "query", "--format", "csv", str(path), QUERY],
            capture_output=True, text=True, timeout=120,
        )
    except subprocess.TimeoutExpired:
        # One pathological file must not abort the sweep. Counting it as
        # not-comparable keeps the other 700-odd results, which is the whole
        # value of a corpus run.
        return None
    if proc.returncode != 0:
        return None
    # `query` exits 0 even when the file failed to PARSE, emitting data from
    # the partial parse (#1908). Until that is fixed, treat a parse complaint
    # on stderr as "not comparable" — otherwise this compares beancount's
    # ledger against a truncated one and reports the difference as a value bug.
    if "parse errors" in proc.stderr:
        return None
    totals = {}
    for row in csv.DictReader(io.StringIO(proc.stdout)):
        acct, cur, n = row.get("account"), row.get("currency"), row.get("n")
        if not acct or not cur or n in (None, ""):
            continue
        try:
            totals[(acct, cur)] = Decimal(n)
        except Exception:
            return None
    return totals


def compare(a: dict, b: dict):
    """Numeric comparison. Display SCALE differences are a documented, separate
    divergence (#1112), so `-1966.700` and `-1966.70` must not be reported."""
    diffs = []
    for key in sorted(set(a) | set(b), key=lambda k: (k[0], k[1])):
        x, y = a.get(key), b.get(key)
        if x is None or y is None:
            # A zero-sum bucket may legitimately be absent on one side.
            other = y if x is None else x
            if other != 0:
                diffs.append((key, x, y))
        elif x != y:
            diffs.append((key, x, y))
    return diffs


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rledger", default="./target/release/rledger")
    ap.add_argument("--corpus", nargs="+", required=True)
    ap.add_argument("--limit", type=int, default=0)
    args = ap.parse_args()

    files = sorted(p for d in args.corpus for p in Path(d).rglob("*.beancount"))
    if args.limit:
        files = files[: args.limit]

    compared = skipped = 0
    divergent = []
    for path in files:
        try:
            bc = beancount_totals(path)
        except Exception:
            bc = None
        if bc is None:
            skipped += 1
            continue
        rl = rledger_totals(args.rledger, path)
        if rl is None:
            skipped += 1
            continue
        compared += 1
        diffs = compare(bc, rl)
        if diffs:
            divergent.append((path, diffs))

    print(f"compared {compared} files, skipped {skipped} "
          f"(errors in either tool, or unbooked postings)")
    print(f"files with a VALUE divergence: {len(divergent)}\n")
    for path, diffs in divergent[:25]:
        print(f"  {path}")
        for (acct, cur), x, y in diffs[:6]:
            print(f"      {acct} {cur}:  beancount={x}  rledger={y}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
