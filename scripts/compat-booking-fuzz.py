#!/usr/bin/env python3
"""Booking fuzzer — differential checks on generated ledgers against beancount.

Booking decides WHICH lot a reduction consumes. Get it wrong and the postings
still balance, the count is still right, and the error list is still empty —
the ledger is simply wrong about what you own and what you gained. That is the
failure mode example-based tests are worst at catching, and the recent fix log
shows why it matters: five booking fixes in twenty commits (#2058, #2069,
#2081, #2093, #2099), each an ordering or lot-selection case nobody had
written a test for.

So this generates ledgers instead and compares the BOOKED LOTS against Python
beancount, which is an independent implementation rather than a restatement of
our own logic. For every account it compares the full lot identity —
(currency, per-unit cost, cost currency, lot date) -> units — so consuming the
wrong lot at the same total value is still a failure.

It also compares ACCEPTANCE. A ledger one engine books and the other rejects
is a divergence even when no numbers differ, and #2099 (report an ambiguous
STRICT match instead of guessing FIFO) is exactly that shape: the bug was
answering at all.

Deliberately NOT generated:

  - AVERAGE and NONE booking. beancount rejects both ("AVERAGE method is not
    supported", "Too many missing numbers"), so every run would be a
    known-unsupported skip rather than a test.
  - Prices on reductions, which interact with cost inference in ways that are
    a separate surface from lot selection.

Usage:
    scripts/compat-booking-fuzz.py --runs 200
    scripts/compat-booking-fuzz.py --seed 12345        # reproduce one case
    scripts/compat-booking-fuzz.py --self-test         # prove it detects a bug
"""

from __future__ import annotations

import argparse
import json
import random
import subprocess
import sys
import tempfile
from decimal import Decimal
from pathlib import Path

# beancount supports these; AVERAGE/NONE are excluded (see module docstring).
METHODS = ["STRICT", "FIFO", "LIFO", "HIFO"]

COMMODITIES = ["HOOL", "ACME", "CORP"]
CASH = "USD"


def gen_ledger(rng: random.Random) -> tuple[str, str]:
    """A ledger exercising lot selection, and the method it uses."""
    method = rng.choice(METHODS)
    commodity = rng.choice(COMMODITIES)
    lines = [
        f'option "booking_method" "{method}"',
        f'2020-01-01 open Assets:Stock  {commodity} "{method}"',
        f"2020-01-01 open Assets:Cash   {CASH}",
        f"2020-01-01 open Income:Gains  {CASH}",
    ]

    # Augmentations. Distinct costs keep FIFO/LIFO/HIFO distinguishable; a
    # repeated cost (rng permitting) exercises coalescing into one lot.
    day = 2
    lots: list[tuple[Decimal, Decimal]] = []
    for _ in range(rng.randint(2, 5)):
        units = Decimal(rng.randint(1, 20))
        cost = Decimal(rng.choice(["10.00", "11.00", "12.00", "9.50", "10.00"]))
        lines += [
            f'2020-01-{day:02d} * "buy"',
            f"  Assets:Stock  {units} {commodity} {{{cost} {CASH}}}",
            f"  Assets:Cash  {-(units * cost)} {CASH}",
        ]
        lots.append((units, cost))
        # Same-date augmentations exercise file-order booking (#2093).
        if rng.random() < 0.3:
            day -= 1
        day += 1

    held = sum(u for u, _ in lots)

    # Reductions. `{}` leaves the method to choose; an explicit cost pins a
    # lot and must select exactly it (or fail, if ambiguous).
    for _ in range(rng.randint(1, 3)):
        if held <= 0:
            break
        qty = Decimal(rng.randint(1, int(held)))
        spec = "{}"
        if rng.random() < 0.4:
            spec = f"{{{rng.choice([c for _, c in lots])} {CASH}}}"
        proceeds = qty * Decimal("13.00")
        lines += [
            f'2020-02-{day:02d} * "sell"',
            f"  Assets:Stock  {-qty} {commodity} {spec}",
            f"  Assets:Cash   {proceeds} {CASH}",
            "  Income:Gains",
        ]
        held -= qty
        day += 1

    return "\n".join(lines) + "\n", method


# A booked result is either an error or lot identity -> units.
Booked = dict[tuple[str, str, str, str, str], Decimal]
ERROR = "ERROR"


def booked_rledger(rledger: str, path: str) -> Booked | str:
    """Lots as rledger books them, or ERROR if it refuses the ledger."""
    check = subprocess.run(
        [rledger, "check", path],
        capture_output=True,
        text=True,
        env={"BEANCOUNT_DISABLE_LOAD_CACHE": "1", "PATH": "/usr/bin:/bin"},
        check=False,
    )
    if check.returncode != 0:
        return ERROR
    # cost_number is the PER-UNIT cost and is null for a costless posting,
    # which is what makes it the right discriminator. `cost(position)` is not:
    # for a costless posting it returns the units themselves, so a cash leg
    # looks like it has a cost of 1.
    query = (
        "SELECT account, units(position) AS u, cost_number AS cn, "
        "cost_currency AS cc, cost_date AS cd"
    )
    out = subprocess.run(
        [rledger, "query", path, "--format", "json", query],
        capture_output=True,
        text=True,
        env={"BEANCOUNT_DISABLE_LOAD_CACHE": "1", "PATH": "/usr/bin:/bin"},
        check=False,
    )
    if out.returncode != 0:
        return ERROR
    try:
        rows = json.loads(out.stdout).get("rows", [])
    except json.JSONDecodeError:
        # A banner or log line on stdout is a failure to read the booking, not
        # a reason to abort the campaign — the beancount side already treats
        # undecodable output this way and the two must agree.
        return ERROR
    lots: Booked = {}
    for row in rows:
        units = row.get("u") or {}
        number = Decimal(str(units.get("number", "0")))
        if number == 0:
            continue
        cost_number = row.get("cn")
        if cost_number is not None:
            key = (
                row["account"], units.get("currency", ""),
                format(Decimal(str(cost_number)).normalize(), "f"),
                row.get("cc") or "", str(row.get("cd") or ""),
            )
        else:
            key = (row["account"], units.get("currency", ""), "", "", "")
        lots[key] = lots.get(key, Decimal(0)) + number
    return {k: v for k, v in lots.items() if v != 0}


def booked_beancount(python: str, path: str) -> Booked | str:
    """The same lots as Python beancount books them."""
    script = """
import json, sys
from decimal import Decimal
from beancount import loader
entries, errors, _ = loader.load_file(sys.argv[1])
if errors:
    print("ERROR"); raise SystemExit
out = {}
for entry in entries:
    for p in getattr(entry, "postings", None) or []:
        n = p.units.number
        if n is None or n == 0:
            continue
        if p.cost is not None:
            key = "|".join([p.account, p.units.currency,
                            format(Decimal(p.cost.number).normalize(), "f"),
                            p.cost.currency, str(p.cost.date or "")])
        else:
            key = "|".join([p.account, p.units.currency, "", "", ""])
        out[key] = str(Decimal(out.get(key, "0")) + n)
print(json.dumps({k: v for k, v in out.items() if Decimal(v) != 0}))
"""
    res = subprocess.run(
        [python, "-c", script, path], capture_output=True, text=True, check=False
    )
    if res.returncode != 0 or res.stdout.strip() == ERROR:
        return ERROR
    try:
        raw = json.loads(res.stdout)
    except json.JSONDecodeError:
        return ERROR
    return {tuple(k.split("|")): Decimal(v) for k, v in raw.items()}


def compare(rl: Booked | str, bq: Booked | str) -> list[str]:
    """Differences between two booked results, most significant first."""
    if rl == ERROR and bq == ERROR:
        return []
    if rl == ERROR:
        return ["rledger rejected the ledger; beancount booked it"]
    if bq == ERROR:
        return ["beancount rejected the ledger; rledger booked it"]
    diffs = []
    for key in sorted(set(rl) | set(bq)):
        a, b = rl.get(key), bq.get(key)
        if a != b:
            diffs.append(f"{'/'.join(key)}: rledger={a} beancount={b}")
    return diffs


def check_one(rledger: str, python: str, seed: int) -> list[str]:
    """Run one generated ledger through both engines."""
    rng = random.Random(seed)
    source, method = gen_ledger(rng)
    with tempfile.NamedTemporaryFile(
        "w", suffix=".beancount", delete=False
    ) as fh:
        fh.write(source)
        path = fh.name
    try:
        diffs = compare(
            booked_rledger(rledger, path), booked_beancount(python, path)
        )
    finally:
        Path(path).unlink(missing_ok=True)
    if diffs:
        return [f"seed={seed} method={method}", *diffs, source]
    return []


def self_test(rledger: str, python: str) -> int:
    """Prove the comparison can report a difference, not just agreement.

    A harness that has only ever printed "no divergences" is indistinguishable
    from one that cannot print anything else, so plant known differences and
    require that each is caught.
    """
    ok = True
    lots_a: Booked = {("Assets:Stock", "HOOL", "10", "USD", "2020-01-02"): Decimal(10)}
    lots_b: Booked = {("Assets:Stock", "HOOL", "11", "USD", "2020-01-03"): Decimal(10)}

    planted = [
        ("wrong lot selected", lots_a, lots_b, 2),
        ("wrong units", lots_a, {list(lots_a)[0]: Decimal(5)}, 1),
        ("rledger rejected only", ERROR, lots_a, 1),
        ("beancount rejected only", lots_a, ERROR, 1),
        ("both rejected (agreement)", ERROR, ERROR, 0),
        ("identical (agreement)", lots_a, dict(lots_a), 0),
    ]
    for name, rl, bq, want in planted:
        got = len(compare(rl, bq))
        if got != want:
            print(f"FAIL self-test '{name}': {got} diffs, want {want}")
            ok = False

    # And the real engines must agree on a hand-checked ledger.
    if check_one(rledger, python, seed=1):
        print("FAIL self-test: engines disagreed on seed=1")
        ok = False

    print("self-test passed" if ok else "self-test FAILED")
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--runs", type=int, default=100)
    ap.add_argument("--seed", type=int, help="run a single seed and report")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--rledger", default="target/release/rledger")
    # Defaults to the running interpreter, matching the sibling compat
    # scripts, which CI invokes under an interpreter that already has
    # beancount. Point it at a dedicated venv when running from elsewhere.
    ap.add_argument("--python", default=sys.executable)
    args = ap.parse_args()

    if args.self_test:
        return self_test(args.rledger, args.python)

    seeds = [args.seed] if args.seed is not None else list(range(args.runs))
    total = len(seeds)
    failures = 0
    for seed in seeds:
        report = check_one(args.rledger, args.python, seed)
        if report:
            failures += 1
            print("\n".join(report))
            print("-" * 60)
    print(f"{total - failures}/{total} agreed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
