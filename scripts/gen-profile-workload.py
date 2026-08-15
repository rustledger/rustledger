#!/usr/bin/env python3
"""Generate the deterministic ledgers the profiling jobs run against.

Usage:

    python3 scripts/gen-profile-workload.py <shape> [transactions] > workload.beancount
    python3 scripts/gen-profile-workload.py --list

`profile.yml` calls this instead of carrying its own generator, so a profile
can be reproduced locally byte-for-byte. It used to be a heredoc inside the
workflow, which meant the only way to see what was being measured was to read
the YAML — and what it measured had drifted a long way from what rledger is
asked to do:

    subsystem            share of instructions on `simple`
    rustledger-parser    48%
    allocator            14.5%
    rowan (CST)          9.6%
    booking              0.3%   <-- the entire inventory engine

`simple` has no `{`, `^` or `#` anywhere in it. So it never books a lot, never
matches a reduction, and never triggers the three cost-brace / link / taglink
error passes that only run when those characters are present. Optimizing
against it would tune the cheapest path through the parser and leave the
subsystems real ledgers actually exercise unmeasured.

Every shape is seeded, so night-over-night instruction counts stay comparable;
the seed is per-shape so shapes do not accidentally share a transaction
sequence. Every shape must also LOAD CLEANLY — a workload with errors profiles
the diagnostic paths instead of the happy path, which is a different program.
`scripts/check-profile-workloads.sh` asserts both properties.
"""

from __future__ import annotations

import datetime
import random
import sys
from collections.abc import Sequence

# One transaction count for every shape, so cross-shape comparison is a
# comparison of WORK PER TRANSACTION rather than of ledger size.
DEFAULT_TXNS = 10000

SHAPES: dict[str, str] = {
    "simple": "Two-posting transfers, one currency. The historical workload — "
    "keep as the floor, not as the benchmark.",
    "investment": "Cost specs, per-unit prices and lot reductions. Exercises "
    "booking and inventory, which `simple` leaves at 0.3%.",
    "tagged": "Tags, links and posting metadata. Triggers the cost-brace, "
    "link and taglink error passes that `simple` skips entirely.",
    "multicurrency": "Several currencies with price directives and @ "
    "conversions. Exercises price lookup and multi-currency balancing.",
}


def _header(title: str, accounts: list[str], commodities: Sequence[str] = ()) -> None:
    print(f'option "title" "{title}"')
    print('option "operating_currency" "USD"')
    for c in commodities:
        print(f"1970-01-01 commodity {c}")
    for a in accounts:
        print(f"2020-01-01 open {a}")
    print()


def gen_simple(n: int) -> None:
    rng = random.Random(42)
    accounts = [
        "Assets:Bank:Checking",
        "Assets:Bank:Savings",
        "Expenses:Food",
        "Expenses:Rent",
        "Income:Salary",
        "Liabilities:CreditCard",
    ]
    _header("Profiling Workload — simple", [f"{a} USD" for a in accounts])
    d = datetime.date(2020, 1, 2)
    for i in range(n):
        d += datetime.timedelta(days=1)
        src, dst = rng.choice(accounts), rng.choice(accounts)
        amt = round(rng.uniform(1, 500), 2)
        print(f'{d.isoformat()} * "Payee {i}" "memo {i}"')
        print(f"  {src}  -{amt} USD")
        print(f"  {dst}   {amt} USD")


def gen_investment(n: int) -> None:
    """Buys that create lots and sells that reduce them.

    Sells are emitted only against a lot the generator knows is still open,
    and always at that lot's exact cost, so every reduction matches under
    STRICT booking. A workload that fails to book would profile the error
    path instead of the inventory engine.
    """
    rng = random.Random(43)
    tickers = ["HOOL", "CORP", "ACME", "GLOB"]
    accounts = [
        "Assets:Broker:Cash USD",
        "Income:Gains USD",
        *[f"Assets:Broker:{t} {t}" for t in tickers],
    ]
    _header("Profiling Workload — investment", accounts, tickers)
    # open lots per ticker: list of (units, cost) still held
    held: dict[str, list[tuple[int, str]]] = {t: [] for t in tickers}
    d = datetime.date(2020, 1, 2)
    for i in range(n):
        d += datetime.timedelta(days=1)
        t = rng.choice(tickers)
        # Sell only when a lot exists; otherwise buy. Roughly 1 sell in 3.
        if held[t] and rng.random() < 0.33:
            units, cost = held[t].pop()
            price = f"{float(cost) * rng.uniform(0.8, 1.3):.2f}"
            print(f'{d.isoformat()} * "Sell {t}" "lot {i}"')
            print(f"  Assets:Broker:{t}  -{units} {t} {{{cost} USD}} @ {price} USD")
            print(f"  Assets:Broker:Cash  {units * float(price):.2f} USD")
            print("  Income:Gains")
        else:
            units = rng.randint(1, 50)
            cost = f"{rng.uniform(5, 400):.2f}"
            held[t].append((units, cost))
            print(f'{d.isoformat()} * "Buy {t}" "lot {i}"')
            print(f"  Assets:Broker:{t}   {units} {t} {{{cost} USD}}")
            print(f"  Assets:Broker:Cash  -{units * float(cost):.2f} USD")


def gen_tagged(n: int) -> None:
    """Tags, links and metadata on both transactions and postings.

    `#` and `^` are what gate three whole-tree error passes in
    `parse_via_cst_inner`; `simple` contains neither character, so those
    passes are dead code in every profile taken so far.
    """
    rng = random.Random(44)
    accounts = ["Assets:Bank:Checking", "Expenses:Travel", "Expenses:Food", "Income:Salary"]
    tags = ["trip-japan", "reimbursable", "q1", "personal", "business"]
    _header("Profiling Workload — tagged", [f"{a} USD" for a in accounts])
    d = datetime.date(2020, 1, 2)
    for i in range(n):
        d += datetime.timedelta(days=1)
        src, dst = rng.choice(accounts), rng.choice(accounts)
        amt = round(rng.uniform(1, 500), 2)
        tag = rng.choice(tags)
        print(
            f'{d.isoformat()} * "Payee {i}" "memo {i}" #{tag} ^invoice-{i % 997}'
        )
        print(f'  reference: "REF-{i}"')
        print(f"  priority: {i % 7}")
        print(f"  {src}  -{amt} USD")
        print(f'    note: "leg a"')
        print(f"  {dst}   {amt} USD")


def gen_multicurrency(n: int) -> None:
    rng = random.Random(45)
    currencies = ["EUR", "GBP", "JPY", "CHF"]
    accounts = [
        "Assets:Bank:USD USD",
        "Income:Salary USD",
        *[f"Assets:Bank:{c} {c}" for c in currencies],
    ]
    _header("Profiling Workload — multicurrency", accounts, currencies)
    d = datetime.date(2020, 1, 2)
    for i in range(n):
        d += datetime.timedelta(days=1)
        c = rng.choice(currencies)
        rate = round(rng.uniform(0.7, 150.0), 4)
        amt = round(rng.uniform(10, 900), 2)
        # A price directive every few transactions, so the price map grows.
        if i % 5 == 0:
            print(f"{d.isoformat()} price {c} {rate} USD")
        print(f'{d.isoformat()} * "FX {i}" "memo {i}"')
        print(f"  Assets:Bank:{c}   {amt} {c} @ {rate} USD")
        print(f"  Assets:Bank:USD  -{amt * rate:.2f} USD")


GENERATORS = {
    "simple": gen_simple,
    "investment": gen_investment,
    "tagged": gen_tagged,
    "multicurrency": gen_multicurrency,
}


def main() -> int:
    args = sys.argv[1:]
    if not args or args[0] in ("-h", "--help"):
        print(__doc__)
        return 0
    if args[0] == "--list":
        for name, why in SHAPES.items():
            print(f"{name:15} {why}")
        return 0
    shape = args[0]
    if shape not in GENERATORS:
        print(
            f"unknown shape {shape!r}; known: {', '.join(GENERATORS)}",
            file=sys.stderr,
        )
        return 2
    n = int(args[1]) if len(args) > 1 else DEFAULT_TXNS
    GENERATORS[shape](n)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
