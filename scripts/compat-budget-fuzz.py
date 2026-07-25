#!/usr/bin/env python3
"""Budget report fuzzer — property + differential checks on generated ledgers.

`report budget` is arithmetic over generated data: an accrual pro-rated across
calendar periods, superseded by date, aggregated across a subtree, compared
against postings. Example-based tests only ever cover the examples someone
thought of, and this report shipped a long tail of defects that hand-written
cases kept missing. This harness generates ledgers instead and checks three
oracles per run:

1. BUDGETED, against a clean-room per-day accrual written the OTHER way from
   the implementation (day by day, over calendar periods computed here), so an
   error in the implementation's per-segment arithmetic cannot be reproduced by
   the oracle.

2. ACTUAL, against an independent recomputation from the parsed ledger: which
   postings a row covers, and from which date they start counting.

3. INVARIANTS that hold regardless of either: the process must exit zero, the
   JSON must parse, and the TOTAL must agree with the rows it sits under.

Why not use Fava as the oracle, since `custom "budget"` is Fava's convention:
its quarter boundaries are off by one (`_IntervalQuarter.get_prev` tests
`month > i` where it needs `>=`, so April lands in Q1 and July in Q2),
reported as beancount/fava#2318. Daily, weekly, monthly and yearly agree with
Fava to full precision; quarterly does not, and hand computation confirms this
implementation. Per the project's Python-compatibility policy we match correct
behavior, not bugs. Fava is therefore a cross-check, not the reference.

Requires: beancount (for parsing the generated ledger back). No Fava.

Usage:

    python3 scripts/compat-budget-fuzz.py --rledger ./target/release/rledger
    python3 scripts/compat-budget-fuzz.py --seed 4000 --count 500
    python3 scripts/compat-budget-fuzz.py --self-test
"""

from __future__ import annotations

import argparse
import datetime
import json
import random
import subprocess
import sys
from collections import defaultdict
from decimal import Decimal, getcontext
from pathlib import Path

# The oracle sums amount/days once per day, which accumulates decimal residue
# over a long window; the implementation works per contiguous segment to avoid
# exactly that. Give the oracle enough precision that its own accumulation error
# can never be mistaken for an implementation error.
getcontext().prec = 60

INTERVALS = ["daily", "weekly", "monthly", "quarterly", "yearly"]
CURRENCIES = ["USD", "EUR", "GBP"]

# Component-distinct names on purpose. This report selects subaccounts by
# component (`Expenses:Food` does not cover `Expenses:FoodCourt`, a deliberate
# deviation from Fava's `startswith`), and mixing prefix-colliding names into the
# corpus would test that deviation rather than the arithmetic.
ACCOUNTS = [
    "Expenses:Food",
    "Expenses:Food:Restaurant",
    "Expenses:Food:Grocery",
    "Expenses:Transport",
    "Expenses:Transport:Bus",
    "Expenses:Rent",
]


def period_bounds(interval: str, day: datetime.date):
    """The calendar period containing `day`, as `(start, next_start)`."""
    if interval == "daily":
        return day, day + datetime.timedelta(days=1)
    if interval == "weekly":
        start = day - datetime.timedelta(days=day.weekday())
        return start, start + datetime.timedelta(days=7)
    if interval == "monthly":
        start = day.replace(day=1)
        nxt = (
            start.replace(year=start.year + 1, month=1)
            if start.month == 12
            else start.replace(month=start.month + 1)
        )
        return start, nxt
    if interval == "quarterly":
        m = ((day.month - 1) // 3) * 3 + 1
        start = datetime.date(day.year, m, 1)
        nm = m + 3
        nxt = (
            datetime.date(day.year + 1, 1, 1)
            if nm > 12
            else datetime.date(day.year, nm, 1)
        )
        return start, nxt
    if interval == "yearly":
        return datetime.date(day.year, 1, 1), datetime.date(day.year + 1, 1, 1)
    raise AssertionError(f"unknown interval {interval!r}")


def covers(budgeted: str, other: str, children: bool) -> bool:
    """Does a budget on `budgeted` account for postings booked to `other`?"""
    if children:
        return other == budgeted or other.startswith(budgeted + ":")
    return other == budgeted


def gen_ledger(rng: random.Random):
    lines = ['option "operating_currency" "USD"', ""]
    accts = rng.sample(ACCOUNTS, rng.randint(1, len(ACCOUNTS)))
    for a in accts:
        lines.append(f"2019-01-01 open {a}")
    lines.append("2019-01-01 open Assets:Cash")
    lines.append("")

    for _ in range(rng.randint(1, 5)):
        a = rng.choice(accts)
        ccy = rng.choice(CURRENCIES[: rng.randint(1, 3)])
        d = datetime.date(2020, 1, 1) + datetime.timedelta(days=rng.randint(0, 1400))
        amt = Decimal(rng.randint(1, 500000)) / Decimal(100)
        lines.append(f'{d} custom "budget" {a} "{rng.choice(INTERVALS)}" {amt} {ccy}')
    lines.append("")

    for _ in range(rng.randint(0, 12)):
        a = rng.choice(accts)
        ccy = rng.choice(CURRENCIES[:2])
        d = datetime.date(2020, 1, 1) + datetime.timedelta(days=rng.randint(0, 1400))
        amt = Decimal(rng.randint(1, 50000)) / Decimal(100)
        lines.append(f'{d} * "txn"')
        lines.append(f"  {a}  {amt} {ccy}")
        lines.append(f"  Assets:Cash  -{amt} {ccy}")
    lines.append("")

    start = datetime.date(2020, 1, 1) + datetime.timedelta(days=rng.randint(0, 1200))
    end = start + datetime.timedelta(days=rng.randint(1, 900))
    return "\n".join(lines) + "\n", start, end


def read_declarations(path: str):
    """`(date, index, account, interval, amount, currency)` per budget directive.

    The index preserves file order so that two declarations on one date
    supersede in the order written, which is what beancount entry order (and
    therefore Fava) does.
    """
    from beancount.core.data import Custom
    from beancount.loader import load_file

    entries, _errors, _options = load_file(path)
    decls = []
    for e in entries:
        if not isinstance(e, Custom) or e.type != "budget":
            continue
        vals = [v.value for v in e.values]
        if len(vals) < 3:
            continue
        acct, interval, amount = vals[0], vals[1], vals[2]
        decls.append(
            (
                e.date,
                len(decls),
                str(acct),
                str(interval).lower(),
                amount.number,
                amount.currency,
            )
        )
    return decls


def expected_budgeted(decls, d_from, d_to, children: bool):
    """Per-day accrual over calendar periods, from the declarations."""
    out = {}
    accounts = {d[2] for d in decls}
    for row_acct, ccy in sorted({(d[2], d[5]) for d in decls}):
        total = Decimal(0)
        for src in (a for a in accounts if covers(row_acct, a, children)):
            mine = sorted(d for d in decls if d[2] == src and d[5] == ccy)
            if not mine:
                continue
            day = d_from
            while day < d_to:
                live = [m for m in mine if m[0] <= day]
                if live:
                    _, _, _, interval, amount, _ = live[-1]
                    start, nxt = period_bounds(interval, day)
                    total += amount / Decimal((nxt - start).days)
                day += datetime.timedelta(days=1)
        if total != 0:
            out[(row_acct, ccy)] = total
    return out


def expected_actual(path: str, decls, rows, d_from, d_to, children: bool):
    """Independent recomputation of each row's `actual`.

    A row's budgeted figure is its own budget plus, under `--children`, its
    descendants' — never its ancestor's — so its spending is clipped by the same
    set. Spending that predates a child's own budget belongs to the parent's
    row, which does cover it.
    """
    from beancount.core.data import Transaction
    from beancount.loader import load_file

    entries, _errors, _options = load_file(path)
    starts: dict[tuple[str, str], datetime.date] = {}
    for d in decls:
        key = (d[2], d[5])
        starts[key] = min(starts.get(key, d[0]), d[0])

    out: dict[tuple[str, str], Decimal] = defaultdict(Decimal)
    for e in entries:
        if not isinstance(e, Transaction) or not (d_from <= e.date < d_to):
            continue
        for p in e.postings:
            for row_acct, ccy in rows:
                if ccy != p.units.currency or not covers(row_acct, p.account, children):
                    continue
                covering = [
                    s
                    for (a, c), s in starts.items()
                    if c == ccy
                    and covers(row_acct, a, children)
                    and covers(a, p.account, children)
                ]
                if not covering:
                    continue
                if e.date >= max(min(covering), d_from):
                    out[(row_acct, ccy)] += p.units.number
    return dict(out)


def tolerance(rendered: str) -> Decimal:
    """Half a unit in the last place the report actually printed.

    The report rounds to the currency's inferred display precision, which can be
    coarse, so a fixed tolerance would flag rendering as if it were arithmetic.
    """
    dp = len(rendered.split(".")[1]) if "." in rendered else 0
    return Decimal(5) * Decimal(10) ** Decimal(-dp - 1) + Decimal("1e-12")


def check_one(rledger, path, src, d_from, d_to, children, failures, seed):
    Path(path).write_text(src)
    args = [
        rledger, "report", path, "budget",
        "--from", str(d_from), "--to", str(d_to),
        "--format", "json", "--no-pager",
    ]
    if children:
        args.append("--children")
    proc = subprocess.run(args, capture_output=True, text=True, timeout=120)
    if proc.returncode != 0:
        failures["nonzero_exit"].append((seed, proc.stderr.strip()[:200]))
        return
    try:
        got = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        failures["invalid_json"].append((seed, str(exc)[:120]))
        return

    rows = {(b["account"], b["currency"]): b for b in got["budgets"]}
    decls = read_declarations(path)

    for key, want in expected_budgeted(decls, d_from, d_to, children).items():
        row = rows.get(key)
        if row is None:
            failures["missing_row"].append((seed, key, str(want)[:24], children))
            continue
        if row["budgeted"] is None:
            failures["budgeted_null"].append((seed, key, children))
            continue
        gotv = Decimal(row["budgeted"])
        if abs(gotv - want) > tolerance(row["budgeted"]):
            failures["budgeted_mismatch"].append(
                (seed, key, f"got={gotv} want={str(want)[:24]}", children)
            )

    act = expected_actual(path, decls, list(rows), d_from, d_to, children)
    for key, row in rows.items():
        if row["actual"] is None:
            failures["actual_null"].append((seed, key, children))
            continue
        want = act.get(key, Decimal(0))
        gotv = Decimal(row["actual"])
        if abs(gotv - want) > tolerance(row["actual"]):
            failures["actual_mismatch"].append(
                (seed, key, f"got={gotv} want={want}", children)
            )

    if not children:
        for tot in got["totals"]:
            if tot["budgeted"] is None or tot["account"] != "TOTAL":
                continue
            summed = sum(
                Decimal(r["budgeted"])
                for r in got["budgets"]
                if r["currency"] == tot["currency"] and r["budgeted"] is not None
            )
            slack = tolerance(tot["budgeted"]) * Decimal(len(got["budgets"]) + 1)
            if abs(summed - Decimal(tot["budgeted"])) > slack:
                failures["total_ne_rows"].append(
                    (seed, tot["currency"], f"rows={summed} total={tot['budgeted']}")
                )


def self_test() -> int:
    """Check the oracle's own arithmetic on cases with known answers."""
    d = datetime.date
    cases = [
        ("monthly", d(2024, 2, 10), d(2024, 2, 1), d(2024, 3, 1)),
        ("quarterly", d(2024, 4, 15), d(2024, 4, 1), d(2024, 7, 1)),
        ("quarterly", d(2024, 10, 1), d(2024, 10, 1), d(2025, 1, 1)),
        ("yearly", d(2024, 6, 1), d(2024, 1, 1), d(2025, 1, 1)),
        ("weekly", d(2025, 1, 1), d(2024, 12, 30), d(2025, 1, 6)),
    ]
    ok = True
    for interval, day, want_start, want_next in cases:
        start, nxt = period_bounds(interval, day)
        if (start, nxt) != (want_start, want_next):
            print(f"FAIL {interval} {day}: got {start}..{nxt} want {want_start}..{want_next}")
            ok = False
    # A whole period accrues the stated amount. Compared with a tolerance
    # because the oracle sums amount/days once per day: 400/29 summed 29 times
    # leaves a residue in the last place. The implementation works per
    # contiguous segment precisely so a fully covered interval comes out EXACT,
    # which is why the oracle is the one that needs the slack here.
    decls = [(d(2020, 1, 1), 0, "Expenses:X", "monthly", Decimal("400"), "USD")]
    got = expected_budgeted(decls, d(2024, 2, 1), d(2024, 3, 1), False)
    leap_feb = got.get(("Expenses:X", "USD"), Decimal(0))
    if abs(leap_feb - Decimal(400)) > Decimal("1e-40"):
        print(f"FAIL leap-February accrual: {got}")
        ok = False
    print("self-test:", "OK" if ok else "FAILED")
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rledger", default="./target/release/rledger")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--count", type=int, default=250)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    tmp = Path("/tmp/compat-budget-fuzz")
    tmp.mkdir(exist_ok=True)
    path = str(tmp / "ledger.beancount")
    failures = defaultdict(list)

    for i in range(args.count):
        seed = args.seed + i
        rng = random.Random(seed)
        src, d_from, d_to = gen_ledger(rng)
        check_one(args.rledger, path, src, d_from, d_to, rng.random() < 0.5, failures, seed)

    print(f"ran {args.count} generated ledgers from seed {args.seed}")
    if not failures:
        print("ALL CLEAN")
        return 0
    for kind, items in sorted(failures.items()):
        print(f"\n=== {kind}: {len(items)} ===")
        for item in items[:5]:
            print("   ", item)
    print("\nReproduce one with --seed <n> --count 1")
    return 1


if __name__ == "__main__":
    sys.exit(main())
