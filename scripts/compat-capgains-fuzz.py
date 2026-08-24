#!/usr/bin/env python3
"""Capital-gains fuzzer — property checks on generated ledgers.

`report capgains` produces numbers people put on a tax return, and it has no
Python beancount counterpart to diff against: beancount has no capgains
report. So this checks it against PROPERTIES and against ITSELF, the way
`compat-budget-fuzz.py` checks the budget report rather than diffing it.

Why this surface. The report classifies each closed lot short or long from
the SURVIVING lot's acquisition date, so it consumes exactly what booking
decides — and booking's lot selection has produced two real bugs recently
(#2097 STRICT_WITH_SIZE, #2115 LIFO ties). A wrong term, or a lot
attributed to the wrong acquisition, still balances, still reports no error, and still looks entirely
plausible: the failure mode example-based tests are worst at catching, on
the surface where being wrong is most expensive.

The oracles, weakest to strongest:

  ARITHMETIC   gain == proceeds - cost_basis, per row. Unambiguous.
  PARTITION    short + long + unknown covers every disposal exactly once,
               by count and by summed gain. A row that falls out of the
               classification is invisible in the totals people read.
  HELD DAYS    held_days == sold - acquired, in days.
  TERM         `--long-term-days N` is defined as "held strictly more than
               N days", which is a rule this script can evaluate exactly.
               The DEFAULT rule is a calendar one ("more than one year"),
               which is not the same function -- so the two are compared
               against each other, and they may legitimately differ only
               where a leap day falls in the span. Anywhere else, a
               disagreement is a bug in one of them.
  FILTER       `--year Y` returns exactly the disposals sold in Y, and
               nothing else moves.

Deliberately NOT asserted: a hard answer for a 29 February acquisition. The
one-year anniversary of 2020-02-29 is genuinely ambiguous (28 February or
1 March 2021), conventions differ, and asserting a guess would encode this
script's opinion as the specification. Those spans are generated, reported
when the two term rules disagree, and left for a human -- see `--leap-report`.

A disposal needs a sale PRICE: booking records a gain only for a reduction
carrying `@`, since a costless transfer of a lot is not a disposal. Every
generated sale therefore carries one, which is also why this file cares
about the price axis added to the booking fuzzer.

Usage:
    scripts/compat-capgains-fuzz.py --runs 200
    scripts/compat-capgains-fuzz.py --seed 12345      # reproduce one case
    scripts/compat-capgains-fuzz.py --self-test       # prove it detects a bug
"""

from __future__ import annotations

import argparse
import json
import random
import subprocess
import sys
import tempfile
from datetime import date, timedelta
from decimal import Decimal
from pathlib import Path

CASH = "USD"
COMMODITIES = ["ACME", "HOOL", "CORP"]
METHODS = ["FIFO", "LIFO", "HIFO", "STRICT"]
ERROR = "ERROR"


def one_year_after(d: date) -> date | None:
    """The one-year anniversary of `d`, or None when it does not exist.

    29 February has no anniversary in a common year. Returning None rather
    than picking 28 February or 1 March keeps the ambiguity visible instead
    of burying a convention in a comparison.
    """
    try:
        return d.replace(year=d.year + 1)
    except ValueError:
        return None


def spans_a_leap_day(a: date, s: date) -> bool:
    """True when 29 February falls in (a, s]."""
    for year in range(a.year, s.year + 1):
        try:
            leap = date(year, 2, 29)
        except ValueError:
            continue
        if a < leap <= s:
            return True
    return False


def gen_ledger(rng: random.Random) -> tuple[str, str]:
    """A ledger whose sales close lots across the term boundary."""
    method = rng.choice(METHODS)
    commodity = rng.choice(COMMODITIES)
    lines = [
        f'option "booking_method" "{method}"',
        f'2019-01-01 open Assets:Stock  {commodity} "{method}"',
        f"2019-01-01 open Assets:Cash   {CASH}",
        f"2019-01-01 open Income:Gains  {CASH}",
    ]

    # Acquisitions. Dates cluster on the term boundary and on leap days,
    # because a uniform draw over several years almost never lands on the
    # day that decides the classification.
    anchors = [
        date(2020, 2, 28), date(2020, 2, 29), date(2020, 3, 1),
        date(2021, 2, 28), date(2021, 3, 1),
        date(2019, 12, 31), date(2020, 1, 1), date(2020, 6, 15),
    ]
    lots: list[tuple[date, Decimal, Decimal]] = []
    for _ in range(rng.randint(1, 4)):
        acq = rng.choice(anchors) + timedelta(days=rng.randint(-1, 1))
        units = Decimal(rng.randint(1, 20))
        # Distinct costs keep booking unambiguous: identical (cost, date)
        # lots pool differently in the two engines (#2118), and this script
        # is about the REPORT, not about re-finding that.
        cost = Decimal(rng.choice(["10.00", "11.50", "12.25", "9.75", "13.00"]))
        lots.append((acq, units, cost))

    # STRICT cannot resolve a bare `{}` against several lots, so it only gets
    # a single-lot ledger. Otherwise every STRICT run would be a booking
    # error rather than a test of the report.
    if method == "STRICT" and len(lots) > 1:
        lots = lots[:1]

    for acq, units, cost in sorted(lots):
        lines += [
            f'{acq.isoformat()} * "buy"',
            f"  Assets:Stock  {units} {commodity} {{{cost} {CASH}}}",
            f"  Assets:Cash  {-(units * cost)} {CASH}",
        ]

    earliest = min(a for a, _, _ in lots)

    # Sales, placed either side of the one-year mark from the earliest lot.
    #
    # Quantities are capped by what is held ON THE SALE DATE, not by the
    # ledger total. Drawing from the total oversold whenever a sale preceded
    # a later acquisition, and 9% of runs died on "Not enough units" — a
    # generator producing ledgers rledger rightly refuses, which tests
    # nothing here and hides how much coverage was actually lost.
    anniversary = one_year_after(earliest) or (earliest + timedelta(days=366))
    sale_dates = sorted(
        max(anniversary + timedelta(days=rng.choice([-2, -1, 0, 1, 2, 30, 400])),
            earliest + timedelta(days=1))
        for _ in range(rng.randint(1, 3))
    )
    sold_so_far = Decimal(0)
    for sold in sale_dates:
        available = sum(u for a, u, _ in lots if a <= sold) - sold_so_far
        if available <= 0:
            continue
        qty = Decimal(rng.randint(1, int(available)))
        price = Decimal(rng.choice(["15.00", "8.00", "12.00"]))
        lines += [
            f'{sold.isoformat()} * "sell"',
            f"  Assets:Stock  {-qty} {commodity} {{}} @ {price} {CASH}",
            f"  Assets:Cash   {qty * price} {CASH}",
            "  Income:Gains",
        ]
        sold_so_far += qty

    return "\n".join(lines) + "\n", method


def run_capgains(rledger: str, path: str, extra: list[str]) -> dict | str:
    """`report capgains --format json`, or ERROR if rledger refuses."""
    out = subprocess.run(
        [rledger, "report", path, "capgains", "--format", "json", *extra],
        capture_output=True,
        text=True,
        env={"BEANCOUNT_DISABLE_LOAD_CACHE": "1", "PATH": "/usr/bin:/bin"},
        check=False,
    )
    if out.returncode != 0:
        return ERROR
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError:
        return ERROR


def check_report(rep: dict) -> list[str]:
    """Every property that holds regardless of which lots booking picked."""
    problems: list[str] = []
    rows = rep.get("disposals", [])

    for r in rows:
        proceeds = Decimal(r["proceeds"])
        basis = Decimal(r["cost_basis"])
        gain = Decimal(r["gain"])
        if gain != proceeds - basis:
            problems.append(
                f"gain != proceeds - cost_basis: {gain} != {proceeds} - {basis} "
                f"({r['commodity']} sold {r['sold']})"
            )
        acquired = date.fromisoformat(r["acquired"])
        sold = date.fromisoformat(r["sold"])
        if r["held_days"] != (sold - acquired).days:
            problems.append(
                f"held_days {r['held_days']} != {(sold - acquired).days} "
                f"({r['acquired']} -> {r['sold']})"
            )
        if Decimal(r["units"]) <= 0:
            problems.append(f"non-positive units {r['units']} sold {r['sold']}")

    # Partition, checked exactly. A row reaching no bucket vanishes from the
    # totals a reader actually looks at while every individual row still
    # checks out, so this compares COUNT and every money column, per term and
    # per currency, in both directions.
    #
    # The buckets are one summary object per CURRENCY carrying a `disposals`
    # count, not one object per disposal. An earlier version counted
    # `len(bucket)` and only complained when every bucket was empty, which
    # made a dropped row, a wrong `disposals` count, or a missing
    # `unknown_term` entry all invisible.
    fields = ("disposals", "proceeds", "cost_basis", "gain")
    expected: dict[tuple[str, str], dict[str, Decimal]] = {}
    for r in rows:
        acc = expected.setdefault(
            (r["term"], r["currency"]), dict.fromkeys(fields, Decimal(0))
        )
        acc["disposals"] += 1
        for f in ("proceeds", "cost_basis", "gain"):
            acc[f] += Decimal(r[f])

    reported: dict[tuple[str, str], dict[str, Decimal]] = {}
    for key, term in (
        ("short_term", "short"),
        ("long_term", "long"),
        ("unknown_term", "unknown"),
    ):
        for b in rep.get(key, []):
            reported[(term, b["currency"])] = {
                f: Decimal(str(b.get(f, 0))) for f in fields
            }

    for k in sorted(set(expected) | set(reported), key=str):
        exp, got = expected.get(k), reported.get(k)
        if exp is None:
            problems.append(f"{k[0]}_term/{k[1]} reported but no disposal rows have it")
            continue
        if got is None:
            problems.append(
                f"{int(exp['disposals'])} {k[0]}-term {k[1]} disposal(s) reach no bucket"
            )
            continue
        for f in fields:
            if exp[f] != got[f]:
                problems.append(
                    f"{k[0]}_term/{k[1]} {f}: bucket={got[f]} rows={exp[f]}"
                )
    return problems


def check_term_rules(rledger: str, path: str) -> list[str]:
    """The calendar rule and an explicit day count must agree off leap days.

    `--long-term-days N` is exactly "held more than N days", which this
    script can evaluate. The default is a calendar rule. They are different
    functions and may differ only where 29 February falls in the span; a
    disagreement anywhere else means one of them is wrong.
    """
    problems: list[str] = []
    default = run_capgains(rledger, path, [])
    fixed = run_capgains(rledger, path, ["--long-term-days", "365"])
    if isinstance(default, str) or isinstance(fixed, str):
        return ["capgains failed to run"]

    for row in fixed.get("disposals", []):
        want = "long" if row["held_days"] > 365 else "short"
        if row["term"] != want:
            problems.append(
                f"--long-term-days 365: held {row['held_days']} classified "
                f"{row['term']}, rule says {want} ({row['acquired']} -> {row['sold']})"
            )

    # Compare the row SETS first. Looking rows up one at a time and skipping
    # misses treated a dropped row as agreement: if the override lost a
    # disposal, only the survivors were compared and the run stayed clean.
    def keyof(r):
        return (r["acquired"], r["sold"], r["units"], r["currency"], r["account"])

    d_keys = sorted(keyof(r) for r in default.get("disposals", []))
    f_keys = sorted(keyof(r) for r in fixed.get("disposals", []))
    if d_keys != f_keys:
        only_default = [k for k in d_keys if k not in f_keys]
        only_fixed = [k for k in f_keys if k not in d_keys]
        if only_default:
            problems.append(
                f"--long-term-days 365 dropped {len(only_default)} disposal(s) "
                f"the default reports, e.g. {only_default[0]}"
            )
        if only_fixed:
            problems.append(
                f"--long-term-days 365 reports {len(only_fixed)} disposal(s) the "
                f"default does not, e.g. {only_fixed[0]}"
            )
        return problems

    keyed = {keyof(r): r for r in fixed.get("disposals", [])}
    for row in default.get("disposals", []):
        other = keyed[keyof(row)]
        if row["term"] == other["term"]:
            continue
        acquired = date.fromisoformat(row["acquired"])
        sold = date.fromisoformat(row["sold"])
        if spans_a_leap_day(acquired, sold):
            continue  # legitimate: the two rules genuinely differ here
        problems.append(
            f"calendar rule says {row['term']} but 365-day rule says "
            f"{other['term']}, and no leap day in span "
            f"({row['acquired']} -> {row['sold']}, {row['held_days']}d)"
        )
    return problems


def check_year_filter(rledger: str, path: str, rep: dict) -> list[str]:
    """`--year Y` returns the disposals sold in Y, and only those."""
    years = {date.fromisoformat(r["sold"]).year for r in rep.get("disposals", [])}
    problems: list[str] = []
    for year in sorted(years):
        got = run_capgains(rledger, path, ["--year", str(year)])
        if isinstance(got, str):
            problems.append(f"--year {year} failed to run")
            continue
        rows = got.get("disposals", [])
        stray = [r for r in rows if date.fromisoformat(r["sold"]).year != year]
        if stray:
            problems.append(f"--year {year} returned {len(stray)} row(s) from another year")
        want = len([r for r in rep["disposals"] if date.fromisoformat(r["sold"]).year == year])
        if len(rows) != want:
            problems.append(f"--year {year} returned {len(rows)} row(s), unfiltered has {want}")
    return problems


def check_one(
    rledger: str, seed: int, leap_report: bool
) -> tuple[list[str], list[str]]:
    rng = random.Random(seed)
    source, method = gen_ledger(rng)
    with tempfile.NamedTemporaryFile("w", suffix=".beancount", delete=False) as fh:
        fh.write(source)
        path = fh.name
    notes: list[str] = []
    try:
        rep = run_capgains(rledger, path, [])
        if rep == ERROR:
            # A ledger rledger refuses is not a capgains finding: booking
            # errors are the booking fuzzer's subject, not this one.
            return [], []
        problems = check_report(rep)
        problems += check_term_rules(rledger, path)
        problems += check_year_filter(rledger, path, rep)
        if leap_report:
            # Diagnostics, kept OUT of `problems`. These are the deliberately
            # ambiguous 29 February spans this script declines to assert on;
            # counting them as failures made the documented inspection mode
            # exit 1 on ledgers the generator produces on purpose.
            for r in rep.get("disposals", []):
                a = date.fromisoformat(r["acquired"])
                if (a.month, a.day) == (2, 29):
                    notes.append(
                        f"seed={seed} LEAP acquired {r['acquired']} sold "
                        f"{r['sold']} held {r['held_days']}d -> {r['term']}"
                    )
    finally:
        Path(path).unlink(missing_ok=True)
    if problems:
        return [f"seed={seed} method={method}", *problems, source], notes
    return [], notes


def self_test(rledger: str) -> int:
    """Prove each check can FAIL, not merely that it passes."""
    ok = True

    def row(**kw):
        base = {
            "sold": "2022-03-02", "account": "Assets:Stock", "commodity": "ACME",
            "units": "6", "acquired": "2021-03-01", "held_days": 366,
            "term": "long", "currency": "USD", "proceeds": "90.00",
            "cost_basis": "60.00", "gain": "30.00",
        }
        base.update(kw)
        return base

    def bucket(**kw):
        base = {
            "currency": "USD", "disposals": 1,
            "proceeds": "90.00", "cost_basis": "60.00", "gain": "30.00",
        }
        base.update(kw)
        return base

    good = {
        "disposals": [row()],
        "short_term": [],
        "long_term": [bucket()],
        "unknown_term": [],
    }
    planted = [
        ("clean report", good, 0),
        # One money column wrong in the row: the arithmetic check fires, and so
        # does the partition, since the row no longer sums to its bucket.
        ("gain does not match proceeds - basis",
         {**good, "disposals": [row(gain="31.00")]}, 2),
        ("held_days disagrees with the dates",
         {**good, "disposals": [row(held_days=999)]}, 1),
        ("bucket gain does not match its rows",
         {**good, "long_term": [bucket(gain="99.00")]}, 1),
        ("bucket disposals count is wrong",
         {**good, "long_term": [bucket(disposals=7)]}, 1),
        ("disposals exist but nothing is bucketed",
         {**good, "long_term": []}, 1),
        ("a bucket exists with no rows behind it",
         {**good, "unknown_term": [bucket(currency="EUR")]}, 1),
        # The unknown_term bucket was previously unchecked entirely.
        ("unknown-term rows reach no bucket",
         {**good, "disposals": [row(term="unknown")], "long_term": []}, 1),
        ("non-positive units", {**good, "disposals": [row(units="0")]}, 1),
    ]
    for name, rep, want in planted:
        got = len(check_report(rep))
        if got != want:
            print(f"FAIL self-test '{name}': {got} problem(s), want {want}")
            ok = False

    # The leap-day helper decides when the two term rules may disagree, so a
    # wrong answer here would silently excuse a real classification bug.
    leap_cases = [
        ("span contains 29 Feb", date(2020, 1, 1), date(2020, 3, 1), True),
        ("span ends exactly on 29 Feb", date(2020, 1, 1), date(2020, 2, 29), True),
        ("span starts on 29 Feb", date(2020, 2, 29), date(2020, 3, 1), False),
        ("common year, no leap day", date(2021, 1, 1), date(2021, 12, 31), False),
        ("multi-year span crossing one", date(2019, 6, 1), date(2021, 6, 1), True),
    ]
    for name, a, s, want in leap_cases:
        got = spans_a_leap_day(a, s)
        if got != want:
            print(f"FAIL self-test 'spans_a_leap_day: {name}': {got}, want {want}")
            ok = False

    if one_year_after(date(2020, 2, 29)) is not None:
        print("FAIL self-test: 29 Feb must have no anniversary in a common year")
        ok = False
    if one_year_after(date(2021, 3, 1)) != date(2022, 3, 1):
        print("FAIL self-test: ordinary anniversary is wrong")
        ok = False

    # And the real binary must agree on a hand-checked ledger: 365 days is
    # SHORT under a "more than one year" rule, 366 is long.
    with tempfile.NamedTemporaryFile("w", suffix=".beancount", delete=False) as fh:
        fh.write(
            'option "booking_method" "FIFO"\n'
            "2020-01-01 open Assets:Stock  ACME\n"
            "2020-01-01 open Assets:Cash   USD\n"
            "2020-01-01 open Income:Gains  USD\n"
            '2021-03-01 * "buy"\n'
            "  Assets:Stock  10 ACME {10.00 USD}\n"
            "  Assets:Cash  -100.00 USD\n"
            '2022-03-01 * "sell"\n'
            "  Assets:Stock  -4 ACME {} @ 15.00 USD\n"
            "  Assets:Cash   60.00 USD\n"
            "  Income:Gains\n"
            '2022-03-02 * "sell"\n'
            "  Assets:Stock  -6 ACME {} @ 15.00 USD\n"
            "  Assets:Cash   90.00 USD\n"
            "  Income:Gains\n"
        )
        path = fh.name
    try:
        rep = run_capgains(rledger, path, ["--year", "2022"])
        if isinstance(rep, str):
            print("FAIL self-test: capgains failed on the hand-checked ledger")
            ok = False
        else:
            terms = {r["held_days"]: r["term"] for r in rep["disposals"]}
            if terms.get(365) != "short" or terms.get(366) != "long":
                print(f"FAIL self-test: term boundary moved: {terms}")
                ok = False
            if check_report(rep):
                print(f"FAIL self-test: hand-checked ledger has problems: {check_report(rep)}")
                ok = False
    finally:
        Path(path).unlink(missing_ok=True)

    print("self-test passed" if ok else "self-test FAILED")
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--runs", type=int, default=100)
    ap.add_argument("--seed", type=int, help="run a single seed and report")
    ap.add_argument("--start-seed", type=int, default=0)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--rledger", default="target/release/rledger")
    ap.add_argument(
        "--leap-report",
        action="store_true",
        help="also print 29 February acquisitions and how they classified",
    )
    args = ap.parse_args()

    if args.self_test:
        return self_test(args.rledger)

    seeds = (
        [args.seed]
        if args.seed is not None
        else list(range(args.start_seed, args.start_seed + args.runs))
    )
    failures = 0
    all_notes: list[str] = []
    for seed in seeds:
        report, notes = check_one(args.rledger, seed, args.leap_report)
        all_notes += notes
        if report:
            failures += 1
            print("\n".join(report))
            print("-" * 60)
    if all_notes:
        # Printed after the failures and tallied separately, so `--leap-report`
        # never changes the verdict.
        print(f"\n{len(all_notes)} leap-day acquisition(s), reported not asserted:")
        for n in all_notes:
            print(f"  {n}")
    print(f"\n{len(seeds) - failures}/{len(seeds)} clean")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
