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
(currency, per-unit cost, cost currency, lot date, label) -> units — so consuming the
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

Lot identity has three components a method can tie on — acquisition date,
per-unit cost, and label — and the first campaign only ever collided on them
by accident. Every divergence it found had same-date lots (12/12, against
0/189 for seeds without them), which meant the generator was answering one
question well and never asking the others: two lots at the same HIGHEST cost
under HIFO, or two lots on the same date under STRICT, essentially never
appeared. `TIES` now constructs each configuration deliberately, and the tie
mode is reported with every divergence so the classes stay separable.

One divergence class is KNOWN and deliberately not fixed: beancount pools
acquisitions sharing (cost, date, label) into a single inventory position,
while rustledger keeps a slot per acquisition, so the two consume in
different orders once a lot identity repeats non-contiguously within a date
(#2118). rustledger's answer respects acquisition order and beancount's
cannot, so we keep ours. Those runs are still compared and still printed —
only their verdict changes, and they are tallied on their own line. The exit
code tracks UNEXPLAINED divergences alone: a permanently red run teaches
everyone to ignore it, which is how the next real regression gets missed.

Usage:
    scripts/compat-booking-fuzz.py --runs 200
    scripts/compat-booking-fuzz.py --runs 500 --start-seed 9000
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


# Lot identity has three components a method can tie on: acquisition date,
# per-unit cost, and label. Random generation collides on them only by
# accident, so the interesting configurations — two lots at the same highest
# cost under HIFO, two lots on the same date under STRICT — were never
# reliably reached. These modes construct the tie instead of hoping for it.
TIES = ["none", "date", "cost", "both", "label"]


def pooling_shape(
    days: list[int], costs: list[Decimal], labels: list[str | None]
) -> bool:
    """True when beancount's lot pooling could reorder consumption (#2118).

    beancount's `Inventory` is keyed by `(currency, cost)`, so acquisitions
    sharing `(cost, date, label)` collapse into ONE position, sitting where
    the FIRST of them sat. rustledger keeps a slot per acquisition. That only
    changes the consumption ORDER when a repeated identity is NON-CONTIGUOUS
    within its date: `[a, b, a]` pools `a`'s later units forward, ahead of
    `b`, while `[a, a, b]` pools into the order it already had.

    Deliberately narrow. This downgrades a real divergence to an expected one,
    so every case it matches is a case this harness stops guarding. Requiring
    the non-contiguous repeat -- rather than merely "some identity repeats" --
    keeps it to the shape #2118 actually describes.
    """
    by_day: dict[int, list[tuple[Decimal, str | None]]] = {}
    for day, cost, label in zip(days, costs, labels, strict=True):
        by_day.setdefault(day, []).append((cost, label))
    for seq in by_day.values():
        for i, ident in enumerate(seq):
            rest = seq[i + 1 :]
            if ident not in rest:
                continue
            j = i + 1 + rest.index(ident)
            if any(seq[k] != ident for k in range(i + 1, j)):
                return True
    return False


def gen_ledger(rng: random.Random) -> tuple[str, str, str, bool]:
    """A ledger exercising lot selection.

    Returns source, booking method, tie mode, and whether the lots take the
    shape beancount's pooling reorders (#2118).
    """
    method = rng.choice(METHODS)
    tie = rng.choice(TIES)
    commodity = rng.choice(COMMODITIES)
    lines = [
        f'option "booking_method" "{method}"',
        f'2020-01-01 open Assets:Stock  {commodity} "{method}"',
        f"2020-01-01 open Assets:Cash   {CASH}",
        f"2020-01-01 open Income:Gains  {CASH}",
    ]

    count = rng.randint(2, 5)
    pool = ["10.00", "11.00", "12.00", "9.50", "13.25", "8.75"]
    if tie == "none":
        # A control has to control for BOTH axes. Drawing costs with
        # replacement from a short pool collided ~79% of the time, so "no
        # tie" runs were quietly full of cost ties and could not be used to
        # attribute a divergence to the date axis.
        costs = [Decimal(c) for c in rng.sample(pool, count)]
    else:
        costs = [Decimal(rng.choice(pool)) for _ in range(count)]
    days = list(range(2, 2 + count))
    labels: list[str | None] = [None] * count

    # Tie a RANDOM-SIZED GROUP, not just the first two. Tying exactly two lost
    # the configuration that found the FIFO coalescing divergence — three lots
    # sharing a date with two of them sharing a cost — because that needs a
    # group of three. The rest stay random so a tie is never the only thing
    # distinguishing the ledger.
    group = rng.randint(2, count)
    if tie in ("date", "both"):
        for i in range(1, group):
            days[i] = days[0]
    if tie in ("cost", "both"):
        for i in range(1, group):
            costs[i] = costs[0]
    elif tie == "date" and group >= 3:
        # Inside a date-tied group of three or more, CONSTRUCT the
        # non-contiguous repeat — [a, b, a] — rather than hope a random draw
        # produces it. That shape is what separates "one coalesced lot" from
        # "two lots that merely share a price", and it is the configuration
        # the FIFO coalescing divergence needs. Drawing independently from a
        # narrowed pool still yielded contiguous runs ([a, a, b]) or all-equal
        # costs most of the time, so the shape was described but not ensured.
        first, second = rng.sample(pool, 2)
        for i in range(group):
            costs[i] = Decimal(first if i % 2 == 0 else second)
    if tie == "label":
        # Same date and cost, distinguished only by label — the one axis that
        # makes two otherwise identical lots addressable separately.
        days[1] = days[0]
        costs[1] = costs[0]
        labels[0], labels[1] = "lot-a", "lot-b"

    lots: list[tuple[Decimal, Decimal, str | None]] = []
    for units_i, cost, day, label in zip(
        [Decimal(rng.randint(1, 20)) for _ in range(count)],
        costs, days, labels, strict=True,
    ):
        spec = f"{cost} {CASH}" + (f', "{label}"' if label else "")
        lines += [
            f'2020-01-{day:02d} * "buy"',
            f"  Assets:Stock  {units_i} {commodity} {{{spec}}}",
            f"  Assets:Cash  {-(units_i * cost)} {CASH}",
        ]
        lots.append((units_i, cost, label))

    held = sum(u for u, _, _ in lots)

    # Reductions. `{}` leaves the choice to the method — the case a tie makes
    # ambiguous. An explicit cost pins a lot, and under a cost tie it pins TWO,
    # which STRICT is supposed to refuse rather than resolve.
    day = 3
    for _ in range(rng.randint(1, 3)):
        if held <= 0:
            break
        qty = Decimal(rng.randint(1, int(held)))
        roll = rng.random()
        if roll < 0.3:
            spec = f"{{{rng.choice([c for _, c, _ in lots])} {CASH}}}"
        elif roll < 0.45 and any(lbl for _, _, lbl in lots):
            chosen = rng.choice([lbl for _, _, lbl in lots if lbl])
            spec = f'{{"{chosen}"}}'
        else:
            spec = "{}"
        proceeds = qty * Decimal("13.00")
        lines += [
            f'2020-02-{day:02d} * "sell"',
            f"  Assets:Stock  {-qty} {commodity} {spec}",
            f"  Assets:Cash   {proceeds} {CASH}",
            "  Income:Gains",
        ]
        held -= qty
        day += 1

    return (
        "\n".join(lines) + "\n",
        method,
        tie,
        pooling_shape(days, costs, labels),
    )


# A booked result is either an error or lot identity -> units.
# Key: account, currency, per-unit cost, cost currency, cost date, label.
Booked = dict[tuple[str, str, str, str, str, str], Decimal]
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
        "cost_currency AS cc, cost_date AS cd, cost_label AS cl"
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
                row.get("cl") or "",
            )
        else:
            key = (row["account"], units.get("currency", ""), "", "", "", "")
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
                            p.cost.currency, str(p.cost.date or ""),
                            p.cost.label or ""])
        else:
            key = "|".join([p.account, p.units.currency, "", "", "", ""])
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


def same_totals(rl: Booked | str, bq: Booked | str) -> bool:
    """True when both engines hold the same units per LOT-BEARING holding.

    Pooling moves units BETWEEN lot identities of one account; it cannot
    create or destroy them. So matching totals is a necessary condition for
    #2118 to be the explanation, and a mismatch means something else is
    wrong no matter how the lots are shaped.

    Cost-less positions are excluded, and that is not a loophole: consuming a
    different lot changes the COST BASIS, so the cash and income legs
    legitimately differ under this divergence -- that difference is the whole
    reason #2118 matters. Including them rejected all five known cases.
    Restricting to lots keeps the guard on the only quantity pooling must
    leave alone, the units held per commodity.
    """
    if isinstance(rl, str) or isinstance(bq, str):
        return False

    def totals(b: Booked) -> dict[tuple[str, str], Decimal]:
        out: dict[tuple[str, str], Decimal] = {}
        for (account, currency, cost, *_), units in b.items():
            if not cost:
                continue
            out[(account, currency)] = out.get((account, currency), Decimal(0)) + units
        return out

    return totals(rl) == totals(bq)


def check_one(rledger: str, python: str, seed: int) -> tuple[str, list[str]]:
    """Run one generated ledger through both engines.

    Returns a verdict -- "agree", "expected", or "real" -- and the report.

    "expected" is #2118 and nothing else: a KNOWN divergence we have decided
    not to fix, because rustledger's answer respects acquisition order and
    beancount's cannot. It is still compared, never skipped; only its verdict
    changes. An unexplained divergence stays "real" and still fails the run,
    which is the whole point of separating them -- five permanent reds is how
    a genuine regression goes unnoticed.
    """
    rng = random.Random(seed)
    source, method, tie, pooled = gen_ledger(rng)
    with tempfile.NamedTemporaryFile(
        "w", suffix=".beancount", delete=False
    ) as fh:
        fh.write(source)
        path = fh.name
    try:
        rl = booked_rledger(rledger, path)
        bq = booked_beancount(python, path)
        diffs = compare(rl, bq)
    finally:
        Path(path).unlink(missing_ok=True)
    if not diffs:
        return "agree", []
    # The shape is computed from the GENERATOR and not from the divergence,
    # so a ledger can take the pooling shape and still diverge for an
    # unrelated reason. `same_totals` guards that: pooling moves units BETWEEN
    # lot identities of a holding and can neither create nor destroy them, so
    # a divergence that moves the totals is something else.
    #
    # An acceptance divergence is waived too, which reverses what this said
    # first. The original reasoning was that pooling "can never" make one
    # engine reject a ledger the other accepts. That is false: pooling changes
    # which lots SURVIVE a reduction, so a later reduction naming an explicit
    # cost can find its lot drained on one engine and present on the other.
    # Seeds 117 and 394 show it in both directions, and 211 lands inside the
    # window CI runs on a PR.
    #
    # Since #2118 provably causes them, refusing to waive them means this gate
    # can NEVER be green -- and a permanently red gate is the exact thing this
    # classifier exists to prevent. They are waived, not hidden: tallied on
    # their own line, printed in full like any other divergence, and named as
    # the more serious face of #2118, a ledger that fails to LOAD rather than
    # one that reports different figures.
    rejected = ERROR in (rl, bq)
    if pooled and rejected:
        verdict, kind = "expected", "acceptance"
    elif pooled and same_totals(rl, bq):
        verdict, kind = "expected", "units"
    else:
        verdict, kind = "real", ""
    tag = f" [expected: #2118 lot pooling, {kind}]" if kind else ""
    return f"expected:{kind}" if verdict == "expected" else "real", [
        f"seed={seed} method={method} tie={tie}{tag}",
        *diffs,
        source,
    ]


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
    if check_one(rledger, python, seed=1)[0] != "agree":
        print("FAIL self-test: engines disagreed on seed=1")
        ok = False

    # The #2118 classifier decides which divergences stop being guarded, so
    # it needs its own evidence that it can still say "no". Shapes it must
    # match, and near-misses it must NOT.
    d = [Decimal(x) for x in ("10", "11")]
    shapes = [
        ("non-contiguous repeat, one date", [2, 2, 2], [d[0], d[1], d[0]],
         [None] * 3, True),
        ("contiguous repeat pools in place", [2, 2, 2], [d[0], d[0], d[1]],
         [None] * 3, False),
        ("repeat across DIFFERENT dates cannot pool", [2, 3, 4],
         [d[0], d[1], d[0]], [None] * 3, False),
        ("no repeat at all", [2, 2], [d[0], d[1]], [None] * 2, False),
        ("labels make the repeat a different identity", [2, 2, 2],
         [d[0], d[1], d[0]], ["a", None, "b"], False),
    ]
    for name, days, costs, labels, want in shapes:
        got = pooling_shape(days, costs, labels)
        if got != want:
            print(f"FAIL self-test 'pooling_shape: {name}': {got}, want {want}")
            ok = False

    # The totals guard is the other half of the waiver, so it needs its own
    # evidence that it can refuse.
    k_a = ("Assets:Stock", "HOOL", "10", "USD", "2020-01-02", "")
    k_b = ("Assets:Stock", "HOOL", "11", "USD", "2020-01-02", "")
    k_cash = ("Income:Gains", "USD", "", "", "", "")
    totals_cases = [
        ("units moved between lots, same total", {k_a: Decimal(3), k_b: Decimal(7)},
         {k_a: Decimal(7), k_b: Decimal(3)}, True),
        ("a unit went missing", {k_a: Decimal(3), k_b: Decimal(7)},
         {k_a: Decimal(3), k_b: Decimal(6)}, False),
        ("one side rejected", ERROR, {k_a: Decimal(3)}, False),
        # The income leg legitimately differs under #2118, so it must not
        # decide the verdict -- while the lots themselves still must match.
        ("cost-less leg differs, lots agree",
         {k_a: Decimal(3), k_cash: Decimal("-21.50")},
         {k_a: Decimal(3), k_cash: Decimal("-39.00")}, True),
        ("cost-less leg agrees, lots do not",
         {k_a: Decimal(3), k_cash: Decimal("-21.50")},
         {k_a: Decimal(4), k_cash: Decimal("-21.50")}, False),
    ]
    for name, rl, bq, want in totals_cases:
        got = same_totals(rl, bq)
        if got != want:
            print(f"FAIL self-test 'same_totals: {name}': {got}, want {want}")
            ok = False

    print("self-test passed" if ok else "self-test FAILED")
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--runs", type=int, default=100)
    ap.add_argument("--seed", type=int, help="run a single seed and report")
    # Seeds are `range(start, start + runs)`. CI fixes the start for PR and
    # push so a red X does not move when an unrelated commit lands, and uses
    # the run id nightly so the campaign explores ground the fixed window
    # never reaches. Same policy as the budget fuzzer.
    ap.add_argument(
        "--start-seed", type=int, default=0, help="first seed of the sweep"
    )
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--rledger", default="target/release/rledger")
    # Defaults to the running interpreter, matching the sibling compat
    # scripts, which CI invokes under an interpreter that already has
    # beancount. Point it at a dedicated venv when running from elsewhere.
    ap.add_argument("--python", default=sys.executable)
    args = ap.parse_args()

    if args.self_test:
        return self_test(args.rledger, args.python)

    seeds = (
        [args.seed]
        if args.seed is not None
        else list(range(args.start_seed, args.start_seed + args.runs))
    )
    total = len(seeds)
    real = expected_units = expected_acceptance = 0
    for seed in seeds:
        verdict, report = check_one(args.rledger, args.python, seed)
        if verdict == "agree":
            continue
        if verdict == "expected:acceptance":
            expected_acceptance += 1
        elif verdict.startswith("expected"):
            expected_units += 1
        else:
            real += 1
        print("\n".join(report))
        print("-" * 60)
    expected = expected_units + expected_acceptance
    agreed = total - real - expected
    print(f"{agreed}/{total} agreed")
    # Printed unconditionally, including the zero. A count that only appears
    # when non-zero reads as "nothing was waived" when the line is simply
    # absent, and waived cases are exactly the ones worth keeping in view.
    print(f"{expected} expected divergence(s) (#2118 lot pooling)")
    # Broken out because it is the more serious face of #2118: not a figure
    # that differs but a ledger one engine refuses to LOAD. Waived so the gate
    # can be green, never silent.
    print(f"  of which {expected_acceptance} are ACCEPTANCE differences")
    print(f"{real} unexplained divergence(s)")
    return 1 if real else 0


if __name__ == "__main__":
    sys.exit(main())
