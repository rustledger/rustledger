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

Repeated lot identities within a date used to be the one KNOWN divergence:
beancount pools acquisitions sharing (cost, date, label) into a single
inventory position, while rustledger kept a slot per acquisition, so the two
consumed in different orders once an identity repeated non-contiguously
within a date (#2118). rustledger now merges interchangeable lots the same
way, so that bucket is empty, and it is a TRIPWIRE rather than a tolerance:
a divergence on a ledger with that shape is reported as a likely #2118
regression, tallied on its own line, and fails the run like any other
unexplained divergence.

Every seed also books a second, independent ledger whose interesting
postings write a units number WITHOUT its currency (`Assets:Cash  -100`,
`Assets:Stock  -5 {}`). Which currency that is follows beancount's
`categorize_by_currency`, ported in #2490: the other postings' one currency
group, else the one currency the account holds, else refused. The generator
aims a shape at each branch (`NUMBER_ONLY_SHAPES`) over accounts holding one
currency, several, none, or one since sold off, and the report tallies
agreement per shape and per holding, including how many ledgers both engines
booked and how many both refused (#2513). It is drawn from its own RNG, so
every seed's lot-selection ledger is unchanged. A reduction's price and cash
leg stay in its lots' cost currency: outside that, the engines diverge with
the commodity written too (see `gen_number_only_ledger`), which is a question
for the booking of costs, not for the currency of a bare number.

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
import re
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

# Prices on a reduction. Annotation-only for balancing -- a posting carrying
# a cost takes its weight from the COST, so a price that disagrees with the
# proceeds is still a balanced transaction, verified against both engines.
# That is what makes this safe to vary: a wrong price produces a divergence,
# not an unbalanced ledger the comparison would reject for the wrong reason.
PRICES = ["12.00", "13.00", "14.50"]


def pooling_shape(
    days: list[int], costs: list[Decimal], labels: list[str | None]
) -> bool:
    """True when the lots take the shape #2118 used to diverge on.

    beancount's `Inventory` is keyed by `(currency, cost)`, so acquisitions
    sharing `(cost, date, label)` collapse into ONE position, sitting where
    the FIRST of them sat. rustledger used to keep a slot per acquisition,
    which changed the consumption ORDER when a repeated identity was
    NON-CONTIGUOUS within its date: `[a, b, a]` pools `a`'s later units
    forward, ahead of `b`, while `[a, a, b]` pools into the order it already
    had. Since #2118 rustledger merges them too.

    This no longer excuses anything. It only labels a divergence as the shape
    #2118 fixed, so a reappearance names its likely cause. Requiring the
    non-contiguous repeat -- rather than merely "some identity repeats" --
    keeps the label to the shape #2118 actually describes.
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


def gen_ledger(rng: random.Random) -> tuple[str, str, str, bool, bool]:
    """A ledger exercising lot selection.

    Returns source, booking method, tie mode, whether the lots take the shape
    #2118 used to diverge on, and whether any reduction carried a price
    annotation.
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
    priced = False
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
        # A price on the reduction. Deliberately NOT always the rate the cash
        # leg implies: cost decides the weight, so a disagreeing price is
        # legal, and pinning it to the proceeds would only ever exercise the
        # case where the two agree.
        price = ""
        price_roll = rng.random()
        if price_roll < 0.25:
            price = f" @ {rng.choice(PRICES)} {CASH}"
            priced = True
        elif price_roll < 0.35:
            price = f" @@ {qty * Decimal(rng.choice(PRICES))} {CASH}"
            priced = True
        lines += [
            f'2020-02-{day:02d} * "sell"',
            f"  Assets:Stock  {-qty} {commodity} {spec}{price}",
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
        priced,
    )


# Number-only postings: a units number written WITHOUT its currency
# (`Assets:Cash  -100`, `Assets:Stock  -5 {}`). Its currency follows
# beancount's `booking_full.categorize_by_currency`, which rustledger ports in
# `rustledger_booking::interpolate::resolve_elided_units_currencies` (#2490):
#
#   1. a posting with no cost and no price, that is the transaction's ONLY
#      posting whose currency is undetermined, takes the currency of the other
#      postings when they all fall in ONE currency group (a posting's group is
#      its cost currency, else its price currency, else its units currency;
#      auto-postings are not counted);
#   2. otherwise it takes the one currency the account held before the
#      transaction (zero positions do not count);
#   3. otherwise the transaction is refused.
#
# Each shape below aims at one branch. Which account it lands on -- one
# currency held, several, never funded, or funded and emptied -- is drawn
# independently, so every shape meets both the accepting and the refusing
# side of step 2. Acceptance divergences count like numeric ones.
NUMBER_ONLY_SHAPES = [
    # Step 1: the other postings are one currency group. Wins over the
    # account's balance even when that names a different currency.
    "plain-one-group",
    # Step 1 does not apply (two other groups), so step 2 decides.
    "plain-several-groups",
    # Only an auto-posting beside it: no group at all, step 2 decides.
    "plain-no-group",
    # Two or three number-only postings in one transaction: a second unknown
    # disables step 1, so each reads its own account's balance.
    "several-number-only",
    # A reduction `-N {}` / `-N {C USD}`: the cost names its own currency,
    # never the commodity, so only the balance can say what N counts.
    "cost-reduce",
    # An augmentation `N {C USD}` into an account: again step 2 only.
    "cost-augment",
    # A priced posting `-N @ R CUR`: the price names its own currency.
    "price",
]

# Holdings an account can have when a number-only posting reaches it. "zeroed"
# held a currency once and sold it all, which must count as holding nothing.
HOLDINGS = ["one", "several", "empty", "zeroed"]
# Weighted toward "one", the only holding step 2 accepts: a refusal anywhere
# in a ledger makes both engines reject all of it, which hides whatever the
# ledger's other transactions would have booked.
HOLDING_WEIGHTS = [5, 2, 1, 1]

CASH_CURRENCIES = ["USD", "EUR", "GBP"]


def _num(rng: random.Random, low: int = 1, high: int = 400) -> Decimal:
    """A positive number at a random precision.

    Precision matters, not just value: beancount infers tolerances from the
    postings AS WRITTEN, where a number-only posting's precision lands under
    its still-missing currency (#2490 review), and an auto-posting beside it
    is quantized by the result.
    """
    places = rng.choice([0, 1, 2, 2, 2, 3])
    whole = rng.randint(low, high)
    frac = rng.randint(0, 10**places - 1) if places else 0
    return Decimal(f"{whole}.{frac:0{places}d}") if places else Decimal(whole)


_NUMBER_ONLY_POSTING = re.compile(r"^\s+[A-Z][\w:-]*\s+-?\d[\d.]*\s*(?:[{@]|$)")


def _is_number_only_posting(line: str) -> bool:
    """True for a posting line whose units number has no currency."""
    return bool(_NUMBER_ONLY_POSTING.match(line))


def gen_number_only_ledger(rng: random.Random) -> tuple[str, list[str]]:
    """A ledger whose interesting transactions write units without a currency.

    Returns the source and the shapes it exercises, each tagged with the
    holding of the account it reads (`plain-no-group/several`).
    """
    method = rng.choice(METHODS)
    lines = [f'option "booking_method" "{method}"']
    if rng.random() < 0.2:
        # Beancount reads a number-only posting's precision under
        # infer_tolerance_from_cost too (#2490, second review).
        lines.append('option "infer_tolerance_from_cost" "TRUE"')
    cash_accts = ["Assets:CashA", "Assets:CashB", "Assets:CashC"]
    stock_accts = ["Assets:StockA", "Assets:StockB"]
    other_accts = ["Expenses:Misc", "Expenses:Other", "Income:Gains",
                   "Equity:Opening", "Liabilities:Card"]
    for acct in [*cash_accts, *other_accts]:
        lines.append(f"2020-01-01 open {acct}")
    for acct in stock_accts:
        # Currencies are deliberately unconstrained: an `open` list is not a
        # source of the currency (beancount ignores it), and a constraint
        # would refuse a wrong guess for a reason other than booking.
        lines.append(f'2020-01-01 open {acct}  "{rng.choice(METHODS)}"')

    holding: dict[str, str] = {}
    # What each account holds once the setup is booked: units currency ->
    # list of (units, per-unit cost or None, cost currency or None).
    held: dict[str, dict[str, list[tuple[Decimal, Decimal | None, str | None]]]] = {}
    setup: list[str] = []

    def fund_cash(acct: str, currency: str, day: int) -> None:
        amt = Decimal(rng.randint(200, 2000)) + Decimal("0.00")
        setup.extend([
            f'2020-01-{day:02d} * "fund"',
            f"  {acct}  {amt} {currency}",
            "  Equity:Opening",
        ])
        held.setdefault(acct, {}).setdefault(currency, []).append((amt, None, None))

    def buy(acct: str, commodity: str, day: int, cost_cur: str) -> None:
        qty = Decimal(rng.randint(1, 20))
        cost = Decimal(rng.choice(["10.00", "11.00", "12.50", "9.75"]))
        setup.extend([
            f'2020-01-{day:02d} * "buy"',
            f"  {acct}  {qty} {commodity} {{{cost} {cost_cur}}}",
            f"  Equity:Opening  {-(qty * cost)} {cost_cur}",
        ])
        held.setdefault(acct, {}).setdefault(commodity, []).append((qty, cost, cost_cur))

    for acct in cash_accts:
        kind = rng.choices(HOLDINGS, weights=HOLDING_WEIGHTS)[0]
        holding[acct] = kind
        # Mostly USD first, so several number-only postings in one
        # transaction often resolve to ONE currency and can balance.
        first = rng.choices(CASH_CURRENCIES, weights=[3, 1, 1])[0]
        currencies = [first, rng.choice([c for c in CASH_CURRENCIES if c != first])]
        if kind == "one":
            fund_cash(acct, currencies[0], 2)
            if rng.random() < 0.5:
                # Several positions, still one currency.
                fund_cash(acct, currencies[0], 3)
        elif kind == "several":
            fund_cash(acct, currencies[0], 2)
            fund_cash(acct, currencies[1], 3)
        elif kind == "zeroed":
            fund_cash(acct, currencies[0], 2)
            amt = held[acct][currencies[0]][0][0]
            setup.extend([
                '2020-01-04 * "empty it"',
                f"  {acct}  {-amt} {currencies[0]}",
                "  Equity:Opening",
            ])
            held[acct] = {}
    for acct in stock_accts:
        kind = rng.choices(HOLDINGS, weights=HOLDING_WEIGHTS)[0]
        holding[acct] = kind
        commodities = rng.sample(COMMODITIES, 2)
        cost_cur = "USD" if rng.random() < 0.8 else "EUR"
        if kind == "one":
            for day in range(2, 2 + rng.randint(1, 3)):
                buy(acct, commodities[0], day, cost_cur)
        elif kind == "several":
            buy(acct, commodities[0], 2, cost_cur)
            buy(acct, commodities[1], 3, cost_cur)
        elif kind == "zeroed":
            buy(acct, commodities[0], 2, cost_cur)
            qty, cost, _ = held[acct][commodities[0]][0]
            setup.extend([
                '2020-01-04 * "sell it all"',
                f"  {acct}  {-qty} {commodities[0]} {{{cost} {cost_cur}}}",
                f"  Equity:Opening  {qty * cost} {cost_cur}",
            ])
            held[acct] = {}
    lines += setup

    def lots_of(acct: str) -> list[tuple[str, Decimal, Decimal | None, str | None]]:
        return [(cur, u, c, cc) for cur, ls in held.get(acct, {}).items()
                for u, c, cc in ls]

    shapes: list[str] = []
    n_txns = rng.choices([1, 2, 3], weights=[7, 2, 1])[0]
    for t in range(n_txns):
        shape = rng.choice(NUMBER_ONLY_SHAPES)
        postings: list[str] = []
        if shape == "plain-one-group":
            acct = rng.choice(cash_accts)
            # The group's currency need not be one the account holds: step 1
            # outranks step 2.
            cur = rng.choice(CASH_CURRENCIES)
            n = _num(rng)
            if rng.random() < 0.5:
                postings += [f"  {acct}  {-n}", f"  Expenses:Misc  {n} {cur}"]
            else:
                # An auto-posting is not a group, so this is still one group.
                part = _num(rng, 1, 100)
                postings += [f"  {acct}  {-n}", f"  Expenses:Misc  {part} {cur}",
                             "  Expenses:Other"]
        elif shape == "plain-several-groups":
            acct = rng.choice(cash_accts)
            c1, c2 = rng.sample(CASH_CURRENCIES, 2)
            n, b = _num(rng), _num(rng, 1, 100)
            postings += [f"  {acct}  {-n}", f"  Expenses:Misc  {n} {c1}",
                         f"  Expenses:Other  {b} {c2}"]
            if rng.random() < 0.6:
                postings.append("  Liabilities:Card")
            else:
                # No auto-posting: balances only if the number-only posting
                # resolves to c1, so a wrong currency is also a wrong verdict.
                postings.append(f"  Liabilities:Card  {-b} {c2}")
        elif shape == "plain-no-group":
            acct = rng.choice(cash_accts)
            postings += [f"  {acct}  {-_num(rng)}", "  Expenses:Misc"]
        elif shape == "several-number-only":
            singles = [a for a in cash_accts if holding[a] == "one"]
            if len(singles) >= 2 and rng.random() < 0.7:
                # Every one resolvable, so this side of the rule is reached
                # at all: drawn independently, two or three accounts all
                # holding one currency is a small fraction of ledgers.
                accts = rng.sample(singles, rng.randint(2, len(singles)))
            else:
                accts = rng.sample(cash_accts, rng.randint(2, 3))
            total = Decimal(0)
            for a in accts:
                n = _num(rng)
                total += n
                postings.append(f"  {a}  {-n}")
            acct = "+".join(accts)
            roll = rng.random()
            if roll < 0.5:
                postings.append("  Expenses:Misc")
            elif roll < 0.7:
                # Number-only too: Expenses:Misc holds whatever earlier
                # transactions of this ledger left there, often nothing.
                postings.append(f"  Expenses:Misc  {total}")
            else:
                postings.append(f"  Expenses:Misc  {total} {rng.choice(CASH_CURRENCIES)}")
        elif shape == "cost-reduce":
            acct = rng.choice(stock_accts)
            lots = lots_of(acct)
            qty = Decimal(rng.randint(1, max(1, int(lots[0][1]) if lots else 5)))
            # The price and the cash leg are in the lots' cost currency. Two
            # divergences that have nothing to do with a currency-less units
            # number live outside that, and reproduce with the commodity
            # written (#2513 campaign, reported for a decision of their own):
            # beancount refuses a reduction priced in another currency than
            # its cost ("Cost and price currencies must match"), and gives a
            # `{}` the other postings' currency as its cost currency, so
            # `{}` beside a USD cash leg finds no EUR lot. rledger books both.
            lot_cur = lots[0][3] if lots else "USD"
            roll = rng.random()
            if roll < 0.45 or not lots:
                spec = "{}"
            elif roll < 0.85:
                spec = f"{{{rng.choice(lots)[2]} {lot_cur}}}"
            else:
                # A cost with its currency elided too: beancount reads that
                # from the other postings' currency group.
                spec = f"{{{rng.choice(lots)[2]}}}"
            price = ""
            if rng.random() < 0.3:
                price = f" @ {rng.choice(PRICES)} {lot_cur}"
            proceeds = qty * Decimal("13.00")
            cash = f"  Assets:CashA  {proceeds} {lot_cur}"
            if rng.random() < 0.25:
                # The cash leg number-only as well.
                cash = f"  Assets:CashA  {proceeds}"
            postings += [f"  {acct}  {-qty} {spec}{price}", cash, "  Income:Gains"]
        elif shape == "cost-augment":
            acct = rng.choice(stock_accts)
            qty = Decimal(rng.randint(1, 10))
            cost = Decimal(rng.choice(["10.00", "14.00", "8.50"]))
            cost_cur = rng.choice(["USD", "USD", "EUR"])
            postings += [f"  {acct}  {qty} {{{cost} {cost_cur}}}",
                         f"  Assets:CashA  {-(qty * cost)} {cost_cur}"]
            if rng.random() < 0.3:
                # An auto-posting instead of the explicit cash leg.
                postings[-1] = "  Equity:Opening"
        else:  # price
            acct = rng.choice(cash_accts)
            n = _num(rng, 1, 200)
            rate = Decimal(rng.choice(["1.10", "0.90", "1.25"]))
            cur = rng.choice(CASH_CURRENCIES)
            roll = rng.random()
            if roll < 0.6:
                price, weight = f"@ {rate} {cur}", n * rate
            elif roll < 0.85:
                price, weight = f"@@ {n * rate} {cur}", n * rate
            else:
                # The price's currency elided as well.
                price, weight = f"@ {rate}", n * rate
            postings += [f"  {acct}  {-n} {price}"]
            if rng.random() < 0.5:
                postings.append(f"  Expenses:Misc  {weight} {cur}")
            else:
                postings.append("  Expenses:Misc")
        if rng.random() < 0.3:
            # Order changes nothing in beancount's rule; it must not here.
            rng.shuffle(postings)
        lines.append(f'2020-02-{t + 1:02d} * "{shape}"')
        lines += postings
        kinds = "+".join(holding.get(a, "?") for a in acct.split("+"))
        shapes.append(f"{shape}/{kinds}")
    return "\n".join(lines) + "\n", shapes


# A booked result is either an error or lot identity -> units.
# Key: account, currency, per-unit cost, cost currency, cost date, label.
Booked = dict[tuple[str, str, str, str, str, str], Decimal]
ERROR = "ERROR"


def _keyed_rows(payload):
    """`rows` as dicts, zipped against `columns`.

    `query --format json` emits rows POSITIONALLY -- arrays of values indexed
    by `columns` -- because a JSON object cannot hold the duplicate column
    names BQL can produce (#2178). These queries name every column distinctly,
    so re-keying is lossless here; do not copy this into a context where the
    column names may collide.
    """
    columns = payload.get("columns") or []
    return [dict(zip(columns, row)) for row in payload.get("rows", [])]


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
        rows = _keyed_rows(json.loads(out.stdout))
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


def classify(diffs: list[str], pooled: bool) -> str:
    """Verdict for one seed: "agree", "regression:2118", or "real".

    Both non-agreeing verdicts FAIL the run. "regression:2118" exists only to
    name the likely cause: until #2118 these were waived as a known
    divergence, and the shape is computed from the GENERATOR, not from the
    divergence, so it says where to look first, never that a case is fine.
    """
    if not diffs:
        return "agree"
    return "regression:2118" if pooled else "real"


def run_engines(rledger: str, python: str, source: str) -> tuple[Booked | str, Booked | str]:
    """Book `source` with both engines."""
    with tempfile.NamedTemporaryFile(
        "w", suffix=".beancount", delete=False
    ) as fh:
        fh.write(source)
        path = fh.name
    try:
        return booked_rledger(rledger, path), booked_beancount(python, path)
    finally:
        Path(path).unlink(missing_ok=True)


def check_one(rledger: str, python: str, seed: int) -> tuple[str, list[str]]:
    """Run one generated ledger through both engines.

    Returns a verdict (see `classify`) and the report.
    """
    rng = random.Random(seed)
    source, method, tie, pooled, priced = gen_ledger(rng)
    rl, bq = run_engines(rledger, python, source)
    diffs = compare(rl, bq)
    verdict = classify(diffs, pooled)
    if verdict == "agree":
        return verdict, []
    tag = (
        " [#2118 REGRESSION? repeated lot identity within a date]"
        if verdict == "regression:2118"
        else ""
    )
    return verdict, [
        f"seed={seed} method={method} tie={tie} "
        f"price={'yes' if priced else 'no'}{tag}",
        *diffs,
        source,
    ]


def number_only_rng(seed: int) -> random.Random:
    """The number-only ledger's generator for `seed`.

    Separate from `random.Random(seed)`, so adding this ledger left every
    seed's lot-selection ledger byte-for-byte what it was.
    """
    return random.Random(f"number-only-{seed}")


def check_number_only(
    rledger: str, python: str, seed: int
) -> tuple[str, list[str], list[str], str]:
    """Run the seed's number-only ledger through both engines.

    Returns a verdict ("agree" or "real"), the report, the shapes the ledger
    exercises, and how both engines took it when they agreed ("booked" or
    "rejected"; "" on a divergence).
    """
    source, shapes = gen_number_only_ledger(number_only_rng(seed))
    rl, bq = run_engines(rledger, python, source)
    diffs = compare(rl, bq)
    if not diffs:
        return "agree", [], shapes, "rejected" if rl == ERROR else "booked"
    return "real", [
        f"seed={seed} ledger=number-only shapes={','.join(shapes)}",
        *diffs,
        source,
    ], shapes, ""


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

    # The #2118 tripwire must FAIL a pooled-shape divergence, not waive it as
    # it did before #2118 was fixed -- and must not mislabel other cases.
    verdicts = [
        ("pooled shape diverges", ["x"], True, "regression:2118"),
        ("other shape diverges", ["x"], False, "real"),
        ("pooled shape agrees", [], True, "agree"),
    ]
    for name, diffs, pooled, want in verdicts:
        got = classify(diffs, pooled)
        if got != want:
            print(f"FAIL self-test 'classify: {name}': {got}, want {want}")
            ok = False

    # The shape label names a regression's likely cause, so it needs its own
    # evidence that it can still say "no". Shapes it must match, and
    # near-misses it must NOT.
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

    # The number-only generator must still produce what its tallies claim:
    # every shape and every holding within a few hundred seeds, and each
    # ledger an actual currency-less units number. A shape the generator
    # silently stopped producing would otherwise report 0/0 forever.
    seen_shapes: set[str] = set()
    seen_holdings: set[str] = set()
    for seed in range(300):
        source, shapes = gen_number_only_ledger(number_only_rng(seed))
        seen_shapes |= {tag.split("/")[0] for tag in shapes}
        seen_holdings |= {k for tag in shapes for k in tag.split("/")[1].split("+")}
        if not any(_is_number_only_posting(line) for line in source.splitlines()):
            print(f"FAIL self-test: number-only seed={seed} has no number-only posting")
            ok = False
            break
    for name, want, seen in (
        ("shape", NUMBER_ONLY_SHAPES, seen_shapes),
        ("holding", HOLDINGS, seen_holdings),
    ):
        missing = sorted(set(want) - seen)
        if missing:
            print(f"FAIL self-test: number-only {name}(s) never generated: {missing}")
            ok = False
    # And the posting detector itself can say no.
    for line, want in (
        ("  Assets:Cash  -100", True),
        ("  Assets:Stock  -5 {}", True),
        ("  Assets:Cash  -1.5 @ 1.10 USD", True),
        ("  Assets:Cash  -100 USD", False),
        ("  Assets:Stock  -5 HOOL {}", False),
        ("  Income:Gains", False),
    ):
        if _is_number_only_posting(line) != want:
            print(f"FAIL self-test '_is_number_only_posting({line!r})': want {want}")
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
    real = regressions = number_only_real = 0
    # Per number-only shape, and per holding of the account a number-only
    # posting reads: [ledgers, agreed, both booked, both rejected]. A ledger
    # counts once under each distinct shape and holding it contains.
    shape_tally = {shape: [0, 0, 0, 0] for shape in NUMBER_ONLY_SHAPES}
    holding_tally = {kind: [0, 0, 0, 0] for kind in HOLDINGS}
    for seed in seeds:
        verdict, report = check_one(args.rledger, args.python, seed)
        if verdict != "agree":
            if verdict == "regression:2118":
                regressions += 1
            else:
                real += 1
            print("\n".join(report))
            print("-" * 60)

        verdict, report, shapes, both = check_number_only(
            args.rledger, args.python, seed
        )
        bases = {tag.split("/")[0] for tag in shapes}
        kinds = {k for tag in shapes for k in tag.split("/")[1].split("+")}
        for tally, keys in ((shape_tally, bases), (holding_tally, kinds)):
            for key in keys:
                row = tally[key]
                row[0] += 1
                if verdict == "agree":
                    row[1] += 1
                    row[2 if both == "booked" else 3] += 1
        if verdict != "agree":
            number_only_real += 1
            print("\n".join(report))
            print("-" * 60)
    agreed = total - real - regressions
    print(f"{agreed}/{total} lot-selection ledgers agreed")
    # Printed unconditionally, including the zero: this line is the #2118
    # tripwire, and a count that only appears when non-zero reads the same
    # as a tripwire that was removed.
    print(f"{regressions} #2118-shaped divergence(s) (repeated lot identity within a date)")
    print(f"{real} other unexplained divergence(s)")
    # Every shape and holding is printed, zeros included, for the same
    # reason: a shape the generator stopped producing must show as 0/0, not
    # vanish. "both booked" / "both rejected" show each shape reached both
    # sides of the rule, not just one.
    print(f"{total - number_only_real}/{total} number-only ledgers agreed")
    for label, tally in (("shape", shape_tally), ("holding", holding_tally)):
        for key, (n, ok, booked, rejected) in tally.items():
            print(
                f"  number-only {label} {key}: {ok}/{n} agreed "
                f"(both booked {booked}, both rejected {rejected})"
            )
    print(f"{number_only_real} number-only divergence(s)")
    return 1 if real or regressions or number_only_real else 0


if __name__ == "__main__":
    sys.exit(main())
