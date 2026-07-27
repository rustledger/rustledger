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
import os
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
# One deliberately long commodity: beancount permits 24 characters, and the
# text report sizes the currency column to content. Without a long one in the
# corpus that column is never stressed and a fixed width would pass unnoticed —
# which is exactly how the `Used` column's constant survived several full runs.
CURRENCIES = ["USD", "EUR", "GBP", "VACATION-FUND-LONG-NAME"]

# Component-distinct names on purpose. This report selects subaccounts by
# component (`Expenses:Food` does not cover `Expenses:FoodCourt`, a deliberate
# deviation from Fava's `startswith`), and mixing prefix-colliding names into the
# corpus would test that deviation rather than the arithmetic.
ACCOUNTS = [
    # One deep account, for the same reason as the long commodity above: the
    # account column is content-sized and needs something wide to size against.
    "Expenses:Home:Improvements:Kitchen:Appliances:Refrigeration",
    "Expenses:Food",
    "Expenses:Food:Restaurant",
    "Expenses:Food:Grocery",
    "Expenses:Transport",
    "Expenses:Transport:Bus",
    "Expenses:Rent",
    # Credit-normal, so the sign normalization and the separate earning total
    # are exercised rather than assumed.
    "Income:Salary",
    "Income:Salary:Bonus",
]


def is_credit_normal(account: str) -> bool:
    """Mirrors `AccountTypes::is_credit_normal` for the default type names."""
    return account.split(":")[0] in ("Income", "Liabilities", "Equity")


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
    lines = ['option "operating_currency" "USD"']
    # Pin every currency to a high display precision. Without this the report
    # rounds to the precision inferred from the postings, which can be 0 dp, and
    # the comparison tolerance (half a unit in the last printed place) would then
    # be +/-0.5 -- loose enough to hide a real arithmetic error. At 10 dp the
    # tolerance is ~5e-11 and the oracles are compared almost exactly.
    for ccy in CURRENCIES:
        lines.append(f'option "display_precision" "{ccy}:0.0000000001"')
    lines.append("")
    accts = rng.sample(ACCOUNTS, rng.randint(1, len(ACCOUNTS)))
    for a in accts:
        lines.append(f"2019-01-01 open {a}")
    lines.append("2019-01-01 open Assets:Cash")
    lines.append("")

    # Occasionally close an account, so the closed-account diagnostics are
    # exercised rather than assumed. Every defect in the warning surface so far
    # has been a guard that excluded a neighboring case, and the generator
    # reached none of them.
    closed = {}
    for a in accts:
        if rng.random() < 0.15:
            when = datetime.date(2020, 1, 1) + datetime.timedelta(days=rng.randint(0, 1400))
            closed[a] = when
    for a, when in sorted(closed.items()):
        lines.append(f"{when} close {a}")
    if closed:
        lines.append("")

    typos = []
    for _ in range(rng.randint(1, 5)):
        a = rng.choice(accts)
        # Slice the WHOLE list: capping at 3 meant the long commodity added
        # for column-width coverage sat at index 3 and was never chosen, so
        # the coverage it was added for did not exist.
        ccy = rng.choice(CURRENCIES[: rng.randint(1, len(CURRENCIES))])
        d = datetime.date(2020, 1, 1) + datetime.timedelta(days=rng.randint(0, 1400))
        # A tiny budget against ordinary spending yields a percentage wide
        # enough to collide with the column beside it (`500000.0%`), which is
        # how the Used column's fixed width survived several runs unnoticed.
        amt = (
            # Tiny enough that ordinary spending against it yields a percentage
            # of nine or more characters (>= 100000.0%). At 0.01 the widest seen
            # was eight, which is why the Used column's fixed width survived
            # several full runs unnoticed.
            Decimal(rng.randint(1, 50)) / Decimal(100000)
            if rng.random() < 0.15
            else Decimal(rng.randint(1, 500000)) / Decimal(100)
        )
        # A typo'd account or currency must be REPORTED, not silently rendered
        # as a tidy 0% row. Both are generated so the warning oracle below has
        # something to be right or wrong about.
        roll = rng.random()
        if roll < 0.08:
            bad = a + "Zz"
            typos.append(("unopened", bad))
            lines.append(f'{d} custom "budget" {bad} "{rng.choice(INTERVALS)}" {amt} {ccy}')
        elif roll < 0.16:
            typos.append(("currency", a))
            lines.append(f'{d} custom "budget" {a} "{rng.choice(INTERVALS)}" {amt} ZZQ')
        else:
            lines.append(f'{d} custom "budget" {a} "{rng.choice(INTERVALS)}" {amt} {ccy}')

    # Another tool's `custom "budget"`. Neither shape declares a budget, so
    # neither may produce a row — the oracle skips both and `unexpected_row`
    # fails if rledger reads either as one. Generated unconditionally so every
    # ledger carries the case: it is cheap, and the defect it guards against
    # (claiming the namespace) shipped once already.
    d = datetime.date(2020, 1, 1) + datetime.timedelta(days=rng.randint(0, 1400))
    # Beancount's own example: the first value is not an account at all.
    lines.append(f'{d} custom "budget" "weekly < 1000.00 USD" 2016-02-28 TRUE 43.03 USD 23')
    # Names an account, but not in Fava's order.
    other = rng.choice(accts)
    lines.append(f'{d} custom "budget" {other} 1000.00 USD TRUE "monthly"')
    lines.append("")

    for _ in range(rng.randint(0, 12)):
        a = rng.choice(accts)
        ccy = rng.choice(CURRENCIES[:2])
        d = datetime.date(2020, 1, 1) + datetime.timedelta(days=rng.randint(0, 1400))
        amt = Decimal(rng.randint(1, 50000)) / Decimal(100)
        sign = -1 if is_credit_normal(a) else 1
        lines.append(f'{d} * "txn"')
        shape = rng.random()
        if shape < 0.12 and not is_credit_normal(a):
            # `@@` total price in the SAME currency: the weight differs from the
            # units in number only, and the weight is what was spent.
            total = (amt + Decimal(rng.randint(1, 500)) / Decimal(100)).quantize(
                Decimal("0.01")
            )
            lines.append(f"  {a}  {amt} {ccy} @@ {total} {ccy}")
            lines.append(f"  Assets:Cash  -{total} {ccy}")
        elif shape < 0.24 and not is_credit_normal(a):
            # Cost spec denominated in another currency.
            rate = Decimal(rng.randint(80, 140)) / Decimal(100)
            other = "EUR" if ccy == "USD" else "USD"
            cost = (amt * rate).quantize(Decimal("0.01"))
            lines.append(f"  {a}  {amt} {ccy} {{{rate} {other}}}")
            lines.append(f"  Assets:Cash  -{cost} {other}")
        elif rng.random() < 0.25 and not is_credit_normal(a):
            # Priced posting: the weight is in another currency, so the report
            # must count it against a budget in EITHER currency.
            rate = Decimal(rng.randint(80, 140)) / Decimal(100)
            other = "EUR" if ccy == "USD" else "USD"
            lines.append(f"  {a}  {amt} {ccy} @ {rate} {other}")
            lines.append(f"  Assets:Cash  -{(amt * rate).quantize(Decimal('0.00001'))} {other}")
        else:
            lines.append(f"  {a}  {sign * amt} {ccy}")
            lines.append(f"  Assets:Cash  {-sign * amt} {ccy}")
    lines.append("")

    start = datetime.date(2020, 1, 1) + datetime.timedelta(days=rng.randint(0, 1200))
    end = start + datetime.timedelta(days=rng.randint(1, 900))
    return "\n".join(lines) + "\n", start, end, closed, typos, accts


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
        # `custom` is beancount's OPEN extension point and the name "budget" is
        # not rledger's alone: beancount's own documented example is
        # `custom "budget" "weekly < 1000.00 USD" 2016-02-28 TRUE 43.03 USD 23`.
        # A payload that is not POSITIONALLY Fava's is another tool's, declares
        # no budget, and must produce no row. Skipping it here is what makes the
        # `unexpected_row` check below a guard against rledger claiming the
        # namespace — which it briefly did, warning on valid beancount.
        if not isinstance(acct, str) or ":" not in acct:
            continue
        if not isinstance(interval, str):
            continue
        if not (hasattr(amount, "number") and hasattr(amount, "currency")):
            continue
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
            # The canonical weight ladder, mirrored from
            # `rustledger_booking::posting_weight`: a cost spec with a number and
            # a currency wins, else a price annotation, else the units. A weight
            # in a SECOND currency means the posting moved money in both, so it
            # counts against a budget in either; a weight in the SAME currency
            # (`90 USD @@ 95 USD`, or a cost denominated in the units currency)
            # supersedes the units, because only one currency moved and the
            # weight is what it cost.
            moved = {p.units.currency: p.units.number}
            weight = None
            if p.cost is not None and getattr(p.cost, "number", None) is not None:
                weight = (p.cost.currency, p.units.number * p.cost.number)
            elif p.price is not None:
                weight = (p.price.currency, p.units.number * p.price.number)
            if weight is not None:
                wccy, wnum = weight
                # ONE assignment covers both rules the comment above states,
                # because `moved` is keyed by currency: a weight in the SAME
                # currency overwrites the units (it supersedes them), and one in
                # a second currency adds a key (both moved). Spelling it as an
                # if/else with identical branches only made it look like the two
                # cases were unimplemented.
                moved[wccy] = wnum
            for row_acct, ccy in rows:
                if ccy not in moved or not covers(row_acct, p.account, children):
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
                    signed = -moved[ccy] if is_credit_normal(p.account) else moved[ccy]
                    out[(row_acct, ccy)] += signed
    return dict(out)


def expected_total_actual(path: str, decls, d_from, d_to, children: bool):
    """Each posting counted ONCE, against whichever budget covers it.

    The totals are deliberately not the sum of the rendered rows: under
    `--children` a parent row and a child row overlap. Coverage therefore uses
    the run's actual `children` flag (a posting on a child IS covered by its
    parent's budget), while each posting still contributes at most once per
    currency it moved.
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
            moved = {p.units.currency: p.units.number}
            if p.cost is not None and getattr(p.cost, "number", None) is not None:
                moved[p.cost.currency] = p.units.number * p.cost.number
            elif p.price is not None:
                moved[p.price.currency] = p.units.number * p.price.number
            for ccy, number in moved.items():
                covering = [
                    s
                    for (a, c), s in starts.items()
                    if c == ccy and covers(a, p.account, children)
                ]
                if not covering:
                    continue
                if e.date >= max(min(covering), d_from):
                    signed = -number if is_credit_normal(p.account) else number
                    out[(ccy, p.account.split(":")[0])] += signed
    return dict(out)


def tolerance(rendered: str) -> Decimal:
    """Half a unit in the last place the report actually printed.

    The report rounds to the currency's inferred display precision, which can be
    coarse, so a fixed tolerance would flag rendering as if it were arithmetic.
    """
    dp = len(rendered.split(".")[1]) if "." in rendered else 0
    return Decimal(5) * Decimal(10) ** Decimal(-dp - 1) + Decimal("1e-12")


def run_format(rledger, path, d_from, d_to, children, fmt):
    args = [
        rledger, "report", path, "budget",
        "--from", str(d_from), "--to", str(d_to),
        "--format", fmt, "--no-pager",
    ]
    if children:
        args.append("--children")
    try:
        return subprocess.run(args, capture_output=True, text=True, timeout=120)
    except subprocess.TimeoutExpired:
        # A hang used to abort the whole run with a traceback naming no seed, so
        # CI reported a crash instead of the input that caused it. Synthesize a
        # failing result and let the caller record it like any other divergence.
        return subprocess.CompletedProcess(
            args, returncode=124, stdout="", stderr="TIMEOUT after 120s"
        )


def check_rendered_formats(rledger, path, d_from, d_to, children, got, failures, seed):
    """Text and CSV must say the same thing as JSON, and stay readable.

    The JSON oracle above cannot see either: every defect this catches shipped
    at some point — an account column truncated so two rows rendered
    identically, numeric columns so narrow that Actual fused with Remaining,
    and a percentage computed from unrounded figures beside rounded amounts.
    """
    json_rows = {
        (b["account"], b["currency"]): b
        for b in list(got["budgets"]) + list(got["totals"])
    }

    csv_proc = run_format(rledger, path, d_from, d_to, children, "csv")
    if csv_proc.returncode != 0:
        failures["csv_nonzero_exit"].append((seed, csv_proc.stderr.strip()[:120]))
        return
    csv_lines = [l for l in csv_proc.stdout.splitlines() if l.strip()]
    for line in csv_lines:
        if line.count(",") != 5:
            failures["csv_field_count"].append((seed, line[:100]))
    for line in csv_lines[1:]:
        parts = line.split(",")
        if len(parts) != 6:
            # Already recorded above as csv_field_count. Unpacking anyway turned
            # a reportable failure into a traceback that aborted the whole run,
            # which is exactly the wrong direction for a harness.
            continue
        acct, ccy, budgeted, actual, remaining, used = parts
        row = json_rows.get((acct, ccy))
        if row is None:
            failures["csv_row_not_in_json"].append((seed, (acct, ccy), children))
            continue
        for field, csv_val in (
            ("budgeted", budgeted), ("actual", actual), ("remaining", remaining)
        ):
            want = row[field] if field != "remaining" else row.get("remaining")
            want_s = "" if want is None else str(want)
            if csv_val != want_s:
                failures["csv_json_disagree"].append(
                    (seed, (acct, ccy), f"{field}: csv={csv_val!r} json={want_s!r}")
                )
        # A zero budget has no meaningful percentage; a finite one beside a
        # zero amount is a contradiction a consumer cannot reconcile.
        if budgeted and Decimal(budgeted) == 0 and used != "":
            failures["used_pct_on_zero_budget"].append((seed, (acct, ccy), used))

    txt_proc = run_format(rledger, path, d_from, d_to, children, "text")
    if txt_proc.returncode != 0:
        failures["text_nonzero_exit"].append((seed, txt_proc.stderr.strip()[:120]))
        return
    # Identify data rows by the accounts and totals the JSON already told us to
    # expect, rather than by an account-root prefix. Matching on `Expenses:`/
    # `Income:` made the check silently vacuous for any other root (Assets,
    # Liabilities, a renamed account type) — it would pass by skipping every row.
    # `json_rows` already carries every total label the run produced (it is built
    # from `budgets` + `totals`), so the bare "TOTAL" below is belt-and-braces.
    # A literal "TOTAL (earned)" used to sit here as well; no such label has ever
    # been emitted — totals are bucketed by account TYPE, so they read
    # "TOTAL (Income)" — and a stale label in a longest-match set is the kind of
    # thing that reads like a live rule when it is only leftovers.
    want_labels = {a for a, _ in json_rows} | {"TOTAL"}
    seen_rows = 0
    for line in txt_proc.stdout.splitlines():
        stripped = line.strip()
        # LONGEST match: "TOTAL" is a prefix of "TOTAL (Income)", and a set has
        # no order, so picking any match split the label in the wrong place and
        # counted a stray sixth column.
        label = max(
            (l for l in want_labels if stripped.startswith(l)),
            key=len,
            default=None,
        )
        if label is None:
            continue
        seen_rows += 1
        # The label may contain a space ("TOTAL (Income)"); the remainder must
        # be exactly the five other columns.
        rest = stripped[len(label):].split()
        if len(rest) != 5:
            failures["text_columns_fused"].append((seed, stripped[:110]))
    if json_rows and seen_rows == 0:
        failures["text_no_rows_matched"].append((seed, "text check matched nothing"))

    # Field counting catches FUSION but is blind to TRUNCATION: a fixed-width
    # column pads rather than cuts in Rust's formatter, so a too-narrow account
    # or currency column still yields six fields while rendering two distinct
    # rows identically. Assert every label appears in full instead, which is the
    # property that actually matters — the reader must be able to tell the rows
    # apart and attribute the figures.
    for acct, ccy in json_rows:
        if acct not in txt_proc.stdout:
            failures["text_label_truncated"].append((seed, acct, "account"))
        if ccy not in txt_proc.stdout:
            failures["text_label_truncated"].append((seed, ccy, "currency"))

    # And neither check sees RAGGEDNESS: a column that is too narrow but pads
    # rather than truncates leaves every row individually well-formed while
    # pushing one row's numbers further right than another's, so the table no
    # longer lines up. Every data row must start its currency at the same
    # offset, which is only true when the account column is sized to content.
    # Every column is content-sized and the last is right-aligned, so every data
    # row is exactly the same length. Any column that pads to a constant instead
    # breaks that the moment one row's value exceeds it — which is the failure a
    # per-row field count and a label check both miss, because each row is
    # individually well-formed and merely starts its numbers in a different
    # place from its neighbor.
    row_widths = set()
    for line in txt_proc.stdout.splitlines():
        stripped = line.rstrip()
        label = max(
            (l for l in want_labels if stripped.strip().startswith(l)),
            key=len,
            default=None,
        )
        if label is not None:
            row_widths.add(len(stripped))
    if len(row_widths) > 1:
        failures["text_columns_ragged"].append((seed, sorted(row_widths)[:6]))


def check_one(
    rledger, path, src, d_from, d_to, children, failures, seed,
    closed=None, typos=None, opened=None,
):
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

    # A row the oracle never predicted is as much a defect as a missing one:
    # without this, spurious rows could never fail the fuzz.
    predicted = expected_budgeted(decls, d_from, d_to, children)
    for key, row in rows.items():
        if key in predicted:
            continue
        # A zero-valued row is legitimate: the key is declared but accrues
        # nothing in this window, and the oracle drops zeros.
        if row["budgeted"] not in (None, "0") and Decimal(row["budgeted"]) != 0:
            failures["unexpected_row"].append(
                (seed, key, f"budgeted={row['budgeted']}", children)
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

    # DIAGNOSTICS. Every defect in this surface so far has been a guard that
    # excluded a neighboring case, and none of them were reachable by the
    # generator. The rule checked here is the one the code documents: a budget
    # that cannot ever see spending must say so, and stderr must carry the same
    # set as the JSON `errors` array.
    stderr_text = proc.stderr
    json_msgs = [e["message"] for e in got.get("errors", [])]
    for msg in json_msgs:
        if msg not in stderr_text:
            failures["error_json_not_on_stderr"].append((seed, msg[:80]))
    for bad in {b for kind, b in (typos or []) if kind == "unopened"}:
        # Only when the row is actually reported (the window may exclude it).
        if any(a == bad for a, _ in rows) and bad not in stderr_text:
            failures["typo_account_unreported"].append((seed, bad, children))
    for acct in {a for kind, a in (typos or []) if kind == "currency"}:
        # Only when the account actually posts something in ANOTHER currency.
        # A budget on an account with no postings yet is legitimate (the budget
        # precedes the spending), and the report deliberately stays quiet there;
        # asserting otherwise made this oracle wrong, not the code.
        posts_other = any(
            a == acct and c != "ZZQ" and Decimal(r["actual"] or 0) != 0
            for (a, c), r in rows.items()
        )
        if posts_other and any(a == acct and c == "ZZQ" for a, c in rows):
            if "ZZQ" not in stderr_text:
                failures["typo_currency_unreported"].append((seed, acct, children))
    # A row can no longer see spending only when EVERY opened account it covers
    # is closed; one closed sibling among open ones leaves it perfectly
    # spendable. Asserting on "any closed account is covered" made this oracle
    # demand a warning the report is right not to give.
    for acct, _ in rows:
        covering = [o for o in (opened or []) if covers(acct, o, children)]
        if not covering:
            continue
        closes = [(closed or {}).get(o) for o in covering]
        if any(c is None for c in closes):
            continue
        last = max(closes)
        if last < d_to and "closed on" not in stderr_text:
            failures["closed_account_unreported"].append((seed, acct, str(last)))

    # Text and CSV, which the JSON oracle above cannot see.
    check_rendered_formats(rledger, path, d_from, d_to, children, got, failures, seed)

    # Totals, in BOTH modes and on BOTH sides. Under --children a parent row and
    # a child row overlap, so the TOTAL is deliberately not the sum of the rows;
    # it counts each budget entry and each posting once. That is computed here
    # from the same per-entry oracles rather than from the rendered rows.
    want_tot: dict[tuple[str, str], list[Decimal]] = defaultdict(
        lambda: [Decimal(0), Decimal(0)]
    )
    for (acct, ccy), val in expected_budgeted(decls, d_from, d_to, False).items():
        want_tot[(ccy, acct.split(":")[0])][0] += val
    for (ccy, kind), val in expected_total_actual(
        path, decls, d_from, d_to, children
    ).items():
        want_tot[(ccy, kind)][1] += val

    for tot in got["totals"]:
        # Totals are bucketed by ACCOUNT TYPE: `TOTAL` is Expenses, everything
        # else is `TOTAL (<Type>)`. Bucketing by credit-normality lumped a
        # credit-card budget in with an income target and called the sum earned.
        label = tot["account"]
        kind = "Expenses" if label == "TOTAL" else label[len("TOTAL ("):-1]
        key = (tot["currency"], kind)
        for idx, field in ((0, "budgeted"), (1, "actual")):
            if tot[field] is None:
                continue
            want = want_tot.get(key, [Decimal(0), Decimal(0)])[idx]
            slack = tolerance(tot[field]) * Decimal(len(got["budgets"]) + 2)
            if abs(Decimal(tot[field]) - want) > slack:
                failures[f"total_{field}_mismatch"].append(
                    (seed, key, f"got={tot[field]} want={str(want)[:24]}", children)
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
    # The comparison must stay tight enough to be worth running. Generated
    # ledgers pin every currency to 10 dp precisely so this holds; if that pin
    # is ever dropped the tolerance silently widens to +/-0.5 for an integer
    # render and the whole harness goes quiet. Verified by mutation: injecting
    # 1e-6 into the oracle's per-day accrual makes a 10-ledger run fail.
    if tolerance("1.0000000000") > Decimal("1e-9"):
        print(f"FAIL tolerance too loose at 10 dp: {tolerance('1.0000000000')}")
        ok = False
    if tolerance("1") <= Decimal("0.05"):
        print("FAIL tolerance model wrong: a 0 dp render should be treated as coarse")
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

    # Per-RUN directory. A fixed path let two runs on one machine — two CI jobs,
    # or a local run beside one — clobber each other's ledger between the write
    # and the read, which surfaces as a divergence that does not reproduce.
    tmp = Path(f"/tmp/compat-budget-fuzz/{args.seed}-{args.count}-{os.getpid()}")
    tmp.mkdir(parents=True, exist_ok=True)
    path = str(tmp / "ledger.beancount")
    failures = defaultdict(list)

    for i in range(args.count):
        seed = args.seed + i
        rng = random.Random(seed)
        src, d_from, d_to, closed, typos, opened = gen_ledger(rng)
        check_one(
            args.rledger, path, src, d_from, d_to, rng.random() < 0.5, failures, seed,
            closed, typos, opened,
        )

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
