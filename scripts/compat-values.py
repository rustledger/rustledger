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

SECOND AXIS: do the two tools AGREE ON WHETHER THE FILE IS WRONG?

The value comparison can only run on files both tools accept, so it used to
drop every other file into one undifferentiated `skipped` count. That hid the
most interesting disagreement there is. A file beancount books cleanly and
rledger REJECTS is a false rejection — #1914 was exactly that, an E3002 rule
applied to the whole transaction instead of per currency group — and it was
invisible here, indistinguishable from a file with unbooked postings.

So the skip bucket is now split, and the two directions of disagreement are
reported as FINDINGS rather than skips:

    rledger rejects, beancount accepts   -> likely false rejection (ours)
    beancount rejects, rledger accepts   -> likely missed detection (ours),
                                            or a deliberate deviation

Deliberately NOT compared: the error TAXONOMIES. beancount raises Python
exception classes (`ValidationError`, `BalanceError`) and rledger emits codes
(`E3001`); there is no honest one-to-one mapping between them, and inventing
one would produce confident nonsense. The assertion is only on the thing both
tools genuinely answer — does this file pass — and the kinds and codes are
printed alongside so a human can act on a disagreement without guessing.

This axis is why #1915 (`100.00 USD @` read as "no price") is reachable at
all. The units were `100.00 USD` before and after the fix, so the value
comparison above cannot see it in principle; what changed was that buggy
rledger raised E3001 on a file beancount accepts.
"""
from __future__ import annotations

import argparse, csv, io, json, re, subprocess, sys
from collections import defaultdict
from decimal import Decimal, InvalidOperation
from pathlib import Path

QUERY = ("SELECT account, currency, sum(number) AS n "
         "GROUP BY account, currency ORDER BY account, currency")


# Axis 3 reads these columns from rledger. The reference side comes from the
# beancount PYTHON API, deliberately NOT from bean-query: beanquery has bugs of
# its own (beanquery#279 is pinned in the BQL suite for exactly this reason),
# and an oracle that inherits the reference implementation's query-layer bugs is
# not an oracle. This asks beancount what it BOOKED.
POSTING_QUERY = (
    "SELECT date, account, number, currency, cost_number, cost_currency, "
    "cost_date, price ORDER BY date, account, number, currency"
)


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


# Deliberate deviations where the two tools are EXPECTED to disagree about
# whether a file errs. Keyed by (basename, direction) so a pin covers one file
# and one direction only — a blanket per-file mask would also hide the opposite
# disagreement appearing later, which is the failure mode the BQL registry's
# surgical-pin rule exists to prevent.
#
# direction is "rledger_only" (we reject, beancount accepts) or
# "beancount_only" (beancount rejects, we accept).
#
# EMPTY ON PURPOSE at introduction. Entries get added only with a written
# reason after a corpus run shows them, never pre-emptively to make the first
# run look clean — an unexplained disagreement is the finding this axis exists
# to produce.
KNOWN_ERROR_DIVERGENCES: dict[tuple[str, str], str] = {}


def beancount_errors(path: Path):
    """(errored, kinds) per Python beancount, or (None, set()) if it crashed.

    Uses ALL errors, not just the fatal ones. `NON_FATAL_ERRORS` answers a
    different question — "are the booked amounts still comparable" — and a
    `BalanceError` very much counts as beancount saying the file is wrong.
    """
    # An ImportError is NOT a per-file "undecidable". Swallowing it would mark
    # every file undecidable and let the step pass having compared nothing —
    # the silent-skip shape CLAUDE.md calls out ("availability-gated tests must
    # fail loudly somewhere"). Let it propagate and kill the run.
    from beancount import loader

    try:
        _, errors, _ = loader.load_file(str(path))
    except Exception:
        return None, set()
    return bool(errors), {type(e).__name__ for e in errors}


def rledger_errors(binary: str, path: Path):
    """(errored, codes) per `rledger check`, or (None, set()) if undecidable.

    `check` is the right probe rather than reusing the `query` run above:
    query exits 0 on a file that failed to parse (#1908), so it cannot answer
    "is this file acceptable" at all.
    """
    try:
        proc = subprocess.run(
            [binary, "check", str(path)],
            capture_output=True, text=True, timeout=120,
        )
    except (subprocess.TimeoutExpired, OSError):
        return None, set()
    # Any letter prefix, not just E: the parser emits P0012 and friends. The
    # first corpus run reported the one genuine finding as "(no code)" because
    # this said `E` — the diagnostic was useless exactly when it mattered.
    codes = set(re.findall(r"\b[A-Z]\d{4}\b", proc.stdout + proc.stderr))
    return proc.returncode != 0, codes


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
    """Do the two ledgers agree AS MONEY?

    Compared at the precision beancount used, not on raw Decimals. The two
    tools legitimately carry different precision for the same balance, because
    they quantize at different layers: beancount rounds when it books, rledger
    books what the arithmetic implies and rounds when it displays. Neither is
    wrong — see #1909, closed after this comparison reported two false
    divergences by asking the wrong question.

    Concretely, `0.035 SPY @ 137.142857143 USD` against an explicit `4.80`
    leaves 5e-12. beancount books `0.00`, losing it; rledger books
    `0.000000000005`, keeping the postings summing to exactly zero and
    rendering `0.03` on every surface that knows the currency. A raw Decimal
    comparison calls that a value bug. It is a representation difference.

    So each side is quantized to beancount's own exponent before comparing:
    beancount has already rounded to the currency's precision at booking, so
    its exponent IS the precision at which these figures are money.

    The cost, stated plainly: a genuine divergence smaller than one display
    unit is invisible here. That is the deliberate trade — it is also, by
    definition, a difference no user could observe in a balance.
    """
    diffs = []
    for key in sorted(set(a) | set(b), key=lambda k: (k[0], k[1])):
        x, y = a.get(key), b.get(key)
        if x is None or y is None:
            # A zero-sum bucket may legitimately be absent on one side.
            other = y if x is None else x
            if other != 0:
                diffs.append((key, x, y))
            continue
        try:
            y_at_bc_precision = y.quantize(x)
        except (InvalidOperation, ValueError):
            # Cannot express rledger's value at beancount's precision at all
            # (wildly different magnitude) — that is a real disagreement.
            diffs.append((key, x, y))
            continue
        if x != y_at_bc_precision:
            diffs.append((key, x, y))
    return diffs


# Deliberate or accepted per-posting divergences, keyed by (basename, FIELD).
#
# Keyed by field, not by file, for the same reason the BQL registry pins per
# (file, query): a whole-file mask would also swallow a DIFFERENT field
# diverging on that file later, which is precisely the regression a registry is
# supposed to keep visible.
#
# Every entry carries why. An entry without a reason is indistinguishable from
# one added to make a run look clean.
KNOWN_POSTING_DIVERGENCES: dict[tuple[str, str], str] = {
    # rust_decimal's ~28-29 significant-digit ceiling. The price here needs 30
    # to round-trip, so we store a value truncated at the coefficient limit.
    # CLAUDE.md records this as NOT fixable locally: the recovery side channel
    # was prototyped and rejected (PR #1613). No real ledger carries a literal
    # this precise.
    ("chapter-4_src_transactions.beancount", "price_number"):
        "rust_decimal 28-29 digit ceiling; documented limitation (#1240, PR #1613)",
    ("chapter-5_src_transactions.beancount", "price_number"):
        "rust_decimal 28-29 digit ceiling; documented limitation (#1240, PR #1613)",

    # `100.00 USD @` with `120.00 CAD`: both postings positive, so the price
    # would have to be -1.20 CAD. beancount computes the MAGNITUDE (+1.2);
    # #1919 decided to refuse a negative inferred price and say so, because a
    # negative price is not meaningful and silently flipping the sign hides a
    # sign error in the user's own ledger. Deliberate, and the error message
    # names the fix.
    ("test-cases_IncompleteInputs.PriceMissing.beancount", "price_number"):
        "negative inferred price refused by design (#1919)",
    ("test-cases_IncompleteInputs.PriceMissing.beancount", "price_currency"):
        "negative inferred price refused by design (#1919)",
    ("test-cases_IncompleteInputs.PriceMissingNumber.beancount", "price_number"):
        "negative inferred price refused by design (#1919)",
    ("test-cases_IncompleteInputs.PriceMissingNumber.beancount", "price_currency"):
        "negative inferred price refused by design (#1919)",

    # Tracked regression fixture; the booked-value axis has reported it for as
    # long as it has existed and compat.yml documents it by name.
    ("issue-520.beancount", "number"): "tracked regression fixture (issue-520)",
    ("issue-520.beancount", "currency"): "tracked regression fixture (issue-520)",
    ("issue-520.beancount", "price_number"): "tracked regression fixture (issue-520)",
    ("issue-520.beancount", "price_currency"): "tracked regression fixture (issue-520)",
    # The `{# total}` / `{per # }` compound-cost divergence, DECIDED in #1943:
    # we keep our behavior. beancount treats a `#` spec as incomplete and
    # solves it from the residual, discarding the written number when the two
    # disagree — `{# 9.95}` against -19.90 cash books 1.990, not 0.995. We
    # honor what the author wrote and report E3001 on the inconsistency,
    # because silently replacing a cost basis propagates into capital gains
    # and every cost-denominated report with nothing to indicate it.
    #
    # All three are parser-lima parser fixtures exercising edge syntax; no
    # real-world corpus file hits this. The reasoning also lives at the
    # canonical site (`cost_number_weight` in rustledger-booking).
    ("test-cases_Balance.TotalCost.beancount", "cost_number"):
        "compound `#` cost: we honor the written number, beancount solves from "
        "the residual (#1943, deliberate)",
    ("test-cases_ParseLots.CostTotalCostOnly.beancount", "cost_number"):
        "compound `#` cost: we honor the written number, beancount solves from "
        "the residual (#1943, deliberate)",
    ("test-cases_ParseLots.CostTotalEmptyTotal.beancount", "cost_number"):
        "compound `#` cost: we honor the written number, beancount solves from "
        "the residual (#1943, deliberate)",
    # NOT pinned on purpose:
    #   - `UnitsMissingNumberWithCost` cost_date, and `ZeroPrices` — unexamined
    #     beyond first triage, so pinning them would be asserting a conclusion
    #     nobody has reached.
}


def _dec(text):
    """Numeric field -> Decimal, or None if absent or unparsable.

    Used for both CSV cells and the JSON amount strings rledger emits, hence
    the deliberately format-neutral name.

    Unparsable maps to None rather than raising, which is a real trade: a
    malformed number reads as "field absent" instead of crashing the sweep.
    That is the right side for a corpus tool - one pathological file must not
    abort the other 700 - but it means a garbled field shows up as a
    present/absent divergence rather than a parse failure. The comparison still
    REPORTS it either way, which is what matters; only the label differs.
    """
    text = (text or "").strip()
    if not text:
        return None
    try:
        return Decimal(text)
    except InvalidOperation:
        return None


def beancount_postings(path: Path):
    """Per-posting rows from beancount, or None if not comparable.

    Row shape matches POSTING_QUERY:
      (date, account, number, currency,
       cost_number, cost_currency, cost_date, price_number, price_currency)
    """
    from beancount import loader
    from beancount.core import data

    try:
        entries, errors, _ = loader.load_file(str(path))
    except Exception:
        return None
    if errors and not {type(e).__name__ for e in errors} <= NON_FATAL_ERRORS:
        return None

    rows = []
    for e in entries:
        if not isinstance(e, data.Transaction):
            continue
        for p in e.postings:
            if p.units is None or p.units.number is None:
                return None  # unbooked; nothing meaningful to compare
            c, pr = p.cost, p.price
            rows.append((
                str(e.date), p.account, p.units.number, p.units.currency,
                getattr(c, "number", None), getattr(c, "currency", None),
                str(c.date) if getattr(c, "date", None) else None,
                pr.number if pr else None, pr.currency if pr else None,
            ))
    return sorted(rows, key=_row_sort_key)


def rledger_postings(binary: str, path: Path):
    """The same rows from rledger, or None if not comparable.

    JSON, NOT CSV, and that is the whole ballgame. CSV renders every number
    through `DisplayContext`, so a price written `56.0763 USD` in a ledger whose
    USD is mostly 2-decimal comes back as `56.08`. The first corpus run of this
    axis reported 32 files diverging on `price_number` for exactly that reason —
    every one of them the harness comparing beancount's STORED value against
    rledger's RENDERED one, and none of them a defect. `--format json` carries
    the stored value (verified: same file, same posting, `56.0763`).

    The lesson generalizes: a differential oracle must not read the other side
    through a presentation layer.
    """
    try:
        proc = subprocess.run(
            [binary, "query", "--format", "json", str(path), POSTING_QUERY],
            capture_output=True, text=True, timeout=120,
        )
    except (subprocess.TimeoutExpired, OSError):
        return None
    if proc.returncode != 0 or "parse errors" in proc.stderr:
        return None
    try:
        payload = json.loads(proc.stdout)
    except (json.JSONDecodeError, ValueError):
        return None

    def amount(v):
        """(number, currency) from a JSON amount, or (None, None)."""
        if not isinstance(v, dict):
            return None, None
        return _dec(v.get("number")), v.get("currency") or None

    rows = []
    for r in payload.get("rows", []):
        price_n, price_c = amount(r.get("price"))
        rows.append((
            r.get("date") or "",
            r.get("account") or "",
            _dec(r.get("number")),
            r.get("currency") or "",
            _dec(r.get("cost_number")),
            r.get("cost_currency") or None,
            r.get("cost_date") or None,
            price_n, price_c,
        ))
    return sorted(rows, key=_row_sort_key)


def _decimal_sort_token(v: Decimal) -> str:
    """A canonical, LOSSLESS, context-free token for ordering Decimals.

    Two properties are required, and neither is "sorts numerically":

    1. numerically equal values must produce the SAME token, or the two sides
       order differently and every row after the divergence is compared against
       the wrong partner;
    2. numerically different values must produce DIFFERENT tokens, or distinct
       rows collide and the pairing is arbitrary.

    The first version satisfied neither reliably. It used `f"{+v:+040.10f}"`,
    which rounds to 10 fractional digits — and the values this comparison most
    cares about are precisely the ones that do not survive that: the
    `rust_decimal` ceiling cases carry ~30 FRACTIONAL digits, so distinct
    prices flattened to the same key. Unary `+` also applies the active
    `decimal` context, so the token depended on ambient state the caller never
    set deliberately.

    `as_tuple()` is context-free. Trailing zeros are stripped by hand (rather
    than via `normalize()`, which consults the context too) so `0.10` and `0.1`
    agree, and an all-zero coefficient drops its sign so `-0.00` and `0.00`
    agree — the tools do not reliably agree on the sign of zero.
    """
    sign, digits, exponent = v.as_tuple()
    if not isinstance(exponent, int):  # NaN / Infinity carry a string exponent
        return f"S{exponent}"
    digits = list(digits)
    while len(digits) > 1 and digits[-1] == 0:
        digits.pop()
        exponent += 1
    if digits == [0]:
        sign, exponent = 0, 0
    # Ordering need only be TOTAL and identical on both sides; it does not have
    # to be numeric, and pretending otherwise is what invited the rounding.
    return f"{sign}|{exponent:+08d}|{''.join(str(d) for d in digits)}"


def _row_sort_key(row):
    """Total order over rows, tolerating None in any numeric slot.

    Sorting has to be identical on both sides or the comparison reports
    permutation as divergence. `None` cannot be compared to `Decimal`, so every
    slot is mapped to a (is_none, value) pair with a string fallback.
    """
    out = []
    for v in row:
        if v is None:
            out.append((1, ""))
        elif isinstance(v, Decimal):
            out.append((0, _decimal_sort_token(v)))
        else:
            out.append((0, str(v)))
    return out


def _num_agrees(bc, rl):
    """Same money? Quantized to beancount's exponent, per the #1909 lesson.

    The two tools legitimately carry different precision for the same figure
    because they quantize at different layers — beancount rounds when it books,
    rledger books what the arithmetic implies and rounds when it displays.
    Comparing raw Decimals reported two false divergences once already, which is
    why `compare()` above does the same thing for units.
    """
    if bc is None or rl is None:
        return bc is None and rl is None
    try:
        return bc == rl.quantize(bc)
    except (InvalidOperation, ValueError):
        return False


def compare_postings(bc_rows, rl_rows):
    """Field-level differences between two per-posting row sets.

    Dates, accounts, currencies and LOT DATES compare exactly — a lot date is
    either the right lot or it is not, and softening that would defeat the
    reason this axis exists. Only the three money fields get the precision
    tolerance.
    """
    diffs = []
    if len(bc_rows) != len(rl_rows):
        diffs.append(("<row count>", "<row count>", len(bc_rows), len(rl_rows)))
        return diffs

    fields = ("date", "account", "number", "currency", "cost_number",
              "cost_currency", "cost_date", "price_number", "price_currency")
    numeric = {"number", "cost_number", "price_number"}
    for bc, rl in zip(bc_rows, rl_rows):
        for name, x, y in zip(fields, bc, rl):
            ok = _num_agrees(x, y) if name in numeric else (x or None) == (y or None)
            if not ok:
                diffs.append((f"{bc[1]} {bc[0]} {name}", name, x, y))
    return diffs


def classify_error_agreement(binary: str, path: Path):
    """Which bucket does this file fall in, and what to print for it.

    Returns (bucket, detail) where bucket is one of "agree", "undecidable",
    "pinned", "rledger_only", "beancount_only".
    """
    bc_err, bc_kinds = beancount_errors(path)
    rl_err, rl_codes = rledger_errors(binary, path)
    if bc_err is None or rl_err is None:
        return "undecidable", ()
    # A beancount LoadError means beancount could not assemble the ledger at
    # all — nearly always a third-party plugin this environment cannot import
    # (beancount_reds_plugins, tariochbctools). Its entry stream is then
    # incomplete, so "beancount rejects and we do not" says nothing about
    # rledger. 19 of the first corpus run's 20 disagreements were exactly this.
    # Counting them as findings would bury the one that was real.
    if bc_err and "LoadError" in bc_kinds:
        return "undecidable", ()
    if bc_err == rl_err:
        return "agree", ()
    direction = "rledger_only" if rl_err else "beancount_only"
    reason = KNOWN_ERROR_DIVERGENCES.get((path.name, direction))
    if reason is not None:
        return "pinned", (direction, reason)
    return direction, sorted(rl_codes if rl_err else bc_kinds)


def self_test(binary: str) -> int:
    """Prove the axis can report DIRTY, not merely survive a clean corpus.

    A sweep that only ever prints zeros is indistinguishable from one that is
    silently broken — this file already shipped one such bug today, where an
    ImportError would have marked every file "undecidable" and passed. So the
    check is run against fixtures with KNOWN answers, including one genuine
    disagreement, and it asserts the pin suppresses that disagreement and
    nothing else.
    """
    import tempfile

    cases = {
        # both accept
        "st_clean.beancount": (
            "2018-01-01 open Assets:A\n"
            "2018-01-01 open Expenses:B\n"
            '2018-07-07 * "fine"\n'
            "  Assets:A   -10.00 USD\n"
            "  Expenses:B  10.00 USD\n"
        ),
        # both reject
        "st_both_bad.beancount": (
            "2018-01-01 open Assets:A\n"
            "2018-01-01 open Assets:B\n"
            '2018-07-07 * "unbalanced"\n'
            "  Assets:A   100.00 USD\n"
            "  Assets:B   -50.00 EUR\n"
        ),
        # rledger rejects, beancount accepts — the Python #877-equivalent that
        # CLAUDE.md records as a deliberate deviation (two-phase validation).
        "st_rledger_only.beancount": (
            "2018-01-01 open Assets:A\n"
            '2018-07-07 * "elided zero into an unopened account"\n'
            "  Assets:A            0.00 USD\n"
            "  Expenses:NeverOpened\n"
        ),
    }
    failures = []

    def check(cond, msg):
        if not cond:
            failures.append(msg)

    with tempfile.TemporaryDirectory() as td:
        paths = {}
        for name, body in cases.items():
            p = Path(td) / name
            p.write_text(body)
            paths[name] = p

        got = {n: classify_error_agreement(binary, p)[0] for n, p in paths.items()}
        check(got["st_clean.beancount"] == "agree",
              f"clean file must agree, got {got['st_clean.beancount']}")
        check(got["st_both_bad.beancount"] == "agree",
              f"both-reject must agree, got {got['st_both_bad.beancount']}")
        # THE important one: the axis must be able to say "dirty".
        check(got["st_rledger_only.beancount"] == "rledger_only",
              "a file rledger rejects and beancount accepts must be reported, "
              f"got {got['st_rledger_only.beancount']}")

        # And the pin must suppress exactly that one, in that one direction.
        KNOWN_ERROR_DIVERGENCES[("st_rledger_only.beancount", "rledger_only")] = "self-test"
        try:
            check(classify_error_agreement(binary, paths["st_rledger_only.beancount"])[0]
                  == "pinned", "a pinned divergence must land in the pinned bucket")
            KNOWN_ERROR_DIVERGENCES.pop(("st_rledger_only.beancount", "rledger_only"))
            KNOWN_ERROR_DIVERGENCES[("st_rledger_only.beancount", "beancount_only")] = "wrong way"
            check(classify_error_agreement(binary, paths["st_rledger_only.beancount"])[0]
                  == "rledger_only",
                  "a pin in the OPPOSITE direction must NOT suppress the finding")
        finally:
            KNOWN_ERROR_DIVERGENCES.pop(("st_rledger_only.beancount", "rledger_only"), None)
            KNOWN_ERROR_DIVERGENCES.pop(("st_rledger_only.beancount", "beancount_only"), None)

    # --- axis 3: the comparator itself -----------------------------------
    # Exercised directly on synthetic rows rather than through a fixture,
    # because the interesting cases are ones no ledger we have produces on
    # demand: a wrong lot date, a wrong cost, and — the one that matters most —
    # a difference that is REPRESENTATION and must NOT be reported.
    def row(number="10", cost="12.00", cost_date="2018-02-01",
            price_n=None, price_c=None):
        return ("2018-02-01", "Assets:B", Decimal(number), "CORP",
                Decimal(cost) if cost is not None else None,
                "USD" if cost is not None else None,
                cost_date, price_n, price_c)

    check(compare_postings([row()], [row()]) == [],
          "identical rows must produce no diff")
    check(compare_postings([row()], [row(cost="13.00")]) != [],
          "a wrong COST must be reported")
    check(compare_postings([row()], [row(cost_date="2018-03-01")]) != [],
          "a wrong LOT DATE must be reported")
    check(compare_postings([row()], [row(price_n=Decimal("15.00"), price_c="USD")]) != [],
          "a price appearing on only one side must be reported")
    check(compare_postings([row()], [row(), row()]) != [],
          "a row-count mismatch must be reported")
    # Representation, not money: beancount books 12.00, rledger carries more
    # places. #1909 was closed after this exact shape was reported as a bug.
    check(compare_postings([row(cost="12.00")],
                           [row(cost="12.000000000005")]) == [],
          "a sub-display-unit difference must NOT be reported")
    # ...but the tolerance must not become a license to differ.
    check(compare_postings([row(cost="12.00")], [row(cost="12.01")]) != [],
          "a difference AT beancount's own precision must still be reported")

    # --- the posting registry ---------------------------------------------
    # Same property the error-axis pin test asserts: a pin must suppress the
    # thing it names and NOTHING else. Keyed by field rather than by file, so
    # the check that matters is that a pin on a different field leaves the
    # finding visible.
    pdiffs = compare_postings([row()], [row(cost="13.00")])
    fields = {d[1] for d in pdiffs}
    check(fields == {"cost_number"},
          f"a wrong cost must be reported as the cost_number field, got {fields}")

    KNOWN_POSTING_DIVERGENCES[("self_test.beancount", "cost_number")] = "self-test"
    KNOWN_POSTING_DIVERGENCES[("self_test.beancount", "price_number")] = "wrong field"
    try:
        suppressed = [
            d for d in pdiffs
            if ("self_test.beancount", d[1]) not in KNOWN_POSTING_DIVERGENCES
        ]
        check(suppressed == [], "a pin on the reported field must suppress it")

        other = compare_postings([row()], [row(cost_date="2018-03-01")])
        still = [
            d for d in other
            if ("self_test.beancount", d[1]) not in KNOWN_POSTING_DIVERGENCES
        ]
        check(still != [],
              "a pin on cost_number/price_number must NOT suppress a cost_date finding")
    finally:
        KNOWN_POSTING_DIVERGENCES.pop(("self_test.beancount", "cost_number"), None)
        KNOWN_POSTING_DIVERGENCES.pop(("self_test.beancount", "price_number"), None)

    # --- the decimal sort token -------------------------------------------
    # Equal values must share a token or the two sides misalign; different
    # values must not, or distinct rows collide. The last two cases are the
    # ones the original `:.10f` token got wrong.
    for a, b, want_same in [
        ("0.10", "0.1", True),
        ("1", "1.0", True),
        ("-0.00", "0.00", True),
        ("12.00", "12.000", True),
        ("0.009693877551020408163265306122", "0.0096938775510204081632653061", False),
        ("1.00000000001", "1.00000000002", False),
    ]:
        same = _decimal_sort_token(Decimal(a)) == _decimal_sort_token(Decimal(b))
        check(same == want_same,
              f"sort token for {a} vs {b}: same={same}, expected {want_same}")

    for f in failures:
        print(f"SELF-TEST FAILED: {f}")
    if failures:
        return 1
    print("self-test OK: error axis reports agreement, reports disagreement, "
          "and pins are direction-scoped; posting axis reports wrong cost, "
          "lot date, price and row count, tolerates representation-only "
          "differences without tolerating real ones, and its pins are "
          "field-scoped")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rledger", default="./target/release/rledger")
    ap.add_argument("--corpus", nargs="+")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--self-test", action="store_true",
                    help="verify the error axis on fixtures with known answers")
    args = ap.parse_args()

    if args.self_test:
        return self_test(args.rledger)

    if not args.corpus:
        ap.error("--corpus is required unless --self-test is given")
    files = sorted(p for d in args.corpus for p in Path(d).rglob("*.beancount"))
    if args.limit:
        files = files[: args.limit]

    compared = skipped = 0
    divergent = []
    err_agree = err_undecidable = 0
    posting_compared = posting_skipped = posting_pinned = 0
    posting_divergent = []
    rledger_only, beancount_only, pinned = [], [], []

    for path in files:
        # --- axis 2: do the tools agree the file is acceptable? ------------
        # Runs for EVERY file, including ones the value comparison cannot use.
        # That is the point: the files it cannot use are where a false
        # rejection hides.
        bucket, detail = classify_error_agreement(args.rledger, path)
        if bucket == "undecidable":
            err_undecidable += 1
        elif bucket == "agree":
            err_agree += 1
        elif bucket == "pinned":
            pinned.append((path, detail))
        elif bucket == "rledger_only":
            rledger_only.append((path, detail))
        else:
            beancount_only.append((path, detail))

        # --- axis 1: booked values (unchanged) -----------------------------
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

        # --- axis 3: per-posting cost, price and lot date ------------------
        # The sums above cancel compensating per-posting errors, and never look
        # at cost or price at all. #1915 is the case in point: `100.00 USD @`
        # was read as "no price", and the UNITS were identical before and after
        # the fix, so no sum could ever have shown it.
        bcp = beancount_postings(path)
        if bcp is None:
            posting_skipped += 1
        else:
            rlp = rledger_postings(args.rledger, path)
            if rlp is None:
                posting_skipped += 1
            else:
                posting_compared += 1
                pdiffs = compare_postings(bcp, rlp)
                kept, pinned_here = [], 0
                for where, field, x, y in pdiffs:
                    if (path.name, field) in KNOWN_POSTING_DIVERGENCES:
                        pinned_here += 1
                    else:
                        kept.append((where, x, y))
                posting_pinned += pinned_here
                if kept:
                    posting_divergent.append((path, kept))

    # Errors first: a file rledger wrongly rejects is a louder problem than a
    # value that differs in the last place, and the CI step only lifts the
    # first 40 lines of this output into the job summary.
    print("=== ERROR AGREEMENT (does each tool accept the file?) ===")
    print(f"files checked:        {len(files)}")
    print(f"agree:                {err_agree}")
    print(f"undecidable:          {err_undecidable}  (beancount LoadError — usually a "
          f"third-party plugin this environment cannot import — or a tool crash/timeout)")
    print(f"known deviations:     {len(pinned)}  (pinned, see KNOWN_ERROR_DIVERGENCES)")
    print(f"rledger rejects, beancount accepts: {len(rledger_only)}  <-- likely OURS")
    print(f"beancount rejects, rledger accepts: {len(beancount_only)}")
    for path, codes in rledger_only[:15]:
        print(f"    rledger-only: {path}  {' '.join(codes) or '(no code)'}")
    for path, kinds in beancount_only[:15]:
        print(f"    beancount-only: {path}  {' '.join(kinds) or '(no kind)'}")
    print()

    print("=== BOOKED VALUES ===")
    print(f"compared {compared} files, skipped {skipped} "
          f"(errors in either tool, or unbooked postings)")
    print(f"files with a VALUE divergence: {len(divergent)}\n")
    for path, diffs in divergent[:25]:
        print(f"  {path}")
        for (acct, cur), x, y in diffs[:6]:
            print(f"      {acct} {cur}:  beancount={x}  rledger={y}")
    print()

    print("=== PER-POSTING (cost, price, lot date) ===")
    print(f"compared {posting_compared} files, skipped {posting_skipped}")
    print(f"known deviations:     {posting_pinned} field(s) pinned "
          f"(see KNOWN_POSTING_DIVERGENCES)")
    print(f"files with a POSTING divergence: {len(posting_divergent)}\n")
    for path, diffs in posting_divergent[:25]:
        print(f"  {path}")
        for where, x, y in diffs[:6]:
            print(f"      {where}:  beancount={x}  rledger={y}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
