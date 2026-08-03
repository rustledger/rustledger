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

import argparse, csv, io, re, subprocess, sys
from collections import defaultdict
from decimal import Decimal, InvalidOperation
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

    for f in failures:
        print(f"SELF-TEST FAILED: {f}")
    if failures:
        return 1
    print("self-test OK: error axis reports agreement, reports disagreement, "
          "and pins are direction-scoped")
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
    return 0


if __name__ == "__main__":
    sys.exit(main())
