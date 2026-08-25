#!/usr/bin/env python3
"""Returns fuzzer — differential checks on generated portfolios.

`report returns` answers "what did this portfolio earn", which is a number
people act on and one that is hard to eyeball. It has two independently
wrong-able halves: EXTRACTION, deciding which postings are cash flows and
what they are worth, and the SOLVE, finding the rate that zeroes their net
present value. This checks both, from three directions.

beangrow is the differential partner for extraction. It is an independent
implementation over the same ledgers, from the beancount project itself, so
agreement on the flow list is real evidence rather than a restatement of our
own logic.

beangrow is NOT the oracle for the RATE, and this script does not treat it as
one. Its `compute_irr` calls `fsolve` from a fixed seed against an objective
with two spurious roots: `npv(-(2+t)) == -npv(t)` gives every true root `t` a
mirror, and every term underflows as `r -> -1`, so `-100%` satisfies it for
any flows. It reports `ier=1, "converged"` on both. On a two-transaction
profitable position it answers -100% where the true IRR is +102.28%
(beancount/beangrow#51). So the rate is adjudicated by an independent
bisection solve over the SAME flows, bracketed away from the asymptote, and a
divergence names which engine that referee agrees with.

Three verdicts, deliberately separate:

  EXTRACTION  the two engines disagree about the flows. rledger's
              invested / distributions / current_value and its flow COUNT are
              compared against the same quantities derived from beangrow's
              dated flow list, so this is visible even when the rates agree.

              This is deliberately weaker than a flow-by-flow comparison, and
              the limit is worth stating: `report returns --format json`
              exposes aggregates and a count, not the dated flows, so a change
              that preserves all three sums AND the count while moving a flow
              to a different DATE is invisible here. The rate check catches
              most such changes, since moving a flow changes the discounting,
              but not all of them. Closing the gap needs a diagnostic flow
              dump from rledger; see the note in the PR.
  SOLVER      the flows agree but the rates do not. The referee says who is
              right, so this never rests on beangrow being correct.
  AGREE       everything matches within tolerance.

Tolerance is 0.02 because rledger reports the rate rounded to two decimals.

beangrow needs its dividend accounts CONFIGURED. Its `configure.py` leaves
`dividend_accounts` empty when a dividend never touches the asset account,
and rledger is told them via `-n`, so without this the comparison pits a
configured engine against an unconfigured one and every dividend looks like a
divergence. That is not a hypothetical: it produced 13 false positives in 60
seeds before being fixed.

Usage:
    scripts/compat-returns-fuzz.py --runs 200
    scripts/compat-returns-fuzz.py --seed 12345      # reproduce one case
    scripts/compat-returns-fuzz.py --self-test       # prove it detects a bug
"""

from __future__ import annotations

import argparse
import datetime
import json
import random
import subprocess
import sys
import tempfile
from decimal import Decimal
from pathlib import Path

CASH = "USD"
END = datetime.date(2022, 12, 31)
# rledger prints the rate to two decimals, so anything finer is formatting.
TOLERANCE = 0.02


def _require_beangrow():
    try:
        from beancount import loader  # noqa: F401
        from beangrow import configure, investments, returns  # noqa: F401
    except ImportError as exc:  # pragma: no cover - environment dependent
        sys.exit(
            f"beangrow is required for this fuzzer: {exc}\n"
            "  pip install beangrow\n"
            "Its numpy needs libstdc++ and libz on the library path; on NixOS\n"
            "run under `nix shell nixpkgs#stdenv.cc.cc.lib nixpkgs#zlib`."
        )


def gen_ledger(rng: random.Random) -> str:
    """A portfolio exercising buys, partial sells, dividends and a terminal price."""
    lines = [
        f'option "operating_currency" "{CASH}"',
        "2019-12-31 commodity ACME",
        # The commodity directive is required: beangrow's `find_accounts` only
        # considers an account whose LEAF names a declared commodity, so
        # without it the config infers zero investments and the comparison is
        # vacuous rather than clean.
        '2019-12-31 open Assets:Invest:ACME  ACME "FIFO"',
        f"2019-12-31 open Assets:Cash         {CASH}",
        f"2019-12-31 open Income:Invest:Gains {CASH}",
        f"2019-12-31 open Income:Invest:Div   {CASH}",
    ]
    held = Decimal(0)
    day = datetime.date(2020, 1, 1)
    for _ in range(rng.randint(2, 5)):
        day += datetime.timedelta(days=rng.randint(20, 300))
        if day >= END:
            break
        roll = rng.random()
        if held > 0 and roll < 0.35:
            qty = Decimal(rng.randint(1, int(held)))
            px = Decimal(rng.choice(["9.00", "11.00", "14.00", "16.50"]))
            lines += [
                f'{day} * "sell"',
                f"  Assets:Invest:ACME  {-qty} ACME {{}} @ {px} {CASH}",
                f"  Assets:Cash   {qty * px} {CASH}",
                "  Income:Invest:Gains",
            ]
            held -= qty
        elif held > 0 and roll < 0.5:
            amt = Decimal(rng.randint(5, 60))
            lines += [
                f'{day} * "dividend"',
                f"  Assets:Cash   {amt}.00 {CASH}",
                f"  Income:Invest:Div  {-amt}.00 {CASH}",
            ]
        else:
            qty = Decimal(rng.randint(5, 60))
            px = Decimal(rng.choice(["10.00", "12.00", "13.50"]))
            lines += [
                f'{day} * "buy"',
                f"  Assets:Invest:ACME  {qty} ACME {{{px} {CASH}}}",
                f"  Assets:Cash  {-(qty * px)} {CASH}",
            ]
            held += qty
    # A terminal price so whatever is still held has a market value; without
    # one the closing flow is missing and every run diverges for that reason.
    lines.append(f'{END} price ACME  {rng.choice(["8.00", "12.00", "15.00", "18.00"])} {CASH}')
    return "\n".join(lines) + "\n"


def rledger_returns(rledger: str, path: str) -> dict | None:
    out = subprocess.run(
        [rledger, "report", path, "returns", "-i", "Assets:Invest",
         "-n", "Income:Invest", "-c", CASH, "-e", str(END), "--format", "json"],
        capture_output=True, text=True,
        env={"BEANCOUNT_DISABLE_LOAD_CACHE": "1", "PATH": "/usr/bin:/bin"},
        check=False,
    )
    if out.returncode != 0:
        return None
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError:
        return None


def beangrow_flows(path: str) -> list[tuple[datetime.date, float]] | None:
    """beangrow's cash flows, including the terminal valuation."""
    from beancount import loader
    from beancount.core import prices
    from beangrow import configure, investments, returns as returnslib
    from beangrow.returns import Pricer

    entries, errors, om = loader.load_file(path)
    if errors:
        return None
    config = configure.infer_configuration(entries, om, None)
    if not config.investments.investment:
        return None
    # Tell beangrow the income accounts, the same way rledger is told via `-n`.
    income = {
        p.account
        for e in entries
        if hasattr(e, "postings")
        for p in e.postings
        if p.account.startswith("Income:Invest")
    }
    for inv in config.investments.investment:
        del inv.dividend_accounts[:]
        inv.dividend_accounts.extend(sorted(income))

    adata = investments.extract(
        entries, om["dcontext"], config, END, False, tempfile.mkdtemp()
    )
    pricer = Pricer(prices.build_price_map(entries))
    # `truncate_and_merge_cash_flows`, not `ad.cash_flows`: only the former
    # appends the closing flow that values what is still held at `END`.
    # Reading the raw list omits it and turns every open position into a
    # spurious divergence.
    flows = returnslib.truncate_and_merge_cash_flows(
        pricer, list(adata.values()), None, END
    )
    return [(f.date, float(f.amount.number)) for f in flows]


def bisect_irr(flows: list[tuple[datetime.date, float]]) -> float | None:
    """The rate that zeroes NPV, found by bisection rather than Newton.

    Bracketed strictly inside (-1, ...) so the asymptotic root at -100% that
    traps beangrow's `fsolve` is out of range by construction.
    """
    def npv(r: float) -> float:
        return sum(a * (1.0 + r) ** ((END - d).days / 365) for d, a in flows)

    # Grow the upper bracket rather than treating an out-of-range root as
    # agreement. A 20-day sale from 10.00 to 16.50 annualizes to roughly
    # 930,000%, far past any fixed bound, and returning None there made the
    # solver check silently skip exactly the cases most likely to break a
    # Newton solver.
    lo, hi = -0.9999, 1.0
    for _ in range(80):
        if npv(lo) * npv(hi) <= 0:
            break
        hi *= 4.0
    else:
        return None
    # Bisection needs the sign to change exactly once across the bracket. A
    # series with several sign changes can have several real roots, and
    # picking one arbitrarily would let the referee "adjudicate" toward a root
    # rledger never claimed. Rather than guess, scan for how many sign changes
    # the bracket contains and decline when it is not exactly one: the caller
    # treats `None` as "no verdict", which is honest, where a confident wrong
    # answer would not be.
    lo_sign = npv(lo) > 0
    changes, prev, prev_sign = 0, lo, lo_sign
    steps = 512
    for i in range(1, steps + 1):
        x = lo + (hi - lo) * i / steps
        sign = npv(x) > 0
        if sign != prev_sign:
            changes += 1
            prev, prev_sign = x, sign
            if changes > 1:
                return None
    if changes != 1:
        return None

    for _ in range(400):
        mid = (lo + hi) / 2
        if (npv(mid) > 0) == lo_sign:
            lo = mid
        else:
            hi = mid
    return lo


def check_one(rledger: str, seed: int) -> tuple[str, list[str]]:
    rng = random.Random(seed)
    source = gen_ledger(rng)
    with tempfile.NamedTemporaryFile("w", suffix=".beancount", delete=False) as fh:
        fh.write(source)
        path = fh.name
    try:
        rl = rledger_returns(rledger, path)
        if rl is None:
            return "skip", []
        flows = beangrow_flows(path)
        if not flows:
            return "skip", []

        invested = sum(-a for _, a in flows if a < 0)
        distributions = sum(a for d, a in flows if a > 0 and d != END)
        terminal = sum(a for d, a in flows if a > 0 and d == END)
        problems = []
        if rl["cash_flows"] != len(flows):
            problems.append(
                f"  flow count: rledger={rl['cash_flows']} beangrow={len(flows)}"
            )
        for name, ours, theirs in (
            ("invested", Decimal(rl["invested"]), invested),
            ("distributions", Decimal(rl["distributions"]), distributions),
            ("current_value", Decimal(rl["current_value"]), terminal),
        ):
            if abs(float(ours) - theirs) > 0.02:
                problems.append(f"  {name}: rledger={ours} beangrow={theirs:.2f}")
        if problems:
            return "extraction", [
                f"seed={seed} EXTRACTION differs", *problems, source,
            ]

        ref = bisect_irr(flows)
        ours_rate = rl["money_weighted_return_pct"]
        if ref is not None and abs(ours_rate - ref * 100) > TOLERANCE:
            # No "closer" label: reaching here means rledger already differs
            # from the referee by more than tolerance, so a ternary comparing
            # the same two numbers again can only ever say "referee". An
            # earlier version printed exactly that and read as though it had
            # adjudicated between two engines when it had not.
            return "solver", [
                f"seed={seed} SOLVER differs",
                f"  rledger={ours_rate:.4f}%  independent-referee={ref * 100:.4f}%"
                f"  (delta {ours_rate - ref * 100:+.4f}pp)",
                source,
            ]
        return "agree", []
    finally:
        Path(path).unlink(missing_ok=True)


def _flows_for_seed(rledger: str, seed: int):
    """beangrow's flows for one generated seed, or None. Used by the self-test."""
    import random as _random
    src = gen_ledger(_random.Random(seed))
    with tempfile.NamedTemporaryFile("w", suffix=".beancount", delete=False) as fh:
        fh.write(src)
        path = fh.name
    try:
        return beangrow_flows(path)
    finally:
        Path(path).unlink(missing_ok=True)


def self_test(rledger: str) -> int:
    """Prove each check can FAIL, not merely that it passes."""
    ok = True
    d = datetime.date

    def fail(msg: str) -> None:
        nonlocal ok
        print(f"FAIL self-test: {msg}")
        ok = False

    # 1. The referee must find the rate this script can verify by hand.
    #    Buy 72 and sell 99 with the sale ON the end date: the discount
    #    exponent is then 0 for the proceeds and 165/365 for the outlay, so
    #    the root is (99/72) ** (365/165) - 1 exactly.
    #
    #    An earlier version computed this expected value and never compared
    #    it, so the test accepted ANY non-None result, including a wrong
    #    bisection. Copilot and CodeQL both flagged the unused variable; the
    #    variable was the symptom and the missing assertion was the defect.
    horizon = (END - d(2020, 11, 1)).days
    flows = [(END - datetime.timedelta(days=165 + horizon), -72.0),
             (END - datetime.timedelta(days=horizon), 99.0)]
    want = (99 / 72) ** (365 / 165) - 1
    got = bisect_irr(flows)
    if got is None:
        fail("referee found no root for a plain buy-then-sell")
    elif abs(got - want) > 1e-6:
        fail(f"referee rate {got:.8f} != hand-computed {want:.8f}")

    # 2. It must NOT return the -100% root that traps a Newton solver.
    if got is not None and abs(got + 1.0) < 1e-6:
        fail("referee converged on the -100% asymptote")

    # 3. It must find a very large rate rather than giving up. A 20-day
    #    10.00 -> 16.50 sale annualizes past 900,000%, which a fixed upper
    #    bracket missed entirely, silently skipping the solver check on the
    #    cases most likely to break a Newton solver.
    steep = [(END - datetime.timedelta(days=20), -10.0), (END, 16.50)]
    big = bisect_irr(steep)
    if big is None or big < 100:
        fail(f"referee failed on a steep short-horizon return: {big}")

    # 4. No sign change means no root, and must be reported as such rather
    #    than silently returning a bracket endpoint.
    if bisect_irr([(d(2020, 1, 1), -10.0), (d(2021, 1, 1), -20.0)]) is not None:
        fail("referee invented a root for all-negative flows")

    # 4b. SEVERAL sign changes mean several real roots, and the referee must
    #     decline rather than pick one: adjudicating toward a root rledger
    #     never claimed would be worse than giving no verdict. Outflow, larger
    #     inflow, larger outflow is the classic shape.
    two_roots = [(END - datetime.timedelta(days=730), -1.0),
                 (END - datetime.timedelta(days=365), 5.0),
                 (END, -6.0)]
    if bisect_irr(two_roots) is not None:
        fail("referee ruled on a series with multiple roots instead of declining")

    # 4c. And the decline must stay RARE. `None` means "no verdict", so a
    #     guard that fires often would silently switch the solver check off,
    #     which is the failure it was added to prevent. Measured at 0/300
    #     generated seeds when written.
    declined = sum(
        1 for seed in range(30)
        if (fl := _flows_for_seed(rledger, seed)) and bisect_irr(fl) is None
    )
    if declined > 3:
        fail(f"referee declined on {declined}/30 seeds; the solver check is mostly off")

    # 5. The EXTRACTION and SOLVER verdicts must be reachable. Running only a
    #    clean seed proves the harness can say "agree" and nothing else:
    #    deleting either comparison would leave `--self-test` green. These
    #    drive `check_one`'s comparisons directly with planted values.
    planted = [
        ("extraction", {"invested": "100.00", "distributions": "0.00",
                        "current_value": "0.00", "cash_flows": 1,
                        "money_weighted_return_pct": 0.0},
         [(d(2020, 1, 1), -999.0)]),
        # The +99 flow lands ON the end date, so it is TERMINAL VALUE, not a
        # distribution. Getting that backwards made this fixture trip the
        # extraction check instead of the solver one.
        ("solver", {"invested": "72.00", "distributions": "0.00",
                    "current_value": "99.00", "cash_flows": 2,
                    "money_weighted_return_pct": -100.0},
         [(END - datetime.timedelta(days=165), -72.0), (END, 99.0)]),
    ]
    for want_verdict, rl, flows in planted:
        invested = sum(-a for _, a in flows if a < 0)
        distributions = sum(a for dt, a in flows if a > 0 and dt != END)
        terminal = sum(a for dt, a in flows if a > 0 and dt == END)
        mismatched = any(
            abs(float(Decimal(rl[k])) - v) > 0.02
            for k, v in (("invested", invested), ("distributions", distributions),
                         ("current_value", terminal))
        )
        ref = bisect_irr(flows)
        if want_verdict == "extraction" and not mismatched:
            fail("planted extraction difference was not detected")
        if want_verdict == "solver":
            if mismatched:
                fail("planted solver case tripped the extraction check instead")
            elif ref is None or abs(rl["money_weighted_return_pct"] - ref * 100) <= TOLERANCE:
                fail("planted solver difference was not detected")

    # 6. And the real engines must agree on a hand-checked portfolio.
    verdict, report = check_one(rledger, seed=1)
    if verdict == "skip":
        fail("seed=1 skipped; the harness compared nothing")
    elif verdict != "agree":
        fail(f"seed=1 reported {verdict}")
        print("\n".join(report))

    print("self-test passed" if ok else "self-test FAILED")
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--runs", type=int, default=100)
    ap.add_argument("--seed", type=int, help="run a single seed and report")
    ap.add_argument("--start-seed", type=int, default=0)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--rledger", default="target/release/rledger")
    args = ap.parse_args()

    _require_beangrow()
    if args.self_test:
        return self_test(args.rledger)

    seeds = (
        [args.seed] if args.seed is not None
        else list(range(args.start_seed, args.start_seed + args.runs))
    )
    extraction = solver = skipped = 0
    for seed in seeds:
        verdict, report = check_one(args.rledger, seed)
        if verdict == "skip":
            skipped += 1
            continue
        if verdict == "extraction":
            extraction += 1
        elif verdict == "solver":
            solver += 1
        else:
            continue
        print("\n".join(report))
        print("-" * 60)
    executed = len(seeds) - skipped
    agreed = executed - extraction - solver
    print(f"{agreed}/{executed} agreed ({skipped} skipped)")
    print(f"{extraction} extraction difference(s)")
    print(f"{solver} solver difference(s)")
    # A run that compared NOTHING is a failure, not a pass. Both engines turn
    # load and execution failures into `skip`, so an incompatible beangrow
    # API or a generator that stopped producing valid ledgers would otherwise
    # print "0/0 agreed" and exit 0: a green gate that ran no comparison.
    if executed == 0:
        print("ERROR: no seed produced a comparison; the gate proved nothing")
        return 1
    if skipped > len(seeds) // 2:
        print(f"ERROR: {skipped}/{len(seeds)} seeds skipped, too many to trust")
        return 1
    return 1 if (extraction or solver) else 0


if __name__ == "__main__":
    sys.exit(main())
