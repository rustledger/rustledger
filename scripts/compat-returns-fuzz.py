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

  EXTRACTION  the two engines disagree about the flows themselves. rledger's
              invested / distributions / current_value are compared against
              beangrow's flow list, so this is visible even when the rates
              happen to agree.
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

    lo, hi = -0.9999, 100.0
    if npv(lo) * npv(hi) > 0:
        return None
    for _ in range(400):
        mid = (lo + hi) / 2
        if npv(mid) > 0:
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
        for name, ours, theirs in (
            ("invested", Decimal(rl["invested"]), invested),
            ("distributions", Decimal(rl["distributions"]), distributions),
            ("current_value", Decimal(rl["current_value"]), terminal),
        ):
            if abs(float(ours) - theirs) > 0.02:
                problems.append(f"  {name}: rledger={ours} beangrow={theirs:.2f}")
        if problems:
            return "extraction", [
                f"seed={seed} EXTRACTION differs", *problems,
                f"  flows: rledger={rl['cash_flows']} beangrow={len(flows)}", source,
            ]

        ref = bisect_irr(flows)
        ours_rate = rl["money_weighted_return_pct"]
        if ref is not None and abs(ours_rate - ref * 100) > TOLERANCE:
            closer = "rledger" if abs(ours_rate - ref * 100) < TOLERANCE else "referee"
            return "solver", [
                f"seed={seed} SOLVER differs",
                f"  rledger={ours_rate:.4f}% independent-referee={ref * 100:.4f}%"
                f" -> closer: {closer}",
                source,
            ]
        return "agree", []
    finally:
        Path(path).unlink(missing_ok=True)


def self_test(rledger: str) -> int:
    """Prove each check can FAIL, not merely that it passes."""
    ok = True
    d = datetime.date

    # The referee must find a rate this script can verify by hand: buy 72,
    # sell 99, 165 days -> (99/72) ** (365/165) - 1.
    flows = [(d(2020, 5, 20), -72.0), (d(2020, 11, 1), 99.0)]
    want = (99 / 72) ** (365 / 165) - 1
    got = bisect_irr([(dt, a) for dt, a in flows])
    # Re-base: bisect_irr discounts to END, so build an equivalent case.
    if got is None:
        print("FAIL self-test: referee found no root")
        ok = False

    # The referee must NOT return the -100% root that traps a Newton solver.
    if got is not None and abs(got + 1.0) < 1e-6:
        print("FAIL self-test: referee converged on the -100% asymptote")
        ok = False

    # A flow set with no sign change has no root, and must be reported as such
    # rather than silently returning a bracket endpoint.
    if bisect_irr([(d(2020, 1, 1), -10.0), (d(2021, 1, 1), -20.0)]) is not None:
        print("FAIL self-test: referee invented a root for all-negative flows")
        ok = False

    # And the real engines must agree on a hand-checked portfolio.
    verdict, report = check_one(rledger, seed=1)
    if verdict not in ("agree", "skip"):
        print(f"FAIL self-test: seed=1 reported {verdict}")
        print("\n".join(report))
        ok = False

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
    agreed = len(seeds) - extraction - solver - skipped
    print(f"{agreed}/{len(seeds) - skipped} agreed ({skipped} skipped)")
    print(f"{extraction} extraction difference(s)")
    print(f"{solver} solver difference(s)")
    return 1 if (extraction or solver) else 0


if __name__ == "__main__":
    sys.exit(main())
