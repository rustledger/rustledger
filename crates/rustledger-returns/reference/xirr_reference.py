#!/usr/bin/env python3
"""Independent XIRR reference — provenance for `xirr_matches_independent_reference`.

This is a deliberately *independent* second implementation of the same canonical
money-weighted-return definition that `rustledger_returns::xirr` computes:

    NPV(r) = Σ  cfᵢ / (1 + r) ** (dᵢ / 365)
    where dᵢ = actual calendar days from the earliest flow date (actual/365),
    and the XIRR is the r that makes NPV(r) = 0.

It differs from the production code in the one place that matters for a
cross-check: the *root-finder*. rledger uses Newton's method with a Brent
fallback; this uses plain bisection. A bug in one solver (bad derivative,
bracket, damping) does not reproduce in the other, so when the two agree on a
rate the agreement is evidence about the *definition*, not a shared quirk.

The reference is itself anchored to an externally-known value: the `sanity`
series (−1000 today, +1100 in exactly 365 non-leap days) must yield exactly
0.10 — the same answer a spreadsheet =XIRR() gives.

Run `python3 xirr_reference.py` to regenerate the golden values embedded in
`crates/rustledger-returns/src/lib.rs`. Stdlib only; no third-party deps.
"""
from datetime import date


def npv(rate, flows):
    origin = min(d for d, _ in flows)
    return sum(cf / (1.0 + rate) ** ((d - origin).days / 365.0) for d, cf in flows)


def xirr(flows):
    """Bisection root of NPV(r) = 0 on [-0.999999, 1000]. Returns None if unbracketed."""
    lo, hi = -0.999999, 1000.0
    flo, fhi = npv(lo, flows), npv(hi, flows)
    if flo == 0.0:
        return lo
    if flo * fhi > 0.0:  # NPV does not cross zero on the interval → no rate
        return None
    for _ in range(200):
        mid = (lo + hi) / 2.0
        fm = npv(mid, flows)
        if abs(fm) < 1e-12 or (hi - lo) < 1e-15:
            return mid
        if flo * fm < 0.0:
            hi, fhi = mid, fm
        else:
            lo, flo = mid, fm
    return (lo + hi) / 2.0


# The scenarios pinned by the Rust test, plus an externally-anchored sanity case.
SANITY = [(date(2021, 1, 1), -1000.0), (date(2022, 1, 1), 1100.0)]  # 365 days → exactly 0.10
SCENARIOS = {
    "one_year_gain": [(date(2020, 1, 1), -1000.0), (date(2021, 1, 1), 1100.0)],
    "dividend_then_sale": [
        (date(2020, 1, 1), -1000.0),
        (date(2020, 7, 1), 30.0),
        (date(2021, 1, 1), 1080.0),
    ],
    "loss_over_18_months": [(date(2020, 1, 1), -1000.0), (date(2021, 6, 1), 800.0)],
    "two_buys_one_sale": [
        (date(2020, 1, 1), -1000.0),
        (date(2020, 6, 1), -500.0),
        (date(2021, 1, 1), 1700.0),
    ],
    "sub_year_annualized": [(date(2020, 1, 1), -1000.0), (date(2020, 4, 1), 1050.0)],
}


def main():
    s = xirr(SANITY)
    # None means the NPV never crossed zero on the bracket (a degenerate/edited
    # series). Guard so that failure reads clearly instead of a TypeError from
    # arithmetic on None.
    assert s is not None, "sanity series did not bracket a rate"
    assert abs(s - 0.10) < 1e-9, f"sanity must be exactly 0.10, got {s}"
    print(f"# sanity (365d, +10%): {s:.10f}  ✓ matches spreadsheet =XIRR()")
    for name, flows in SCENARIOS.items():
        r = xirr(flows)
        assert r is not None, f"{name}: series did not bracket a rate"
        # Self-consistency: NPV at the returned rate must be ~0.
        resid = npv(r, flows)
        assert abs(resid) < 1e-9, f"{name}: NPV at solved rate = {resid}"
        print(f"{name:24s} {r:.10f}")


if __name__ == "__main__":
    main()
