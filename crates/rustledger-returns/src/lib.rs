//! Investment returns math for beancount ledgers (#1814).
//!
//! This crate is the shared, pure computation engine for `rledger`'s returns
//! reporting. It deliberately owns only the *math* — no ledger loading, no
//! price database, no I/O — so that every consumer (the CLI `report returns`
//! command, and later the query engine, the FFI component, and rustfava) reuses
//! ONE implementation rather than re-deriving it (the repo's canonical-function
//! discipline).
//!
//! The layers:
//!
//! - [`xirr`] — the money-weighted return (MWR) over a [`CashFlow`] series.
//! - [`extract_cash_flows`] — turning a booked ledger into that series: which
//!   postings cross an investment's boundary, terminal market valuation, and
//!   conversion to one reporting currency. Prices are supplied through the
//!   [`PriceOracle`] trait, so the crate stays a leaf (it does no ledger
//!   loading, owns no price index, and does no I/O — those remain the caller's).
//! - [`twr`] — the time-weighted return, which values the portfolio at each
//!   cash-flow date and chains the sub-period returns, so it measures the
//!   *investments'* performance independent of contribution timing (the
//!   GIPS / manager-comparison metric). Report both, MWR as the headline.
//!
//! # Sign convention
//!
//! Flows are **investor-centric**: money the investor puts IN (buying an asset)
//! is **negative**; money the investor gets OUT (sale proceeds, dividends, and
//! the terminal market value of the position still held at the report end date)
//! is **positive**. [`xirr`] finds the annual rate at which the present value of
//! all flows nets to zero — the return the investor actually earned given *when*
//! they moved money, which is what a personal investor evaluating their own
//! performance wants (money-weighted, a.k.a. XIRR).

use rust_decimal::Decimal;
use rust_decimal::prelude::ToPrimitive;
use rustledger_core::NaiveDate;

mod extract;
pub use extract::{
    AccountRole, ExtractError, PriceOracle, Returns, Scope, compute_returns, compute_returns_multi,
    extract_cash_flows, extract_flows, terminal_value, twr,
};

/// A single dated cash flow in one reporting currency.
///
/// See the [crate] docs for the sign convention (investor outlay negative,
/// proceeds positive).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CashFlow {
    /// The date the flow occurred.
    pub date: NaiveDate,
    /// The signed amount, in the report's single reporting currency.
    pub amount: Decimal,
}

impl CashFlow {
    /// Construct a cash flow.
    #[must_use]
    pub const fn new(date: NaiveDate, amount: Decimal) -> Self {
        Self { date, amount }
    }
}

/// Day-count basis: actual days over a 365-day year, matching the convention
/// used by spreadsheet `XIRR` and beangrow.
const DAYS_PER_YEAR: f64 = 365.0;
/// A rate is accepted as a root when `|NPV|` is within this **fraction of the
/// gross flow magnitude**. A relative tolerance is essential: a fixed absolute
/// threshold is unreachable for a million-dollar portfolio (so the solver would
/// spin) and trivially satisfied for a sub-cent one (so it would accept any
/// rate as a "root").
const NPV_REL_TOLERANCE: f64 = 1e-9;
/// Floor on the resolved absolute tolerance, so a near-zero gross magnitude
/// can't drive it to 0.
const NPV_ABS_FLOOR: f64 = 1e-12;
/// Lower end of the root-search bracket: just above the `rate = -1` pole, so
/// near-total-loss IRRs (down to ~-99.99999%) are still reachable.
const RATE_LOWER_BOUND: f64 = -0.999_999_9;
/// Step / bracket width below which a root is considered pinned (in rate units).
const STEP_EPSILON: f64 = 1e-12;
/// Newton iterations before falling back to Brent's method.
const NEWTON_MAX_ITER: usize = 100;
/// Brent iterations once a sign-change bracket is found. Brent converges
/// superlinearly, so this is generous.
const BRENT_MAX_ITER: usize = 100;

// Per-thread count of accepted inverse-quadratic-interpolation steps, so a test
// can prove Brent's IQI branch is actually exercised (not silently masked by
// its bisection safeguard). Thread-local: solving runs synchronously on the
// caller's thread, so parallel tests don't interfere.
#[cfg(test)]
thread_local! {
    static IQI_ACCEPTED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Money-weighted return: the annualized internal rate of return (XIRR) of an
/// irregularly-spaced cash-flow series.
///
/// Returns `None` when there is no rate to find or the solver cannot locate
/// one:
/// - fewer than two flows;
/// - no sign change (every flow the same sign — e.g. only purchases, with no
///   sale or terminal valuation — has no IRR);
/// - every flow falls on the same day (no time elapses, so no annual rate is
///   defined — see below);
/// - the result is non-finite.
///
/// The rate is a fraction (`0.10` = 10% per year). The day count is actual/365
/// from the earliest flow date.
///
/// # Degenerate series
///
/// If all flows share one date, NPV does not depend on the rate (it is either a
/// nonzero constant — no root — or identically zero — where *every* rate is a
/// "root"). Neither yields a meaningful annual return, so this returns `None`
/// rather than fabricating one from the solver's seed.
///
/// # Multiple roots
///
/// A cash-flow series with more than one sign change can have several
/// mathematically valid IRRs. Like spreadsheet `XIRR` and beangrow, this
/// returns a single root (the one the solver converges to); for the
/// conventional "outflows then inflows" shape there is exactly one. A
/// series whose only roots have even multiplicity within the search range
/// (the NPV curve touches zero without crossing) may not be bracketed and can
/// return `None`.
///
/// # Extreme losses
///
/// IRRs below roughly **-99.99999%/year** — a near-total annual loss whose rate
/// falls below the search bracket's lower bound, against the `rate = -1` pole —
/// return `None`. The result is never a fabricated or garbage rate: both solvers
/// return only a genuinely-converged root (Newton re-checks NPV at a stalled
/// step; Brent returns only a root proven by a converged, finite,
/// sign-changing bracket), and a bracket corrupted by a non-finite NPV near the
/// pole is rejected before refinement — so such cases yield `None`, not a wrong
/// number.
#[must_use]
pub fn xirr(flows: &[CashFlow]) -> Option<f64> {
    if flows.len() < 2 {
        return None;
    }

    // An IRR exists only if the flows change sign (money out AND money in).
    let has_positive = flows
        .iter()
        .any(|f| f.amount.is_sign_positive() && !f.amount.is_zero());
    let has_negative = flows.iter().any(|f| f.amount.is_sign_negative());
    if !(has_positive && has_negative) {
        return None;
    }

    let origin = flows.iter().map(|f| f.date).min()?;
    // Degenerate: all flows on one day → NPV is rate-independent → no rate.
    if flows.iter().all(|f| f.date == origin) {
        return None;
    }

    // Degenerate: the flows on *every* date net to zero. Then NPV(r) =
    // Σ Sₜ/(1+r)ᵗ with every date-net Sₜ = 0, i.e. NPV is *identically* zero at
    // every rate — no rate is distinguished, so the IRR is undefined. This slips
    // past the all-same-date guard when there are ≥2 dates (e.g. same-day
    // deposit/withdrawal washes on two different days); without this check
    // Newton's iteration-0 `|NPV| < tol` succeeds at the seed and returns 0.10, a
    // fabricated return. Checked exactly in `Decimal` (the `(1+r)⁻ᵗ` for distinct
    // t are linearly independent, so identically-zero NPV ⟺ every Sₜ = 0).
    let mut net_by_date: std::collections::BTreeMap<NaiveDate, Decimal> =
        std::collections::BTreeMap::new();
    for f in flows {
        *net_by_date.entry(f.date).or_default() += f.amount;
    }
    if net_by_date.values().all(rust_decimal::Decimal::is_zero) {
        return None;
    }

    // Reduce to (years-from-first-flow, amount) pairs once. A `Decimal` that
    // cannot be represented as `f64` propagates as `None` (no fabricated rate)
    // rather than being silently zeroed, which would corrupt the result.
    let series: Vec<(f64, f64)> = flows
        .iter()
        .map(|f| {
            let days = f.date.since(origin).map_or(0, |span| span.get_days());
            Some((f64::from(days) / DAYS_PER_YEAR, f.amount.to_f64()?))
        })
        .collect::<Option<Vec<_>>>()?;

    // Relative tolerance scaled to the size of the flows (see NPV_REL_TOLERANCE).
    let gross: f64 = series.iter().map(|&(_, a)| a.abs()).sum();
    let tol = (gross * NPV_REL_TOLERANCE).max(NPV_ABS_FLOOR);

    // Both solvers self-verify: `newton` returns only a genuine root (its
    // stall branch re-checks NPV) or `None`; `brent` returns only a root proven
    // by a converged, finite, sign-changing bracket (IVT) or `None`. So a
    // non-root can never reach here — no NPV re-check on the result. Crucially
    // we do NOT re-verify `|NPV| <= tol`: near the rate=-1 pole the NPV
    // derivative is enormous, so a rate pinned to full f64 precision can still
    // have `|NPV|` a little above `tol`; that is a *genuine* root (the rate is
    // correct), and an NPV re-check would wrongly reject it.
    let candidate = newton(&series, tol).or_else(|| brent(&series, tol))?;
    candidate.is_finite().then_some(candidate)
}

/// Net present value of the series at `rate`.
fn npv(series: &[(f64, f64)], rate: f64) -> f64 {
    let base = 1.0 + rate;
    series.iter().map(|&(t, a)| a / base.powf(t)).sum()
}

/// NPV and its derivative at `rate` in a single pass. Newton needs both, and
/// sharing the `base.powf(t)` halves the transcendental work per iteration.
fn npv_and_derivative(series: &[(f64, f64)], rate: f64) -> (f64, f64) {
    let base = 1.0 + rate;
    let mut value = 0.0;
    let mut slope = 0.0;
    for &(t, a) in series {
        let discount = base.powf(t);
        value += a / discount;
        slope += -t * a / (discount * base);
    }
    (value, slope)
}

/// Newton's method from a 10% seed. Returns `None` (letting the caller fall back
/// to Brent) if it leaves the valid domain (`rate <= -1`), the derivative
/// vanishes, or it stalls at a point that is not actually a root.
fn newton(series: &[(f64, f64)], tol: f64) -> Option<f64> {
    let mut rate = 0.1;
    for _ in 0..NEWTON_MAX_ITER {
        let (value, slope) = npv_and_derivative(series, rate);
        if value.abs() < tol {
            return finite(rate);
        }
        if slope == 0.0 || !slope.is_finite() {
            return None;
        }
        let next = rate - value / slope;
        if !next.is_finite() || next <= -1.0 {
            return None;
        }
        if (next - rate).abs() < STEP_EPSILON {
            // Stalled. Accept ONLY if it is genuinely a root; otherwise give up
            // so Brent can try. (Without the NPV check, a step underflowing
            // near the rate=-1 pole would be returned as a fake root.)
            return if next.is_finite() && npv(series, next).abs() < tol {
                Some(next)
            } else {
                None
            };
        }
        rate = next;
    }
    None
}

/// Bracket a sign change on `[RATE_LOWER_BOUND, hi]` (growing `hi`) then refine
/// with **Brent's method** — the robust fallback for when Newton diverges.
///
/// Brent keeps bisection's guaranteed convergence (a bracket is always
/// maintained) but reaches the root superlinearly by preferring inverse
/// quadratic interpolation, then the secant step, and only bisecting when those
/// would step outside the bracket or fail to shrink it fast enough. This is the
/// method `scipy.optimize.brentq` uses and is the standard best-in-class 1-D
/// bracketing root-finder.
// `a`, `b`, `c`, `d`, `s` are the canonical Brent variable names (Wikipedia,
// Numerical Recipes, scipy); renaming them would obscure the reference algorithm.
#[allow(clippy::many_single_char_names)]
fn brent(series: &[(f64, f64)], tol: f64) -> Option<f64> {
    // ---- Bracket a sign change (`low` and a grown `high` straddle a root). ----
    // A non-finite NPV at a bound (a far-dated flow whose discount overflows
    // right against the rate=-1 pole) means we cannot form a *trustworthy*
    // bracket — `opposite_signs` on an inf/NaN could misfire. Reject it so a
    // corrupted bracket never reaches the refinement loop and produce `None`,
    // rather than a garbage rate. This is why the caller needs no NPV re-check:
    // every bracket that survives here is finite and genuinely sign-changing.
    let low = RATE_LOWER_BOUND;
    let f_low = npv(series, low);
    if !f_low.is_finite() {
        return None;
    }
    if f_low.abs() < tol {
        return finite(low); // a root sitting exactly on the lower bound
    }

    let mut high = 1.0;
    let mut f_high = npv(series, high);
    let mut bracketed = false;
    for _ in 0..60 {
        if !f_high.is_finite() {
            return None;
        }
        if f_high.abs() < tol {
            return finite(high); // a probed bound landed on a root
        }
        if opposite_signs(f_low, f_high) {
            bracketed = true;
            break;
        }
        high *= 2.0;
        if !high.is_finite() {
            break;
        }
        f_high = npv(series, high);
    }
    if !bracketed {
        return None;
    }

    // ---- Brent's method on the bracket [a, b]. ----
    // Invariant: `b` is the running best estimate (smaller |f|), `a` the
    // opposite-signed contra-point; `c`/`d` are the two previous iterates.
    let (mut a, mut b) = (low, high);
    let (mut fa, mut fb) = (f_low, f_high);
    if fa.abs() < fb.abs() {
        std::mem::swap(&mut a, &mut b);
        std::mem::swap(&mut fa, &mut fb);
    }
    let mut c = a;
    let mut fc = fa;
    let mut d = c; // only read once `used_bisection` is false (guarded below)
    let mut used_bisection = true;

    for _ in 0..BRENT_MAX_ITER {
        if fb.abs() < tol || (b - a).abs() < STEP_EPSILON {
            return finite(b);
        }

        // Propose the next point: inverse quadratic interpolation when the three
        // NPVs are distinct (`> 0.0` differences, not `!=`, keeps the float
        // lint happy and rejects an exact tie), else the secant step.
        let distinct = (fa - fc).abs() > 0.0 && (fb - fc).abs() > 0.0;
        let mut s = if distinct {
            a * fb * fc / ((fa - fb) * (fa - fc))
                + b * fa * fc / ((fb - fa) * (fb - fc))
                + c * fa * fb / ((fc - fa) * (fc - fb))
        } else {
            b - fb * (b - a) / (fb - fa)
        };

        // Reject the interpolated `s` and bisect instead when it steps outside
        // [(3a+b)/4, b], or fails to shrink the interval fast enough, or isn't
        // finite — the safeguards that give Brent its bisection guarantee.
        let bound = a.mul_add(3.0, b) / 4.0;
        let (blo, bhi) = if bound <= b { (bound, b) } else { (b, bound) };
        let bisect = !s.is_finite()
            || s < blo
            || s > bhi
            || (used_bisection && (s - b).abs() >= (b - c).abs() / 2.0)
            || (!used_bisection && (s - b).abs() >= (c - d).abs() / 2.0)
            || (used_bisection && (b - c).abs() < STEP_EPSILON)
            || (!used_bisection && (c - d).abs() < STEP_EPSILON);
        if bisect {
            s = 0.5 * (a + b);
        }
        used_bisection = bisect;
        #[cfg(test)]
        if !bisect && distinct {
            // Observability (canonical-function discipline): count accepted
            // inverse-quadratic steps so a test can prove the IQI branch is
            // actually taken, not silently masked by the bisection safeguard.
            IQI_ACCEPTED.with(|c| c.set(c.get() + 1));
        }

        let fs = npv(series, s);
        d = c;
        c = b;
        fc = fb;
        // Keep the sub-interval that still straddles the root.
        if opposite_signs(fa, fs) {
            b = s;
            fb = fs;
        } else {
            a = s;
            fa = fs;
        }
        // Restore the invariant that `b` is the better estimate.
        if fa.abs() < fb.abs() {
            std::mem::swap(&mut a, &mut b);
            std::mem::swap(&mut fa, &mut fb);
        }
    }
    // Exhausted the iteration budget without the bracket collapsing — treat as
    // non-convergence (`None`) rather than surfacing an unconverged `b`. Brent
    // converges superlinearly, so a legitimate bracket always exits the loop
    // above; reaching here means a pathological input, not a valid root.
    None
}

/// Guard: reject NaN/inf so callers never surface a garbage rate.
fn finite(rate: f64) -> Option<f64> {
    rate.is_finite().then_some(rate)
}

/// Whether two NPV values straddle zero (a sign-change bracket). Exact roots
/// sitting on a bound are handled separately by the endpoint checks in
/// [`brent`], so this treats `0.0` as non-negative.
fn opposite_signs(a: f64, b: f64) -> bool {
    (a < 0.0) != (b < 0.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::naive_date;

    fn d(y: i32, m: u32, day: u32) -> NaiveDate {
        naive_date(y, m, day).unwrap()
    }

    fn approx(a: f64, b: f64, eps: f64) -> bool {
        (a - b).abs() < eps
    }

    /// NPV of a flow list at `rate` — for asserting a returned rate is a root.
    fn npv_at(flows: &[CashFlow], rate: f64) -> f64 {
        let origin = flows.iter().map(|f| f.date).min().unwrap();
        let series: Vec<(f64, f64)> = flows
            .iter()
            .map(|f| {
                let days = f.date.since(origin).map_or(0, |s| s.get_days());
                (f64::from(days) / DAYS_PER_YEAR, f.amount.to_f64().unwrap())
            })
            .collect();
        npv(&series, rate)
    }

    #[test]
    fn one_year_ten_percent() {
        // -1000 today, +1100 in exactly 365 days → 10%.
        let flows = [
            CashFlow::new(d(2020, 1, 1), dec!(-1000)),
            CashFlow::new(d(2020, 12, 31), dec!(1100)),
        ];
        let r = xirr(&flows).expect("has a rate");
        assert!(approx(r, 0.10, 1e-6), "expected ~0.10, got {r}");
    }

    #[test]
    fn excel_xirr_reference_example() {
        // The canonical spreadsheet XIRR example → ≈ 0.373362535.
        let flows = [
            CashFlow::new(d(2008, 1, 1), dec!(-10000)),
            CashFlow::new(d(2008, 3, 1), dec!(2750)),
            CashFlow::new(d(2008, 10, 30), dec!(4250)),
            CashFlow::new(d(2009, 2, 15), dec!(3250)),
            CashFlow::new(d(2009, 4, 1), dec!(2750)),
        ];
        let r = xirr(&flows).expect("has a rate");
        assert!(approx(r, 0.373_362_5, 1e-5), "expected ~0.3734, got {r}");
    }

    #[test]
    fn negative_return_is_found() {
        // Put in 1000, get back 900 a year later → -10%.
        let flows = [
            CashFlow::new(d(2020, 1, 1), dec!(-1000)),
            CashFlow::new(d(2020, 12, 31), dec!(900)),
        ];
        let r = xirr(&flows).expect("has a rate");
        assert!(approx(r, -0.10, 1e-6), "expected ~-0.10, got {r}");
    }

    #[test]
    fn newton_and_brent_agree() {
        // Sanity: the NPV at the returned rate is ~0 (whichever solver won).
        let flows = [
            CashFlow::new(d(2019, 6, 15), dec!(-5000)),
            CashFlow::new(d(2020, 1, 1), dec!(-2000)),
            CashFlow::new(d(2021, 3, 20), dec!(1500)),
            CashFlow::new(d(2023, 12, 31), dec!(8200)),
        ];
        let r = xirr(&flows).expect("has a rate");
        let origin = flows.iter().map(|f| f.date).min().unwrap();
        let series: Vec<(f64, f64)> = flows
            .iter()
            .map(|f| {
                let days = f.date.since(origin).map_or(0, |s| s.get_days());
                (f64::from(days) / DAYS_PER_YEAR, f.amount.to_f64().unwrap())
            })
            .collect();
        assert!(
            npv(&series, r).abs() < 1e-4,
            "NPV at solved rate must be ~0"
        );
    }

    #[test]
    fn no_sign_change_is_none() {
        // Only purchases, no sale/terminal value → no IRR.
        let flows = [
            CashFlow::new(d(2020, 1, 1), dec!(-1000)),
            CashFlow::new(d(2021, 1, 1), dec!(-500)),
        ];
        assert_eq!(xirr(&flows), None);
    }

    #[test]
    fn fewer_than_two_flows_is_none() {
        assert_eq!(xirr(&[]), None);
        assert_eq!(xirr(&[CashFlow::new(d(2020, 1, 1), dec!(-1000))]), None);
    }

    #[test]
    fn zero_flows_do_not_count_as_a_sign_change() {
        // A 0 flow plus only-negative flows still has no positive → None.
        let flows = [
            CashFlow::new(d(2020, 1, 1), dec!(-1000)),
            CashFlow::new(d(2020, 6, 1), dec!(0)),
        ];
        assert_eq!(xirr(&flows), None);
    }

    #[test]
    fn same_date_flows_return_none() {
        // Same-day wash → NPV is rate-independent → no meaningful rate.
        // (Before the degenerate guard this fabricated the 0.10 solver seed.)
        assert_eq!(
            xirr(&[
                CashFlow::new(d(2020, 1, 1), dec!(1000)),
                CashFlow::new(d(2020, 1, 1), dec!(-1000)),
            ]),
            None
        );
        // Same day, net nonzero — still no elapsed time, so still undefined.
        assert_eq!(
            xirr(&[
                CashFlow::new(d(2020, 1, 1), dec!(1000)),
                CashFlow::new(d(2020, 1, 1), dec!(-600)),
            ]),
            None
        );
    }

    #[test]
    fn every_date_netting_to_zero_is_none_not_a_fabricated_rate() {
        // #1817: two same-day washes on two DIFFERENT dates. The flows change
        // sign and span >1 day, so this slips past the sign and all-same-date
        // guards, but every date nets to zero → NPV is identically zero at every
        // rate → the return is undefined. Before the fix, Newton's iteration-0
        // check succeeded at the seed and xirr fabricated 0.10.
        let flows = [
            CashFlow::new(d(2020, 1, 1), dec!(-1000)),
            CashFlow::new(d(2020, 1, 1), dec!(1000)),
            CashFlow::new(d(2020, 6, 1), dec!(-500)),
            CashFlow::new(d(2020, 6, 1), dec!(500)),
        ];
        assert_eq!(xirr(&flows), None);
    }

    #[test]
    fn undiscounted_sum_zero_but_time_structured_is_still_solved() {
        // Guard against over-firing: the UNDISCOUNTED total is zero here
        // (-1000 + 1000), but the dates differ, so NPV is zero only at r=0 (not
        // identically) — a genuine 0% return, which must still be solved.
        let flows = [
            CashFlow::new(d(2020, 1, 1), dec!(-1000)),
            CashFlow::new(d(2020, 12, 31), dec!(1000)),
        ];
        let r = xirr(&flows).expect("a 0% return is defined");
        assert!(approx(r, 0.0, 1e-6), "expected ~0%, got {r}");
    }

    #[test]
    fn near_total_loss_is_found() {
        // Lose ~99.995%: -1000 in, +0.05 back a year later → IRR ≈ -0.99995.
        // The old lower bound of -0.9999 could not reach this.
        let flows = [
            CashFlow::new(d(2020, 1, 1), dec!(-1000)),
            CashFlow::new(d(2020, 12, 31), dec!(0.05)),
        ];
        let r = xirr(&flows).expect("large-loss IRR must still be found");
        assert!(approx(r, -0.99995, 1e-4), "expected ~-0.99995, got {r}");
    }

    #[test]
    fn large_magnitude_resolves() {
        // The 10% one-year shape at million-scale must still resolve to ~0.10.
        // An absolute NPV tolerance of 1e-7 is unreachable at this magnitude;
        // the relative tolerance makes it work.
        let flows = [
            CashFlow::new(d(2020, 1, 1), dec!(-1000000)),
            CashFlow::new(d(2020, 12, 31), dec!(1100000)),
        ];
        let r = xirr(&flows).expect("million-scale series must resolve");
        assert!(approx(r, 0.10, 1e-6), "expected ~0.10, got {r}");
    }

    #[test]
    fn tiny_magnitude_requires_relative_tolerance() {
        // Flows ~1e-8 in magnitude with a ~50% return. Under an ABSOLUTE 1e-7
        // NPV tolerance, |NPV| is below 1e-7 for every rate, so the solver would
        // accept the 0.10 seed as a bogus root on iteration 0. The relative
        // tolerance keeps the check meaningful and finds the true ~49.8% rate.
        let flows = [
            CashFlow::new(d(2020, 1, 1), dec!(-0.00000002)),
            CashFlow::new(d(2021, 1, 1), dec!(0.00000003)),
        ];
        let r = xirr(&flows).expect("tiny-magnitude series must still resolve");
        assert!(
            approx(r, 0.498, 3e-3),
            "expected the true ~0.498, not the 0.10 seed, got {r}"
        );
    }

    #[test]
    fn brent_solves_a_bracketed_root_precisely() {
        // Exercise the Brent fallback directly on a clean root (10% one-year:
        // -1000 + 1100/(1+r) = 0 → r = 0.10). Confirms the interpolation
        // converges to full precision, not merely within the accept tolerance.
        let series = [(0.0, -1000.0), (1.0, 1100.0)];
        let r = brent(&series, 1e-9).expect("bracketed root");
        assert!((r - 0.10).abs() < 1e-9, "Brent must nail 0.10, got {r}");
    }

    #[test]
    fn deep_loss_within_bracket_is_found() {
        // #1815 round-3 review: a ~-99.99995% loss (-1000 in, +0.0005 out a year
        // later; IRR ≈ -0.9999995) is INSIDE the search bracket. Brent pins the
        // rate to full precision, but near the pole the NPV derivative is huge,
        // so |NPV| stays a hair above `tol`. The result must still be the rate —
        // an NPV re-check used to wrongly reject it as None.
        let flows = [
            CashFlow::new(d(2020, 1, 1), dec!(-1000)),
            CashFlow::new(d(2020, 12, 31), dec!(0.0005)),
        ];
        let r = xirr(&flows).expect("a deep-but-in-bracket loss must resolve");
        assert!(
            approx(r, -0.999_999_5, 1e-6),
            "expected ~-0.9999995, got {r}"
        );
    }

    #[test]
    fn brent_exercises_inverse_quadratic_interpolation() {
        // Prove the IQI branch actually runs, so a corrupted IQI formula can't
        // hide behind the bisection safeguard (canonical-function discipline).
        IQI_ACCEPTED.with(|c| c.set(0));
        // A smooth, well-conditioned bracket: after the first (secant) step the
        // three NPVs are distinct and the interpolated point is accepted.
        let series = [(0.0, -1000.0), (0.5, 100.0), (1.0, 1050.0)];
        let r = brent(&series, 1e-9).expect("bracketed root");
        assert!((-1.0..2.0).contains(&r), "sane root, got {r}");
        assert!(
            IQI_ACCEPTED.with(std::cell::Cell::get) > 0,
            "Brent must exercise inverse-quadratic interpolation, not only its \
             bisection safeguard"
        );
    }

    #[test]
    fn extreme_loss_below_supported_range_returns_none() {
        // IRR ≈ -99.99999% sits BELOW the bracket's lower bound (-0.9999999), so
        // no bracket forms and the result is a graceful None — never a
        // fabricated or garbage rate.
        let flows = [
            CashFlow::new(d(2020, 1, 1), dec!(-1000)),
            CashFlow::new(d(2020, 12, 31), dec!(0.00005)),
        ];
        assert_eq!(xirr(&flows), None);
    }

    #[test]
    fn multiple_sign_changes_returns_a_valid_root() {
        // -100, +230, -132 has IRRs at exactly 10% and 20%. We return one root;
        // assert it is a genuine root (NPV ≈ 0), not a specific one.
        let flows = [
            CashFlow::new(d(2020, 1, 1), dec!(-100)),
            CashFlow::new(d(2020, 12, 31), dec!(230)),
            CashFlow::new(d(2021, 12, 31), dec!(-132)),
        ];
        let r = xirr(&flows).expect("a root exists");
        assert!(
            npv_at(&flows, r).abs() < 1e-6,
            "returned rate {r} must be a root, NPV = {}",
            npv_at(&flows, r)
        );
    }
}
