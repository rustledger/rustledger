//! Investment returns math for beancount ledgers (#1814).
//!
//! This crate is the shared, pure computation engine for `rledger`'s returns
//! reporting. It deliberately owns only the *math* — no ledger loading, no
//! price database, no I/O — so that every consumer (the CLI `report returns`
//! command, and later the query engine, the FFI component, and rustfava) reuses
//! ONE implementation rather than re-deriving it (the repo's canonical-function
//! discipline). Cash-flow *extraction* from a ledger — which postings cross an
//! investment's boundary, dividend classification, currency conversion, and the
//! terminal market valuation — is the caller's job; this crate takes the
//! resulting [`CashFlow`] series and returns a rate.
//!
//! This first cut ships the money-weighted return ([`xirr`]). Time-weighted
//! return (Modified Dietz / true TWR) needs per-date portfolio valuations that
//! only the extraction layer can supply, so it lands alongside that layer.
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
/// Absolute NPV below which a rate is accepted as a root (reporting-currency
/// units).
const NPV_TOLERANCE: f64 = 1e-7;
/// Newton iterations before falling back to bisection.
const NEWTON_MAX_ITER: usize = 100;
/// Bisection steps once a sign-change bracket is found.
const BISECT_MAX_ITER: usize = 200;

/// Money-weighted return: the annualized internal rate of return (XIRR) of an
/// irregularly-spaced cash-flow series.
///
/// Returns `None` when there is no rate to find or the solver cannot locate
/// one:
/// - fewer than two flows;
/// - no sign change (every flow the same sign — e.g. only purchases, with no
///   sale or terminal valuation — has no IRR);
/// - the result is non-finite.
///
/// The rate is a fraction (`0.10` = 10% per year). The day count is actual/365
/// from the earliest flow date.
///
/// # Multiple roots
///
/// A cash-flow series with more than one sign change can have several
/// mathematically valid IRRs. Like spreadsheet `XIRR` and beangrow, this
/// returns a single root (the one the solver converges to); for the
/// conventional "outflows then inflows" shape there is exactly one.
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

    // Reduce to (years-from-first-flow, amount) pairs once.
    let origin = flows.iter().map(|f| f.date).min()?;
    let series: Vec<(f64, f64)> = flows
        .iter()
        .map(|f| {
            let days = f.date.since(origin).map_or(0, |span| span.get_days());
            (
                f64::from(days) / DAYS_PER_YEAR,
                f.amount.to_f64().unwrap_or(0.0),
            )
        })
        .collect();

    newton(&series).or_else(|| bisect(&series))
}

/// Net present value of the series at `rate`.
fn npv(series: &[(f64, f64)], rate: f64) -> f64 {
    let base = 1.0 + rate;
    series.iter().map(|&(t, a)| a / base.powf(t)).sum()
}

/// d(NPV)/d(rate).
fn npv_derivative(series: &[(f64, f64)], rate: f64) -> f64 {
    let base = 1.0 + rate;
    series
        .iter()
        .map(|&(t, a)| -t * a / base.powf(t + 1.0))
        .sum()
}

/// Newton's method from a 10% seed. Bails to `None` (letting the caller fall
/// back to bisection) if it leaves the valid domain (`rate <= -1`) or stalls.
fn newton(series: &[(f64, f64)]) -> Option<f64> {
    let mut rate = 0.1;
    for _ in 0..NEWTON_MAX_ITER {
        let value = npv(series, rate);
        if value.abs() < NPV_TOLERANCE {
            return finite(rate);
        }
        let slope = npv_derivative(series, rate);
        if slope == 0.0 {
            return None;
        }
        let next = rate - value / slope;
        if !next.is_finite() || next <= -1.0 {
            return None;
        }
        if (next - rate).abs() < 1e-12 {
            return finite(next);
        }
        rate = next;
    }
    None
}

/// Bracket a sign change on `(-0.9999, hi]` (growing `hi`) then bisect. Robust
/// where Newton diverges, at the cost of speed.
fn bisect(series: &[(f64, f64)]) -> Option<f64> {
    let low = -0.999_9;
    let f_low = npv(series, low);

    // Grow the upper bound until it brackets a root with `low` (i.e. NPV
    // changes sign between them). Bounded doubling; give up if no bracket.
    let mut high = 1.0;
    let mut f_high = npv(series, high);
    let mut bracketed = false;
    for _ in 0..60 {
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

    let (mut a, mut b) = (low, high);
    let mut f_a = f_low;
    for _ in 0..BISECT_MAX_ITER {
        let mid = 0.5 * (a + b);
        let f_mid = npv(series, mid);
        if f_mid.abs() < NPV_TOLERANCE || (b - a).abs() < 1e-12 {
            return finite(mid);
        }
        if f_a * f_mid < 0.0 {
            b = mid;
        } else {
            a = mid;
            f_a = f_mid;
        }
    }
    finite(0.5 * (a + b))
}

/// Guard: reject NaN/inf so callers never surface a garbage rate.
fn finite(rate: f64) -> Option<f64> {
    rate.is_finite().then_some(rate)
}

/// Whether two NPV values straddle zero (a sign-change bracket). Treats zero as
/// non-negative so an exact root at a bound still brackets.
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
    fn newton_and_bisection_agree() {
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
}
