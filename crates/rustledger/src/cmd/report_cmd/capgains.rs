//! Realized capital-gains / tax-lot report.
//!
//! Where `report holdings` shows what you still HOLD, this shows what you SOLD:
//! one row per disposed tax lot, classified short vs long term by holding period,
//! with proceeds, cost basis, and realized gain/loss, plus per-term and
//! per-currency summaries.
//!
//! It consumes [`rustledger_booking::CapitalGain`]s straight from
//! [`Ledger::capital_gains`](rustledger_loader::Ledger) — the realized gains the
//! loader's own booking pass computes, once, in booking order, with the ledger's
//! own method, and *before* `@@` normalization (so total-price proceeds are exact).
//! The report does NOT re-book the stream: re-deriving the loader's lot-matching is
//! exactly the drift the canonical-function discipline warns against, and every
//! way of doing it (a defaulted booking method, a hand-rolled canonical sort, the
//! pre- vs post-normalization stream, a re-implemented interpolate/apply loop) was
//! a bug this report worked through before the gains were exposed at the source.
//! A transaction the loader cannot book is recorded in `Ledger::errors` (printed by
//! the shared load path), so an incomplete report is surfaced through the normal
//! error channel.
//!
//! **Short positions** are reported when covered: the lot's cost is the price the
//! units were sold at when the short was opened, so proceeds are the short-open
//! value and cost basis is the cover cost (the mirror of a long disposal), and the
//! gain is always short-term (the US rule). **Unknown holding period**: a lot with
//! no acquisition date — e.g. under `AVERAGE` booking, which merges lots and drops
//! their dates — is classified `unknown`, not silently `short`.
//!
//! **Realized IRR** (`--irr`): the annualized money-weighted return of each closed
//! round trip — `−cost_basis` at acquisition, `+proceeds` at sale — solved with the
//! canonical [`rustledger_returns::xirr`], plus a pooled rate per term and per
//! currency. This is a **realized-only** return: it can only see lots you actually
//! closed, so it is NOT the portfolio's total return. For that (including what you
//! still hold, valued at market) use `report returns`, which is the beangrow-shaped
//! total-return report; this column is the per-lot view `returns` cannot give.
//!
//! Gains are reported in each lot's **cost currency**; a multi-currency ledger is
//! summarized per currency. Not a tax filing: wash-sale adjustment, currency-gain
//! separation, lots seeded by `pad` (no well-defined cost basis), and jurisdiction
//! rules beyond the long-term threshold are out of scope (run `rledger check` to
//! validate the ledger first).

use super::returns::{fmt_rate, fmt_rate_pct, json_rate};
use super::{OutputFormat, csv_escape, json_escape};
use anyhow::Result;
use rust_decimal::Decimal;
use rustledger_booking::CapitalGain;
use rustledger_core::{DisplayContext, NaiveDate};
use rustledger_returns::{CashFlow, xirr};
use std::collections::BTreeMap;
use std::io::Write;

/// Holding-period classification of a disposal.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Term {
    Short,
    Long,
    /// Holding period could not be determined — the lot carried no acquisition
    /// date (e.g. an AVERAGE-cost lot, which merges lots and drops their dates).
    /// Reported honestly as unknown rather than silently defaulted to short.
    Unknown,
}

impl Term {
    /// Machine-readable term (CSV / JSON).
    const fn as_str(self) -> &'static str {
        match self {
            Self::Short => "short",
            Self::Long => "long",
            Self::Unknown => "unknown",
        }
    }
    /// Compact label for the text table.
    const fn abbr(self) -> &'static str {
        match self {
            Self::Short => "ST",
            Self::Long => "LT",
            Self::Unknown => "??",
        }
    }
}

/// One realized disposal: a single tax lot sold.
struct Disposal {
    sold: NaiveDate,
    account: String,
    commodity: String,
    units: Decimal,
    acquired: Option<NaiveDate>,
    /// Whole days held (`sold - acquired`), `None` if the lot carried no date.
    held_days: Option<i64>,
    term: Term,
    proceeds: Decimal,
    cost_basis: Decimal,
    gain: Decimal,
    /// The cost currency the figures are denominated in.
    currency: String,
    /// Closing a short position — excluded from IRR (see [`lot_flows`]).
    short_sale: bool,
    /// Annualized money-weighted return of this lot's round trip, when defined
    /// and requested (`--irr`). `None` = not requested, or undefined for this lot.
    irr: Option<f64>,
}

/// The cash flows of one closed round trip: the basis paid out at acquisition and
/// the proceeds received at sale — the input to this lot's IRR.
///
/// `None` when a round-trip rate is undefined, so the lot renders `n/a` **and** is
/// excluded from the pooled aggregate. Eligibility is decided here, once, so the
/// per-lot cell and the pooled rate always agree about which lots count:
/// - **short sales** — the money-in-then-out shape makes an IRR unconventional and
///   misleading, so it is deliberately not reported;
/// - **no acquisition date** (an `AVERAGE`-cost lot merges lots and drops dates),
///   so the outflow cannot be dated;
/// - **same-day round trips** (zero-day holding), where annualizing divides by a
///   zero time span;
/// - **non-positive cost basis**, which has no rate of return;
/// - **negative proceeds** (a disposal that cost more to close than it returned),
///   which is outside the domain of a simple round-trip rate.
///
/// A **total loss** (`proceeds == 0`) is NOT excluded: its rate is exactly -100%
/// (you cannot lose more than the whole basis, at any horizon), handled by
/// [`solve_irr`]. Dropping it would silently flatter every pooled rate by hiding
/// capital that never came back.
fn lot_flows(d: &Disposal) -> Option<[CashFlow; 2]> {
    if d.short_sale || d.cost_basis <= Decimal::ZERO || d.proceeds < Decimal::ZERO {
        return None;
    }
    let acquired = d.acquired?;
    if d.held_days? <= 0 {
        return None;
    }
    Some([
        CashFlow::new(acquired, -d.cost_basis),
        CashFlow::new(d.sold, d.proceeds),
    ])
}

/// Solve an annualized rate for one series of CLOSED round-trip flows.
///
/// The single entry point for both the per-lot cell and the pooled aggregate, so
/// the two can never answer differently for the same flows.
///
/// **Total loss** (`-100%`) is handled here rather than in the canonical
/// [`xirr`], and deliberately so: `xirr` returns `None` for any series without a
/// sign change, which is correct for its other caller — in `report returns` an
/// all-negative series means "bought and still holding", NOT a loss, and reporting
/// -100% there would be flatly wrong. Only THIS caller knows its series is a
/// *closed* round trip, where nothing coming back really does mean the whole basis
/// was lost, at any horizon. The knowledge is the caller's, so the special case
/// belongs to the caller. (`rustledger-returns` pins the `None` contract in
/// `no_sign_change_is_none` / `zero_flows_do_not_count_as_a_sign_change`; if that
/// ever changes, revisit this.)
fn solve_irr(flows: &[CashFlow]) -> Option<f64> {
    if flows.is_empty() {
        return None;
    }
    // Nothing came back from a closed round trip: the whole outlay was lost.
    if flows.iter().all(|f| f.amount <= Decimal::ZERO) {
        return Some(-1.0);
    }
    xirr(flows)
}

/// One lot's own annualized round-trip rate (`None` when the lot has no defined
/// round trip — see [`lot_flows`] — or when the rate is not solvable).
fn lot_irr(d: &Disposal) -> Option<f64> {
    solve_irr(&lot_flows(d)?)
}

/// Solve each row's own round-trip rate (the `--irr` pass). Rows whose rate is
/// undefined keep `None` and render `n/a`.
fn fill_lot_irr(rows: &mut [Disposal]) {
    for d in rows {
        d.irr = lot_irr(d);
    }
}

/// A pooled rate and the denominator it was actually computed over.
///
/// The two are reported together because they differ: the gain/proceeds totals on
/// the same summary line count EVERY disposal, while the rate can only include
/// lots with a defined round trip (see [`lot_flows`]). Printing a rate beside a
/// count it was not computed from is how "why doesn't this reconcile?" starts.
struct PooledIrr {
    rate: Option<f64>,
    /// Lots that contributed flows.
    eligible: usize,
    /// Lots in the bucket, eligible or not.
    total: usize,
}

impl PooledIrr {
    /// `10.00%`, or `10.00% (2 of 5 lots)` when some lots had no defined rate, so
    /// the reader can see the rate's denominator is not the line's disposal count.
    fn render(&self) -> String {
        let rate = fmt_rate_cell(self.rate);
        if self.eligible == self.total {
            rate
        } else {
            format!("{rate} ({} of {} lots)", self.eligible, self.total)
        }
    }
}

/// Pooled realized IRR over the eligible closed lots in `currency`, optionally
/// restricted to one `term` bucket.
///
/// **Precondition:** [`fill_lot_irr`] has run over `rows` — eligibility keys off
/// each row's solved `irr`, so an unfilled slice pools nothing. The render path
/// guarantees this (rates are filled before `render`), and it is what keeps a
/// summary rate consistent with the cells above it.
///
/// Pooling every lot's flows into one series and solving once is the
/// beangrow-shaped aggregate: a money-weighted return over all the capital that
/// actually cycled through, not an average of per-lot rates. The rate is `None`
/// when no lot is eligible or the series has no computable root (e.g. no sign
/// change); the returned counts say how much of the bucket it covers.
fn aggregate_irr(rows: &[Disposal], currency: &str, term: Option<Term>) -> PooledIrr {
    let mut total = 0usize;
    let mut eligible = 0usize;
    let mut flows: Vec<CashFlow> = Vec::new();
    for d in rows
        .iter()
        .filter(|d| d.currency == currency && term.is_none_or(|t| d.term == t))
    {
        total += 1;
        // Pool a lot ONLY if its own rate solved, reusing the ALREADY-SOLVED
        // `d.irr` — the literal value in its cell, so the cell and the aggregate
        // cannot disagree about which lots count, and no lot is re-solved once per
        // summary cell. (Pooling on flow-availability instead would let a lot that
        // renders `n/a` silently drive the aggregate and be counted as covered.)
        if d.irr.is_some()
            && let Some(f) = lot_flows(d)
        {
            eligible += 1;
            flows.extend(f);
        }
    }
    if flows.is_empty() {
        return PooledIrr {
            rate: None,
            eligible,
            total,
        };
    }
    flows.sort_by_key(|f| f.date);
    PooledIrr {
        // Same solver as the per-lot cell, so a bucket of one lot reports that
        // lot's rate rather than contradicting it.
        rate: solve_irr(&flows),
        eligible,
        total,
    }
}

/// Transform the loader's canonical [`CapitalGain`]s into report [`Disposal`]s,
/// classifying each lot's holding period.
///
/// The gains are computed ONCE by the loader's own booking pass (in booking order,
/// with the ledger's own method, before `@@` normalization) and exposed on the
/// `Ledger` — this report consumes them directly rather than re-booking the stream,
/// so it cannot drift from `rledger check`.
///
/// The realized gain is `proceeds − cost_basis`, which is only meaningful when the
/// two are in the SAME currency. A **cross-currency** disposal — the sale price is
/// in a different currency than the lot's cost basis, so the gain needs an FX rate
/// this tool does not apply — is dropped from the rows and counted in the returned
/// `cross_currency` total so the caller can surface it (rather than silently
/// omitting it). `long_term_days = Some(n)` means held strictly more than `n` days;
/// `None` uses the leap-year-safe calendar rule.
fn to_disposals(gains: &[CapitalGain], long_term_days: Option<i64>) -> (Vec<Disposal>, usize) {
    let mut cross_currency = 0usize;
    let rows: Vec<Disposal> = gains
        .iter()
        .filter_map(|g| {
            // Cross-currency: proceeds and basis are in different currencies, so
            // `proceeds − cost_basis` has no defined value. Count and drop.
            if g.proceeds.currency != g.cost_basis.currency {
                cross_currency += 1;
                return None;
            }
            let held_days = g
                .acquired_date
                .and_then(|a| a.until((jiff::Unit::Day, g.sale_date)).ok())
                .map(|s| i64::from(s.get_days()))
                // A lot "acquired" after the sale (a future-dated cost) yields a
                // negative span — nonsensical as a holding period, so drop it.
                .filter(|&d| d >= 0);
            // Short-sale gains are always short-term (US rule). Otherwise the holding
            // period is determinable only when the lot has an acquisition date AND a
            // non-negative span (`held_days` is `Some`) — a lot with no date (AVERAGE
            // cost) or a future-dated one is `unknown`, never silently short.
            let term = match (g.short_sale, g.acquired_date, held_days) {
                (true, _, _) => Term::Short,
                (_, Some(a), Some(_))
                    if is_long_term(a, g.sale_date, held_days, long_term_days) =>
                {
                    Term::Long
                }
                (_, Some(_), Some(_)) => Term::Short,
                _ => Term::Unknown,
            };
            Some(Disposal {
                sold: g.sale_date,
                account: g.account.to_string(),
                commodity: g.currency.to_string(),
                units: g.units,
                acquired: g.acquired_date,
                held_days,
                term,
                proceeds: g.proceeds.number,
                cost_basis: g.cost_basis.number,
                gain: g.proceeds.number - g.cost_basis.number,
                currency: g.cost_basis.currency.to_string(),
                short_sale: g.short_sale,
                irr: None,
            })
        })
        .collect();
    (rows, cross_currency)
}

/// Classify a holding period as long-term.
///
/// `long_term_days = Some(n)`: held strictly more than `n` days (`held_days` is the
/// already-computed `sold − acquired` span, so this reuses it rather than
/// recomputing). `None`: the calendar rule — the sale is more than one calendar year
/// after acquisition. The calendar rule is leap-year correct (jiff anniversaries a
/// Feb-29 acquisition to Feb-28), which a fixed 365-day count is not: a one-year
/// holding spanning a leap day is 366 days and a raw `> 365` test would wrongly call
/// it long-term.
fn is_long_term(
    acquired: NaiveDate,
    sold: NaiveDate,
    held_days: Option<i64>,
    long_term_days: Option<i64>,
) -> bool {
    match long_term_days {
        Some(n) => held_days.is_some_and(|d| d > n),
        None => acquired
            .checked_add(jiff::Span::new().years(1))
            .is_ok_and(|one_year| sold > one_year),
    }
}

/// Filters applied to the collected disposals before rendering.
pub(super) struct CapgainsFilter<'a> {
    /// Only disposals from accounts under this prefix.
    pub account: Option<&'a str>,
    /// Only disposals in this calendar year.
    pub year: Option<i32>,
    /// Exclude disposals after this date (the horizon).
    pub end: Option<NaiveDate>,
}

/// Generate the capital-gains report.
///
/// `gains` are the loader's canonical realized gains (`Ledger::capital_gains`).
/// `long_term_days` is the holding-period threshold: `None` uses the calendar
/// "> 1 year" rule (leap-year correct), `Some(n)` a fixed day count. `with_irr`
/// adds the annualized realized-return columns (see the module docs).
///
/// # Errors
/// Propagates writer I/O errors.
pub(super) fn report_capgains<W: Write>(
    gains: &[CapitalGain],
    filter: &CapgainsFilter,
    long_term_days: Option<i64>,
    with_irr: bool,
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
    warnings: &mut dyn super::Diagnostics,
) -> Result<()> {
    let (disposals, cross_currency) = to_disposals(gains, long_term_days);
    // A cross-currency disposal (sale price in a different currency than the lot's
    // cost basis) has no gain without an FX rate, so it is dropped from the rows.
    // Surface the count on stderr rather than silently omitting it.
    if cross_currency > 0 {
        warnings.emit(super::Diagnostic::message(format!(
            "{cross_currency} cross-currency disposal(s) omitted (sale price \
             in a different currency than the cost basis; no FX conversion applied)"
        )));
    }
    let mut rows: Vec<Disposal> = disposals
        .into_iter()
        .filter(|d| {
            filter
                .account
                .is_none_or(|p| rustledger_core::is_subaccount_or_equal(&d.account, p))
                // `Date::year()` is `i16`; widen it to compare against the `i32`
                // filter without the lossy `i16::try_from(y)` (which silently
                // matched nothing for any year outside `i16`).
                && filter.year.is_none_or(|y| i32::from(d.sold.year()) == y)
                && filter.end.is_none_or(|e| d.sold <= e)
        })
        .collect();
    // Deterministic: by sale date, then account, then commodity.
    rows.sort_by(|a, b| {
        (a.sold, &a.account, &a.commodity).cmp(&(b.sold, &b.account, &b.commodity))
    });
    // Solve per-lot rates AFTER filtering: only rows that will actually be printed
    // cost a solver run.
    if with_irr {
        fill_lot_irr(&mut rows);
    }
    render(&rows, with_irr, ctx, format, writer)
}

/// Per-(currency, term) running totals for the summary.
#[derive(Default, Clone, Copy)]
struct Totals {
    proceeds: Decimal,
    cost_basis: Decimal,
    gain: Decimal,
    count: usize,
}

impl Totals {
    fn add(&mut self, d: &Disposal) {
        self.proceeds += d.proceeds;
        self.cost_basis += d.cost_basis;
        self.gain += d.gain;
        self.count += 1;
    }
}

fn render<W: Write>(
    rows: &[Disposal],
    with_irr: bool,
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    // TEXT is for humans, so it renders amounts through the ledger `DisplayContext`
    // (display precision, thousands separators). CSV and JSON are machine-readable,
    // so they emit the EXACT `Decimal` verbatim (via `Display`) — never the display
    // formatter, which would round to display precision and inject `render_commas`
    // separators, corrupting the exported figures.
    let money = |n: Decimal, ccy: &str| ctx.format_amount_number(n, ccy);
    // Summary: per currency, split short-term / long-term / unknown. Only the TEXT
    // and JSON renderers use these; the CSV renderer emits per-disposal rows only,
    // so skip the buckets entirely for it.
    let mut short: BTreeMap<String, Totals> = BTreeMap::new();
    let mut long: BTreeMap<String, Totals> = BTreeMap::new();
    let mut unknown: BTreeMap<String, Totals> = BTreeMap::new();
    if !matches!(format, OutputFormat::Csv) {
        for d in rows {
            let bucket = match d.term {
                Term::Short => &mut short,
                Term::Long => &mut long,
                Term::Unknown => &mut unknown,
            };
            bucket.entry(d.currency.clone()).or_default().add(d);
        }
    }

    match format {
        OutputFormat::Csv => {
            // The `irr` column appears only under `--irr`, so the default schema is
            // unchanged for existing consumers.
            writeln!(
                writer,
                "sold,account,commodity,units,acquired,held_days,term,currency,proceeds,cost_basis,gain{}",
                if with_irr { ",irr_pct" } else { "" }
            )?;
            for d in rows {
                // Raw `Decimal` (no separators, no rounding) for machine parsing.
                writeln!(
                    writer,
                    "{},{},{},{},{},{},{},{},{},{},{}{}",
                    d.sold,
                    csv_escape(&d.account),
                    csv_escape(&d.commodity),
                    d.units,
                    d.acquired.map_or_else(String::new, |a| a.to_string()),
                    d.held_days.map_or_else(String::new, |h| h.to_string()),
                    d.term.as_str(),
                    csv_escape(&d.currency),
                    d.proceeds,
                    d.cost_basis,
                    d.gain,
                    // 2-decimal percent (e.g. `10.42`), empty when undefined or
                    // beyond the reporting cap.
                    if with_irr {
                        format!(",{}", fmt_rate_machine(d.irr))
                    } else {
                        String::new()
                    },
                )?;
            }
        }
        OutputFormat::Json => {
            let obj = |d: &Disposal| {
                format!(
                    r#"{{"sold": "{}", "account": "{}", "commodity": "{}", "units": "{}", "acquired": {}, "held_days": {}, "term": "{}", "currency": "{}", "proceeds": "{}", "cost_basis": "{}", "gain": "{}"{}}}"#,
                    d.sold,
                    json_escape(&d.account),
                    json_escape(&d.commodity),
                    d.units,
                    d.acquired
                        .map_or_else(|| "null".to_string(), |a| format!("\"{a}\"")),
                    d.held_days
                        .map_or_else(|| "null".to_string(), |h| h.to_string()),
                    d.term.as_str(),
                    json_escape(&d.currency),
                    d.proceeds,
                    d.cost_basis,
                    d.gain,
                    // Numeric rate, or `null` when undefined; present only under
                    // `--irr` so the default schema is unchanged.
                    if with_irr {
                        format!(r#", "irr_pct": {}"#, rate_json(d.irr))
                    } else {
                        String::new()
                    },
                )
            };
            let disposals: Vec<String> = rows.iter().map(obj).collect();
            // Each term bucket carries the pooled IRR of that bucket's lots.
            let summ = |b: &BTreeMap<String, Totals>, term: Term| -> String {
                let parts: Vec<String> = b
                    .iter()
                    .map(|(c, t)| {
                        format!(
                            r#"{{"currency": "{}", "disposals": {}, "proceeds": "{}", "cost_basis": "{}", "gain": "{}"{}}}"#,
                            json_escape(c),
                            t.count,
                            t.proceeds,
                            t.cost_basis,
                            t.gain,
                            if with_irr {
                                {
                                    let p = aggregate_irr(rows, c, Some(term));
                                    format!(
                                        r#", "irr_pct": {}, "irr_lots": {}, "irr_lots_total": {}"#,
                                        rate_json(p.rate),
                                        p.eligible,
                                        p.total
                                    )
                                }
                            } else {
                                String::new()
                            },
                        )
                    })
                    .collect();
                format!("[{}]", parts.join(", "))
            };
            // Whole-report realized IRR per currency (all terms pooled).
            let totals_irr = if with_irr {
                let mut currencies: Vec<&String> = short
                    .keys()
                    .chain(long.keys())
                    .chain(unknown.keys())
                    .collect();
                currencies.sort_unstable();
                currencies.dedup();
                let parts: Vec<String> = currencies
                    .iter()
                    .map(|c| {
                        {
                            let p = aggregate_irr(rows, c, None);
                            format!(
                                r#"{{"currency": "{}", "irr_pct": {}, "irr_lots": {}, "irr_lots_total": {}}}"#,
                                json_escape(c),
                                rate_json(p.rate),
                                p.eligible,
                                p.total
                            )
                        }
                    })
                    .collect();
                format!(r#", "total_irr_pct": [{}]"#, parts.join(", "))
            } else {
                String::new()
            };
            writeln!(
                writer,
                r#"{{"disposals": [{}], "short_term": {}, "long_term": {}, "unknown_term": {}{}}}"#,
                disposals.join(", "),
                summ(&short, Term::Short),
                summ(&long, Term::Long),
                summ(&unknown, Term::Unknown),
                totals_irr,
            )?;
        }
        OutputFormat::Text => {
            // Wide enough for millions with thousands separators (e.g.
            // `1,500,000.00`) without the amount columns overflowing; the IRR
            // column adds its own width when shown.
            let rule: usize = if with_irr { 101 } else { 91 };
            // The trailing IRR cell, empty when the column is off.
            let irr_cell = |r: Option<f64>| {
                if with_irr {
                    format!("{:>10}", fmt_rate_cell(r))
                } else {
                    String::new()
                }
            };
            writeln!(writer, "Realized capital gains")?;
            writeln!(writer, "{}", "=".repeat(rule))?;
            writeln!(writer)?;
            if rows.is_empty() {
                writeln!(writer, "No realized disposals in range.")?;
                return Ok(());
            }
            writeln!(
                writer,
                "{:<11}{:<22}{:>10}{:<12}{:>6}{:>15}{:>15}{}",
                "Sold",
                "Commodity / account",
                "Units",
                "  Acquired",
                "Term",
                "Proceeds",
                "Gain",
                if with_irr {
                    format!("{:>10}", "IRR")
                } else {
                    String::new()
                },
            )?;
            writeln!(writer, "{}", "-".repeat(rule))?;
            for d in rows {
                writeln!(
                    writer,
                    "{:<11}{:<22}{:>10}{:<12}{:>6}{:>15}{:>15}{}",
                    // `Date` `Display` ignores fmt width flags, so stringify first
                    // to keep the columns aligned.
                    d.sold.to_string(),
                    truncate(
                        &format!("{} {}", d.commodity, short_account(&d.account)),
                        22
                    ),
                    money(d.units, &d.commodity),
                    d.acquired
                        .map_or_else(|| "  —".to_string(), |a| format!("  {a}")),
                    d.term.abbr(),
                    money(d.proceeds, &d.currency),
                    money(d.gain, &d.currency),
                    irr_cell(d.irr),
                )?;
            }
            writeln!(writer, "{}", "-".repeat(rule))?;
            // Per-currency short-term / long-term / unknown totals, then net.
            let mut currencies: Vec<&String> = short
                .keys()
                .chain(long.keys())
                .chain(unknown.keys())
                .collect();
            currencies.sort_unstable();
            currencies.dedup();
            for c in currencies {
                for (label, bucket, term) in [
                    ("Short-term", &short, Term::Short),
                    ("Long-term", &long, Term::Long),
                    ("Unknown-term", &unknown, Term::Unknown),
                ] {
                    if let Some(t) = bucket.get(c) {
                        writeln!(
                            writer,
                            "{label:<12}{:>3} disposals   proceeds {:>15}   gain {:>15} {c}{}",
                            t.count,
                            money(t.proceeds, c),
                            money(t.gain, c),
                            // The Unknown bucket is dateless by definition, so its
                            // pooled rate can never be defined — a permanent `n/a`
                            // there would be noise.
                            if with_irr && term != Term::Unknown {
                                format!("   IRR {}", aggregate_irr(rows, c, Some(term)).render())
                            } else {
                                String::new()
                            },
                        )?;
                    }
                }
                let net = short.get(c).map(|t| t.gain).unwrap_or_default()
                    + long.get(c).map(|t| t.gain).unwrap_or_default()
                    + unknown.get(c).map(|t| t.gain).unwrap_or_default();
                writeln!(
                    writer,
                    "{:<12}net realized gain {:>15} {c}{}",
                    "TOTAL",
                    money(net, c),
                    if with_irr {
                        format!("   IRR {}", aggregate_irr(rows, c, None).render())
                    } else {
                        String::new()
                    },
                )?;
            }
        }
    }
    Ok(())
}

/// A rate for CSV: a 2-decimal **percent**, empty when undefined or beyond
/// [`RATE_REPORTING_CAP_PCT`].
///
/// Deliberately the same unit and precision as the sibling `returns` report's
/// `money_weighted_return_pct` (it shares [`fmt_rate`]): two reports emitting the
/// same conceptual metric 100x apart would be a scripting trap. The `_pct` column
/// name says the unit out loud.
fn fmt_rate_machine(rate: Option<f64>) -> String {
    match rate {
        Some(r) if rate_is_reportable(r) => fmt_rate(Some(r)),
        _ => String::new(),
    }
}

/// A rate for JSON: a 2-decimal percent number, or `null` when undefined or beyond
/// [`RATE_REPORTING_CAP_PCT`].
fn rate_json(rate: Option<f64>) -> String {
    match rate {
        Some(r) if rate_is_reportable(r) => json_rate(Some(r)),
        _ => "null".to_string(),
    }
}

/// Rates above this magnitude (percent) are not reported as a number.
///
/// An annualized rate is unbounded above: a one-day round trip compounds its gain
/// 365 times, so a +20% day reaches ~8e30 %/yr. Such a figure is arithmetically
/// true but financially meaningless, and printing it breaks both surfaces — it
/// overflows the fixed-width text column, and at ~31 significant digits it exceeds
/// what `rust_decimal` (this project's own numeric type, ~28-29 digits) can parse
/// back. So past this cap the text cell shows `>9999%` and machine output is empty
/// / `null`: no fabricated precision, and nothing a consumer cannot read.
///
/// There is no lower cap: a round trip cannot lose more than its basis, so no rate
/// is below -100%.
const RATE_REPORTING_CAP_PCT: f64 = 9999.0;

/// Whether a rate is small enough to report as a number.
fn rate_is_reportable(r: f64) -> bool {
    r * 100.0 <= RATE_REPORTING_CAP_PCT
}

/// A rate for the fixed-width text column: [`fmt_rate_pct`], but an
/// unreportably-large rate becomes `>9999%` so it cannot break the table layout.
fn fmt_rate_cell(rate: Option<f64>) -> String {
    match rate {
        Some(r) if !rate_is_reportable(r) => format!(">{RATE_REPORTING_CAP_PCT:.0}%"),
        other => fmt_rate_pct(other),
    }
}

/// The leaf of an account path (`Assets:Broker:AAPL` -> `AAPL`), for the compact
/// text column.
fn short_account(account: &str) -> &str {
    account.rsplit(':').next().unwrap_or(account)
}

/// Truncate to a column width, keeping the informative head.
fn truncate(s: &str, width: usize) -> String {
    if s.chars().count() <= width {
        s.to_string()
    } else {
        let head: String = s.chars().take(width.saturating_sub(1)).collect();
        format!("{head}…")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_core::{Amount, naive_date};

    fn d(y: i32, m: u32, day: u32) -> NaiveDate {
        naive_date(y, m, day).unwrap()
    }

    fn money(n: i64, ccy: &str) -> Amount {
        Amount::new(Decimal::from(n), ccy)
    }

    /// Build a canonical `CapitalGain` (as the loader would hand the report),
    /// denominated in USD on commodity AAPL.
    #[allow(clippy::too_many_arguments)]
    fn gain(
        account: &str,
        sale: NaiveDate,
        acquired: Option<NaiveDate>,
        units: i64,
        basis: i64,
        proceeds: i64,
        short_sale: bool,
    ) -> CapitalGain {
        CapitalGain {
            account: account.into(),
            currency: "AAPL".into(),
            units: Decimal::from(units),
            cost_basis: money(basis, "USD"),
            proceeds: money(proceeds, "USD"),
            sale_date: sale,
            acquired_date: acquired,
            short_sale,
        }
    }

    /// Whole days between two dates (the `held_days` the report computes).
    fn held(a: NaiveDate, s: NaiveDate) -> Option<i64> {
        a.until((jiff::Unit::Day, s))
            .ok()
            .map(|sp| i64::from(sp.get_days()))
    }

    /// `to_disposals` classifies the holding period: a short sale is always short;
    /// a lot with no acquisition date is unknown; otherwise the threshold decides.
    #[test]
    fn to_disposals_classifies_term() {
        let gains = vec![
            gain(
                "Assets:Broker:Stock",
                d(2024, 1, 1),
                Some(d(2020, 1, 1)),
                5,
                500,
                750,
                false,
            ),
            gain(
                "Assets:Broker:Stock",
                d(2024, 1, 1),
                Some(d(2023, 12, 1)),
                5,
                500,
                600,
                false,
            ),
            gain(
                "Assets:Broker:Stock",
                d(2024, 1, 1),
                None,
                6,
                690,
                900,
                false,
            ),
            gain(
                "Assets:Broker:Stock",
                d(2024, 1, 1),
                Some(d(2020, 1, 1)),
                5,
                400,
                500,
                true,
            ),
        ];
        let (ds, cross) = to_disposals(&gains, None);
        assert_eq!(cross, 0);
        assert_eq!(ds[0].term.as_str(), "long"); // held ~4 years
        assert_eq!(ds[1].term.as_str(), "short"); // held ~1 month
        assert_eq!(ds[2].term.as_str(), "unknown"); // no acquisition date
        assert_eq!(ds[3].term.as_str(), "short"); // short sale, always short
        // A dateless lot has no held_days; a short still shows its span.
        assert_eq!(ds[2].held_days, None);
        assert_eq!(ds[3].held_days, held(d(2020, 1, 1), d(2024, 1, 1)));
    }

    /// A lot "acquired" AFTER the sale (a future-dated cost — invalid data) has an
    /// undeterminable holding period: classified `unknown`, never silently `short`.
    #[test]
    fn future_dated_acquisition_is_unknown_not_short() {
        let g = gain(
            "Assets:Broker:Stock",
            d(2020, 1, 1),       // sold
            Some(d(2021, 1, 1)), // "acquired" a year AFTER the sale
            5,
            400,
            500,
            false,
        );
        let (ds, _) = to_disposals(&[g], None);
        assert_eq!(ds[0].term.as_str(), "unknown");
        assert_eq!(ds[0].held_days, None, "negative span dropped");
    }

    /// Per-lot rates annualize the round trip, and the pooled rate is a genuine
    /// money-weighted solve over both lots' flows.
    ///
    /// The fixture deliberately avoids a 10% rate: `xirr` seeds Newton at exactly
    /// 0.10, so a 10% fixture can be satisfied by the seed at iteration 0 and would
    /// not prove the solver searched. The two lots also carry DIFFERENT rates so an
    /// assertion cannot pass by matching the wrong lot. Expected values are from an
    /// independent bisection XIRR over the same flows.
    #[test]
    fn per_lot_irr_annualizes_the_round_trip() {
        let gains = vec![
            // 365 days: 1000 -> 1250 = 25%/yr.
            gain(
                "Assets:Broker:Stock",
                d(2020, 12, 31),
                Some(d(2020, 1, 1)),
                10,
                1000,
                1250,
                false,
            ),
            // 730 days: 1000 -> 1440 = 1.44x over 2y = 20%/yr compounded.
            gain(
                "Assets:Broker:Stock",
                d(2021, 12, 31),
                Some(d(2020, 1, 1)),
                10,
                1000,
                1440,
                false,
            ),
        ];
        let (mut ds, _) = to_disposals(&gains, None);
        fill_lot_irr(&mut ds);
        let near = |r: Option<f64>, want: f64| (r.expect("defined rate") - want).abs() < 1e-4;
        assert!(near(ds[0].irr, 0.25), "one-year 25% gain: {:?}", ds[0].irr);
        assert!(
            near(ds[1].irr, 0.20),
            "two-year 44% gain -> 20%/yr compounded: {:?}",
            ds[1].irr
        );
        // Pooled: a single money-weighted solve over all four flows — NOT the mean
        // of 25% and 20% (which would be 22.5%).
        let pooled = aggregate_irr(&ds, "USD", None);
        assert!(
            near(pooled.rate, 0.216_743),
            "pooled money-weighted rate: {:?}",
            pooled.rate
        );
        assert_eq!(
            (pooled.eligible, pooled.total),
            (2, 2),
            "both lots eligible"
        );
    }

    /// Hermetic coverage of the `--irr` RENDER paths (CSV header + cell, JSON
    /// fields, text column + pooled line). The end-to-end tests exercise the real
    /// binary but skip when it is absent, so these run everywhere.
    #[test]
    fn irr_render_paths_are_covered_in_process() {
        let gains = vec![
            // 365 days, 1000 -> 1250 = 25%/yr.
            gain(
                "Assets:Broker:Stock",
                d(2020, 12, 31),
                Some(d(2020, 1, 1)),
                10,
                1000,
                1250,
                false,
            ),
            // A short sale: no defined rate, so it renders empty/null/n-a.
            gain(
                "Assets:Broker:Stock",
                d(2020, 12, 31),
                Some(d(2020, 1, 1)),
                5,
                400,
                500,
                true,
            ),
        ];
        let ctx = DisplayContext::new();
        let filter = CapgainsFilter {
            account: None,
            year: None,
            end: None,
        };
        let render_as = |f: &OutputFormat| {
            let mut buf = Vec::new();
            report_capgains(
                &gains,
                &filter,
                None,
                true,
                &ctx,
                f,
                &mut buf,
                &mut crate::cmd::report_cmd::CollectedDiagnostics::default(),
            )
            .unwrap();
            String::from_utf8(buf).unwrap()
        };

        let csv = render_as(&OutputFormat::Csv);
        assert!(csv.lines().next().unwrap().ends_with(",irr_pct"));
        // The priced lot carries a percent rate; the short sale's cell is empty.
        // (Both are term=short here: a 365-day hold across the 2020 leap day is not
        // yet more than one calendar year.)
        let rows: Vec<&str> = csv.lines().skip(1).collect();
        assert_eq!(rows.len(), 2, "two disposal rows: {csv}");
        assert!(
            rows.iter().any(|l| l.ends_with(",25.00")),
            "priced lot's percent rate: {csv}"
        );
        let short_row = rows
            .iter()
            .find(|l| l.contains(",Assets:Broker:Stock,AAPL,5,"))
            .expect("the short-sale row");
        let cols: Vec<&str> = short_row.split(',').collect();
        assert_eq!(cols.len(), 12, "all columns present: {short_row}");
        assert_eq!(cols[11], "", "short sale's rate cell is empty: {short_row}");

        let json = render_as(&OutputFormat::Json);
        assert!(json.contains(r#""irr_pct": 25.00"#), "{json}");
        assert!(
            json.contains(r#""irr_pct": null"#),
            "short sale is null: {json}"
        );
        assert!(json.contains(r#""total_irr_pct""#), "{json}");
        assert!(
            json.contains(r#""irr_lots": 1"#),
            "coverage in JSON: {json}"
        );

        let txt = render_as(&OutputFormat::Text);
        assert!(txt.contains("IRR"), "column header: {txt}");
        assert!(txt.contains("25.00%"), "rate cell: {txt}");
        assert!(txt.contains("n/a"), "undefined cell: {txt}");
        assert!(
            txt.contains("(1 of 2 lots)"),
            "pooled coverage annotated: {txt}"
        );
    }

    /// A rate too large to report (a one-day round trip annualizes past the cap)
    /// shows `>9999%` in text and is EMPTY/`null` in machine output — never a
    /// 31-digit number that this project's own `Decimal` could not parse back.
    #[test]
    fn unreportably_large_rate_is_capped_in_text_and_omitted_in_machine_output() {
        // 1 day, 1000 -> 1200: annualizes to ~8e30.
        let huge = gain(
            "Assets:Broker:Stock",
            d(2020, 1, 2),
            Some(d(2020, 1, 1)),
            10,
            1000,
            1200,
            false,
        );
        let (mut ds, _) = to_disposals(&[huge], None);
        fill_lot_irr(&mut ds);
        let r = ds[0].irr.expect("a (huge) rate is solved");
        assert!(r > 1e20, "sanity: the rate really is astronomic: {r}");
        assert!(!rate_is_reportable(r));
        assert_eq!(fmt_rate_cell(Some(r)), ">9999%");
        assert_eq!(fmt_rate_machine(Some(r)), "", "CSV cell is empty");
        assert_eq!(rate_json(Some(r)), "null", "JSON is null");
        // A normal rate is unaffected by the cap.
        assert_eq!(fmt_rate_machine(Some(0.25)), "25.00");
        assert_eq!(rate_json(Some(0.25)), "25.00");
        assert_eq!(fmt_rate_cell(Some(0.25)), "25.00%");
    }

    /// A bucket whose lots are ALL total losses reports -100%, not `n/a`: the
    /// pooled series has no inflow to bracket, but the answer is not unknown, and a
    /// summary line must never contradict the single row it summarizes.
    #[test]
    fn all_total_loss_bucket_agrees_with_its_rows() {
        let gains = vec![gain(
            "Assets:Broker:Stock",
            d(2020, 6, 1),
            Some(d(2020, 1, 1)),
            10,
            1000,
            0,
            false,
        )];
        let (mut ds, _) = to_disposals(&gains, None);
        fill_lot_irr(&mut ds);
        assert_eq!(ds[0].irr, Some(-1.0), "the row is -100%");
        let pooled = aggregate_irr(&ds, "USD", None);
        assert_eq!(
            pooled.rate,
            Some(-1.0),
            "the bucket must not read n/a while its only row reads -100%"
        );
        assert_eq!((pooled.eligible, pooled.total), (1, 1));
    }

    /// A total loss is the exact -100% pole, not `n/a` — and it stays in the pool,
    /// so the pooled rate cannot be flattered by hiding capital that never returned.
    #[test]
    fn total_loss_is_minus_one_hundred_percent_and_stays_pooled() {
        let gains = vec![
            gain(
                "Assets:Broker:Stock",
                d(2020, 12, 31),
                Some(d(2020, 1, 1)),
                10,
                1000,
                1100,
                false,
            ),
            // Worthless: proceeds 0.
            gain(
                "Assets:Broker:Stock",
                d(2020, 12, 31),
                Some(d(2020, 1, 1)),
                10,
                1000,
                0,
                false,
            ),
        ];
        let (mut ds, _) = to_disposals(&gains, None);
        fill_lot_irr(&mut ds);
        let writeoff = ds.iter().find(|d| d.proceeds.is_zero()).expect("writeoff");
        assert_eq!(writeoff.irr, Some(-1.0), "total loss is exactly -100%");
        let pooled = aggregate_irr(&ds, "USD", None);
        assert_eq!(
            (pooled.eligible, pooled.total),
            (2, 2),
            "the write-off is pooled, not silently dropped"
        );
        // Independently: -1000 and -1000 out, +1100 back over one year => -45%.
        assert!(
            (pooled.rate.expect("rate") + 0.45).abs() < 1e-4,
            "pooled: {:?}",
            pooled.rate
        );
    }

    /// IRR is opt-in: `to_disposals` alone never computes a rate.
    #[test]
    fn per_lot_irr_is_not_computed_unless_requested() {
        let gains = vec![gain(
            "Assets:Broker:Stock",
            d(2020, 12, 31),
            Some(d(2020, 1, 1)),
            10,
            1000,
            1250,
            false,
        )];
        let (ds, _) = to_disposals(&gains, None);
        assert_eq!(ds[0].irr, None, "no IRR unless the --irr pass runs");
    }

    /// The undefined cases render `n/a` and are excluded from the pooled aggregate:
    /// a same-day round trip, a dateless (AVERAGE-cost) lot, and a short sale.
    #[test]
    fn irr_is_undefined_for_same_day_dateless_and_short_lots() {
        let gains = vec![
            // Same-day: zero-day span.
            gain(
                "Assets:Broker:Stock",
                d(2020, 1, 1),
                Some(d(2020, 1, 1)),
                10,
                100,
                120,
                false,
            ),
            // Dateless (AVERAGE cost).
            gain(
                "Assets:Broker:Stock",
                d(2020, 6, 1),
                None,
                6,
                690,
                900,
                false,
            ),
            // Short sale.
            gain(
                "Assets:Broker:Stock",
                d(2021, 6, 1),
                Some(d(2020, 1, 1)),
                5,
                400,
                500,
                true,
            ),
        ];
        let (mut ds, _) = to_disposals(&gains, None);
        fill_lot_irr(&mut ds);
        assert!(ds.iter().all(|d| d.irr.is_none()), "all three undefined");
        assert!(
            ds.iter().all(|d| lot_flows(d).is_none()),
            "none contribute flows"
        );
        let pooled = aggregate_irr(&ds, "USD", None);
        assert_eq!(pooled.rate, None, "no eligible lot -> no pooled rate");
        assert_eq!(
            (pooled.eligible, pooled.total),
            (0, 3),
            "coverage is reported so the rate is never read as covering all 3"
        );
    }

    /// A cross-currency disposal (proceeds and basis in different currencies) is
    /// dropped from the rows and counted, so the caller can warn.
    #[test]
    fn cross_currency_disposal_is_dropped_and_counted() {
        let same = gain(
            "Assets:Broker:Stock",
            d(2024, 1, 1),
            Some(d(2020, 1, 1)),
            5,
            500,
            750,
            false,
        );
        let cross = CapitalGain {
            account: "Assets:Broker:Stock".into(),
            currency: "AAPL".into(),
            units: Decimal::from(3),
            cost_basis: money(270, "EUR"),
            proceeds: money(450, "USD"), // different currency than the basis
            sale_date: d(2024, 1, 1),
            acquired_date: Some(d(2020, 1, 1)),
            short_sale: false,
        };
        let (ds, cross_count) = to_disposals(&[same, cross], None);
        assert_eq!(ds.len(), 1, "only the same-currency disposal is kept");
        assert_eq!(cross_count, 1, "the cross-currency disposal is counted");
        assert_eq!(ds[0].gain, Decimal::from(250));
    }

    #[test]
    fn short_account_returns_leaf() {
        assert_eq!(short_account("Assets:Broker:AAPL"), "AAPL");
        assert_eq!(short_account("Cash"), "Cash");
    }

    #[test]
    fn truncate_keeps_head_and_marks_elision() {
        assert_eq!(truncate("abc", 5), "abc"); // shorter than width: unchanged
        assert_eq!(truncate("abcde", 5), "abcde"); // exactly width: unchanged
        assert_eq!(truncate("abcdef", 5), "abcd…"); // over width: head + ellipsis
    }

    /// The calendar long-term rule is leap-year correct: a holding from Jan 1 2020
    /// (a leap year) to Jan 1 2021 is 366 days but NOT more than one calendar year,
    /// so it is short-term — where a raw `> 365` day count would wrongly say long.
    /// A lot ACQUIRED on 29 February has no anniversary in a common year, and
    /// the rule resolves it to 28 February — so long-term begins 1 March.
    ///
    /// This pins a `jiff` behavior, not ours. The module comment states it
    /// ("jiff anniversaries a Feb-29 acquisition to Feb-28") and the whole
    /// short/long split for such a lot rests on it, but nothing checked it:
    /// `long_term_calendar_rule_handles_leap_year` uses a span that CROSSES a
    /// leap day, which is a different thing from a lot bought ON one. If a
    /// future jiff resolved the anniversary to 1 March instead, the boundary
    /// would move a day and every affected disposal would silently change
    /// term — on a figure that goes to a tax return.
    ///
    /// The convention itself is genuinely arguable; this test records which
    /// one we implement, so changing it has to be deliberate.
    #[test]
    fn long_term_rule_resolves_a_leap_day_acquisition_to_feb_28() {
        let acquired = d(2020, 2, 29);
        for (sold, want, why) in [
            (
                d(2021, 2, 28),
                false,
                "365d, the resolved anniversary itself",
            ),
            (d(2021, 3, 1), true, "366d, the first day past it"),
        ] {
            assert_eq!(
                is_long_term(acquired, sold, held(acquired, sold), None),
                want,
                "2020-02-29 -> {sold}: {why}",
            );
        }
    }

    #[test]
    fn long_term_calendar_rule_handles_leap_year() {
        // Exactly one year later — 366 days across the 2020 leap day.
        assert!(
            !is_long_term(
                d(2020, 1, 1),
                d(2021, 1, 1),
                held(d(2020, 1, 1), d(2021, 1, 1)),
                None
            ),
            "exactly one year is NOT long-term (need > 1 year)"
        );
        // One day past the anniversary is long-term.
        assert!(is_long_term(
            d(2020, 1, 1),
            d(2021, 1, 2),
            held(d(2020, 1, 1), d(2021, 1, 2)),
            None
        ));
        // A fixed 365-day override, by contrast, calls the 366-day span long-term.
        assert!(is_long_term(
            d(2020, 1, 1),
            d(2021, 1, 1),
            held(d(2020, 1, 1), d(2021, 1, 1)),
            Some(365)
        ));
    }

    /// `--long-term-days N` overrides the calendar rule with a fixed day count.
    #[test]
    fn long_term_days_override() {
        assert!(is_long_term(
            d(2020, 1, 1),
            d(2020, 3, 1),
            held(d(2020, 1, 1), d(2020, 3, 1)),
            Some(30)
        ));
        assert!(!is_long_term(
            d(2020, 1, 1),
            d(2020, 1, 20),
            held(d(2020, 1, 1), d(2020, 1, 20)),
            Some(30)
        ));
        // Boundary: held EXACTLY the threshold is NOT long (strictly more than N).
        assert_eq!(held(d(2020, 1, 1), d(2020, 1, 31)), Some(30));
        assert!(!is_long_term(
            d(2020, 1, 1),
            d(2020, 1, 31),
            Some(30),
            Some(30)
        ));
    }

    fn csv(gains: &[CapitalGain], filter: &CapgainsFilter) -> String {
        let ctx = DisplayContext::new();
        let mut buf = Vec::new();
        report_capgains(
            gains,
            filter,
            None,
            false,
            &ctx,
            &OutputFormat::Csv,
            &mut buf,
            &mut crate::cmd::report_cmd::CollectedDiagnostics::default(),
        )
        .unwrap();
        String::from_utf8(buf).unwrap()
    }

    /// The `--year` filter compares the full `i32` year (no lossy `i16::try_from`).
    #[test]
    fn year_filter_matches_the_right_year() {
        let gains = vec![gain(
            "Assets:Broker:Stock",
            d(2021, 6, 1),
            Some(d(2020, 1, 1)),
            4,
            400,
            600,
            false,
        )];
        let f = |year| CapgainsFilter {
            account: None,
            year,
            end: None,
        };
        assert!(csv(&gains, &f(Some(2021))).lines().count() > 1);
        assert_eq!(
            csv(&gains, &f(Some(2020))).lines().count(),
            1,
            "header only"
        );
        assert!(csv(&gains, &f(None)).lines().count() > 1);
    }

    /// The account filter keeps only disposals under the given prefix.
    #[test]
    fn account_filter_scopes_by_prefix() {
        let gains = vec![gain(
            "Assets:Broker:Stock",
            d(2020, 6, 1),
            Some(d(2020, 1, 1)),
            4,
            400,
            600,
            false,
        )];
        let f = |account| CapgainsFilter {
            account,
            year: None,
            end: None,
        };
        assert!(csv(&gains, &f(Some("Assets:Broker"))).lines().count() > 1);
        assert_eq!(csv(&gains, &f(Some("Assets:Other"))).lines().count(), 1);
    }

    /// The text renderer emits a header, a data row, and the term summary.
    #[test]
    fn text_render_smoke() {
        let gains = vec![gain(
            "Assets:Broker:Stock",
            d(2022, 6, 1),
            Some(d(2020, 1, 1)),
            4,
            400,
            600,
            false,
        )];
        let ctx = DisplayContext::new();
        let filter = CapgainsFilter {
            account: None,
            year: None,
            end: None,
        };
        let mut buf = Vec::new();
        report_capgains(
            &gains,
            &filter,
            None,
            false,
            &ctx,
            &OutputFormat::Text,
            &mut buf,
            &mut crate::cmd::report_cmd::CollectedDiagnostics::default(),
        )
        .unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(out.contains("Realized capital gains"));
        assert!(out.contains("AAPL"));
        assert!(
            out.contains("Long-term"),
            "held > 1 year → long-term summary"
        );
        assert!(out.contains("net realized gain"));
    }

    /// The net total sums ALL three term buckets (short + long + unknown). Distinct
    /// non-zero gains in each bucket pin the summation so no `+` can be flipped
    /// without changing the printed net (127 = 100 + 20 + 7).
    #[test]
    fn text_net_sums_all_term_buckets() {
        let gains = vec![
            // Long: held > 1 year, gain 100.
            gain(
                "Assets:Broker:Stock",
                d(2024, 1, 1),
                Some(d(2020, 1, 1)),
                1,
                400,
                500,
                false,
            ),
            // Short: short sale, gain 20.
            gain(
                "Assets:Broker:Stock",
                d(2024, 1, 1),
                Some(d(2023, 12, 1)),
                1,
                400,
                420,
                true,
            ),
            // Unknown: no acquisition date, gain 7.
            gain(
                "Assets:Broker:Stock",
                d(2024, 1, 1),
                None,
                1,
                100,
                107,
                false,
            ),
        ];
        let ctx = DisplayContext::new();
        let filter = CapgainsFilter {
            account: None,
            year: None,
            end: None,
        };
        let mut buf = Vec::new();
        report_capgains(
            &gains,
            &filter,
            None,
            false,
            &ctx,
            &OutputFormat::Text,
            &mut buf,
            &mut crate::cmd::report_cmd::CollectedDiagnostics::default(),
        )
        .unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(
            out.contains("Short-term") && out.contains("Long-term") && out.contains("Unknown-term")
        );
        // Net = 100 + 20 + 7 = 127 (any dropped/negated bucket changes this).
        let net_line = out
            .lines()
            .find(|l| l.starts_with("TOTAL"))
            .expect("net line");
        assert!(net_line.contains("127 USD"), "net line: {net_line}");
    }
}
