//! Realized capital-gains / tax-lot report.
//!
//! Where `report holdings` shows what you still HOLD, this shows what you SOLD:
//! one row per disposed tax lot, classified short vs long term by holding period,
//! with proceeds, cost basis, and realized gain/loss, plus per-term and
//! per-currency summaries.
//!
//! It consumes [`rustledger_booking::CapitalGain`] — the canonical, per-lot
//! realized gain the booking engine computes when it matches a reduction against
//! its lots — so it cannot drift from the engine's lot-matching (a sale crossing
//! several lots is already one `CapitalGain` per lot, each with its own
//! acquisition date).
//!
//! It runs its own [`BookingEngine`] over the **pre-booking parsed stream**, in
//! booking order (`book` then `apply` per transaction, exactly like the loader's
//! own pass). The parsed stream is used deliberately rather than the loader's
//! stored directives: the stored stream has already expanded multi-lot reductions
//! and normalized `@@` total prices to per-unit (dividing the total by each
//! expanded posting's units), which is lossy for total-price sale proceeds —
//! re-booking it would over-count. Booking the parsed stream instead lets `book`
//! observe each sale's original `@@`/`@` price and record exact proceeds.
//!
//! **Short positions** are reported when covered: the lot's cost is the price the
//! units were sold at when the short was opened, so proceeds are the short-open
//! value and cost basis is the cover cost (the mirror of a long disposal), and the
//! gain is always short-term (the US rule). **Unknown holding period**: a lot with
//! no acquisition date — e.g. under `AVERAGE` booking, which merges lots and drops
//! their dates — is classified `unknown`, not silently `short`.
//!
//! Gains are reported in each lot's **cost currency**; a multi-currency ledger is
//! summarized per currency. Not a tax filing: wash-sale adjustment, currency-gain
//! separation, lots seeded by `pad` (no well-defined cost basis), and jurisdiction
//! rules beyond the long-term threshold are out of scope (run `rledger check` to
//! validate the ledger first).

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::Result;
use rust_decimal::Decimal;
use rustledger_booking::BookingEngine;
use rustledger_core::{BookingMethod, Directive, DisplayContext, NaiveDate};
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
}

/// Book `directives` (the pre-booking parsed stream) in booking order and collect
/// one [`Disposal`] per matched lot.
///
/// `long_term_days` is the holding-period threshold: `Some(n)` classifies a lot
/// held strictly more than `n` days as long-term; `None` uses the leap-year-safe
/// calendar rule (long-term when the sale is more than one calendar year after
/// acquisition).
///
/// Each transaction is `book`ed (which computes the per-lot gains against the
/// current inventory) then `apply`ed (which accumulates the lots) — the same
/// two-step the loader (`run_booking`) and `rustledger_booking::book_transactions`
/// use. This deliberately re-derives that loop rather than calling the canonical
/// `book`/`book_transactions` free functions, because they return only the booked
/// directives and DROP the per-lot [`rustledger_booking::CapitalGain`]s this report
/// exists to surface — the gains are reachable only via `BookingEngine::book`
/// directly. To stay faithful to `rledger check`, this loop mirrors the loader
/// exactly: the ledger's own booking method (below), canonical + booking-order
/// sorting (the caller canonical-sorts; this sorts by `booking_sort_key`), and
/// `interpolate`-then-`apply`. The end-to-end tests exercise the real binary path.
///
/// Transactions are visited in booking order (`booking_sort_key`) so a same-date
/// sell never books before the buy that seeds its lot. A transaction that fails to
/// book (an un-booked ledger; `rledger check` flags it) is skipped rather than
/// aborting the whole report.
fn collect_disposals(
    directives: &[Directive],
    method: BookingMethod,
    long_term_days: Option<i64>,
) -> Vec<Disposal> {
    // Use the ledger's OWN booking method (not `BookingEngine::new`'s FIFO
    // default) so the report's lot-matching matches `rledger check`: a ledger
    // booked Strict where a bare-`{}` sale is ambiguous must fail to book here
    // too, rather than the report silently FIFO-matching a gain the ledger rejects.
    let mut engine = BookingEngine::with_method(method);
    engine.register_account_methods(directives.iter());

    // Visit in booking order — sells after the same-date buys that seed their
    // lots — while leaving `directives` itself untouched (a stable index sort,
    // mirroring `rustledger_booking::book`).
    let mut order: Vec<usize> = (0..directives.len()).collect();
    order.sort_by_key(|&i| rustledger_core::booking_sort_key(&directives[i]));

    let mut out = Vec::new();
    for &i in &order {
        let Directive::Transaction(txn) = &directives[i] else {
            continue;
        };
        // `book` computes the per-lot gains against the CURRENT inventory but does
        // NOT mutate it.
        let Ok(booked) = engine.book(txn) else {
            continue;
        };
        for g in &booked.gains {
            let held_days = g
                .acquired_date
                .and_then(|a| a.until((jiff::Unit::Day, txn.date)).ok())
                .map(|s| i64::from(s.get_days()));
            // Short-sale gains are always short-term (US rule); otherwise a lot with
            // no acquisition date has an unknown holding period; otherwise apply the
            // threshold.
            let term = if g.short_sale {
                Term::Short
            } else {
                match g.acquired_date {
                    None => Term::Unknown,
                    Some(a) if is_long_term(a, txn.date, held_days, long_term_days) => Term::Long,
                    Some(_) => Term::Short,
                }
            };
            out.push(Disposal {
                sold: txn.date,
                account: g.account.to_string(),
                commodity: g.currency.to_string(),
                units: g.units,
                acquired: g.acquired_date,
                held_days,
                term,
                proceeds: g.proceeds.number,
                cost_basis: g.cost_basis.number,
                gain: g.amount.number,
                currency: g.amount.currency.to_string(),
            });
        }
        // Accumulate inventory. Interpolate first (fills elided legs) to mirror the
        // loader's `book_and_interpolate` → `apply` pipeline; if interpolation fails,
        // fall back to the booked transaction so a lot with explicit units still
        // enters inventory and a later sale can match it — never silently drop a lot
        // from an otherwise `rledger check`-clean ledger.
        let applied = match rustledger_booking::interpolate(&booked.transaction) {
            Ok(interp) => interp.transaction,
            Err(_) => booked.transaction,
        };
        engine.apply(&applied);
    }
    out
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
/// `directives` must be the PRE-booking parsed stream (the dispatcher passes
/// `loaded.parsed_directives`); [`collect_disposals`] books it itself.
/// `long_term_days` is the holding-period threshold: `None` uses the calendar
/// "> 1 year" rule (leap-year correct), `Some(n)` a fixed day count.
///
/// # Errors
/// Propagates writer I/O errors.
pub(super) fn report_capgains<W: Write>(
    directives: &[Directive],
    filter: &CapgainsFilter,
    long_term_days: Option<i64>,
    method: BookingMethod,
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let mut rows: Vec<Disposal> = collect_disposals(directives, method, long_term_days)
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
    render(&rows, ctx, format, writer)
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
    // Summary: per currency, split short-term / long-term / unknown.
    let mut short: BTreeMap<String, Totals> = BTreeMap::new();
    let mut long: BTreeMap<String, Totals> = BTreeMap::new();
    let mut unknown: BTreeMap<String, Totals> = BTreeMap::new();
    for d in rows {
        let bucket = match d.term {
            Term::Short => &mut short,
            Term::Long => &mut long,
            Term::Unknown => &mut unknown,
        };
        bucket.entry(d.currency.clone()).or_default().add(d);
    }

    match format {
        OutputFormat::Csv => {
            writeln!(
                writer,
                "sold,account,commodity,units,acquired,held_days,term,currency,proceeds,cost_basis,gain"
            )?;
            for d in rows {
                // Raw `Decimal` (no separators, no rounding) for machine parsing.
                writeln!(
                    writer,
                    "{},{},{},{},{},{},{},{},{},{},{}",
                    d.sold,
                    csv_escape(&d.account),
                    csv_escape(&d.commodity),
                    d.units,
                    d.acquired.map_or_else(String::new, |a| a.to_string()),
                    d.held_days.map_or_else(String::new, |h| h.to_string()),
                    d.term.as_str(),
                    d.currency,
                    d.proceeds,
                    d.cost_basis,
                    d.gain,
                )?;
            }
        }
        OutputFormat::Json => {
            let obj = |d: &Disposal| {
                format!(
                    r#"{{"sold": "{}", "account": "{}", "commodity": "{}", "units": "{}", "acquired": {}, "held_days": {}, "term": "{}", "currency": "{}", "proceeds": "{}", "cost_basis": "{}", "gain": "{}"}}"#,
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
                )
            };
            let disposals: Vec<String> = rows.iter().map(obj).collect();
            let summ = |b: &BTreeMap<String, Totals>| -> String {
                let parts: Vec<String> = b
                    .iter()
                    .map(|(c, t)| {
                        format!(
                            r#"{{"currency": "{}", "disposals": {}, "proceeds": "{}", "cost_basis": "{}", "gain": "{}"}}"#,
                            json_escape(c),
                            t.count,
                            t.proceeds,
                            t.cost_basis,
                            t.gain,
                        )
                    })
                    .collect();
                format!("[{}]", parts.join(", "))
            };
            writeln!(
                writer,
                r#"{{"disposals": [{}], "short_term": {}, "long_term": {}, "unknown_term": {}}}"#,
                disposals.join(", "),
                summ(&short),
                summ(&long),
                summ(&unknown),
            )?;
        }
        OutputFormat::Text => {
            const RULE: usize = 79;
            writeln!(writer, "Realized capital gains")?;
            writeln!(writer, "{}", "=".repeat(RULE))?;
            writeln!(writer)?;
            if rows.is_empty() {
                writeln!(writer, "No realized disposals in range.")?;
                return Ok(());
            }
            writeln!(
                writer,
                "{:<11}{:<22}{:>8}{:<12}{:>6}{:>11}{:>11}",
                "Sold", "Commodity / account", "Units", "  Acquired", "Term", "Proceeds", "Gain"
            )?;
            writeln!(writer, "{}", "-".repeat(RULE))?;
            for d in rows {
                writeln!(
                    writer,
                    "{:<11}{:<22}{:>8}{:<12}{:>6}{:>11}{:>11}",
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
                )?;
            }
            writeln!(writer, "{}", "-".repeat(RULE))?;
            // Per-currency short-term / long-term / unknown totals, then net.
            let mut currencies: Vec<&String> = short
                .keys()
                .chain(long.keys())
                .chain(unknown.keys())
                .collect();
            currencies.sort_unstable();
            currencies.dedup();
            for c in currencies {
                for (label, bucket) in [
                    ("Short-term", &short),
                    ("Long-term", &long),
                    ("Unknown-term", &unknown),
                ] {
                    if let Some(t) = bucket.get(c) {
                        writeln!(
                            writer,
                            "{label:<12}{:>3} disposals   proceeds {:>12}   gain {:>12} {c}",
                            t.count,
                            money(t.proceeds, c),
                            money(t.gain, c),
                        )?;
                    }
                }
                let net = short.get(c).map(|t| t.gain).unwrap_or_default()
                    + long.get(c).map(|t| t.gain).unwrap_or_default()
                    + unknown.get(c).map(|t| t.gain).unwrap_or_default();
                writeln!(
                    writer,
                    "{:<12}net realized gain {:>12} {c}",
                    "TOTAL",
                    money(net, c)
                )?;
            }
        }
    }
    Ok(())
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
    use rustledger_core::{
        Amount, CostNumber, CostSpec, Posting, PriceAnnotation, Transaction, naive_date,
    };

    fn d(y: i32, m: u32, day: u32) -> NaiveDate {
        naive_date(y, m, day).unwrap()
    }

    fn money(n: i64, ccy: &str) -> Amount {
        Amount::new(Decimal::from(n), ccy)
    }

    /// `Assets:Broker:Stock` bought at `cost`/unit; cash leg keeps it balanced.
    fn buy(date: NaiveDate, units: i64, cost: i64) -> Directive {
        let spec = CostSpec::empty()
            .with_number(CostNumber::PerUnit {
                value: Decimal::from(cost),
            })
            .with_currency("USD");
        Directive::Transaction(
            Transaction::new(date, "buy")
                .with_synthesized_posting(
                    Posting::new("Assets:Broker:Stock", money(units, "AAPL")).with_cost(spec),
                )
                .with_synthesized_posting(Posting::new("Assets:Bank", money(-units * cost, "USD"))),
        )
    }

    /// Sell `units` (positive) with an empty cost that lot-matches, at `price`
    /// (per-unit `@`). The cash leg is left to balance conceptually — booking a
    /// reduction does not require it for gain computation.
    fn sell_at(date: NaiveDate, units: i64, price: PriceAnnotation) -> Directive {
        Directive::Transaction(
            Transaction::new(date, "sell")
                .with_synthesized_posting(
                    Posting::new("Assets:Broker:Stock", money(-units, "AAPL"))
                        .with_cost(CostSpec::empty())
                        .with_price(price),
                )
                .with_synthesized_posting(Posting::new("Assets:Bank", money(0, "USD"))),
        )
    }

    /// The headline regression: a buy followed by a sell yields a non-empty
    /// disposal list with the correct gain. (Before the book/apply fix the engine
    /// inventory never accumulated and this returned nothing.)
    #[test]
    fn disposals_are_collected_not_empty() {
        let dirs = vec![
            buy(d(2020, 1, 1), 10, 100),
            sell_at(d(2020, 6, 1), 4, PriceAnnotation::unit(money(150, "USD"))),
        ];
        let disposals = collect_disposals(&dirs, BookingMethod::Fifo, None);
        assert_eq!(disposals.len(), 1, "the sale must produce a disposal");
        let g = &disposals[0];
        assert_eq!(g.units, Decimal::from(4));
        assert_eq!(g.cost_basis, Decimal::from(400));
        assert_eq!(g.proceeds, Decimal::from(600));
        assert_eq!(g.gain, Decimal::from(200));
        assert_eq!(g.acquired, Some(d(2020, 1, 1)));
    }

    /// A sale crossing several lots yields one disposal per lot, each with its own
    /// acquisition date and basis.
    #[test]
    fn multi_lot_sale_is_one_disposal_per_lot() {
        let dirs = vec![
            buy(d(2020, 1, 1), 5, 100),
            buy(d(2020, 6, 1), 5, 120),
            sell_at(d(2021, 3, 1), 8, PriceAnnotation::unit(money(150, "USD"))),
        ];
        let disposals = collect_disposals(&dirs, BookingMethod::Fifo, None);
        assert_eq!(disposals.len(), 2);
        assert_eq!(disposals[0].acquired, Some(d(2020, 1, 1)));
        assert_eq!(disposals[0].units, Decimal::from(5));
        assert_eq!(disposals[1].acquired, Some(d(2020, 6, 1)));
        assert_eq!(disposals[1].units, Decimal::from(3));
    }

    /// A single-lot `@@` (total) sale records the stated total as proceeds
    /// EXACTLY, even when it does not divide evenly by the units.
    #[test]
    fn total_price_proceeds_are_exact() {
        let dirs = vec![
            buy(d(2020, 1, 1), 3, 30),
            sell_at(d(2020, 6, 1), 3, PriceAnnotation::total(money(100, "USD"))),
        ];
        let disposals = collect_disposals(&dirs, BookingMethod::Fifo, None);
        assert_eq!(disposals.len(), 1);
        assert_eq!(
            disposals[0].proceeds,
            Decimal::from(100),
            "no 99.999…28dp division tail"
        );
        assert_eq!(disposals[0].gain, Decimal::from(10));
    }

    /// Booking order, not stream order: a sell listed BEFORE the same-date buy that
    /// seeds its lot still matches (the loader books same-date augmentations first).
    #[test]
    fn books_in_booking_order_not_stream_order() {
        // Sell appears first in the vector, buy second, both on 2020-01-01.
        let dirs = vec![
            sell_at(d(2020, 1, 1), 4, PriceAnnotation::unit(money(150, "USD"))),
            buy(d(2020, 1, 1), 10, 100),
        ];
        let disposals = collect_disposals(&dirs, BookingMethod::Fifo, None);
        assert_eq!(disposals.len(), 1, "sell matches the same-date buy's lot");
        assert_eq!(disposals[0].gain, Decimal::from(200));
    }

    /// Whole days between two dates (the `held_days` the report computes).
    fn held(a: NaiveDate, s: NaiveDate) -> Option<i64> {
        a.until((jiff::Unit::Day, s))
            .ok()
            .map(|sp| i64::from(sp.get_days()))
    }

    /// The calendar long-term rule is leap-year correct: a holding from Jan 1 2020
    /// (a leap year) to Jan 1 2021 is 366 days but NOT more than one calendar year,
    /// so it is short-term — where a raw `> 365` day count would wrongly say long.
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
        // 60 days > 30.
        assert!(is_long_term(
            d(2020, 1, 1),
            d(2020, 3, 1),
            held(d(2020, 1, 1), d(2020, 3, 1)),
            Some(30)
        ));
        // 19 days, not > 30.
        assert!(!is_long_term(
            d(2020, 1, 1),
            d(2020, 1, 20),
            held(d(2020, 1, 1), d(2020, 1, 20)),
            Some(30)
        ));
    }

    /// The `--year` filter compares the full `i32` year and does not silently drop
    /// disposals for years outside `i16` (the old lossy `i16::try_from` did).
    #[test]
    fn year_filter_matches_the_right_year() {
        let dirs = vec![
            buy(d(2020, 1, 1), 10, 100),
            sell_at(d(2021, 6, 1), 4, PriceAnnotation::unit(money(150, "USD"))),
        ];
        let ctx = DisplayContext::new();
        let render_year = |year: Option<i32>| {
            let filter = CapgainsFilter {
                account: None,
                year,
                end: None,
            };
            let mut buf = Vec::new();
            report_capgains(
                &dirs,
                &filter,
                None,
                BookingMethod::Fifo,
                &ctx,
                &OutputFormat::Csv,
                &mut buf,
            )
            .unwrap();
            String::from_utf8(buf).unwrap()
        };
        // Data row present for 2021, absent for 2020 (only a buy that year).
        assert!(render_year(Some(2021)).lines().count() > 1);
        assert_eq!(render_year(Some(2020)).lines().count(), 1, "header only");
        assert!(render_year(None).lines().count() > 1);
    }

    /// The account filter keeps only disposals under the given prefix.
    #[test]
    fn account_filter_scopes_by_prefix() {
        let dirs = vec![
            buy(d(2020, 1, 1), 10, 100),
            sell_at(d(2020, 6, 1), 4, PriceAnnotation::unit(money(150, "USD"))),
        ];
        let ctx = DisplayContext::new();
        let render_acct = |acct: Option<&str>| {
            let filter = CapgainsFilter {
                account: acct,
                year: None,
                end: None,
            };
            let mut buf = Vec::new();
            report_capgains(
                &dirs,
                &filter,
                None,
                BookingMethod::Fifo,
                &ctx,
                &OutputFormat::Csv,
                &mut buf,
            )
            .unwrap();
            String::from_utf8(buf).unwrap()
        };
        assert!(render_acct(Some("Assets:Broker")).lines().count() > 1);
        assert_eq!(render_acct(Some("Assets:Other")).lines().count(), 1);
    }

    /// The text renderer emits a header, a data row, and the term summary.
    #[test]
    fn text_render_smoke() {
        let dirs = vec![
            buy(d(2020, 1, 1), 10, 100),
            sell_at(d(2022, 6, 1), 4, PriceAnnotation::unit(money(150, "USD"))),
        ];
        let ctx = DisplayContext::new();
        let filter = CapgainsFilter {
            account: None,
            year: None,
            end: None,
        };
        let mut buf = Vec::new();
        report_capgains(
            &dirs,
            &filter,
            None,
            BookingMethod::Fifo,
            &ctx,
            &OutputFormat::Text,
            &mut buf,
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
}
