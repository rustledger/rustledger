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
//! Gains are reported in each lot's **cost currency**; a multi-currency ledger is
//! summarized per currency. Not a tax filing: wash-sale adjustment, currency-gain
//! separation, lots seeded by `pad` (no well-defined cost basis), and jurisdiction
//! rules beyond the long-term threshold are out of scope (run `rledger check` to
//! validate the ledger first).

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::Result;
use rust_decimal::Decimal;
use rustledger_booking::CapitalGain;
use rustledger_core::{DisplayContext, NaiveDate};
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
    let rows = gains
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
/// "> 1 year" rule (leap-year correct), `Some(n)` a fixed day count.
///
/// # Errors
/// Propagates writer I/O errors.
pub(super) fn report_capgains<W: Write>(
    gains: &[CapitalGain],
    filter: &CapgainsFilter,
    long_term_days: Option<i64>,
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let (disposals, cross_currency) = to_disposals(gains, long_term_days);
    // A cross-currency disposal (sale price in a different currency than the lot's
    // cost basis) has no gain without an FX rate, so it is dropped from the rows.
    // Surface the count on stderr rather than silently omitting it.
    if cross_currency > 0 {
        eprintln!(
            "warning: {cross_currency} cross-currency disposal(s) omitted (sale price \
             in a different currency than the cost basis; no FX conversion applied)"
        );
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
                    csv_escape(&d.currency),
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
            // Wide enough for millions with thousands separators (e.g.
            // `1,500,000.00`) without the amount columns overflowing.
            const RULE: usize = 91;
            writeln!(writer, "Realized capital gains")?;
            writeln!(writer, "{}", "=".repeat(RULE))?;
            writeln!(writer)?;
            if rows.is_empty() {
                writeln!(writer, "No realized disposals in range.")?;
                return Ok(());
            }
            writeln!(
                writer,
                "{:<11}{:<22}{:>10}{:<12}{:>6}{:>15}{:>15}",
                "Sold", "Commodity / account", "Units", "  Acquired", "Term", "Proceeds", "Gain"
            )?;
            writeln!(writer, "{}", "-".repeat(RULE))?;
            for d in rows {
                writeln!(
                    writer,
                    "{:<11}{:<22}{:>10}{:<12}{:>6}{:>15}{:>15}",
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
                            "{label:<12}{:>3} disposals   proceeds {:>15}   gain {:>15} {c}",
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
                    "{:<12}net realized gain {:>15} {c}",
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
        report_capgains(gains, filter, None, &ctx, &OutputFormat::Csv, &mut buf).unwrap();
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
        report_capgains(&gains, &filter, None, &ctx, &OutputFormat::Text, &mut buf).unwrap();
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
        report_capgains(&gains, &filter, None, &ctx, &OutputFormat::Text, &mut buf).unwrap();
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
