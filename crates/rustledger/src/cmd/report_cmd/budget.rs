//! Budget report — budgeted vs actual spending over a period.
//!
//! Beancount has no budgeting of its own; the de-facto convention is **Fava's
//! `custom "budget"` directive**, which is plain, unextended Beancount syntax:
//!
//! ```text
//! 2024-01-01 custom "budget" Expenses:Food      "monthly" 400.00 USD
//! 2024-01-01 custom "budget" Expenses:Transport "weekly"   25.00 USD
//! 2024-06-01 custom "budget" Expenses:Food      "monthly" 450.00 USD
//! ```
//!
//! This report reads exactly that, so a ledger already budgeted for Fava works
//! here unchanged — no new syntax, and the ledger stays the only source of truth.
//!
//! # Semantics (matching Fava)
//!
//! - **Per-day accrual, not period matching.** Every day in the half-open range
//!   `[from, to)` accrues `amount / days_in_the_calendar_interval_containing_that_day`.
//!   The denominator is the interval's true calendar length, so a monthly budget
//!   divides by 28/29/30/31 and a yearly one by 365/366. Arbitrary partial periods
//!   therefore pro-rate for free, with no special case.
//! - **Calendar anchoring.** Intervals align to calendar boundaries (month = the
//!   1st, quarter = Jan/Apr/Jul/Oct 1, year = Jan 1, week = ISO Monday), *not* to
//!   the date the directive was written. A budget declared mid-month accrues from
//!   that day on, but each day is still divided by the surrounding calendar month.
//! - **Supersession is per (account, currency).** A later directive replaces an
//!   earlier one for the same account *and currency* from its own date; budgets in
//!   different currencies for one account stay simultaneously active and are
//!   reported separately.
//! - **A parent budget does not cover its children.** `Expenses:Food` budgets only
//!   postings booked to `Expenses:Food` itself. Pass `--children` to also count
//!   subaccounts, which *sums* the parent's own budget with any child budgets
//!   (they add; the child is not absorbed).
//!
//! # A deliberate deviation from Fava
//!
//! Fava selects children with a naive `child.startswith(account)` string test, so
//! a budget on `Expenses:Food` also captures **`Expenses:FoodCourt`** — a
//! different account that merely shares a name prefix. This report uses the
//! canonical [`rustledger_core::is_subaccount_or_equal`], which compares account
//! *components*, so only true subaccounts (`Expenses:Food:Restaurant`) match. Per
//! the project's Python-compatibility policy we match correct behavior, not bugs.

use super::{OutputFormat, csv_escape, json_escape};
use anyhow::Result;
use rust_decimal::Decimal;
use rustledger_core::{
    AccountTypes, Directive, DisplayContext, MetaValue, NaiveDate, is_subaccount_or_equal,
};
use std::collections::BTreeMap;
use std::io::Write;

/// A budget interval, which fixes both the calendar anchoring and the per-day
/// denominator.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Interval {
    Day,
    Week,
    Month,
    Quarter,
    Year,
}

impl Interval {
    /// Parse an interval keyword.
    ///
    /// Fava accepts ten spellings — both the bare noun and the `-ly` form of each
    /// interval — matched case-insensitively, even though its documentation
    /// advertises only the five `-ly` forms. Accepting all ten keeps ledgers that
    /// rely on the implementation (rather than the docs) working.
    fn parse(s: &str) -> Option<Self> {
        match s.to_ascii_lowercase().as_str() {
            "day" | "daily" => Some(Self::Day),
            "week" | "weekly" => Some(Self::Week),
            "month" | "monthly" => Some(Self::Month),
            "quarter" | "quarterly" => Some(Self::Quarter),
            "year" | "yearly" => Some(Self::Year),
            _ => None,
        }
    }

    /// The first day of the calendar interval containing `day`.
    fn start_of(self, day: NaiveDate) -> NaiveDate {
        match self {
            Self::Day => day,
            // ISO week: back up to Monday.
            Self::Week => day
                .checked_sub(
                    jiff::Span::new().days(i64::from(day.weekday().to_monday_zero_offset())),
                )
                .unwrap_or(day),
            Self::Month => day.first_of_month(),
            Self::Quarter => {
                let m = ((day.month() - 1) / 3) * 3 + 1;
                NaiveDate::new(day.year(), m, 1).unwrap_or(day)
            }
            Self::Year => day.first_of_year(),
        }
    }

    /// The first day of the interval after the one starting at `start`.
    fn next_start(self, start: NaiveDate) -> NaiveDate {
        let span = match self {
            Self::Day => jiff::Span::new().days(1),
            Self::Week => jiff::Span::new().days(7),
            Self::Month => jiff::Span::new().months(1),
            Self::Quarter => jiff::Span::new().months(3),
            Self::Year => jiff::Span::new().years(1),
        };
        start.checked_add(span).unwrap_or(start)
    }
}

/// One `custom "budget"` declaration.
#[derive(Clone, Debug)]
struct BudgetEntry {
    /// Effective from this date (the directive's own date).
    from: NaiveDate,
    account: String,
    interval: Interval,
    amount: Decimal,
    currency: String,
}

/// A malformed `custom "budget"` directive, reported rather than silently ignored.
pub(super) struct BudgetError {
    pub date: NaiveDate,
    pub reason: String,
}

/// Read every `custom "budget"` directive, newest-last per (account, currency).
///
/// Malformed entries are collected as errors rather than dropped: a budget that
/// silently does not apply is worse than one that is reported, since the report
/// would otherwise show `0.00` budgeted and look like deliberate under-spend.
fn parse_budgets(directives: &[Directive]) -> (Vec<BudgetEntry>, Vec<BudgetError>) {
    let mut out = Vec::new();
    let mut errors = Vec::new();
    for d in directives {
        let Directive::Custom(c) = d else { continue };
        if c.custom_type != "budget" {
            continue;
        }
        // Shape: <Account> "<interval>" <amount>
        let [
            MetaValue::Account(acct),
            MetaValue::String(interval_raw),
            MetaValue::Amount(amount),
        ] = c.values.as_slice()
        else {
            errors.push(BudgetError {
                date: c.date,
                reason: "expected: custom \"budget\" <Account> \"<interval>\" <amount> <CCY>"
                    .to_string(),
            });
            continue;
        };
        let account = acct.to_string();
        let Some(interval) = Interval::parse(interval_raw) else {
            errors.push(BudgetError {
                date: c.date,
                reason: format!(
                    "invalid interval {interval_raw:?} (use daily, weekly, monthly, quarterly or yearly)"
                ),
            });
            continue;
        };
        out.push(BudgetEntry {
            from: c.date,
            account,
            interval,
            amount: amount.number,
            currency: amount.currency.to_string(),
        });
    }
    // Effective-date order, so the "latest in force" scan below is a simple walk.
    out.sort_by_key(|e| e.from);
    (out, errors)
}

/// The budget in force for `(account, currency)` on `day`, if any.
///
/// Supersession is keyed on the pair, not the account alone: a EUR budget and a
/// USD budget for one account are both live and neither replaces the other.
fn in_force<'a>(
    budgets: &'a [BudgetEntry],
    account: &str,
    currency: &str,
    day: NaiveDate,
) -> Option<&'a BudgetEntry> {
    budgets
        .iter()
        .rfind(|b| b.account == account && b.currency == currency && b.from <= day)
}

/// Accrue the budgeted amount for one `(account, currency)` over `[from, to)`.
///
/// Conceptually this is Fava's per-day accrual — every day contributes
/// `amount / days_in_its_calendar_interval` — which is what makes an arbitrary
/// window pro-rate with no special case. It is evaluated **per contiguous
/// segment** rather than per day, though, because summing `400/29` twenty-nine
/// times does not recover exactly `400` in decimal arithmetic: the residue
/// surfaced as `399.99999999999999999999999997` in machine output. A segment
/// contributes `amount × days_in_segment / days_in_interval` — multiplying before
/// dividing, so a fully-covered interval is exactly `amount` — which is
/// mathematically identical to the day-by-day sum but exact at the boundaries
/// that matter most (a whole month of a monthly budget IS the monthly figure).
///
/// Segments break at whichever comes first: the end of the calendar interval, the
/// start of a superseding budget, or the end of the window.
fn accrue(
    budgets: &[BudgetEntry],
    account: &str,
    currency: &str,
    from: NaiveDate,
    to: NaiveDate,
) -> Decimal {
    let next_day = |d: NaiveDate| d.checked_add(jiff::Span::new().days(1)).unwrap_or(d);
    let days_between = |a: NaiveDate, b: NaiveDate| {
        i64::from(a.until((jiff::Unit::Day, b)).map_or(0, |s| s.get_days()))
    };

    let mut total = Decimal::ZERO;
    let mut cursor = from;
    while cursor < to {
        let Some(b) = in_force(budgets, account, currency, cursor) else {
            // No budget yet in force: skip ahead to the next declaration that
            // starts inside the window, or stop.
            match budgets
                .iter()
                .filter(|e| e.account == account && e.currency == currency && e.from > cursor)
                .map(|e| e.from)
                .min()
            {
                Some(next) if next < to => cursor = next,
                _ => break,
            }
            continue;
        };
        let istart = b.interval.start_of(cursor);
        let inext = b.interval.next_start(istart);
        // The next superseding declaration, if it lands inside this interval.
        let next_change = budgets
            .iter()
            .filter(|e| e.account == account && e.currency == currency && e.from > cursor)
            .map(|e| e.from)
            .min();
        let mut seg_end = inext.min(to);
        if let Some(change) = next_change
            && change < seg_end
        {
            seg_end = change;
        }
        // Guarantee forward progress even on a pathological interval.
        if seg_end <= cursor {
            seg_end = next_day(cursor).min(to);
        }
        let seg_days = days_between(cursor, seg_end);
        let interval_days = days_between(istart, inext).max(1);
        if seg_days > 0 {
            total += b.amount * Decimal::from(seg_days) / Decimal::from(interval_days);
        }
        cursor = seg_end;
    }
    total
}

/// Sign-normalize a posting total so "actual" always counts the same direction the
/// budget was declared in.
///
/// Expense postings are debits (positive) and a spending budget is written
/// positive, so those already agree. Income postings are **credits** (negative)
/// while an earning target is also written positive — without this flip, earning
/// exactly your 5000 target would report `actual -5000`, `remaining 10000` and
/// `used -100%`. The same applies to any credit-normal account (income, liability,
/// equity), so the test is the canonical config-aware
/// [`AccountTypes::is_credit_normal`] rather than a hardcoded `Income:` prefix.
fn normalized_actual(types: &AccountTypes, account: &str, raw: Decimal) -> Decimal {
    if types.is_credit_normal(account) {
        -raw
    } else {
        raw
    }
}

/// One row of the report: an account's budget versus what it actually spent.
struct BudgetRow {
    account: String,
    currency: String,
    budgeted: Decimal,
    actual: Decimal,
}

impl BudgetRow {
    /// Budget minus actual. Positive is under budget (money left), negative over.
    ///
    /// `actual` is already sign-normalized (see [`normalized_actual`]) so this
    /// subtraction reads the same way for a spending budget and an earning target.
    fn remaining(&self) -> Decimal {
        self.budgeted - self.actual
    }

    /// Fraction of the budget used, `None` when nothing was budgeted (which would
    /// be a division by zero, not 0% or 100%).
    fn used_fraction(&self) -> Option<f64> {
        if self.budgeted.is_zero() {
            return None;
        }
        let b: f64 = self.budgeted.try_into().ok()?;
        let a: f64 = self.actual.try_into().ok()?;
        Some(a / b)
    }
}

/// Filters for the budget report.
pub(super) struct BudgetFilter<'a> {
    /// Only accounts under this prefix.
    pub account: Option<&'a str>,
    /// Report window start (inclusive).
    pub from: NaiveDate,
    /// Report window end (**exclusive**, matching the accrual model).
    pub to: NaiveDate,
    /// Count postings in subaccounts toward a parent's budget, summing the
    /// parent's own budget with any child budgets.
    pub children: bool,
}

/// Generate the budget report.
///
/// # Errors
/// Propagates writer I/O errors.
pub(super) fn report_budget<W: Write>(
    directives: &[Directive],
    filter: &BudgetFilter,
    types: &AccountTypes,
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let (budgets, errors) = parse_budgets(directives);
    for e in &errors {
        eprintln!(
            "warning: {}: malformed budget directive: {}",
            e.date, e.reason
        );
    }

    // Actual spend per (account, currency) inside the window. Postings are read
    // directly rather than through `account_balances` because a budget is about
    // FLOW over a period, not the running balance an inventory realizes.
    let mut actuals: BTreeMap<(String, String), Decimal> = BTreeMap::new();
    for d in directives {
        let Directive::Transaction(txn) = d else {
            continue;
        };
        if txn.date < filter.from || txn.date >= filter.to {
            continue;
        }
        for p in &txn.postings {
            let Some(units) = p.units.as_ref().and_then(|u| u.as_amount()) else {
                continue;
            };
            *actuals
                .entry((p.account.to_string(), units.currency.to_string()))
                .or_default() += units.number;
        }
    }

    // One row per budgeted (account, currency). A budget with no spending still
    // appears (that is the point of a budget report); spending with no budget does
    // not — `report balances` already answers that question.
    let mut keys: Vec<(String, String)> = budgets
        .iter()
        .map(|b| (b.account.clone(), b.currency.clone()))
        .collect();
    keys.sort();
    keys.dedup();

    let mut rows: Vec<BudgetRow> = keys
        .into_iter()
        .filter(|(account, _)| {
            filter
                .account
                .is_none_or(|p| is_subaccount_or_equal(account, p))
        })
        .map(|(account, currency)| {
            let budgeted = if filter.children {
                // Sum this account's own budget with every child's: Fava's
                // child mode adds them rather than letting the parent absorb.
                let mut all: Vec<&String> = budgets
                    .iter()
                    .filter(|b| {
                        b.currency == currency && is_subaccount_or_equal(&b.account, &account)
                    })
                    .map(|b| &b.account)
                    .collect();
                all.sort();
                all.dedup();
                all.iter()
                    .map(|a| accrue(&budgets, a, &currency, filter.from, filter.to))
                    .sum()
            } else {
                accrue(&budgets, &account, &currency, filter.from, filter.to)
            };
            let actual = actuals
                .iter()
                .filter(|((a, c), _)| {
                    *c == currency
                        && if filter.children {
                            is_subaccount_or_equal(a, &account)
                        } else {
                            *a == account
                        }
                })
                .map(|((a, _), v)| normalized_actual(types, a, *v))
                .sum();
            BudgetRow {
                account,
                currency,
                budgeted,
                actual,
            }
        })
        .collect();
    rows.sort_by(|a, b| (&a.account, &a.currency).cmp(&(&b.account, &b.currency)));

    // Totals are computed from the underlying data rather than by summing the rows:
    // under `--children` a parent row and a child row both include the child's
    // budget and spending, so adding the rows up would count it twice.
    let totals = compute_totals(&budgets, &actuals, filter, types);
    render(&rows, &totals, filter, ctx, format, writer)
}

/// Whole-report totals per currency, counting every budget and every posting once.
///
/// Summing the rendered rows would be wrong under `--children`: a parent row and a
/// child row each include the child, so the child would be counted twice. These are
/// derived from the distinct budget entries and the postings they cover instead.
fn compute_totals(
    budgets: &[BudgetEntry],
    actuals: &BTreeMap<(String, String), Decimal>,
    filter: &BudgetFilter,
    types: &AccountTypes,
) -> BTreeMap<String, (Decimal, Decimal)> {
    // Distinct budgeted (account, currency) pairs, after the account filter.
    let mut pairs: Vec<(String, String)> = budgets
        .iter()
        .filter(|b| {
            filter
                .account
                .is_none_or(|p| is_subaccount_or_equal(&b.account, p))
        })
        .map(|b| (b.account.clone(), b.currency.clone()))
        .collect();
    pairs.sort();
    pairs.dedup();

    let mut totals: BTreeMap<String, (Decimal, Decimal)> = BTreeMap::new();
    for (account, currency) in &pairs {
        let e = totals.entry(currency.clone()).or_default();
        e.0 += accrue(budgets, account, currency, filter.from, filter.to);
    }
    // Each posting counts once, against whichever budgeted accounts cover it.
    for ((account, currency), raw) in actuals {
        let covered = pairs.iter().any(|(b, c)| {
            c == currency
                && if filter.children {
                    is_subaccount_or_equal(account, b)
                } else {
                    account == b
                }
        });
        if covered {
            let e = totals.entry(currency.clone()).or_default();
            e.1 += normalized_actual(types, account, *raw);
        }
    }
    totals
}

/// A used-fraction as a percentage cell, or `n/a` when nothing was budgeted.
fn fmt_used(used: Option<f64>) -> String {
    used.map_or_else(|| "n/a".to_string(), |u| format!("{:.1}%", u * 100.0))
}

fn render<W: Write>(
    rows: &[BudgetRow],
    totals: &BTreeMap<String, (Decimal, Decimal)>,
    filter: &BudgetFilter,
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    let money = |n: Decimal, ccy: &str| ctx.format_amount_number(n, ccy);
    match format {
        OutputFormat::Csv => {
            writeln!(
                writer,
                "account,currency,budgeted,actual,remaining,used_pct"
            )?;
            for r in rows {
                // Raw `Decimal` for machine consumption; the text report owns
                // display precision and separators.
                writeln!(
                    writer,
                    "{},{},{},{},{},{}",
                    csv_escape(&r.account),
                    csv_escape(&r.currency),
                    r.budgeted,
                    r.actual,
                    r.remaining(),
                    r.used_fraction()
                        .map_or_else(String::new, |u| format!("{:.1}", u * 100.0)),
                )?;
            }
        }
        OutputFormat::Json => {
            let objs: Vec<String> = rows
                .iter()
                .map(|r| {
                    format!(
                        r#"{{"account": "{}", "currency": "{}", "budgeted": "{}", "actual": "{}", "remaining": "{}", "used_pct": {}}}"#,
                        json_escape(&r.account),
                        json_escape(&r.currency),
                        r.budgeted,
                        r.actual,
                        r.remaining(),
                        r.used_fraction()
                            .map_or_else(|| "null".to_string(), |u| format!("{:.1}", u * 100.0)),
                    )
                })
                .collect();
            writeln!(
                writer,
                r#"{{"from": "{}", "to": "{}", "budgets": [{}]}}"#,
                filter.from,
                filter.to,
                objs.join(", ")
            )?;
        }
        OutputFormat::Text => {
            const RULE: usize = 84;
            writeln!(writer, "Budget")?;
            writeln!(writer, "{}", "=".repeat(RULE))?;
            writeln!(writer)?;
            // The window is stated because the budget figure is pro-rated to it —
            // without the dates the number is not interpretable.
            writeln!(
                writer,
                "Period      {} to {} (end exclusive)",
                filter.from, filter.to
            )?;
            writeln!(writer)?;
            if rows.is_empty() {
                writeln!(
                    writer,
                    "No budgets declared. Add e.g.:\n  2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD"
                )?;
                return Ok(());
            }
            writeln!(
                writer,
                "{:<30}{:>13}{:>13}{:>13}{:>9}",
                "Account", "Budgeted", "Actual", "Remaining", "Used"
            )?;
            writeln!(writer, "{}", "-".repeat(RULE))?;
            for r in rows {
                writeln!(
                    writer,
                    "{:<30}{:>13}{:>13}{:>13}{:>9}",
                    truncate(&r.account, 30),
                    money(r.budgeted, &r.currency),
                    money(r.actual, &r.currency),
                    money(r.remaining(), &r.currency),
                    fmt_used(r.used_fraction()),
                )?;
            }
            writeln!(writer, "{}", "-".repeat(RULE))?;
            // Totals per currency (summing across currencies would be meaningless),
            // counting each budget and posting once — see `compute_totals`.
            for (ccy, (b, a)) in totals {
                let (b, a) = (*b, *a);
                let row = BudgetRow {
                    account: String::new(),
                    currency: ccy.clone(),
                    budgeted: b,
                    actual: a,
                };
                writeln!(
                    writer,
                    "{:<30}{:>13}{:>13}{:>13}{:>9} {ccy}",
                    "TOTAL",
                    money(b, ccy),
                    money(a, ccy),
                    money(row.remaining(), ccy),
                    fmt_used(row.used_fraction()),
                )?;
            }
        }
    }
    Ok(())
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
    use rustledger_core::naive_date;

    fn d(y: i32, m: u32, day: u32) -> NaiveDate {
        naive_date(y, m, day).unwrap()
    }

    fn budget(from: NaiveDate, account: &str, interval: Interval, amount: i64) -> BudgetEntry {
        BudgetEntry {
            from,
            account: account.to_string(),
            interval,
            amount: Decimal::from(amount),
            currency: "USD".to_string(),
        }
    }

    /// Fava accepts both the bare noun and the `-ly` form of every interval,
    /// case-insensitively — ten keywords, though its docs list only five.
    #[test]
    fn interval_parsing_accepts_all_ten_fava_keywords() {
        for (s, want) in [
            ("day", Interval::Day),
            ("daily", Interval::Day),
            ("week", Interval::Week),
            ("weekly", Interval::Week),
            ("month", Interval::Month),
            ("monthly", Interval::Month),
            ("quarter", Interval::Quarter),
            ("quarterly", Interval::Quarter),
            ("year", Interval::Year),
            ("yearly", Interval::Year),
        ] {
            assert_eq!(Interval::parse(s), Some(want), "keyword {s}");
            assert_eq!(
                Interval::parse(&s.to_uppercase()),
                Some(want),
                "case-insensitive {s}"
            );
        }
        assert_eq!(
            Interval::parse("fortnightly"),
            None,
            "unknown -> None, not a default"
        );
    }

    /// A whole calendar period accrues EXACTLY the stated amount — including
    /// February, whose length differs between leap and common years. This is the
    /// report's central promise: "my monthly budget is 400" must read 400.
    #[test]
    fn whole_period_accrues_the_exact_stated_amount() {
        let b = vec![budget(d(2024, 1, 1), "Expenses:Food", Interval::Month, 400)];
        // Leap February: 29 days.
        assert_eq!(
            accrue(&b, "Expenses:Food", "USD", d(2024, 2, 1), d(2024, 3, 1)),
            Decimal::from(400),
            "29-day February still totals exactly the monthly amount"
        );
        // Common February: 28 days.
        assert_eq!(
            accrue(&b, "Expenses:Food", "USD", d(2025, 2, 1), d(2025, 3, 1)),
            Decimal::from(400)
        );
        // 31-day month.
        assert_eq!(
            accrue(&b, "Expenses:Food", "USD", d(2024, 1, 1), d(2024, 2, 1)),
            Decimal::from(400)
        );
        // A whole year of a monthly budget is twelve months' worth.
        assert_eq!(
            accrue(&b, "Expenses:Food", "USD", d(2024, 1, 1), d(2025, 1, 1)),
            Decimal::from(4800)
        );
    }

    /// An arbitrary partial window pro-rates by real calendar days: 14 of
    /// February 2024's 29 days is 14/29 of the monthly figure.
    #[test]
    fn partial_window_prorates_by_calendar_days() {
        let b = vec![budget(d(2024, 1, 1), "Expenses:Food", Interval::Month, 400)];
        let got = accrue(&b, "Expenses:Food", "USD", d(2024, 2, 1), d(2024, 2, 15));
        let want = Decimal::from(400) * Decimal::from(14) / Decimal::from(29);
        assert_eq!(got, want);
        // Sanity: the fraction is a real 29-day denominator, not 28 or 30.
        assert!(
            got > Decimal::from(193) && got < Decimal::from(194),
            "got {got}"
        );
    }

    /// A later directive supersedes from its own date; a window spanning the
    /// change picks up each rate for exactly the days it was in force.
    #[test]
    fn later_directive_supersedes_from_its_date() {
        let b = vec![
            budget(d(2024, 1, 1), "Expenses:Food", Interval::Month, 400),
            budget(d(2024, 6, 1), "Expenses:Food", Interval::Month, 450),
        ];
        // May (old rate) + June (new rate).
        assert_eq!(
            accrue(&b, "Expenses:Food", "USD", d(2024, 5, 1), d(2024, 7, 1)),
            Decimal::from(850)
        );
        // Whole year: Jan-May at 400, Jun-Dec at 450.
        assert_eq!(
            accrue(&b, "Expenses:Food", "USD", d(2024, 1, 1), d(2025, 1, 1)),
            Decimal::from(5 * 400 + 7 * 450)
        );
    }

    /// Supersession is keyed on (account, CURRENCY): a second currency is a
    /// parallel budget, not a replacement.
    #[test]
    fn currencies_coexist_rather_than_superseding() {
        let mut eur = budget(d(2024, 2, 1), "Expenses:Food", Interval::Month, 100);
        eur.currency = "EUR".to_string();
        let b = vec![
            budget(d(2024, 1, 1), "Expenses:Food", Interval::Month, 400),
            eur,
        ];
        assert_eq!(
            accrue(&b, "Expenses:Food", "USD", d(2024, 2, 1), d(2024, 3, 1)),
            Decimal::from(400),
            "the EUR entry must not supersede the USD one"
        );
        assert_eq!(
            accrue(&b, "Expenses:Food", "USD", d(2024, 3, 1), d(2024, 4, 1)),
            Decimal::from(400)
        );
        assert_eq!(
            accrue(&b, "Expenses:Food", "EUR", d(2024, 2, 1), d(2024, 3, 1)),
            Decimal::from(100)
        );
    }

    /// Days before the first declaration accrue nothing — a budget starts when it
    /// is declared, it is not retroactive.
    #[test]
    fn nothing_accrues_before_the_first_declaration() {
        let b = vec![budget(d(2024, 6, 1), "Expenses:Food", Interval::Month, 300)];
        assert_eq!(
            accrue(&b, "Expenses:Food", "USD", d(2024, 1, 1), d(2024, 6, 1)),
            Decimal::ZERO
        );
        // A window straddling the declaration picks up only the covered part.
        assert_eq!(
            accrue(&b, "Expenses:Food", "USD", d(2024, 5, 1), d(2024, 7, 1)),
            Decimal::from(300),
            "May accrues nothing; June accrues the full month"
        );
    }

    /// Weekly and yearly denominators are the real ones (7, and 365/366).
    #[test]
    fn weekly_and_yearly_denominators() {
        let w = vec![budget(d(2024, 1, 1), "Expenses:T", Interval::Week, 70)];
        // 29 days of February at 10/day.
        assert_eq!(
            accrue(&w, "Expenses:T", "USD", d(2024, 2, 1), d(2024, 3, 1)),
            Decimal::from(290)
        );
        let y = vec![budget(d(2024, 1, 1), "Expenses:T", Interval::Year, 3660)];
        // A whole leap year is exactly the yearly figure.
        assert_eq!(
            accrue(&y, "Expenses:T", "USD", d(2024, 1, 1), d(2025, 1, 1)),
            Decimal::from(3660)
        );
        // One day of a 366-day year.
        assert_eq!(
            accrue(&y, "Expenses:T", "USD", d(2024, 3, 1), d(2024, 3, 2)),
            Decimal::from(3660) / Decimal::from(366)
        );
    }

    /// Quarters anchor to Jan/Apr/Jul/Oct 1 — the calendar, not the directive date.
    #[test]
    fn quarters_anchor_to_calendar_boundaries() {
        assert_eq!(Interval::Quarter.start_of(d(2024, 5, 17)), d(2024, 4, 1));
        assert_eq!(Interval::Quarter.start_of(d(2024, 12, 31)), d(2024, 10, 1));
        // A budget declared mid-quarter still divides by the whole quarter's days.
        let b = vec![budget(d(2024, 4, 1), "Expenses:T", Interval::Quarter, 910)];
        assert_eq!(
            accrue(&b, "Expenses:T", "USD", d(2024, 4, 1), d(2024, 7, 1)),
            Decimal::from(910),
            "Q2 accrues exactly the quarterly amount"
        );
    }

    /// Weeks anchor to ISO Monday.
    #[test]
    fn weeks_anchor_to_iso_monday() {
        // 2024-03-07 is a Thursday; its ISO week began Monday 2024-03-04.
        assert_eq!(Interval::Week.start_of(d(2024, 3, 7)), d(2024, 3, 4));
        assert_eq!(Interval::Week.start_of(d(2024, 3, 4)), d(2024, 3, 4));
    }

    /// `remaining` is budget − actual, and `used` is undefined (not 0%) when
    /// nothing was budgeted.
    #[test]
    fn remaining_and_used_semantics() {
        let r = BudgetRow {
            account: "Expenses:Food".into(),
            currency: "USD".into(),
            budgeted: Decimal::from(400),
            actual: Decimal::from(120),
        };
        assert_eq!(r.remaining(), Decimal::from(280));
        assert!((r.used_fraction().unwrap() - 0.30).abs() < 1e-9);
        // Overspent: remaining goes negative rather than clamping at zero.
        let over = BudgetRow {
            actual: Decimal::from(500),
            ..r
        };
        assert_eq!(over.remaining(), Decimal::from(-100));
        assert!(over.used_fraction().unwrap() > 1.0);
        // No budget -> no percentage (a division by zero is not 0% or 100%).
        let none = BudgetRow {
            account: "Expenses:Food".into(),
            currency: "USD".into(),
            budgeted: Decimal::ZERO,
            actual: Decimal::from(50),
        };
        assert_eq!(none.used_fraction(), None);
        assert_eq!(fmt_used(None), "n/a");
    }
}
