//! Budget report — budgeted vs actual spending over a period.
//!
//! The budget *model* — reading Fava's `custom "budget"` directives, the calendar
//! interval arithmetic, supersession and the per-day accrual — lives in the
//! [`rustledger_budget`] leaf crate, so the CLI, the FFI component and rustfava
//! share one implementation. This module owns only what is specific to the
//! report: pairing budgets with actual spending, the `--children` and `--account`
//! selection rules, totals, and rendering.
//!
//! # Report-specific semantics
//!
//! - **A parent budget does not cover its children.** `Expenses:Food` budgets only
//!   postings booked to `Expenses:Food` itself. Pass `--children` to also count
//!   subaccounts, which *sums* the parent's own budget with any child budgets
//!   (they add; the child is not absorbed).
//! - **Only budgeted accounts appear.** Spending with no budget is not shown —
//!   `report balances` already answers that question.
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
use rustledger_budget::{BudgetError, Budgets};
use rustledger_core::{AccountTypes, Directive, DisplayContext, NaiveDate, is_subaccount_or_equal};
use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;

/// Budgets naming an account the ledger never opens.
///
/// A typo'd account is the worst kind of budget bug: it parses, so `check` is
/// happy, and it renders as a real row at `0.0%` used — the user reads "I have
/// spent none of my food budget" while the actual spending sits on the correctly
/// spelled account, which the report deliberately omits for having no budget.
/// One warning turns that silent misreport into an obvious fix.
fn unopened_account_errors(directives: &[Directive], budgets: &Budgets) -> Vec<BudgetError> {
    let opened: BTreeSet<&str> = directives
        .iter()
        .filter_map(|d| match d {
            Directive::Open(o) => Some(o.account.as_str()),
            _ => None,
        })
        .collect();
    // A ledger with no `open` directives at all is not using them; do not warn on
    // every budget in that case.
    if opened.is_empty() {
        return Vec::new();
    }
    let mut seen = BTreeSet::new();
    budgets
        .entries()
        .iter()
        .filter(|b| !opened.contains(b.account.as_str()))
        .filter(|b| seen.insert(b.account.clone()))
        .map(|b| BudgetError {
            date: b.from,
            reason: format!(
                "budget for {} but no such account is opened; the budget will \
                 report no spending",
                b.account
            ),
        })
        .collect()
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
    let (budgets, mut errors) = Budgets::from_directives(directives);
    errors.extend(unopened_account_errors(directives, &budgets));
    errors.sort_by_key(|e| e.date);
    for e in &errors {
        eprintln!("warning: {}: {}", e.date, e.reason);
    }

    // Every currency anyone budgeted in. Used to decide which side of a
    // priced/costed posting the spending counts against (see below).
    let budgeted_currencies: BTreeSet<&str> = budgets
        .entries()
        .iter()
        .map(|b| b.currency.as_str())
        .collect();

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
            // Which currency does this posting spend? For a plain posting the
            // units are the whole story. For one carried at a cost or a price
            // (`Expenses:Travel 90.00 EUR @ 1.10 USD`) there are two defensible
            // answers, so prefer the one the user actually budgeted in: units if
            // that currency is budgeted anywhere, else the canonical balance
            // weight, which is what the money really cost them. Without this a
            // USD food budget silently ignored every foreign-currency grocery
            // run and reported the user as fully under budget.
            //
            // The weight (and its cost-beats-price ladder) comes from
            // `rustledger_booking::posting_weight`, the same one `rledger check`
            // and BQL's `weight` column use, so budget totals cannot drift from
            // the balance rules.
            let counted = if budgeted_currencies.contains(units.currency.as_str()) {
                (units.currency.to_string(), units.number)
            } else {
                rustledger_booking::posting_weight(p)
                    .filter(|w| budgeted_currencies.contains(w.currency.as_str()))
                    .map_or_else(
                        || (units.currency.to_string(), units.number),
                        |w| (w.currency.to_string(), w.number),
                    )
            };
            *actuals
                .entry((p.account.to_string(), counted.0))
                .or_default() += counted.1;
        }
    }

    // One row per budgeted (account, currency). A budget with no spending still
    // appears (that is the point of a budget report); spending with no budget does
    // not — `report balances` already answers that question.
    //
    // "Budgeted" means *in force somewhere in this window*, i.e. declared before
    // the exclusive end. A budget written today does not retroactively apply to
    // last year: without this filter, reviewing a past period produced a row with
    // `0.00` budgeted and a full window of spending against it, reporting the
    // whole period as overspend for a budget that did not exist yet.
    let keys = budgets.keys_in_force_before(filter.to);

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
                    .entries()
                    .iter()
                    .filter(|b| {
                        b.currency == currency && is_subaccount_or_equal(&b.account, &account)
                    })
                    .map(|b| &b.account)
                    .collect();
                all.sort();
                all.dedup();
                all.iter()
                    .map(|a| budgets.accrue(a, &currency, filter.from, filter.to))
                    .sum()
            } else {
                budgets.accrue(&account, &currency, filter.from, filter.to)
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
    render(
        &rows,
        &totals,
        filter,
        Empty::diagnose(&budgets, filter),
        ctx,
        format,
        writer,
    )
}

/// Whole-report totals per currency, counting every budget and every posting once.
///
/// Summing the rendered rows would be wrong under `--children`: a parent row and a
/// child row each include the child, so the child would be counted twice. These are
/// derived from the distinct budget entries and the postings they cover instead.
fn compute_totals(
    budgets: &Budgets,
    actuals: &BTreeMap<(String, String), Decimal>,
    filter: &BudgetFilter,
    types: &AccountTypes,
) -> BTreeMap<String, (Decimal, Decimal)> {
    // Distinct budgeted (account, currency) pairs, after the account filter.
    let pairs: Vec<(String, String)> = budgets
        .keys_in_force_before(filter.to)
        .into_iter()
        .filter(|(account, _)| {
            filter
                .account
                .is_none_or(|p| is_subaccount_or_equal(account, p))
        })
        .collect();

    let mut totals: BTreeMap<String, (Decimal, Decimal)> = BTreeMap::new();
    for (account, currency) in &pairs {
        let e = totals.entry(currency.clone()).or_default();
        e.0 += budgets.accrue(account, currency, filter.from, filter.to);
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

/// Why a report came out with no rows.
///
/// An empty budget report is ambiguous in a way that matters: "you have no
/// budgets", "your budgets start later than the period you asked about" and
/// "your `--account` filter excluded them" send the user to three different
/// places, and reporting the wrong one sends them hunting a parsing bug that
/// does not exist.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Empty {
    /// The ledger declares no budgets at all.
    NoneDeclared,
    /// Budgets exist but all start on or after the window's exclusive end.
    NoneInWindow { earliest: NaiveDate },
    /// Budgets were in force, but `--account` excluded every one.
    FilteredOut,
}

impl Empty {
    fn diagnose(budgets: &Budgets, filter: &BudgetFilter) -> Self {
        let Some(earliest) = budgets.earliest() else {
            return Self::NoneDeclared;
        };
        if !budgets.any_in_force_before(filter.to) {
            return Self::NoneInWindow { earliest };
        }
        Self::FilteredOut
    }
}

/// A whole-report total as a row, so totals and rows render through one path.
fn total_row(currency: &str, budgeted: Decimal, actual: Decimal) -> BudgetRow {
    BudgetRow {
        account: "TOTAL".to_string(),
        currency: currency.to_string(),
        budgeted,
        actual,
    }
}

/// A used-fraction as a percentage cell, or `n/a` when nothing was budgeted.
fn fmt_used(used: Option<f64>) -> String {
    used.map_or_else(|| "n/a".to_string(), |u| format!("{:.1}%", u * 100.0))
}

fn render<W: Write>(
    rows: &[BudgetRow],
    totals: &BTreeMap<String, (Decimal, Decimal)>,
    filter: &BudgetFilter,
    empty: Empty,
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
            // Numbers render through the ledger's `DisplayContext`, like every
            // other report's CSV (the U4 invariant): a pro-rated budget is a
            // repeating decimal, and emitting it raw handed spreadsheets a
            // 28-digit number where the text report showed `45.16`.
            // `csv_escape` on the amounts because `render_commas` puts thousands
            // separators inside the field.
            for r in rows {
                writeln!(
                    writer,
                    "{},{},{},{},{},{}",
                    csv_escape(&r.account),
                    csv_escape(&r.currency),
                    csv_escape(&money(r.budgeted, &r.currency)),
                    csv_escape(&money(r.actual, &r.currency)),
                    csv_escape(&money(r.remaining(), &r.currency)),
                    r.used_fraction()
                        .map_or_else(String::new, |u| format!("{:.1}", u * 100.0)),
                )?;
            }
            // The whole-report total, as its own row per currency. Consumers
            // cannot re-derive it by summing the rows: under `--children` a
            // parent row and a child row both include the child.
            for (ccy, (b, a)) in totals {
                let row = total_row(ccy, *b, *a);
                writeln!(
                    writer,
                    "{},{},{},{},{},{}",
                    csv_escape(&row.account),
                    csv_escape(ccy),
                    csv_escape(&money(row.budgeted, ccy)),
                    csv_escape(&money(row.actual, ccy)),
                    csv_escape(&money(row.remaining(), ccy)),
                    row.used_fraction()
                        .map_or_else(String::new, |u| format!("{:.1}", u * 100.0)),
                )?;
            }
        }
        OutputFormat::Json => {
            let obj = |r: &BudgetRow| {
                format!(
                    r#"{{"account": "{}", "currency": "{}", "budgeted": "{}", "actual": "{}", "remaining": "{}", "used_pct": {}}}"#,
                    json_escape(&r.account),
                    json_escape(&r.currency),
                    money(r.budgeted, &r.currency),
                    money(r.actual, &r.currency),
                    money(r.remaining(), &r.currency),
                    r.used_fraction()
                        .map_or_else(|| "null".to_string(), |u| format!("{:.1}", u * 100.0)),
                )
            };
            let objs: Vec<String> = rows.iter().map(obj).collect();
            // An explicit per-currency total, matching `returns`' `"total"`
            // object: consumers must not re-derive it by summing `budgets`,
            // because under `--children` parent and child rows overlap.
            let total_objs: Vec<String> = totals
                .iter()
                .map(|(ccy, (b, a))| obj(&total_row(ccy, *b, *a)))
                .collect();
            writeln!(
                writer,
                r#"{{"from": "{}", "to": "{}", "budgets": [{}], "totals": [{}]}}"#,
                filter.from,
                filter.to,
                objs.join(", "),
                total_objs.join(", ")
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
                // Distinguish "you have no budgets" from "your filter excluded
                // them all" — telling a user with budgets that they have none
                // sends them looking for a parsing bug that isn't there.
                match empty {
                    Empty::NoneDeclared => writeln!(
                        writer,
                        "No budgets declared. Add e.g.:\n  2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD"
                    )?,
                    Empty::NoneInWindow { earliest } => writeln!(
                        writer,
                        "No budgets were in force in this period. \
                         A budget applies from its own date onward, and the earliest \
                         one here is dated {earliest}."
                    )?,
                    Empty::FilteredOut => writeln!(
                        writer,
                        "No budgets match --account {}. (Accounts are matched by \
                         component, so a partial component name matches nothing.)",
                        filter.account.unwrap_or_default()
                    )?,
                }
                return Ok(());
            }
            // A currency column: without it two rows for one account in two
            // currencies are indistinguishable, and the reader has no way to tell
            // which figure is which.
            writeln!(
                writer,
                "{:<28}{:<6}{:>13}{:>13}{:>13}{:>9}",
                "Account", "Ccy", "Budgeted", "Actual", "Remaining", "Used"
            )?;
            writeln!(writer, "{}", "-".repeat(RULE))?;
            for r in rows {
                writeln!(
                    writer,
                    "{:<28}{:<6}{:>13}{:>13}{:>13}{:>9}",
                    truncate(&r.account, 28),
                    r.currency,
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
                let row = total_row(ccy, *b, *a);
                writeln!(
                    writer,
                    "{:<28}{:<6}{:>13}{:>13}{:>13}{:>9}",
                    row.account,
                    ccy,
                    money(row.budgeted, ccy),
                    money(row.actual, ccy),
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
