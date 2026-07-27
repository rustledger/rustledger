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
use rustledger_budget::{Bucket, BudgetError, BudgetRow, BudgetTotal, Budgets, Empty};
use rustledger_core::{
    Account, AccountTypeKind, AccountTypes, Currency, Directive, DisplayContext, NaiveDate,
};
use std::collections::BTreeMap;
use std::io::Write;

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
    warnings: &mut dyn super::Diagnostics,
) -> Result<()> {
    let budgets = Budgets::from_directives(directives);

    // Budgeted VERSUS ACTUAL is the model's job, not the renderer's — and so
    // are the WARNINGS. Which currency a priced posting spends, which direction
    // a credit-normal account counts in, from which day spending starts
    // counting, and which budgets deserve a complaint are all decisions another
    // consumer would otherwise re-derive. The comparison hands back the whole
    // answer, already filtered to the reported accounts and sorted, so this
    // command and `session.budget` cannot disagree about it.
    let comparison = budgets.compare(
        directives,
        types,
        filter.from,
        filter.to,
        filter.children,
        filter.account,
    );
    let rows = comparison.rows;
    let totals = comparison.totals;
    let mut errors = comparison.errors;
    let empty = comparison.empty;

    // A budget too small to survive display rounding stays a CLI concern: it is
    // a fact about this renderer's precision, not about the ledger, and the
    // crate has no `DisplayContext`. Diagnosed through the SAME `Rounding` the
    // renderer uses, so the warning and the rendered `0.00` cannot disagree.
    let rounding = Rounding::new(types, &rows, &totals, ctx);
    errors.extend(rounding.sub_precision_errors(&rows, filter.from));
    // Built once and handed on: `render` needs the same rounding, and
    // constructing it a second time rebuilt every total row to rediscover the
    // display scales this one already found.

    // Emitted HERE, after every error is known: the un-representable-figure
    // errors are only discovered once rows and totals exist, and an earlier
    // emission point sent them to the JSON array but never to stderr, so a text
    // or CSV user saw `n/a` cells with nothing explaining them.
    // Sorted ONCE, here, because the sub-precision warning above is appended
    // after the crate has already ordered its own. The crate's sort is what
    // makes every consumer see the same order; this one only places the
    // rendering diagnostic among them.
    errors.sort_by_key(|e| e.date);
    for e in &errors {
        // To the caller's sink, not the process's stderr: an agent envelope
        // cannot see the latter, and a warning it cannot see is the silent
        // misreport these exist to prevent.
        // Structured: a `BudgetError` already carries the date and the account
        // this is about, and flattening them into a line threw away exactly the
        // fields an agent wants to key on.
        warnings.emit(super::Diagnostic {
            code: None,
            date: Some(e.date),
            account: e.account.as_ref().map(|a| a.as_str().to_string()),
            message: e.reason.clone(),
        });
    }
    render(
        &Rendering { types, ctx, format },
        &rows,
        &totals,
        filter,
        empty,
        &errors,
        &rounding,
        writer,
        warnings,
    )
}

/// The diagnosis in prose. The VARIANTS live in `rustledger-budget` because
/// they are a fact about the ledger; the wording lives here because it is a
/// fact about this command — it names `--account` and quotes a `custom` line a
/// terminal user can paste.
fn empty_message(empty: Empty, filter: &BudgetFilter) -> String {
    match empty {
        // Says that each one IS reported, not WHERE. Warnings go to stderr,
        // which a terminal interleaves above this line but an `ag-rledger`
        // JSON envelope drops entirely — so "see the warnings above" pointed
        // an agent at something its transport had already discarded. The
        // JSON format carries them in-band in `errors`.
        Empty::AllRejected { shown: true } => {
            "No usable budgets: every `custom \"budget\"` directive in this \
                 ledger was rejected. Each one is reported as a warning."
                .to_string()
        }
        Empty::AllRejected { shown: false } => {
            "No usable budgets: every `custom \"budget\"` directive in this \
                 ledger was rejected. Re-run without --account to see which ones \
                 and why."
                .to_string()
        }
        Empty::NoneDeclared => "No budgets declared. Add e.g.:\n  2024-01-01 custom \"budget\" \
                 Expenses:Food \"monthly\" 400.00 USD"
            .to_string(),
        Empty::NoneInWindow { earliest } => format!(
            "No budgets were in force in this period. A budget applies from \
                 its own date onward, and the earliest one here is dated \
                 {earliest}."
        ),
        Empty::FilteredOut => format!(
            "No budgets match --account {}. (Accounts are matched by raw \
                 prefix, the same as `report balances`.)",
            super::sanitize_display(filter.account.unwrap_or_default())
        ),
    }
}

/// A whole-report total as a row, so totals and rows render through one path.
///
/// Totals are per ACCOUNT TYPE, not per direction. Adding a 5000 salary target
/// to a 400 travel budget gives a figure that means nothing and a `Used`
/// percentage reading far healthier than the spending is — but bucketing merely
/// by credit-normality repeated the mistake one level up, lumping a credit-card
/// spending budget in with an income target and labeling the sum "earned".
/// Expenses keep the bare `TOTAL` label, being the overwhelmingly common case.
///
/// The Expenses case is a MATCH ARM on the typed bucket, not a comparison
/// against a root name. When the bucket was a raw string this decision read
/// `kind == "Expenses"`, so a ledger setting `option "name_expenses" "Depenses"`
/// emitted no row any consumer recognized as the primary total — including this
/// repo's own fuzz oracle. With the classification carried as a value there is
/// no string to get wrong, and the ledger's own vocabulary comes back out of
/// `AccountTypes::root_name` for the label.
fn total_row(types: &AccountTypes, total: &BudgetTotal) -> BudgetRow {
    BudgetRow {
        account: Account::new(total.bucket.label(types)),
        currency: total.currency.clone(),
        budgeted: total.budgeted,
        actual: total.actual,
    }
}

/// A used-fraction as a percentage cell, or `n/a` when nothing was budgeted.
fn fmt_used(used: Option<f64>) -> String {
    used.map_or_else(|| "n/a".to_string(), |u| format!("{:.1}%", u * 100.0))
}

/// The report's display-rounding rule, in one place.
///
/// Rounding to display precision happens ONCE, up front, and every format
/// renders from the rounded values — deriving the percentage from unrounded
/// figures beside rounded amounts printed a row of four fields a reader could
/// not reconcile (`budgeted 0, actual 0, remaining 0, used_pct 2033.3`).
///
/// Named and shared because the rounding is not only a rendering concern: the
/// diagnostic that reports a budget too small to survive it has to apply the
/// very same rule, and a second copy of "how many decimals does this currency
/// get" is exactly the drift this repo's canonical-function discipline exists
/// to prevent.
struct Rounding<'a> {
    ctx: &'a DisplayContext,
    /// Chosen scale per currency the ledger's `DisplayContext` does not know —
    /// a budget declared before any spending is recorded. ONE per currency, so
    /// the cells of a row agree with each other.
    untracked: BTreeMap<Currency, u32>,
}

impl<'a> Rounding<'a> {
    /// How many decimals to show for a currency the ledger never describes.
    /// Enough for a crypto-scale budget, far from `Decimal`'s 28.
    const MAX_UNTRACKED_DP: u32 = 8;

    fn new(
        types: &AccountTypes,
        rows: &[BudgetRow],
        totals: &[BudgetTotal],
        ctx: &'a DisplayContext,
    ) -> Self {
        let mut untracked: BTreeMap<Currency, u32> = BTreeMap::new();
        let all_totals: Vec<BudgetRow> = totals.iter().map(|t| total_row(types, t)).collect();
        for r in rows.iter().chain(all_totals.iter()) {
            if ctx.get_precision(&r.currency).is_some() {
                continue;
            }
            let seen = [r.budgeted, r.actual, r.remaining()]
                .into_iter()
                .flatten()
                // Raw scale, not normalized: a declared `100.00 USD` keeps its
                // trailing zeros, while a pro-rated (28-digit) value is capped.
                .map(|v| v.scale().min(Self::MAX_UNTRACKED_DP))
                .max()
                .unwrap_or(0);
            let e = untracked.entry(r.currency.clone()).or_default();
            *e = (*e).max(seen);
        }
        Self { ctx, untracked }
    }

    fn untracked_scale(&self, ccy: &str) -> Option<u32> {
        self.untracked.get(ccy).copied()
    }

    fn round(&self, v: Decimal, ccy: &str) -> Decimal {
        self.ctx.get_precision(ccy).map_or_else(
            || v.round_dp(self.untracked_scale(ccy).unwrap_or(Self::MAX_UNTRACKED_DP)),
            |dp| v.round_dp(dp),
        )
    }

    /// Budgets that exist but are too small to survive display rounding.
    ///
    /// A budget below its currency's precision renders as `0.00`, and a zero
    /// budget makes the Used percentage undefined — so the row prints
    /// `budgeted 0.00 … Used n/a`, which is exactly how this report says
    /// "nothing was budgeted here". A real 0.004/month budget with 500.00 of
    /// spending against it therefore read as an unbudgeted account rather than
    /// a 12,500,000% overrun. Rounding first stays; that it DESTROYS
    /// information is what the report has to say out loud.
    fn sub_precision_errors(&self, rows: &[BudgetRow], on: NaiveDate) -> Vec<BudgetError> {
        rows.iter()
            .filter_map(|r| {
                let b = r.budgeted?;
                (!b.is_zero() && self.round(b, &r.currency).is_zero()).then(|| BudgetError {
                    date: on,
                    account: Some(r.account.clone()),
                    reason: format!(
                        "budget for {} is {} {}, smaller than the display precision \
                         for {}; it is shown as zero and its Used percentage as n/a",
                        r.account, b, r.currency, r.currency
                    ),
                })
            })
            .collect()
    }
}

/// How to render, as opposed to what: the ledger's account naming and display
/// precision plus the chosen output format. Bundled because they travel
/// together through every rendering path and are never chosen independently.
struct Rendering<'a> {
    types: &'a AccountTypes,
    ctx: &'a DisplayContext,
    format: &'a OutputFormat,
}

#[allow(clippy::too_many_arguments)]
fn render<W: Write>(
    env: &Rendering<'_>,
    rows: &[BudgetRow],
    totals: &[BudgetTotal],
    filter: &BudgetFilter,
    empty: Option<Empty>,
    errors: &[BudgetError],
    rounding: &Rounding<'_>,
    writer: &mut W,
    warnings: &mut dyn super::Diagnostics,
) -> Result<()> {
    // 9 parameters is over the lint's threshold; every one is genuinely
    // distinct here and bundling them would only move the list.
    let Rendering { types, ctx, format } = *env;
    let round_disp = |v: Decimal, ccy: &str| -> Decimal { rounding.round(v, ccy) };
    let round_row = |r: &BudgetRow| BudgetRow {
        account: r.account.clone(),
        currency: r.currency.clone(),
        budgeted: r.budgeted.map(|v| round_disp(v, &r.currency)),
        actual: r.actual.map(|v| round_disp(v, &r.currency)),
    };
    let rows: Vec<BudgetRow> = rows.iter().map(round_row).collect();
    let rows = &rows[..];
    // Canonical order from the crate is by (currency, account type), and type
    // order is beancount's statement order — assets, liabilities, equity,
    // income, expenses — which puts the headline expenses total LAST, under
    // `TOTAL (Income)`. Correct for a general-purpose ordering, wrong for a
    // reader: this report is about spending, and the bare `TOTAL` is the line
    // they came for. Reading order is a rendering concern, so it is chosen
    // here rather than by bending the type's `Ord`.
    let mut ordered: Vec<&BudgetTotal> = totals.iter().collect();
    ordered.sort_by(|a, b| {
        let headline = |t: &BudgetTotal| t.bucket.kind() != Some(AccountTypeKind::Expenses);
        (&a.currency, headline(a), &a.bucket).cmp(&(&b.currency, headline(b), &b.bucket))
    });
    // Kept paired with the bucket they came from: the JSON below reports the
    // TYPE and the ledger's own root name as separate fields, and a rendered
    // label cannot be taken apart again to recover them.
    let total_rows: Vec<(BudgetRow, &Bucket)> = ordered
        .into_iter()
        .map(|t| (round_row(&total_row(types, t)), &t.bucket))
        .collect();

    // A pro-rated budget is a repeating decimal, so it MUST be rounded for
    // display. The ledger's `DisplayContext` answers for any currency it has
    // seen; for one it has not (a budget added before any spending is recorded)
    // the report picks the scale itself — see `untracked_scale`, which chooses
    // ONE per currency so the cells of a row agree with each other.
    let money = |n: Decimal, ccy: &str| {
        ctx.get_precision(ccy).map_or_else(
            || {
                let dp = rounding.untracked_scale(ccy).unwrap_or(0);
                format!("{n:.*}", dp as usize)
            },
            |_| ctx.format_amount_number(n, ccy),
        )
    };
    // An un-representable figure is reported as absent, never as a clamped
    // number. Text says `n/a`; machine output follows the same convention the
    // other reports use for an absent number — an empty CSV cell and a JSON
    // `null` — so a consumer parsing decimals is not handed the literal "n/a".
    let money_text =
        |n: Option<Decimal>, ccy: &str| n.map_or_else(|| "n/a".to_string(), |v| money(v, ccy));
    let money_csv = |n: Option<Decimal>, ccy: &str| n.map_or_else(String::new, |v| money(v, ccy));
    let money_json = |n: Option<Decimal>, ccy: &str| {
        n.map_or_else(|| "null".to_string(), |v| format!("\"{}\"", money(v, ccy)))
    };
    match format {
        OutputFormat::Csv => {
            // CSV is a strict data format — a comment row would break the
            // parsers this output exists for — so the diagnosis goes to stderr,
            // where this report already puts everything a reader needs that is
            // not a data row. Without it three different empty reports were one
            // bare header line.
            if let Some(empty) = empty {
                warnings.emit(super::Diagnostic::message(empty_message(empty, filter)));
            }
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
                    csv_escape(&money_csv(r.budgeted, &r.currency)),
                    csv_escape(&money_csv(r.actual, &r.currency)),
                    csv_escape(&money_csv(r.remaining(), &r.currency)),
                    r.used_fraction()
                        .map_or_else(String::new, |u| format!("{:.1}", u * 100.0)),
                )?;
            }
            // The whole-report total, as its own row per currency. Consumers
            // cannot re-derive it by summing the rows: under `--children` a
            // parent row and a child row both include the child.
            // CSV keeps its six-column schema and the rendered label; adding
            // columns would break every consumer of a format that exists to be
            // parsed positionally. A caller that needs the bucket typed should
            // ask for JSON, which carries it.
            for (row, _) in &total_rows {
                let (ccy, row) = (row.currency.as_str(), row);
                writeln!(
                    writer,
                    "{},{},{},{},{},{}",
                    csv_escape(&row.account),
                    csv_escape(ccy),
                    csv_escape(&money_csv(row.budgeted, ccy)),
                    csv_escape(&money_csv(row.actual, ccy)),
                    csv_escape(&money_csv(row.remaining(), ccy)),
                    row.used_fraction()
                        .map_or_else(String::new, |u| format!("{:.1}", u * 100.0)),
                )?;
            }
        }
        OutputFormat::Json => {
            let obj = |r: &BudgetRow| {
                format!(
                    r#"{{"account": "{}", "currency": "{}", "budgeted": {}, "actual": {}, "remaining": {}, "used_pct": {}}}"#,
                    json_escape(&r.account),
                    json_escape(&r.currency),
                    money_json(r.budgeted, &r.currency),
                    money_json(r.actual, &r.currency),
                    money_json(r.remaining(), &r.currency),
                    r.used_fraction()
                        .map_or_else(|| "null".to_string(), |u| format!("{:.1}", u * 100.0)),
                )
            };
            let objs: Vec<String> = rows.iter().map(obj).collect();
            // An explicit per-currency total, matching `returns`' `"total"`
            // object: consumers must not re-derive it by summing `budgets`,
            // because under `--children` parent and child rows overlap.
            // Totals carry `kind` and `root` as well as the rendered label, the
            // same split `session.budget` makes. One string cannot hold both:
            // a ledger with `option "name_income" "Revenue"` renders
            // `TOTAL (Revenue)`, and a consumer keying on that cannot tell it is
            // the income total, while one keying on `TOTAL` cannot tell it from
            // the expenses total on a ledger that also has one. `kind` is the
            // closed vocabulary (the five types plus "other"); `root` is the
            // ledger's spelling.
            let total_objs: Vec<String> = total_rows
                .iter()
                .map(|(r, bucket)| {
                    let (kind, root) = match bucket {
                        Bucket::Typed(k) => (k.as_str(), types.root_name(*k)),
                        Bucket::Other(root) => ("other", root.as_str()),
                    };
                    let base = obj(r);
                    format!(
                        r#"{}, "kind": "{}", "root": "{}"}}"#,
                        base.trim_end_matches('}'),
                        json_escape(kind),
                        json_escape(root)
                    )
                })
                .collect();
            // Rejected directives are reported in-band as well as on stderr.
            // Without this a dashboard cannot tell "this ledger has no budgets"
            // from "every budget in it was rejected": both produced an empty
            // `budgets` array and exit 0, so the user's typo stayed invisible
            // for as long as they only looked at the UI.
            let error_objs: Vec<String> = errors
                .iter()
                .map(|e| {
                    format!(
                        r#"{{"date": "{}", "message": "{}"}}"#,
                        e.date,
                        json_escape(&e.reason)
                    )
                })
                .collect();
            // `empty` says WHY there are no rows, and is null whenever there
            // are. Without it the three empty reports were byte-identical to a
            // machine consumer, which is the ambiguity `Empty` exists to
            // remove — it was just never rendered outside the text branch.
            let empty_obj = empty.map_or_else(
                || "null".to_string(),
                |e| {
                    format!(
                        r#"{{"code": "{}", "message": "{}"}}"#,
                        e.code(),
                        json_escape(&empty_message(e, filter))
                    )
                },
            );
            writeln!(
                writer,
                r#"{{"from": "{}", "to": "{}", "budgets": [{}], "totals": [{}], "errors": [{}], "empty": {}}}"#,
                filter.from,
                filter.to,
                objs.join(", "),
                total_objs.join(", "),
                error_objs.join(", "),
                empty_obj
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
                if let Some(empty) = empty {
                    writeln!(writer, "{}", empty_message(empty, filter))?;
                }
                return Ok(());
            }
            // A currency column: without it two rows for one account in two
            // currencies are indistinguishable, and the reader has no way to tell
            // which figure is which.
            //
            // Sized to the widest commodity actually present rather than a fixed
            // width, because truncating a commodity re-creates exactly the bug
            // the column was added to fix: beancount permits 24-character names,
            // and two that share a suffix (`VACATION-FUND-A`, `OTHER-FUND-A`)
            // would render identically and misattribute their figures. Widening
            // costs a few columns on the rare long-ticker ledger; truncating
            // costs correctness on it.
            // EVERY column is sized to its content, for one reason: a cell that
            // does not fit either merges with its neighbor (so the reader
            // cannot tell where Actual ends and Remaining begins) or is
            // truncated (so two distinct values render identically and the
            // figures beside them are misattributed). Both are worse than a
            // wide table. This was learned twice here — first on the currency
            // column, then on the account and numeric columns — so it is now
            // applied uniformly rather than per column.
            let cells = |r: &BudgetRow| {
                [
                    money_text(r.budgeted, &r.currency),
                    money_text(r.actual, &r.currency),
                    money_text(r.remaining(), &r.currency),
                ]
            };
            let width = |f: &dyn Fn(&BudgetRow) -> usize, floor: usize| {
                rows.iter()
                    .chain(total_rows.iter().map(|(r, _)| r))
                    .map(f)
                    .max()
                    .unwrap_or(floor)
                    .max(floor)
            };
            let acct_w = width(&|r| r.account.chars().count(), "Account".len());
            let ccy_w = width(&|r| r.currency.chars().count(), "Ccy".len());
            let num_w =
                |i: usize, head: &str| width(&|r| cells(r)[i].chars().count(), head.len()) + 2;
            let (bw, aw, rw) = (
                num_w(0, "Budgeted"),
                num_w(1, "Actual"),
                num_w(2, "Remaining"),
            );
            // The Used column is content-sized too. It was left at a constant
            // while the others were fixed, so a percentage of nine or more
            // characters (a tiny budget with real spending against it —
            // `500000.0%`) butted straight against Remaining and the reader
            // could read `-4999.00500000` as one figure.
            let uw = width(
                &|r| fmt_used(r.used_fraction()).chars().count(),
                "Used".len(),
            ) + 2;
            let rule = RULE.max(acct_w + 1 + ccy_w + bw + aw + rw + uw);
            writeln!(
                writer,
                "{:<acct_w$} {:<ccy_w$}{:>bw$}{:>aw$}{:>rw$}{:>uw$}",
                "Account", "Ccy", "Budgeted", "Actual", "Remaining", "Used"
            )?;
            writeln!(writer, "{}", "-".repeat(rule))?;
            let line = |r: &BudgetRow| {
                let [b, a, rem] = cells(r);
                format!(
                    "{:<acct_w$} {:<ccy_w$}{:>bw$}{:>aw$}{:>rw$}{:>uw$}",
                    // Sanitized, not truncated: every column is sized to its
                    // content, so nothing is cut, but a control character in a
                    // label would still split the fixed-width row. Widths are
                    // computed on the same char counts (sanitizing is 1:1).
                    super::sanitize_display(&r.account),
                    super::sanitize_display(&r.currency),
                    b,
                    a,
                    rem,
                    fmt_used(r.used_fraction()),
                )
            };
            for r in rows {
                writeln!(writer, "{}", line(r))?;
            }
            writeln!(writer, "{}", "-".repeat(rule))?;
            // Totals per currency (summing across currencies would be
            // meaningless), counting each budget and posting once — see
            // `compute_totals`. Rendered through the same path as the rows so
            // the two cannot drift in shape.
            for (r, _) in &total_rows {
                writeln!(writer, "{}", line(r))?;
            }
        }
    }
    Ok(())
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
            budgeted: Some(Decimal::from(400)),
            actual: Some(Decimal::from(120)),
        };
        assert_eq!(r.remaining(), Some(Decimal::from(280)));
        assert!((r.used_fraction().unwrap() - 0.30).abs() < 1e-9);
        // Overspent: remaining goes negative rather than clamping at zero.
        let over = BudgetRow {
            actual: Some(Decimal::from(500)),
            ..r
        };
        assert_eq!(over.remaining(), Some(Decimal::from(-100)));
        assert!(over.used_fraction().unwrap() > 1.0);
        // No budget -> no percentage (a division by zero is not 0% or 100%).
        let none = BudgetRow {
            account: "Expenses:Food".into(),
            currency: "USD".into(),
            budgeted: Some(Decimal::ZERO),
            actual: Some(Decimal::from(50)),
        };
        assert_eq!(none.used_fraction(), None);
        assert_eq!(fmt_used(None), "n/a");
        // An un-representable accrual has no remaining and no percentage — it is
        // reported as `n/a`, never as a clamped number.
        let overflowed = BudgetRow {
            account: "Expenses:Food".into(),
            currency: "USD".into(),
            budgeted: None,
            actual: Some(Decimal::from(50)),
        };
        assert_eq!(overflowed.remaining(), None);
        assert_eq!(overflowed.used_fraction(), None);
    }
}
