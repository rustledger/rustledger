//! What is wrong with a budget report that its figures alone do not show.
//!
//! A typo'd account, a currency the account never posts, a budget still
//! accruing after its account closed, a figure too large to represent: each
//! renders as a plausible-looking row, so without these the report's most
//! dangerous failure is the one that looks fine.
//!
//! In the CRATE, not in the CLI, because they are not a rendering concern. When
//! they lived in the command, `session.budget` over the FFI returned rows with
//! an empty `errors` list — a host showed a tidy `0.0%` bar for a budget on a
//! misspelled account, which is precisely the silent misreport these exist to
//! catch. Anything that must be true of a budget report belongs where every
//! consumer of the report can see it.

use crate::{Bucket, BudgetError, Budgets, Comparison, covers, passes_account_filter};
use rustledger_core::{AccountTypes, Directive, NaiveDate};
use std::collections::{BTreeMap, BTreeSet};

/// Budgets naming an account the ledger never opens.
///
/// A typo'd account is the worst kind of budget bug: it parses, so `check` is
/// happy, and it renders as a real row at `0.0%` used — the user reads "I have
/// spent none of my food budget" while the actual spending sits on the correctly
/// spelled account, which the report deliberately omits for having no budget.
/// One warning turns that silent misreport into an obvious fix.
pub fn unopened_account_errors(
    directives: &[Directive],
    budgets: &Budgets,
    to: NaiveDate,
    children: bool,
) -> Vec<BudgetError> {
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
        // Only budgets this report could actually show. All three diagnostics
        // now share this bound: a budget declared after the window contributes
        // no row, no total and no figure, so accusing it of a defect the reader
        // cannot see in the output is noise — and worse for the currency check
        // below, which judged such a budget against postings from a window it
        // does not apply to.
        .filter(|b| b.from < to)
        // A parent budgeted as an aggregate (`Expenses:Food` with only
        // `Expenses:Food:Groceries` opened) is a normal, working setup — but ONLY
        // under `--children`, which is what makes the children's spending answer
        // the parent's budget. In the default mode that budget really does report
        // nothing, so exempting it there restored the silent misreport this check
        // exists to catch.
        .filter(|b| {
            let covered_by_a_child =
                children && opened.iter().any(|o| rustledger_core::is_subaccount_or_equal(o, &b.account));
            !opened.contains(b.account.as_str()) && !covered_by_a_child
        })
        .filter(|b| seen.insert(b.account.clone()))
        .map(|b| BudgetError {
            date: b.from,
            account: Some(b.account.clone()),
            reason: format!(
                "budget for {} but no such account is opened; the budget will \
                 report no spending",
                b.account
            ),
        })
        .collect()
}
/// Budgets that keep accruing after their account was closed.
///
/// `close` means no further postings are possible, so every day after it
/// contributes budget that nothing can ever be spent against — the row then
/// reads as a large underspend. The accrual is deliberately NOT changed: a
/// budget is a declaration in its own right, Fava does not consider `close`
/// either, and silently dropping the tail would be its own surprise. Warning
/// says the same thing without changing a number.
pub fn closed_account_errors(
    directives: &[Directive],
    budgets: &Budgets,
    to: NaiveDate,
    children: bool,
) -> Vec<BudgetError> {
    let mut closed: BTreeMap<&str, NaiveDate> = BTreeMap::new();
    let mut opened: BTreeSet<&str> = BTreeSet::new();
    for d in directives {
        match d {
            Directive::Close(c) => {
                let e = closed.entry(c.account.as_str()).or_insert(c.date);
                *e = (*e).min(c.date);
            }
            Directive::Open(o) => {
                opened.insert(o.account.as_str());
            }
            _ => {}
        }
    }
    let mut seen = BTreeSet::new();
    budgets
        .entries()
        .filter_map(|b| {
            // Coverage, not identity: under `--children` a parent budget is
            // answered by its children, so a parent whose covering accounts are
            // ALL closed can no longer see spending either.
            //
            // "All", not "any": an earlier version warned as soon as one covered
            // account closed, which produced a warning saying no spending could
            // be booked directly above a row showing spending booked through a
            // sibling that was still open. The relevant date is then the LAST
            // close, not the first, because spending remains possible until
            // every covering account has shut.
            let covering: Vec<&str> = opened
                .iter()
                .copied()
                .filter(|acct| covers(&b.account, acct, children))
                .collect();
            if covering.is_empty() {
                return None;
            }
            let when = *covering
                .iter()
                .map(|acct| closed.get(acct))
                .collect::<Option<Vec<_>>>()?
                .into_iter()
                .max()?;
            // Only if the budget is still running past the close inside this
            // window; a budget that ended before it is unremarkable.
            // Any budget that accrues on or after the close is unspendable for
            // those days. A budget declared AFTER the close is the worse case —
            // it can never see a single posting — and an earlier `b.from <= when`
            // guard silently excluded exactly that one.
            (when < to && b.from < to && seen.insert(b.account.clone())).then(|| BudgetError {
                date: when,
                account: Some(b.account.clone()),
                reason: if b.from >= when {
                    format!(
                        "budget for {} starts {} but the account was closed on {}; \
                         no spending can ever be booked to it",
                        b.account, b.from, when
                    )
                } else {
                    format!(
                        "budget for {} keeps accruing after the account was closed on {}; \
                         no spending can be booked to it after that date",
                        b.account, when
                    )
                },
            })
        })
        .collect()
}
/// Budgets whose currency the account never posts in.
///
/// The sibling of the typo'd-account check, and the same silent misreport: a
/// budget written in `USF` against an account that posts `USD` renders a tidy
/// `0.0%` used row while the real spending sits one keystroke away. Only
/// accounts that DO post something are checked, so a budget set up before any
/// spending is recorded stays quiet.
pub fn mismatched_currency_errors(
    directives: &[Directive],
    budgets: &Budgets,
    children: bool,
    from: NaiveDate,
    to: NaiveDate,
) -> Vec<BudgetError> {
    // Every currency each account actually moves — units and, for a priced or
    // costed posting, the weight currency too, since `90 EUR @ 1.10 USD` is
    // legitimately budgetable in either.
    // Windowed, like every other posting walk in this report. Scanning the whole
    // ledger let a currency the account stopped posting years ago suppress the
    // warning: an EUR budget for 2024 stayed silent because the account posted
    // EUR in 2019, which is precisely the silent misreport this exists to catch.
    let mut posted: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
    for d in directives {
        let Directive::Transaction(txn) = d else {
            continue;
        };
        if txn.date < from || txn.date >= to {
            continue;
        }
        for p in &txn.postings {
            let Some(units) = p.units.as_ref().and_then(|u| u.as_amount()) else {
                continue;
            };
            let entry = posted.entry(p.account.as_str()).or_default();
            entry.insert(units.currency.to_string());
            if let Some(w) = rustledger_booking::posting_weight(p) {
                entry.insert(w.currency.to_string());
            }
        }
    }
    // Which currencies a budget could possibly see, under the SAME coverage rule
    // the report uses: with `--children` a parent budget is answered by its
    // children's postings, so checking the parent account alone both missed the
    // typo it exists to catch (spending lives on the children) and warned falsely
    // when the parent itself happened to post one other currency.
    let covered_currencies = |budgeted: &str| -> BTreeSet<String> {
        posted
            .iter()
            .filter(|(account, _)| covers(budgeted, account, children))
            .flat_map(|(_, currencies)| currencies.iter().cloned())
            .collect()
    };
    let mut seen = BTreeSet::new();
    budgets
        .entries()
        // Same window bound as the other two diagnostics. The posting scan above
        // is already windowed; judging an out-of-window budget on in-window
        // evidence accused a 2030 budget of a currency typo on the strength of
        // 2024 spending, and phrased it as settled fact.
        .filter(|b| b.from < to)
        .filter(|b| {
            let seen_currencies = covered_currencies(&b.account);
            !seen_currencies.is_empty() && !seen_currencies.contains(b.currency.as_str())
        })
        .filter(|b| seen.insert((b.account.clone(), b.currency.clone())))
        .map(|b| {
            let actually = covered_currencies(&b.account)
                .into_iter()
                .collect::<Vec<_>>()
                .join(", ");
            BudgetError {
                date: b.from,
                account: Some(b.account.clone()),
                reason: format!(
                    "budget for {} is in {}, but that account only posts {}; \
                     the budget will report no spending",
                    b.account, b.currency, actually
                ),
            }
        })
        .collect()
}

/// Everything wrong with a budget report that its figures alone do not show.
///
/// The ONE entry point. Every consumer of `compare` gets the same warnings, so
/// a host cannot render a report the CLI would have annotated. `account_filter`
/// narrows to the budgets this invocation reports on: restricting to one
/// account should not emit warnings about accounts the caller excluded.
///
/// Sorted by date, so the order is stable across formats and runs.
pub fn collect(
    budgets: &Budgets,
    directives: &[Directive],
    comparison: &Comparison,
    types: &AccountTypes,
    from: NaiveDate,
    to: NaiveDate,
    children: bool,
    account_filter: Option<&str>,
) -> Vec<BudgetError> {
    // The directives that could not be read come first in provenance but not in
    // order: everything is sorted by date at the end, so the caller never sees
    // parse failures and report warnings interleaved differently depending on
    // which surface it asked.
    let mut errors = budgets.errors().to_vec();
    errors.extend(unopened_account_errors(directives, budgets, to, children));
    errors.extend(mismatched_currency_errors(
        directives, budgets, children, from, to,
    ));
    errors.extend(closed_account_errors(directives, budgets, to, children));
    if let Some(prefix) = account_filter {
        errors.retain(|e| {
            e.account
                .as_ref()
                .is_none_or(|a| passes_account_filter(a.as_str(), Some(prefix)))
        });
    }
    errors.extend(unrepresentable_errors(comparison, types, from));
    errors.sort_by_key(|e| e.date);
    errors
}

/// Figures the comparison could not represent.
///
/// Reported in band as well as rendered absent: without this a consumer sees an
/// absent number with an empty error list and cannot tell an overflow from a bug
/// in its own parsing. A TOTAL can overflow even when every row it sums is
/// individually representable, so covering only the rows left the commonest
/// overflow silent.
fn unrepresentable_errors(
    comparison: &Comparison,
    types: &AccountTypes,
    on: NaiveDate,
) -> Vec<BudgetError> {
    let mut out = Vec::new();
    for r in &comparison.rows {
        if r.budgeted.is_none() || r.actual.is_none() {
            out.push(BudgetError {
                date: on,
                account: Some(r.account.clone()),
                reason: format!(
                    "budget for {} in {} is too large to represent; the figure \
                     is reported as absent rather than clamped",
                    r.account, r.currency
                ),
            });
        }
    }
    for t in &comparison.totals {
        if t.budgeted.is_none() || t.actual.is_none() {
            // A total whose component is unknown is itself unknown: summing only
            // the representable rows would print an authoritative-looking figure
            // that silently omits an account. It stays absent, and says why.
            let label = match &t.bucket {
                Bucket::Typed(kind) => types.root_name(*kind).to_string(),
                Bucket::Other(root) => root.as_str().to_string(),
            };
            out.push(BudgetError {
                date: on,
                account: None,
                reason: format!(
                    "the {label} total for {} is absent because at least one \
                     budget in it is too large to represent; the rows show which",
                    t.currency
                ),
            });
        }
    }
    out
}
