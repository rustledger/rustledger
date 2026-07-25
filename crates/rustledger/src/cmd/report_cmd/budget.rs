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
use rustledger_budget::{BudgetEntry, BudgetError, Budgets};
use rustledger_core::{AccountTypes, Directive, DisplayContext, NaiveDate, is_subaccount_or_equal};
use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;

/// Does this account pass the `--account` filter?
///
/// A raw prefix test, matching `balances`, `holdings`, `journal` and `networth`
/// (balances.rs:29) — one flag must select the same accounts in every report, so
/// a user can reconcile a budget's `actual` against `report balances`, and so a
/// partial prefix behaves the same everywhere.
///
/// This is deliberately NOT the component-aware [`is_subaccount_or_equal`] used
/// for budget COVERAGE below. They answer different questions: coverage decides
/// which spending a budget is responsible for — where treating
/// `Expenses:FoodCourt` as part of `Expenses:Food` would be wrong, and is a Fava
/// bug we do not copy — while this is a display filter the user typed.
fn passes_account_filter(account: &str, filter: Option<&str>) -> bool {
    filter.is_none_or(|prefix| account.starts_with(prefix))
}

/// Budgets naming an account the ledger never opens.
///
/// A typo'd account is the worst kind of budget bug: it parses, so `check` is
/// happy, and it renders as a real row at `0.0%` used — the user reads "I have
/// spent none of my food budget" while the actual spending sits on the correctly
/// spelled account, which the report deliberately omits for having no budget.
/// One warning turns that silent misreport into an obvious fix.
fn unopened_account_errors(
    directives: &[Directive],
    budgets: &Budgets,
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
        .iter()
        // A parent budgeted as an aggregate (`Expenses:Food` with only
        // `Expenses:Food:Groceries` opened) is a normal, working setup — but ONLY
        // under `--children`, which is what makes the children's spending answer
        // the parent's budget. In the default mode that budget really does report
        // nothing, so exempting it there restored the silent misreport this check
        // exists to catch.
        .filter(|b| {
            let covered_by_a_child =
                children && opened.iter().any(|o| is_subaccount_or_equal(o, &b.account));
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

/// Does a budget on `budgeted` account for spending booked to `posting_account`?
///
/// The single definition of budget COVERAGE, used by both the rendered rows and
/// the whole-report totals. They were two independent spellings of this rule, so
/// a change to one silently made the TOTAL stop describing the rows above it —
/// and the integration tests, which assert on rendered text, would not have
/// caught it.
///
/// Component-aware by design: `Expenses:FoodCourt` is NOT part of
/// `Expenses:Food`, though Fava's `startswith` test says otherwise.
fn covers(budgeted: &str, posting_account: &str, children: bool) -> bool {
    if children {
        is_subaccount_or_equal(posting_account, budgeted)
    } else {
        posting_account == budgeted
    }
}

/// Budgets that keep accruing after their account was closed.
///
/// `close` means no further postings are possible, so every day after it
/// contributes budget that nothing can ever be spent against — the row then
/// reads as a large underspend. The accrual is deliberately NOT changed: a
/// budget is a declaration in its own right, Fava does not consider `close`
/// either, and silently dropping the tail would be its own surprise. Warning
/// says the same thing without changing a number.
fn closed_account_errors(
    directives: &[Directive],
    budgets: &Budgets,
    to: NaiveDate,
) -> Vec<BudgetError> {
    let mut closed: BTreeMap<&str, NaiveDate> = BTreeMap::new();
    for d in directives {
        if let Directive::Close(c) = d {
            let e = closed.entry(c.account.as_str()).or_insert(c.date);
            *e = (*e).min(c.date);
        }
    }
    let mut seen = BTreeSet::new();
    budgets
        .entries()
        .iter()
        .filter_map(|b| {
            let when = *closed.get(b.account.as_str())?;
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
fn mismatched_currency_errors(
    directives: &[Directive],
    budgets: &Budgets,
    children: bool,
) -> Vec<BudgetError> {
    // Every currency each account actually moves — units and, for a priced or
    // costed posting, the weight currency too, since `90 EUR @ 1.10 USD` is
    // legitimately budgetable in either.
    let mut posted: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
    for d in directives {
        let Directive::Transaction(txn) = d else {
            continue;
        };
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
        .iter()
        .filter(|b| {
            let seen_currencies = covered_currencies(&b.account);
            !seen_currencies.is_empty() && !seen_currencies.contains(&b.currency)
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

/// The first date on which any budget in `covered` was responsible for spending
/// booked to `posting_account` — the day this posting starts counting.
///
/// The dual of the accrual: `accrue` credits nothing before a budget exists, so
/// the actual side must ignore spending from before it too, or a budget added in
/// June is charged with January's groceries.
///
/// This is deliberately per-POSTING-ACCOUNT, not per row. Under `--children` a
/// row covers several budgets with different declaration dates, and taking one
/// minimum for the whole row let an early child budget drag the parent's window
/// backwards — charging the parent row with spending that predated the parent's
/// own budget, and disagreeing with the TOTAL, which had this rule written the
/// other way. Rows and totals now share this one function; that divergence is
/// the same shape as the double-counting bug `covers` was extracted to prevent.
fn clip_start<'a>(
    budgets: &Budgets,
    covered: impl IntoIterator<Item = &'a str>,
    posting_account: &str,
    currency: &str,
    children: bool,
) -> Option<NaiveDate> {
    covered
        .into_iter()
        .filter(|b| covers(b, posting_account, children))
        .filter_map(|b| budgets.effective_start(b, currency))
        .min()
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
    /// `None` when the accrual is not representable — rendered `n/a`, never a
    /// clamped number passed off as the answer.
    budgeted: Option<Decimal>,
    /// `None` when the spending sum is not representable, for the same reason.
    actual: Option<Decimal>,
}

impl BudgetRow {
    /// Budget minus actual. Positive is under budget (money left), negative over.
    ///
    /// `actual` is already sign-normalized (see [`normalized_actual`]) so this
    /// subtraction reads the same way for a spending budget and an earning target.
    fn remaining(&self) -> Option<Decimal> {
        self.budgeted?.checked_sub(self.actual?)
    }

    /// Fraction of the budget used, `None` when nothing was budgeted (which would
    /// be a division by zero, not 0% or 100%).
    fn used_fraction(&self) -> Option<f64> {
        let budgeted = self.budgeted?;
        if budgeted.is_zero() {
            return None;
        }
        let b: f64 = budgeted.try_into().ok()?;
        let a: f64 = self.actual?.try_into().ok()?;
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
    errors.extend(unopened_account_errors(
        directives,
        &budgets,
        filter.children,
    ));
    errors.extend(mismatched_currency_errors(
        directives,
        &budgets,
        filter.children,
    ));
    errors.extend(closed_account_errors(directives, &budgets, filter.to));
    // Whether the ledger had ANY unusable budget, computed before the filter:
    // `Empty::diagnose` must not conclude "no budgets declared" for a ledger
    // whose budgets were all rejected merely because `--account` excluded them
    // from display.
    let had_errors = !errors.is_empty();
    // Only warn about budgets this invocation actually reports on: narrowing to
    // one account should not emit stderr noise (or JSON `errors` entries) about
    // accounts the user explicitly excluded.
    if let Some(prefix) = filter.account {
        errors.retain(|e| {
            e.account
                .as_deref()
                .is_none_or(|a| passes_account_filter(a, Some(prefix)))
        });
    }
    // Warnings are emitted below, once the rows are built: an un-representable
    // figure is only discovered then, and stderr and the JSON `errors` array
    // must report the same set.

    // Actual spend per (account, currency) inside the window. Postings are read
    // directly rather than through `account_balances` because a budget is about
    // FLOW over a period, not the running balance an inventory realizes.
    //
    // A posting priced or held at a cost moved money in TWO currencies:
    // `Expenses:Travel 90.00 EUR @ 1.10 USD` is both 90 EUR of travel and 99 USD
    // out of pocket, and both are true. It is therefore recorded under both keys,
    // and each budget row reads only its own currency — a EUR budget sees 90, a
    // USD budget sees 99, and neither is affected by whether the other exists.
    //
    // Deciding this once, globally, from "which currencies did anyone budget in"
    // was wrong: adding an unrelated `custom "budget" Expenses:Travel ... EUR`
    // moved an *Expenses:Food* posting from its USD row to a EUR key no row read,
    // silently zeroing that account's reported spend. Rows never sum across
    // currencies, so recording both costs nothing and couples nothing.
    //
    // The weight (and its cost-beats-price ladder) comes from
    // `rustledger_booking::posting_weight`, shared with BQL's `weight` column so
    // the two cannot drift. Note it is NOT byte-for-byte the balance validator's
    // rule: the two differ on cost specs lacking an explicit currency and on a
    // bare `{}` (issue #1026), both documented on `posting_weight` itself.
    let mut actuals: BTreeMap<(String, String), Vec<(NaiveDate, Decimal)>> = BTreeMap::new();
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
            match rustledger_booking::posting_weight(p) {
                // Same currency, different number (`90.00 USD @@ 95.00 USD`, or a
                // cost denominated in the units currency): there is only ONE
                // currency here and the weight is what the posting really moved.
                // Recording the units instead made the report disagree with
                // `rledger check` and BQL's `weight` column on the same posting.
                Some(weight) if weight.currency == units.currency => {
                    actuals
                        .entry((p.account.to_string(), weight.currency.to_string()))
                        .or_default()
                        .push((txn.date, weight.number));
                }
                // Two currencies: the posting is budgetable in either, so record
                // both and let each row read its own.
                Some(weight) => {
                    actuals
                        .entry((p.account.to_string(), units.currency.to_string()))
                        .or_default()
                        .push((txn.date, units.number));
                    actuals
                        .entry((p.account.to_string(), weight.currency.to_string()))
                        .or_default()
                        .push((txn.date, weight.number));
                }
                None => {
                    actuals
                        .entry((p.account.to_string(), units.currency.to_string()))
                        .or_default()
                        .push((txn.date, units.number));
                }
            }
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
    // A row is live when a budget it COVERS is live, which under `--children`
    // is not the same as the account's own declarations being live: a parent
    // whose own budget starts next year still aggregates a child budget that is
    // running now, and dropping that row lost the aggregate the flag exists to
    // provide. Row identities still come from declared pairs, so no row is
    // invented for an account nobody budgeted in that currency.
    let keys: Vec<(String, String)> = if filter.children {
        budgets
            .all_keys()
            .into_iter()
            .filter(|(account, currency)| {
                budgets.entries().iter().any(|b| {
                    b.currency == *currency
                        && b.from < filter.to
                        && covers(account, &b.account, true)
                })
            })
            .collect()
    } else {
        budgets.keys_in_force_before(filter.to)
    };

    let budgets_ref = &budgets;
    let mut rows: Vec<BudgetRow> = keys
        .into_iter()
        .filter(|(account, _)| passes_account_filter(account, filter.account))
        .map(|(account, currency)| {
            // The budget accounts this row is responsible for: itself, plus every
            // child budget under `--children` (Fava's child mode adds them rather
            // than letting the parent absorb them).
            let covered_budgets: Vec<&String> = if filter.children {
                let mut all: Vec<&String> = budgets
                    .entries()
                    .iter()
                    .filter(|b| b.currency == currency && covers(&account, &b.account, true))
                    .map(|b| &b.account)
                    .collect();
                all.sort();
                all.dedup();
                all
            } else {
                vec![&account]
            };
            // An un-representable accrual (only reachable from an absurd declared
            // amount) is reported as such rather than clamped: a clamped figure
            // is wrong by an unbounded factor and looks authoritative.
            let budgeted: Option<Decimal> = covered_budgets
                .iter()
                .map(|a| budgets.accrue(a, &currency, filter.from, filter.to))
                .try_fold(Decimal::ZERO, |acc, seg| {
                    seg.and_then(|s| acc.checked_add(s))
                });
            // Spending counts from the day a budget covering THAT account
            // existed — see `clip_start`. Summed with `checked_add` for the same
            // reason the budgeted side is: a ledger `check` accepts must not
            // panic the report.
            let actual = actuals
                .iter()
                .filter(|((a, c), _)| *c == currency && covers(&account, a, filter.children))
                .flat_map(|((a, _), entries)| {
                    let start = clip_start(
                        budgets_ref,
                        covered_budgets.iter().map(|s| s.as_str()),
                        a,
                        &currency,
                        filter.children,
                    )
                    .unwrap_or(filter.from)
                    .max(filter.from);
                    entries
                        .iter()
                        .filter(move |(date, _)| *date >= start)
                        .map(move |(_, v)| normalized_actual(types, a, *v))
                })
                .try_fold(Decimal::ZERO, Decimal::checked_add);
            BudgetRow {
                account,
                currency,
                budgeted,
                actual,
            }
        })
        .collect();
    rows.sort_by(|a, b| (&a.account, &a.currency).cmp(&(&b.account, &b.currency)));

    let totals = compute_totals(&budgets, &actuals, filter, types);

    // An un-representable figure is reported in band as well as rendered `n/a`,
    // for ROWS AND TOTALS alike. Without this a consumer sees `"budgeted": null`
    // with an empty `errors` array and cannot tell an overflow from a bug in its
    // own parsing — and a TOTAL can overflow even when every row it sums is
    // individually representable, so covering only the rows left the commonest
    // overflow silent.
    let unrepresentable = |label: &str, ccy: &str| BudgetError {
        date: filter.from,
        account: Some(label.to_string()),
        reason: format!(
            "budget for {label} in {ccy} is too large to represent; \
             the figure is reported as absent rather than clamped"
        ),
    };
    for r in &rows {
        if r.budgeted.is_none() || r.actual.is_none() {
            errors.push(unrepresentable(&r.account, &r.currency));
        }
    }
    for ((ccy, credit), (b, a)) in &totals {
        if b.is_none() || a.is_none() {
            let row = total_row(ccy, *credit, *b, *a);
            errors.push(unrepresentable(&row.account, ccy));
        }
    }

    // Emitted HERE, after every error is known: the un-representable-figure
    // errors are only discovered once rows and totals exist, and an earlier
    // emission point sent them to the JSON array but never to stderr, so a text
    // or CSV user saw `n/a` cells with nothing explaining them.
    errors.sort_by_key(|e| e.date);
    for e in &errors {
        eprintln!("warning: {}: {}", e.date, e.reason);
    }
    render(
        &rows,
        &totals,
        filter,
        Empty::diagnose(&budgets, had_errors, !errors.is_empty(), filter),
        &errors,
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
    actuals: &BTreeMap<(String, String), Vec<(NaiveDate, Decimal)>>,
    filter: &BudgetFilter,
    types: &AccountTypes,
) -> BTreeMap<(String, bool), (Option<Decimal>, Option<Decimal>)> {
    // Distinct budgeted (account, currency) pairs, after the account filter.
    let pairs: Vec<(String, String)> = budgets
        .keys_in_force_before(filter.to)
        .into_iter()
        .filter(|(account, _)| passes_account_filter(account, filter.account))
        .collect();

    let mut totals: BTreeMap<(String, bool), (Option<Decimal>, Option<Decimal>)> = BTreeMap::new();
    for (account, currency) in &pairs {
        let e = totals
            .entry((currency.clone(), types.is_credit_normal(account)))
            .or_insert((Some(Decimal::ZERO), Some(Decimal::ZERO)));
        e.0 = e.0.and_then(|acc| {
            budgets
                .accrue(account, currency, filter.from, filter.to)
                .and_then(|seg| acc.checked_add(seg))
        });
    }
    // Each posting counts once, against whichever budgeted accounts cover it —
    // and, as on the row side, only from the day one of those budgets existed.
    for ((account, currency), entries) in actuals {
        // The same `clip_start` the rows use, over the budget accounts that
        // cover this posting's account in this currency.
        let covering = pairs
            .iter()
            .filter(|(_, c)| c == currency)
            .map(|(b, _)| b.as_str());
        let Some(start) = clip_start(budgets, covering, account, currency, filter.children) else {
            continue;
        };
        let start = start.max(filter.from);
        let e = totals
            .entry((currency.clone(), types.is_credit_normal(account)))
            .or_insert((Some(Decimal::ZERO), Some(Decimal::ZERO)));
        for (_, raw) in entries.iter().filter(|(d, _)| *d >= start) {
            e.1 =
                e.1.and_then(|acc| acc.checked_add(normalized_actual(types, account, *raw)));
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
    /// Every budget directive in the ledger was rejected as malformed.
    /// `shown` is false when `--account` filtered away every warning, in which
    /// case pointing the user at warnings that are not on screen is worse than
    /// saying nothing.
    AllRejected { shown: bool },
    /// Budgets exist but all start on or after the window's exclusive end.
    NoneInWindow { earliest: NaiveDate },
    /// Budgets were in force, but `--account` excluded every one.
    FilteredOut,
}

impl Empty {
    fn diagnose(
        budgets: &Budgets,
        had_errors: bool,
        errors_shown: bool,
        filter: &BudgetFilter,
    ) -> Self {
        // Diagnose over the budgets the user asked about. Testing "is anything
        // in force" across the WHOLE ledger let an unrelated account's live
        // budget mask the real reason: a report filtered to an account whose
        // budget simply starts later was blamed on the `--account` prefix, and
        // the user sent to debug a name that was in fact matching.
        let in_scope: Vec<&BudgetEntry> = budgets
            .entries()
            .iter()
            .filter(|e| passes_account_filter(&e.account, filter.account))
            .collect();
        // Three different answers, in order of what the user most needs to know.
        if budgets.is_empty() {
            // Nothing parsed at all: either the ledger has no budgets, or every
            // directive in it was rejected. Saying "no budgets declared" for the
            // latter sends the user looking for syntax they are not missing.
            return if had_errors {
                Self::AllRejected {
                    shown: errors_shown,
                }
            } else {
                Self::NoneDeclared
            };
        }
        let Some(earliest) = in_scope.iter().map(|e| e.from).min() else {
            // Budgets exist, but none of them are under `--account`.
            return Self::FilteredOut;
        };
        if !in_scope.iter().any(|e| e.from < filter.to) {
            return Self::NoneInWindow { earliest };
        }
        Self::FilteredOut
    }
}

/// A whole-report total as a row, so totals and rows render through one path.
fn total_row(
    currency: &str,
    credit_normal: bool,
    budgeted: Option<Decimal>,
    actual: Option<Decimal>,
) -> BudgetRow {
    BudgetRow {
        // Spending budgets and earning targets are totaled separately: adding a
        // 5000 salary target to a 400 travel budget gives a figure that means
        // nothing, and a `Used` percentage that reads far healthier than the
        // spending actually is.
        account: if credit_normal {
            "TOTAL (earned)".to_string()
        } else {
            "TOTAL".to_string()
        },
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
    totals: &BTreeMap<(String, bool), (Option<Decimal>, Option<Decimal>)>,
    filter: &BudgetFilter,
    empty: Empty,
    errors: &[BudgetError],
    ctx: &DisplayContext,
    format: &OutputFormat,
    writer: &mut W,
) -> Result<()> {
    // Round to display precision ONCE, up front, and render every format from
    // the rounded values. Computing the percentage from the unrounded figures
    // while showing rounded ones let a row print `budgeted 0, actual 0,
    // remaining 0, used_pct 2033.3` — four fields a consumer cannot reconcile.
    // All four now derive from the same numbers.
    /// How many decimals to show for a currency the ledger never describes.
    /// Enough for a crypto-scale budget, far from `Decimal`'s 28.
    const MAX_UNTRACKED_DP: u32 = 8;
    let untracked_scale: BTreeMap<String, u32> = {
        let mut m: BTreeMap<String, u32> = BTreeMap::new();
        let all_totals: Vec<BudgetRow> = totals
            .iter()
            .map(|((ccy, credit), (b, a))| total_row(ccy, *credit, *b, *a))
            .collect();
        for r in rows.iter().chain(all_totals.iter()) {
            if ctx.get_precision(&r.currency).is_some() {
                continue;
            }
            let seen = [r.budgeted, r.actual, r.remaining()]
                .into_iter()
                .flatten()
                // Raw scale, not normalized: a declared `100.00 USD` keeps its
                // trailing zeros, while a pro-rated (28-digit) value is capped.
                .map(|v| v.scale().min(MAX_UNTRACKED_DP))
                .max()
                .unwrap_or(0);
            let e = m.entry(r.currency.clone()).or_default();
            *e = (*e).max(seen);
        }
        m
    };
    let round_disp = |v: Decimal, ccy: &str| -> Decimal {
        ctx.get_precision(ccy).map_or_else(
            || {
                v.round_dp(
                    untracked_scale
                        .get(ccy)
                        .copied()
                        .unwrap_or(MAX_UNTRACKED_DP),
                )
            },
            |dp| v.round_dp(dp),
        )
    };
    let round_row = |r: &BudgetRow| BudgetRow {
        account: r.account.clone(),
        currency: r.currency.clone(),
        budgeted: r.budgeted.map(|v| round_disp(v, &r.currency)),
        actual: r.actual.map(|v| round_disp(v, &r.currency)),
    };
    let rows: Vec<BudgetRow> = rows.iter().map(round_row).collect();
    let rows = &rows[..];
    let total_rows: Vec<BudgetRow> = totals
        .iter()
        .map(|((ccy, credit), (b, a))| round_row(&total_row(ccy, *credit, *b, *a)))
        .collect();

    // A pro-rated budget is a repeating decimal, so it MUST be rounded for
    // display. The ledger's `DisplayContext` answers for any currency it has
    // seen; for one it has not (a budget added before any spending is recorded)
    // the report picks the scale itself — see `untracked_scale`, which chooses
    // ONE per currency so the cells of a row agree with each other.
    let money = |n: Decimal, ccy: &str| {
        ctx.get_precision(ccy).map_or_else(
            || {
                let dp = untracked_scale.get(ccy).copied().unwrap_or(0);
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
            for row in &total_rows {
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
            let total_objs: Vec<String> = total_rows.iter().map(obj).collect();
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
            writeln!(
                writer,
                r#"{{"from": "{}", "to": "{}", "budgets": [{}], "totals": [{}], "errors": [{}]}}"#,
                filter.from,
                filter.to,
                objs.join(", "),
                total_objs.join(", "),
                error_objs.join(", ")
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
                    Empty::AllRejected { shown: true } => writeln!(
                        writer,
                        "No usable budgets: every `custom \"budget\"` directive in \
                         this ledger was rejected. See the warnings above."
                    )?,
                    Empty::AllRejected { shown: false } => writeln!(
                        writer,
                        "No usable budgets: every `custom \"budget\"` directive in \
                         this ledger was rejected. Re-run without --account to see \
                         which ones and why."
                    )?,
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
                        "No budgets match --account {}. (Accounts are matched by raw \
                         prefix, the same as `report balances`.)",
                        super::sanitize_display(filter.account.unwrap_or_default())
                    )?,
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
                    .chain(total_rows.iter())
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
            for r in &total_rows {
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
