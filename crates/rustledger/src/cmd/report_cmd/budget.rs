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
use rustledger_budget::{
    Bucket, BudgetEntry, BudgetError, BudgetRow, BudgetTotal, Budgets, covers,
    passes_account_filter,
};
use rustledger_core::{
    Account, AccountTypeKind, AccountTypes, Currency, Directive, DisplayContext, NaiveDate,
    is_subaccount_or_equal,
};
use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;

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
fn mismatched_currency_errors(
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
        filter.to,
        filter.children,
    ));
    errors.extend(mismatched_currency_errors(
        directives,
        &budgets,
        filter.children,
        filter.from,
        filter.to,
    ));
    errors.extend(closed_account_errors(
        directives,
        &budgets,
        filter.to,
        filter.children,
    ));
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

    // Budgeted VERSUS ACTUAL is the model's job, not the renderer's: which
    // currency a priced posting spends, which direction a credit-normal account
    // counts in, and from which day spending starts counting against a budget
    // are all decisions another consumer would otherwise have to re-derive.
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

    // An un-representable figure is reported in band as well as rendered `n/a`,
    // for ROWS AND TOTALS alike. Without this a consumer sees `"budgeted": null`
    // with an empty `errors` array and cannot tell an overflow from a bug in its
    // own parsing — and a TOTAL can overflow even when every row it sums is
    // individually representable, so covering only the rows left the commonest
    // overflow silent.
    let unrepresentable = |label: &Account, ccy: &Currency| BudgetError {
        date: filter.from,
        account: Some(label.clone()),
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
    for t in &totals {
        if t.budgeted.is_none() || t.actual.is_none() {
            let row = total_row(types, t);
            // A total whose component is unknown is itself unknown: summing only
            // the representable rows would print an authoritative-looking figure
            // that silently omits an account. It stays absent, and says why.
            errors.push(BudgetError {
                date: filter.from,
                account: Some(row.account.clone()),
                reason: format!(
                    "{} for {} is absent because at least one budget in it is \
                     too large to represent; the rows above show which",
                    row.account, t.currency
                ),
            });
        }
    }

    // A budget too small to survive display rounding is diagnosed through the
    // SAME `Rounding` the renderer uses, so the warning and the rendered `0.00`
    // can never disagree about what the display precision is.
    let rounding = Rounding::new(types, &rows, &totals, ctx);
    errors.extend(rounding.sub_precision_errors(&rows, filter.from));

    // Emitted HERE, after every error is known: the un-representable-figure
    // errors are only discovered once rows and totals exist, and an earlier
    // emission point sent them to the JSON array but never to stderr, so a text
    // or CSV user saw `n/a` cells with nothing explaining them.
    errors.sort_by_key(|e| e.date);
    for e in &errors {
        eprintln!("warning: {}: {}", e.date, e.reason);
    }
    render(
        &Rendering { types, ctx, format },
        &rows,
        &totals,
        filter,
        Empty::diagnose(&budgets, had_errors, !errors.is_empty(), filter),
        &errors,
        writer,
    )
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
    /// A stable machine-readable tag for the diagnosis.
    ///
    /// The prose below is for humans and may be reworded; this is what a
    /// dashboard branches on.
    const fn code(self) -> &'static str {
        match self {
            Self::NoneDeclared => "none_declared",
            Self::AllRejected { .. } => "all_rejected",
            Self::NoneInWindow { .. } => "none_in_window",
            Self::FilteredOut => "filtered_out",
        }
    }

    /// The diagnosis in prose, written ONCE and rendered by every format.
    ///
    /// It used to exist only inside the text branch, so CSV and JSON emitted
    /// byte-identical empty output for "you have no budgets", "your budgets
    /// start later than this window" and "--account excluded them all" — the
    /// exact ambiguity this type was introduced to remove, preserved for every
    /// consumer that is not a human reading a terminal.
    fn message(self, filter: &BudgetFilter) -> String {
        match self {
            // Says that each one IS reported, not WHERE. Warnings go to stderr,
            // which a terminal interleaves above this line but an `ag-rledger`
            // JSON envelope drops entirely — so "see the warnings above" pointed
            // an agent at something its transport had already discarded. The
            // JSON format carries them in-band in `errors`.
            Self::AllRejected { shown: true } => {
                "No usable budgets: every `custom \"budget\"` directive in this \
                 ledger was rejected. Each one is reported as a warning."
                    .to_string()
            }
            Self::AllRejected { shown: false } => {
                "No usable budgets: every `custom \"budget\"` directive in this \
                 ledger was rejected. Re-run without --account to see which ones \
                 and why."
                    .to_string()
            }
            Self::NoneDeclared => "No budgets declared. Add e.g.:\n  2024-01-01 custom \"budget\" \
                 Expenses:Food \"monthly\" 400.00 USD"
                .to_string(),
            Self::NoneInWindow { earliest } => format!(
                "No budgets were in force in this period. A budget applies from \
                 its own date onward, and the earliest one here is dated \
                 {earliest}."
            ),
            Self::FilteredOut => format!(
                "No budgets match --account {}. (Accounts are matched by raw \
                 prefix, the same as `report balances`.)",
                super::sanitize_display(filter.account.unwrap_or_default())
            ),
        }
    }

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
    let label = match &total.bucket {
        Bucket::Typed(AccountTypeKind::Expenses) => "TOTAL".to_string(),
        Bucket::Typed(kind) => format!("TOTAL ({})", types.root_name(*kind)),
        Bucket::Other(root) => format!("TOTAL ({root})"),
    };
    BudgetRow {
        account: Account::new(label),
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

fn render<W: Write>(
    env: &Rendering<'_>,
    rows: &[BudgetRow],
    totals: &[BudgetTotal],
    filter: &BudgetFilter,
    empty: Empty,
    errors: &[BudgetError],
    writer: &mut W,
) -> Result<()> {
    let Rendering { types, ctx, format } = *env;
    let rounding = Rounding::new(types, rows, totals, ctx);
    let round_disp = |v: Decimal, ccy: &str| -> Decimal { rounding.round(v, ccy) };
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
        .map(|t| round_row(&total_row(types, t)))
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
            if rows.is_empty() {
                eprintln!("note: {}", empty.message(filter));
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
            // `empty` says WHY there are no rows, and is null whenever there
            // are. Without it the three empty reports were byte-identical to a
            // machine consumer, which is the ambiguity `Empty` exists to
            // remove — it was just never rendered outside the text branch.
            let empty_obj = if rows.is_empty() {
                format!(
                    r#"{{"code": "{}", "message": "{}"}}"#,
                    empty.code(),
                    json_escape(&empty.message(filter))
                )
            } else {
                "null".to_string()
            };
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
                writeln!(writer, "{}", empty.message(filter))?;
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
