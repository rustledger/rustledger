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

use crate::{BudgetError, Budgets, Comparison, covers, passes_account_filter};
use rustledger_core::{Account, AccountTypes, Currency, Directive, NaiveDate};
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
            // The opened accounts in this budget's subtree, as an ordered RANGE
            // rather than a scan of every account the ledger opens. Same bound
            // and same reasoning as `subtree_range` in `compare`: `;` (0x3B) is
            // the byte after `:`, so it admits every true subaccount, and
            // `covers` still decides — a range that merely narrows cannot
            // change the answer, and `take_while` here would be the bug that
            // one already had.
            let upper = format!("{};", b.account);
            let covering: Vec<&str> = if children {
                opened
                    .range(b.account.as_str()..upper.as_str())
                    .copied()
                    .filter(|acct| covers(&b.account, acct, true))
                    .collect()
            } else {
                // Exact match: a budget covers only its own account.
                opened
                    .get(b.account.as_str())
                    .copied()
                    .into_iter()
                    .collect()
            };
            if covering.is_empty() {
                return None;
            }
            // The LAST covering account to close, and WHICH one it was. Under
            // `--children` a budget on `Expenses:Food` can be answered entirely
            // by `Expenses:Food:Restaurant`, and it is that descendant's `close`
            // the date comes from — naming only the budgeted account sent the
            // reader looking for a `close Expenses:Food` directive that does not
            // exist in their ledger.
            let (last_closed, when) = covering
                .iter()
                .map(|acct| closed.get(acct).map(|d| (*acct, *d)))
                .collect::<Option<Vec<_>>>()?
                .into_iter()
                .max_by_key(|(_, d)| *d)?;
            // Only if the budget is still running past the close inside this
            // window; a budget that ended before it is unremarkable.
            // Any budget that accrues on or after the close is unspendable for
            // those days. A budget declared AFTER the close is the worse case —
            // it can never see a single posting — and an earlier `b.from <= when`
            // guard silently excluded exactly that one.
            (when < to && b.from < to && seen.insert(b.account.clone())).then(|| BudgetError {
                date: when,
                account: Some(b.account.clone()),
                reason: {
                    // Name the account that actually closed whenever it is not
                    // the budgeted one, so the date and the directive the reader
                    // is sent to look at belong together.
                    let closed_what = if last_closed == b.account.as_str() {
                        format!("the account was closed on {when}")
                    } else {
                        format!("{last_closed}, the last account it covers, was closed on {when}")
                    };
                    if b.from >= when {
                        format!(
                            "budget for {} starts {} but {closed_what}; \
                             no spending can ever be booked to it",
                            b.account, b.from
                        )
                    } else {
                        format!(
                            "budget for {} keeps accruing after {closed_what}; \
                             no spending can be booked to it after that date",
                            b.account
                        )
                    }
                },
            })
        })
        .collect()
}
/// Budgets whose currency the account never posts in.
///
/// `posted` is "which currencies did each account move in this window", read
/// off the spending the comparison already collected rather than re-derived.
/// It was re-derived once — the same window filter, the same units-and-weight
/// rule, written twice — and two places deciding which currencies a posting
/// moves is exactly the drift this repo's canonical-function discipline exists
/// to prevent: a change to one would have made the warning disagree with the
/// figures it sits beside.
///
/// The sibling of the typo'd-account check, and the same silent misreport: a
/// budget written in `USF` against an account that posts `USD` renders a tidy
/// `0.0%` used row while the real spending sits one keystroke away. Only
/// accounts that DO post something are checked, so a budget set up before any
/// spending is recorded stays quiet.
pub fn mismatched_currency_errors(
    posted: &BTreeMap<&Account, BTreeSet<&Currency>>,
    budgets: &Budgets,
    children: bool,
    to: NaiveDate,
) -> Vec<BudgetError> {
    // Which currencies a budget could possibly see, under the SAME coverage rule
    // the report uses: with `--children` a parent budget is answered by its
    // children's postings, so checking the parent account alone both missed the
    // typo it exists to catch (spending lives on the children) and warned falsely
    // when the parent itself happened to post one other currency.
    let covered_currencies = |budgeted: &str| -> BTreeSet<String> {
        posted
            .iter()
            .filter(|(account, _)| covers(budgeted, account.as_str(), children))
            .flat_map(|(_, currencies)| currencies.iter().map(|c| c.as_str().to_string()))
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
        .filter(|b| seen.insert((b.account.clone(), b.currency.clone())))
        // Computed ONCE per budget and carried to the message. It was computed
        // in the filter and again to format, and each call scans every posting
        // account and clones every currency it finds.
        .filter_map(|b| {
            let seen_currencies = covered_currencies(&b.account);
            let mismatched =
                !seen_currencies.is_empty() && !seen_currencies.contains(b.currency.as_str());
            mismatched.then_some((b, seen_currencies))
        })
        .map(|(b, seen_currencies)| {
            let actually = seen_currencies.into_iter().collect::<Vec<_>>().join(", ");
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
/// The window and selection a report was asked for.
///
/// Bundled because they travel together through every diagnostic and are never
/// chosen independently — and because passing them positionally made this the
/// kind of call where two arguments of the same type can be swapped silently.
pub struct Scope<'a> {
    /// Inclusive start of the reported window.
    pub from: NaiveDate,
    /// Exclusive end.
    pub to: NaiveDate,
    /// Whether a budget covers its subaccounts.
    pub children: bool,
    /// Raw account prefix the report is narrowed to, if any.
    pub account_filter: Option<&'a str>,
}

pub fn collect(
    budgets: &Budgets,
    directives: &[Directive],
    comparison: &Comparison,
    types: &AccountTypes,
    scope: &Scope<'_>,
    posted: &BTreeMap<&Account, BTreeSet<&Currency>>,
) -> Vec<BudgetError> {
    let Scope {
        from,
        to,
        children,
        account_filter,
    } = *scope;
    // The directives that could not be read come first in provenance but not in
    // order: everything is sorted by date at the end, so the caller never sees
    // parse failures and report warnings interleaved differently depending on
    // which surface it asked.
    let mut errors = budgets.errors().to_vec();
    errors.extend(unopened_account_errors(directives, budgets, to, children));
    errors.extend(mismatched_currency_errors(posted, budgets, children, to));
    errors.extend(closed_account_errors(directives, budgets, to, children));
    if let Some(prefix) = account_filter {
        // An error we cannot attribute to an account is dropped under an
        // explicit filter, not kept. `is_none_or` kept it, so a report narrowed
        // to `Expenses` warned about a directive whose account could not even be
        // lexed — and, worse, that surviving warning made `AllRejected` claim
        // every rejection was on screen when the attributable ones had been
        // filtered away. A caller who asked about one account is owed warnings
        // about that account; one we cannot place is not known to be about it.
        errors.retain(|e| {
            e.account
                .as_ref()
                .is_some_and(|a| passes_account_filter(a.as_str(), Some(prefix)))
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
            out.push(BudgetError {
                date: on,
                account: None,
                reason: format!(
                    "{} for {} is absent because at least one budget in it is \
                     too large to represent; the rows show which",
                    t.bucket.label(types),
                    t.currency
                ),
            });
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Bucket, BudgetEntry, BudgetRow, BudgetTotal, Interval};
    use rust_decimal::Decimal;
    use rustledger_core::{Close, Open, naive_date};

    fn d(y: i32, m: u32, day: u32) -> NaiveDate {
        naive_date(y, m, day).unwrap()
    }

    fn budget(from: NaiveDate, account: &str, currency: &str) -> BudgetEntry {
        BudgetEntry {
            from,
            account: Account::new(account),
            interval: Interval::Month,
            amount: Decimal::from(100),
            currency: Currency::new(currency),
        }
    }

    fn open(day: NaiveDate, account: &str) -> Directive {
        Directive::Open(Open::new(day, account))
    }

    fn close(day: NaiveDate, account: &str) -> Directive {
        Directive::Close(Close::new(day, account))
    }

    fn reasons(errors: &[BudgetError]) -> Vec<&str> {
        errors.iter().map(|e| e.reason.as_str()).collect()
    }

    /// A budget on an account the ledger never opens is the worst kind of budget
    /// bug: it parses, renders as a real row at 0.0% used, and the real spending
    /// sits on the correctly spelled account the report omits for having no
    /// budget.
    #[test]
    fn an_unopened_budgeted_account_is_reported() {
        let dirs = vec![open(d(2024, 1, 1), "Expenses:Food")];
        let b = Budgets::new(vec![
            budget(d(2024, 1, 1), "Expenses:Food", "USD"),
            budget(d(2024, 1, 1), "Expenses:Fodo", "USD"),
        ]);
        let got = unopened_account_errors(&dirs, &b, d(2024, 3, 1), false);
        assert_eq!(got.len(), 1, "{:?}", reasons(&got));
        assert!(got[0].reason.contains("Expenses:Fodo"), "{:?}", got[0]);

        // A ledger with no `open` directives at all is not using them.
        assert!(unopened_account_errors(&[], &b, d(2024, 3, 1), false).is_empty());

        // Windowed: a budget declared at or after the exclusive end is not this
        // report's business.
        let later = Budgets::new(vec![budget(d(2099, 1, 1), "Expenses:Fodo", "USD")]);
        assert!(unopened_account_errors(&dirs, &later, d(2024, 3, 1), false).is_empty());

        // Under `--children` a parent budgeted as an aggregate is normal — its
        // children answer it — but in the default mode it really does report
        // nothing, so the exemption must NOT apply there.
        let parent = Budgets::new(vec![budget(d(2024, 1, 1), "Expenses:Food", "USD")]);
        let child_only = vec![open(d(2024, 1, 1), "Expenses:Food:Restaurant")];
        assert!(unopened_account_errors(&child_only, &parent, d(2024, 3, 1), true).is_empty());
        assert_eq!(
            unopened_account_errors(&child_only, &parent, d(2024, 3, 1), false).len(),
            1,
            "without --children the parent's budget really does see nothing"
        );
    }

    /// `close` means no further postings, so every day after it accrues budget
    /// nothing can be spent against — the row reads as a large underspend.
    #[test]
    fn a_budget_outliving_its_account_is_reported() {
        let dirs = vec![
            open(d(2024, 1, 1), "Expenses:Food"),
            close(d(2024, 2, 15), "Expenses:Food"),
        ];
        let b = Budgets::new(vec![budget(d(2024, 1, 1), "Expenses:Food", "USD")]);
        let got = closed_account_errors(&dirs, &b, d(2024, 4, 1), false);
        assert_eq!(got.len(), 1, "{:?}", reasons(&got));
        assert!(got[0].reason.contains("keeps accruing"), "{:?}", got[0]);

        // A budget declared AFTER the close can never see a posting at all —
        // the worse case, and phrased differently.
        let after = Budgets::new(vec![budget(d(2024, 3, 1), "Expenses:Food", "USD")]);
        let got = closed_account_errors(&dirs, &after, d(2024, 4, 1), false);
        assert!(got[0].reason.contains("can ever be booked"), "{:?}", got[0]);

        // A close at or after the window's exclusive end strands nothing.
        assert!(closed_account_errors(&dirs, &b, d(2024, 2, 1), false).is_empty());

        // An account that never closes is unremarkable.
        let never = vec![open(d(2024, 1, 1), "Expenses:Food")];
        assert!(closed_account_errors(&never, &b, d(2024, 4, 1), false).is_empty());
    }

    /// ALL of a budget's covering accounts must be closed, not any: warning while
    /// a sibling is still open would sit directly above a row showing spending
    /// booked through it. The date is the LAST close, and the message names
    /// whichever account it was.
    #[test]
    fn children_close_only_when_every_covering_account_has() {
        let b = Budgets::new(vec![budget(d(2024, 1, 1), "Expenses:Food", "USD")]);
        let one_open = vec![
            open(d(2024, 1, 1), "Expenses:Food:Restaurant"),
            open(d(2024, 1, 1), "Expenses:Food:Groceries"),
            close(d(2024, 2, 10), "Expenses:Food:Restaurant"),
        ];
        assert!(
            closed_account_errors(&one_open, &b, d(2024, 4, 1), true).is_empty(),
            "spending can still be booked through the open sibling"
        );

        let mut both = one_open;
        both.push(close(d(2024, 2, 20), "Expenses:Food:Groceries"));
        let got = closed_account_errors(&both, &b, d(2024, 4, 1), true);
        assert_eq!(got.len(), 1, "{:?}", reasons(&got));
        // The LAST close, and the account it belongs to — not the budgeted
        // account, which has no `close` directive of its own.
        assert_eq!(got[0].date, d(2024, 2, 20));
        assert!(
            got[0].reason.contains("Expenses:Food:Groceries"),
            "{:?}",
            got[0]
        );
    }

    /// A budget in a currency the account never posts reports no spending, and
    /// looks exactly like an unspent budget.
    #[test]
    fn a_currency_the_account_never_posts_is_reported() {
        let food = Account::new("Expenses:Food");
        let usd = Currency::new("USD");
        let posted: BTreeMap<&Account, BTreeSet<&Currency>> =
            std::iter::once((&food, std::iter::once(&usd).collect())).collect();

        let eur = Budgets::new(vec![budget(d(2024, 1, 1), "Expenses:Food", "EUR")]);
        let got = mismatched_currency_errors(&posted, &eur, false, d(2024, 3, 1));
        assert_eq!(got.len(), 1, "{:?}", reasons(&got));
        assert!(got[0].reason.contains("only posts USD"), "{:?}", got[0]);

        // The currency it does post is silent.
        let ok = Budgets::new(vec![budget(d(2024, 1, 1), "Expenses:Food", "USD")]);
        assert!(mismatched_currency_errors(&posted, &ok, false, d(2024, 3, 1)).is_empty());

        // An account that posted NOTHING in the window is unspent, not a
        // mismatch — warning there would name an empty list of currencies.
        let other = Budgets::new(vec![budget(d(2024, 1, 1), "Expenses:Travel", "EUR")]);
        assert!(mismatched_currency_errors(&posted, &other, false, d(2024, 3, 1)).is_empty());

        // Windowed by the budget's own date, like the other two.
        let later = Budgets::new(vec![budget(d(2099, 1, 1), "Expenses:Food", "EUR")]);
        assert!(mismatched_currency_errors(&posted, &later, false, d(2024, 3, 1)).is_empty());
    }

    /// The opened-account range must never EXCLUDE a covering account.
    ///
    /// The budget's OWN account is deliberately not opened: that forces the
    /// range to reach past a sibling to find the children, which is where the
    /// bound matters. `'0'` (0x30) and `'-'` (0x2D) sort below `':'` (0x3A), so
    /// `Expenses:Food0` lands between `Expenses:Food` and its children. A scan
    /// that stops at the first non-covering account finds nothing at all here,
    /// and a budget whose every covering account has closed goes unreported.
    ///
    /// An earlier version of this test opened every account including the
    /// budget's own, so the range never had to travel — and it passed against
    /// the broken form. Verified by applying that form and watching this fail.
    #[test]
    fn the_opened_range_never_hides_a_covering_account() {
        let b = Budgets::new(vec![budget(d(2024, 1, 1), "Expenses:Food", "USD")]);
        // Siblings that sort INSIDE the parent's byte range, then the real
        // children behind them. `Expenses:Food` itself is never opened.
        let dirs = vec![
            open(d(2024, 1, 1), "Expenses:Food0"),
            open(d(2024, 1, 1), "Expenses:Food-Bar"),
            open(d(2024, 1, 1), "Expenses:Food:Restaurant"),
            close(d(2024, 2, 1), "Expenses:Food:Restaurant"),
        ];
        let got = closed_account_errors(&dirs, &b, d(2024, 4, 1), true);
        assert_eq!(
            got.len(),
            1,
            "the only covering account closed, so this must warn — finding \
             nothing means the range stopped at a sibling"
        );
        assert!(
            got[0].reason.contains("Expenses:Food:Restaurant"),
            "{:?}",
            got[0]
        );

        // ...and the siblings are NOT covering, so closing them changes nothing
        // while a real child stays open.
        let sibling_closed = vec![
            open(d(2024, 1, 1), "Expenses:Food0"),
            close(d(2024, 2, 1), "Expenses:Food0"),
            open(d(2024, 1, 1), "Expenses:Food:Restaurant"),
        ];
        assert!(
            closed_account_errors(&sibling_closed, &b, d(2024, 4, 1), true).is_empty(),
            "a closed SIBLING is not a closed covering account"
        );
    }

    /// Every diagnostic's window bound is EXCLUSIVE at `to`: a budget or a close
    /// dated exactly on it contributes nothing to this report and must not be
    /// judged by it. Only a date ON the bound separates `<` from `<=`.
    #[test]
    fn the_window_bound_is_exclusive_in_every_diagnostic() {
        let to = d(2024, 3, 1);
        let on_bound = Budgets::new(vec![budget(to, "Expenses:Nosuch", "USD")]);
        let inside = Budgets::new(vec![budget(d(2024, 2, 28), "Expenses:Nosuch", "USD")]);
        let opened = vec![open(d(2024, 1, 1), "Expenses:Food")];
        assert!(unopened_account_errors(&opened, &on_bound, to, false).is_empty());
        assert_eq!(
            unopened_account_errors(&opened, &inside, to, false).len(),
            1
        );

        let food = Account::new("Expenses:Food");
        let usd = Currency::new("USD");
        let posted: BTreeMap<&Account, BTreeSet<&Currency>> =
            std::iter::once((&food, std::iter::once(&usd).collect())).collect();
        let eur_on = Budgets::new(vec![budget(to, "Expenses:Food", "EUR")]);
        let eur_in = Budgets::new(vec![budget(d(2024, 2, 28), "Expenses:Food", "EUR")]);
        assert!(mismatched_currency_errors(&posted, &eur_on, false, to).is_empty());
        assert_eq!(
            mismatched_currency_errors(&posted, &eur_in, false, to).len(),
            1
        );

        // The closed check has TWO bounds: the close date and the budget's own.
        let b = Budgets::new(vec![budget(d(2024, 1, 1), "Expenses:Food", "USD")]);
        let close_on = vec![
            open(d(2024, 1, 1), "Expenses:Food"),
            close(to, "Expenses:Food"),
        ];
        let close_in = vec![
            open(d(2024, 1, 1), "Expenses:Food"),
            close(d(2024, 2, 28), "Expenses:Food"),
        ];
        assert!(closed_account_errors(&close_on, &b, to, false).is_empty());
        assert_eq!(closed_account_errors(&close_in, &b, to, false).len(), 1);
        let budget_on = Budgets::new(vec![budget(to, "Expenses:Food", "USD")]);
        assert!(closed_account_errors(&close_in, &budget_on, to, false).is_empty());
    }

    /// `collect` is the one entry point, and it really does gather from every
    /// source — the parse failures the index kept, the three report checks, and
    /// the absent figures.
    #[test]
    fn collect_gathers_from_every_source() {
        let types = AccountTypes::default();
        let b = Budgets::new(vec![budget(d(2024, 1, 1), "Expenses:Fodo", "USD")]);
        let dirs = vec![open(d(2024, 1, 1), "Expenses:Food")];
        let comparison = Comparison {
            rows: vec![BudgetRow {
                account: Account::new("Expenses:Fodo"),
                currency: Currency::new("USD"),
                budgeted: None,
                actual: Some(Decimal::ONE),
            }],
            totals: Vec::new(),
            errors: Vec::new(),
            empty: None,
        };
        let scope = Scope {
            from: d(2024, 1, 1),
            to: d(2024, 3, 1),
            children: false,
            account_filter: None,
        };
        let posted = BTreeMap::new();
        let got = collect(&b, &dirs, &comparison, &types, &scope, &posted);
        // The unopened-account warning AND the absent figure, in date order.
        assert_eq!(got.len(), 2, "{:?}", reasons(&got));
        assert!(got.iter().any(|e| e.reason.contains("no such account")));
        assert!(
            got.iter()
                .any(|e| e.reason.contains("too large to represent"))
        );
    }

    /// An absent figure is reported in band: without this a consumer sees a null
    /// number with an empty error list and cannot tell an overflow from a bug in
    /// its own parsing.
    #[test]
    fn an_absent_figure_is_explained() {
        let types = AccountTypes::default();
        let row = |budgeted: Option<i64>, actual: Option<i64>| BudgetRow {
            account: Account::new("Expenses:Food"),
            currency: Currency::new("USD"),
            budgeted: budgeted.map(Decimal::from),
            actual: actual.map(Decimal::from),
        };
        let cmp = |rows: Vec<BudgetRow>, totals: Vec<BudgetTotal>| Comparison {
            rows,
            totals,
            errors: Vec::new(),
            empty: None,
        };

        // EITHER half absent is enough — an overflowing budget beside ordinary
        // spending is the common shape.
        for r in [row(None, Some(1)), row(Some(1), None)] {
            let c = cmp(vec![r], vec![]);
            assert_eq!(unrepresentable_errors(&c, &types, d(2024, 1, 1)).len(), 1);
        }
        assert!(
            unrepresentable_errors(
                &cmp(vec![row(Some(1), Some(2))], vec![]),
                &types,
                d(2024, 1, 1)
            )
            .is_empty()
        );

        // A TOTAL can overflow even when every row it sums is representable, and
        // it is named with the label the table renders.
        let total = BudgetTotal {
            bucket: Bucket::Typed(rustledger_core::AccountTypeKind::Expenses),
            currency: Currency::new("USD"),
            budgeted: None,
            actual: Some(Decimal::ONE),
        };
        let got = unrepresentable_errors(&cmp(vec![], vec![total]), &types, d(2024, 1, 1));
        assert_eq!(got.len(), 1);
        assert!(got[0].reason.starts_with("TOTAL for USD"), "{:?}", got[0]);
    }
}
