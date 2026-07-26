//! Budgeted versus actual: pairing declarations with the spending they cover.
//!
//! This is the other half of the model. [`Budgets`] answers "what was budgeted";
//! everything here answers "and what was actually spent against it", which is
//! the question a budget report exists to ask. It lived in the CLI until now,
//! which meant any other consumer — rustfava, the FFI component — could get only
//! half an answer and had to re-derive the rest: which currency a priced posting
//! spends, which direction a credit-normal account counts in, and from which day
//! spending starts counting against a budget. Each of those has been a bug at
//! least once; none of them is guessable from the outside.
//!
//! There is a second, blunter reason it belongs here. `cargo mutants` audits
//! this crate in about four minutes. The same audit against the CLI report
//! module costs roughly eight minutes *per mutant*, because every mutant
//! rebuilds a large binary crate and re-runs integration tests that spawn the
//! process. Logic that lives here can be exhaustively verified; logic that lives
//! there effectively cannot.

use crate::{BudgetError, Budgets, covers};
use rust_decimal::Decimal;
use rustledger_core::{Account, AccountTypeKind, AccountTypes, Currency, Directive, NaiveDate};
use std::collections::{BTreeMap, BTreeSet};

/// One row of a comparison: an account's budget against its spending.
///
/// `budgeted` and `actual` are `None` when the figure is not representable —
/// only reachable from an absurd declared amount. A clamped number would be
/// wrong by an unbounded factor while looking authoritative, so absence is
/// reported instead and the consumer decides how to show it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BudgetRow {
    /// The budgeted account.
    pub account: Account,
    /// The currency this row is denominated in.
    pub currency: Currency,
    /// Accrued budget over the window.
    pub budgeted: Option<Decimal>,
    /// Spending counted against it, sign-normalized.
    pub actual: Option<Decimal>,
}

/// Fraction of a budget used, `None` when nothing was budgeted — which is a
/// division by zero, not 0% and not 100%.
///
/// Free function because a row and a total answer it identically and neither
/// owns the rule. The total used to borrow the row's by CONSTRUCTING a throwaway
/// `BudgetRow` around a dummy account, which is a lot of ceremony to reach four
/// lines of arithmetic — and it made the total's behavior depend on a type it
/// has nothing to do with.
fn used_fraction(budgeted: Option<Decimal>, actual: Option<Decimal>) -> Option<f64> {
    let budgeted = budgeted?;
    if budgeted.is_zero() {
        return None;
    }
    let b: f64 = budgeted.try_into().ok()?;
    let a: f64 = actual?.try_into().ok()?;
    Some(a / b)
}

impl BudgetRow {
    /// Budget minus actual. Positive is under budget, negative over.
    #[must_use]
    pub fn remaining(&self) -> Option<Decimal> {
        self.budgeted?.checked_sub(self.actual?)
    }

    /// Fraction of the budget used, `None` when nothing was budgeted — which is
    /// a division by zero, not 0% and not 100%.
    #[must_use]
    pub fn used_fraction(&self) -> Option<f64> {
        used_fraction(self.budgeted, self.actual)
    }
}

/// Which bucket a total sums over.
///
/// Deliberately EXHAUSTIVE, not `#[non_exhaustive]`. Adding a variant should
/// break every `match` on it — the CLI's total label, the FFI's `kind` mapping
/// and the overflow warning each have to decide what a new bucket means, and a
/// compiler error is the only thing that makes them. `#[non_exhaustive]` would
/// force a wildcard arm into all three and let a new variant fall silently into
/// whatever that arm does, which is the failure mode this crate has spent its
/// review history removing. A major version is the cheaper price.
///
/// Per account TYPE, not per direction: bucketing merely by credit-normality
/// sums a credit-card spending budget into an income target, which is as
/// meaningless as the cross-currency sum the currency key already prevents.
///
/// TYPED rather than the account's raw root string. A raw root made
/// `kind == "Expenses"` a writable comparison, and a ledger setting
/// `option "name_expenses" "Depenses"` then produced no bucket any consumer
/// recognized as the primary one. With the classification carried as a value
/// there is no string to compare and the mistake cannot be expressed.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Bucket {
    /// One of the five account types the ledger's options define.
    Typed(AccountTypeKind),
    /// A root outside those five. Beancount permits only the five at the top
    /// level, so this is unreachable for a validated ledger — but `AccountTypes`
    /// answers `Option`, and inventing a classification for an unclassifiable
    /// account is how a total ends up describing rows it does not contain.
    Other(Account),
}

impl Bucket {
    /// Classify an account, config-aware.
    #[must_use]
    pub fn of(types: &AccountTypes, account: &Account) -> Self {
        types.kind(account.as_str()).map_or_else(
            || Self::Other(Account::new(root_of(account.as_str()))),
            Self::Typed,
        )
    }

    /// How a total over this bucket is labelled.
    ///
    /// THE definition, so a warning about a total and the row that total renders
    /// as cannot name it differently — they did: the overflow warning said "the
    /// Expenses total for USD" while the table said `TOTAL`, and a reader
    /// searching the output for the label in the warning found nothing.
    ///
    /// Expenses keep the bare `TOTAL`, being the overwhelmingly common case in a
    /// budget report; every other bucket is named, in the ledger's own
    /// vocabulary.
    #[must_use]
    pub fn label(&self, types: &AccountTypes) -> String {
        match self {
            Self::Typed(AccountTypeKind::Expenses) => "TOTAL".to_string(),
            Self::Typed(kind) => format!("TOTAL ({})", types.root_name(*kind)),
            Self::Other(root) => format!("TOTAL ({root})"),
        }
    }

    /// The account type, when the root is one of the five.
    #[must_use]
    pub const fn kind(&self) -> Option<AccountTypeKind> {
        match self {
            Self::Typed(k) => Some(*k),
            Self::Other(_) => None,
        }
    }
}

/// The first component of an account name.
fn root_of(account: &str) -> &str {
    account.split(':').next().unwrap_or(account)
}

/// One whole-comparison total: a bucket's budgeted and actual in one currency.
///
/// The pair used to be an unnamed `(Option<Decimal>, Option<Decimal>)` tuple in
/// a map value, so which element was which could only be learned from prose.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BudgetTotal {
    /// The account type this total sums over.
    pub bucket: Bucket,
    /// The currency it is denominated in.
    pub currency: Currency,
    /// Accrued budget over the window.
    pub budgeted: Option<Decimal>,
    /// Spending counted against it, sign-normalized.
    pub actual: Option<Decimal>,
}

impl BudgetTotal {
    /// Budget minus actual. Positive is under budget, negative over.
    #[must_use]
    pub fn remaining(&self) -> Option<Decimal> {
        self.budgeted?.checked_sub(self.actual?)
    }

    /// Fraction of the budget used — see [`BudgetRow::used_fraction`].
    #[must_use]
    pub fn used_fraction(&self) -> Option<f64> {
        used_fraction(self.budgeted, self.actual)
    }
}

/// Why a budget report came out with no rows.
///
/// Exhaustive for the same reason as [`Bucket`]: a new way for a report to be
/// empty is a new sentence someone has to write, and the compiler asking for it
/// beats a wildcard arm answering with the wrong one.
///
/// An empty report is ambiguous in a way that matters: "you have no budgets",
/// "your budgets start later than the period you asked about" and "your filter
/// excluded them all" are three different answers, and telling a user with
/// budgets that they have none sends them looking for a parsing bug that is not
/// there.
///
/// In the crate because it is a fact about the LEDGER and the window, not about
/// rendering — an FFI host needs it as much as a terminal does, and could not
/// get it while it lived in the command. Each surface phrases it; the variants
/// are the shared vocabulary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Empty {
    /// The ledger declares no budgets at all.
    NoneDeclared,
    /// Every budget directive in the ledger was rejected.
    ///
    /// `shown` is false when an account filter removed every warning, in which
    /// case pointing the user at warnings that are not on screen is worse than
    /// saying nothing.
    AllRejected {
        /// Whether any of those warnings survived the account filter.
        shown: bool,
    },
    /// Budgets exist but all start on or after the window's exclusive end.
    NoneInWindow {
        /// The earliest budget in scope, so a caller can say how much later.
        earliest: NaiveDate,
    },
    /// Budgets were in force, but the account filter excluded every one.
    FilteredOut,
}

impl Empty {
    /// A stable machine-readable tag. Prose may be reworded; this is what a
    /// dashboard branches on.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::NoneDeclared => "none_declared",
            Self::AllRejected { .. } => "all_rejected",
            Self::NoneInWindow { .. } => "none_in_window",
            Self::FilteredOut => "filtered_out",
        }
    }
}

/// Budgeted and actual, per row and in total.
///
/// No `Default`. The derived one produced `rows: []` with `empty: None`, which
/// this type's own invariant forbids — every consumer reads an absent `empty`
/// beside no rows as "there are rows", and there were none. A `Comparison` only
/// ever comes from [`Budgets::compare`], which cannot construct that state.
#[derive(Clone, Debug)]
pub struct Comparison {
    /// One row per budgeted `(account, currency)`, sorted.
    pub rows: Vec<BudgetRow>,
    /// Totals counting each budget and each posting exactly once, sorted by
    /// `(currency, bucket)`.
    ///
    /// Deliberately NOT the sum of `rows`: under `children` a parent row and a
    /// child row overlap by design, so adding the rows double-counts the child.
    pub totals: Vec<BudgetTotal>,
    /// Everything wrong with this report — unreadable directives, budgets on
    /// accounts that are never opened or already closed, currencies an account
    /// never posts, figures too large to represent — filtered to the accounts
    /// reported on and sorted by date.
    ///
    /// Produced HERE, with the rows, because a consumer that assembles it
    /// separately can assemble it differently: the CLI and the FFI once
    /// disagreed about which warnings a ledger deserved, and about their order.
    /// The one thing a caller may still add is a diagnostic about its own
    /// rendering, which this crate cannot know (see the CLI's sub-precision
    /// warning).
    pub errors: Vec<BudgetError>,
    /// Why there are no rows, when there are none. `None` when there are.
    pub empty: Option<Empty>,
}

/// Does this account pass a raw-prefix filter?
///
/// A raw prefix, deliberately NOT the component-wise [`covers`]. They answer
/// different questions: coverage decides which spending a budget is responsible
/// for, where treating `Expenses:FoodCourt` as part of `Expenses:Food` would be
/// wrong; this is a display filter a user typed, and must select the same
/// accounts a prefix filter selects in any other report.
#[must_use]
pub fn passes_account_filter(account: &str, filter: Option<&str>) -> bool {
    filter.is_none_or(|prefix| account.starts_with(prefix))
}

/// Sign-normalize a posting total so "actual" counts the direction the budget
/// was declared in.
///
/// Expense postings are debits (positive) and a spending budget is written
/// positive, so those agree already. Income postings are credits (negative)
/// while an earning target is also written positive — without this flip, earning
/// exactly a 5000 target reports `actual -5000`, `remaining 10000` and
/// `used -100%`. The test is the config-aware [`AccountTypes::is_credit_normal`]
/// rather than a hardcoded `Income:` prefix, so a ledger that renames its
/// account types still works.
#[must_use]
pub fn normalized_actual(types: &AccountTypes, account: &str, raw: Decimal) -> Decimal {
    if types.is_credit_normal(account) {
        -raw
    } else {
        raw
    }
}

/// The ordered range of `set` that could lie in `account`'s subtree.
///
/// A NARROWING only — the caller still applies [`covers`], so over-inclusion is
/// harmless and the answer cannot change. `take_while` here would be a bug: a
/// sibling component like `Expenses:Food0` sorts BETWEEN `Expenses:Food` and
/// `Expenses:Food:Restaurant`, because `'0'` (0x30) precedes `':'` (0x3A), so
/// stopping at the first non-covered account would silently drop the child
/// behind it. The `;` bound (0x3B, just past `':'`) admits every true
/// subaccount and a few siblings, which `covers` then rejects.
fn subtree_range<'a>(
    set: &'a BTreeSet<Account>,
    account: &Account,
) -> impl Iterator<Item = &'a Account> {
    let mut upper = account.as_str().to_string();
    upper.push(';');
    set.range(account.clone()..Account::new(upper))
}

/// Every account a budget could sit on that would cover `posting_account`:
/// the account itself, plus its ancestors when `children` is set.
///
/// Bounded by account DEPTH (three or four in practice), which is what lets
/// coverage be answered by lookup instead of by scanning every budget.
fn covering_accounts(posting_account: &str, children: bool) -> impl Iterator<Item = &str> {
    let mut end = Some(posting_account.len());
    std::iter::from_fn(move || {
        let e = end?;
        let slice = &posting_account[..e];
        end = if children {
            posting_account[..e].rfind(':')
        } else {
            None
        };
        Some(slice)
    })
}

/// The first date on which any budget in `scope` was responsible for spending
/// booked to `posting_account`.
///
/// The dual of the accrual: `accrue` credits nothing before a budget exists, so
/// the actual side must ignore spending from before it, or a budget added in
/// June is charged with January's groceries.
///
/// Resolved per POSTING ACCOUNT, not per row. Under `children` a row covers
/// several budgets with different declaration dates, and taking one minimum for
/// the whole row let an early child budget drag the parent's window backwards —
/// charging the parent with spending that predated the parent's own budget, and
/// disagreeing with the totals, which had the rule written the other way.
///
/// `scope` is the set of budgeted accounts the caller is answering for. Walking
/// the posting account's ANCESTORS and testing membership is equivalent to
/// filtering the scope by [`covers`] — the same component-wise rule, read from
/// the other end — and is bounded by depth rather than by the number of
/// budgets. Filtering the scope was the report's dominant cost on a ledger
/// budgeting hundreds of accounts, because both the rows and the totals do it
/// once per posting account.
#[must_use]
fn clip_start(
    budgets: &Budgets,
    scope: &BTreeSet<Account>,
    posting_account: &str,
    currency: &str,
    children: bool,
) -> Option<NaiveDate> {
    covering_accounts(posting_account, children)
        // Borrowed, not constructed. `Account::new(&str)` is a fresh `Arc<str>`
        // — interning happens in the loader's dedup pass, not here — so building
        // one per ancestor to ask a set a question allocated on the report's
        // hottest path. `Account: Borrow<str>` with a lexicographic `Ord`, so
        // the set answers `&str` directly.
        .filter(|a| scope.contains(*a))
        .filter_map(|a| budgets.effective_start(a, currency))
        .min()
}

/// The slice of `actuals` that could possibly be covered by a budget on
/// `account`, as a `BTreeMap` range rather than a full scan.
///
/// Purely a NARROWING: [`covers`] still decides, so this cannot change an
/// answer, only how many keys are asked. That matters because the caller asks
/// once per row — on a ledger budgeting 1600 accounts, scanning every posting
/// account for every row was seconds of the report.
///
/// The bound works because account components are `:`-separated and `;` is the
/// next byte after `:`. Every true subaccount of `Expenses:Food` sorts below
/// `Expenses:Food;`, while `Expenses:FoodCourt` sorts above it — the same
/// component-wise distinction `covers` makes, which is why the two agree.
fn covered_range<'a>(
    actuals: &'a BTreeMap<(Account, Currency), Vec<(NaiveDate, Decimal)>>,
    account: &Account,
    children: bool,
) -> impl Iterator<Item = (&'a (Account, Currency), &'a Vec<(NaiveDate, Decimal)>)> {
    use std::ops::Bound::{Excluded, Included};
    // The two modes differ only in where the subtree ends. `;` (0x3B) is just
    // past the `:` that starts a child component, so it admits every true
    // subaccount; `\0` admits nothing beyond the account itself. Either way
    // `covers` still decides — see `subtree_range` for why a bound is used
    // rather than stopping at the first non-covered key.
    let terminator = if children { ';' } else { '\0' };
    let mut upper = account.as_str().to_string();
    upper.push(terminator);
    // The empty currency is the least possible, so `(account, "")` is the first
    // key that could belong to `account` in any currency.
    actuals.range((
        Included((account.clone(), Currency::new(""))),
        Excluded((Account::new(upper), Currency::new(""))),
    ))
}

/// Spending per `(account, currency)` inside `[from, to)`, dated.
///
/// Postings are read directly rather than through an inventory because a budget
/// is about FLOW over a period, not the running balance an inventory realizes.
///
/// A posting priced or held at a cost moved money in TWO currencies:
/// `Expenses:Travel 90.00 EUR @ 1.10 USD` is both 90 EUR of travel and 99 USD
/// out of pocket, and both are true. It is recorded under both keys so each row
/// reads its own currency, and neither is affected by whether the other exists.
/// Deciding this once from "which currencies did anyone budget in" was wrong:
/// adding an unrelated budget in a second currency silently moved another
/// account's spending to a key no row read.
///
/// A weight in the SAME currency as the units (`90.00 USD @@ 95.00 USD`, or a
/// cost denominated in the units currency) supersedes them: only one currency
/// moved, and the weight is what it cost. The ladder comes from
/// [`rustledger_booking::posting_weight`], shared with BQL's `weight` column so
/// the two cannot drift.
fn collect_actuals(
    directives: &[Directive],
    from: NaiveDate,
    to: NaiveDate,
) -> BTreeMap<(Account, Currency), Vec<(NaiveDate, Decimal)>> {
    let mut actuals: BTreeMap<(Account, Currency), Vec<(NaiveDate, Decimal)>> = BTreeMap::new();
    let mut record = |account: &Account, currency: &Currency, date: NaiveDate, amount: Decimal| {
        actuals
            .entry((account.clone(), currency.clone()))
            .or_default()
            .push((date, amount));
    };
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
            match rustledger_booking::posting_weight(p) {
                Some(w) if w.currency == units.currency => {
                    record(&p.account, &w.currency, txn.date, w.number);
                }
                Some(w) => {
                    record(&p.account, &units.currency, txn.date, units.number);
                    record(&p.account, &w.currency, txn.date, w.number);
                }
                None => {
                    record(&p.account, &units.currency, txn.date, units.number);
                }
            }
        }
    }
    actuals
}

impl Budgets {
    /// Compare every budget in force over `[from, to)` against the spending it
    /// covers.
    ///
    /// `children` makes a budget cover its subaccounts, summing a parent's own
    /// budget with any child budgets (they add; the child is not absorbed).
    /// `account_filter` is a raw prefix restricting which rows are reported, and
    /// the totals with them.
    #[must_use]
    pub fn compare(
        &self,
        directives: &[Directive],
        types: &AccountTypes,
        from: NaiveDate,
        to: NaiveDate,
        children: bool,
        account_filter: Option<&str>,
    ) -> Comparison {
        let actuals = collect_actuals(directives, from, to);

        // A row exists per budgeted `(account, currency)`. A budget with no
        // spending still appears — that is the point of a budget report —
        // while spending with no budget does not; a balances report already
        // answers that.
        //
        // A row is live when a budget it COVERS is live, which under `children`
        // is not the same as the account's own declarations being live: a parent
        // whose own budget starts next year still aggregates a child budget
        // running now. Row identities still come from declared pairs, so no row
        // is invented for an account nobody budgeted in that currency.
        // Accrue each declared `(account, currency)` ONCE.
        //
        // The rows and the totals both need it — a row sums the accruals of the
        // budgets it covers, a total sums them per account type — and they were
        // each calling `accrue` independently, so every pair was pro-rated
        // twice. `accrue` walks the window segment by segment and is the
        // report's dominant cost, so that was half the work in the whole
        // comparison. Every pair either loop can ask for is a declared one:
        // a row's covered set is filtered to accounts with an effective start
        // in that currency, which is what `all_keys` enumerates.
        let accrued: BTreeMap<(Account, Currency), Option<Decimal>> = self
            .all_keys()
            .into_iter()
            .map(|(account, currency)| {
                let v = self.accrue(account.as_str(), currency.as_str(), from, to);
                ((account, currency), v)
            })
            .collect();

        // Every budgeted account, ordered, so a row's subtree is a contiguous
        // range rather than a filter over all declarations.
        let budget_accounts: BTreeSet<Account> =
            self.entries().map(|b| b.account.clone()).collect();

        // Each key with the budgeted accounts it answers for, resolved ONCE.
        // Liveness and the covered set are the same subtree walk asking two
        // questions ("is any of these live?" and "which are they?"), and doing
        // it twice per key doubled the dominant term of the whole comparison.
        let keys: Vec<((Account, Currency), BTreeSet<Account>)> = if children {
            // A row is live when a budget it COVERS is live, which under
            // `children` is not the same as the account's own declarations
            // being live: a parent whose own budget starts next year still
            // aggregates a child budget running now. Row identities still come
            // from declared pairs, so no row is invented for an account nobody
            // budgeted in that currency.
            self.all_keys()
                .into_iter()
                // Filtered FIRST. The covered set below is a subtree walk per
                // key, and building it for keys the caller then discards was
                // the bulk of the work on a narrowed report.
                .filter(|(account, _)| passes_account_filter(account.as_str(), account_filter))
                .filter_map(|(account, currency)| {
                    let covered: BTreeSet<Account> = subtree_range(&budget_accounts, &account)
                        .filter(|a| covers(account.as_str(), a.as_str(), true))
                        .filter(|a| {
                            self.effective_start(a.as_str(), currency.as_str())
                                .is_some()
                        })
                        .cloned()
                        .collect();
                    let live = covered.iter().any(|a| {
                        self.effective_start(a.as_str(), currency.as_str())
                            .is_some_and(|start| start < to)
                    });
                    live.then_some(((account, currency), covered))
                })
                .collect()
        } else {
            self.keys_in_force_before(to)
                .into_iter()
                .filter(|(account, _)| passes_account_filter(account.as_str(), account_filter))
                .map(|(account, currency)| {
                    let covered = std::iter::once(account.clone()).collect();
                    ((account, currency), covered)
                })
                .collect()
        };

        let mut rows: Vec<BudgetRow> = keys
            .into_iter()
            .map(|((account, currency), covered)| {
                let budgeted: Option<Decimal> = covered
                    .iter()
                    .map(|a| {
                        accrued
                            .get(&(a.clone(), currency.clone()))
                            .copied()
                            .flatten()
                    })
                    .try_fold(Decimal::ZERO, |acc, seg| {
                        seg.and_then(|s| acc.checked_add(s))
                    });
                let actual = covered_range(&actuals, &account, children)
                    .filter(|((a, c), _)| {
                        *c == currency && covers(account.as_str(), a.as_str(), children)
                    })
                    .flat_map(|((a, _), entries)| {
                        let start =
                            clip_start(self, &covered, a.as_str(), currency.as_str(), children)
                                .unwrap_or(from)
                                .max(from);
                        entries
                            .iter()
                            .filter(move |(date, _)| *date >= start)
                            .map(move |(_, v)| normalized_actual(types, a.as_str(), *v))
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

        let totals = self.totals(
            &actuals,
            &accrued,
            types,
            from,
            to,
            children,
            account_filter,
        );
        let mut comparison = Comparison {
            rows,
            totals,
            errors: Vec::new(),
            empty: None,
        };
        // "Which currencies did each account move in this window" comes from
        // the spending already collected above, not from a second walk of the
        // directives — two derivations of that fact would drift, and the
        // warning would end up disagreeing with the figures beside it.
        let mut posted: BTreeMap<&Account, BTreeSet<&Currency>> = BTreeMap::new();
        for (account, currency) in actuals.keys() {
            posted.entry(account).or_default().insert(currency);
        }
        comparison.errors = crate::diagnostics::collect(
            self,
            directives,
            &comparison,
            types,
            &crate::diagnostics::Scope {
                from,
                to,
                children,
                account_filter,
            },
            &posted,
        );
        comparison.empty = comparison
            .rows
            .is_empty()
            .then(|| self.diagnose_empty(to, account_filter, &comparison.errors));
        comparison
    }

    /// Why a report over this window came out empty.
    ///
    /// Diagnosed over the budgets the CALLER asked about. Testing "is anything
    /// in force" across the whole ledger let an unrelated account's live budget
    /// mask the real reason: a report filtered to an account whose budget simply
    /// starts later was blamed on the filter, and the user sent to debug a name
    /// that was in fact matching.
    fn diagnose_empty(
        &self,
        to: NaiveDate,
        account_filter: Option<&str>,
        errors: &[BudgetError],
    ) -> Empty {
        let in_scope: Vec<&crate::BudgetEntry> = self
            .entries()
            .filter(|e| passes_account_filter(e.account.as_str(), account_filter))
            .collect();
        // Three different answers, in order of what the user most needs to know.
        if self.is_empty() {
            // Nothing parsed at all: either the ledger has no budgets, or every
            // directive in it was rejected. Saying "no budgets declared" for the
            // latter sends the user looking for syntax they are not missing.
            return if self.errors().is_empty() {
                Empty::NoneDeclared
            } else {
                Empty::AllRejected {
                    shown: !errors.is_empty(),
                }
            };
        }
        let Some(earliest) = in_scope.iter().map(|e| e.from).min() else {
            // Budgets exist, but none of them are under the filter.
            return Empty::FilteredOut;
        };
        if !in_scope.iter().any(|e| e.from < to) {
            return Empty::NoneInWindow { earliest };
        }
        Empty::FilteredOut
    }

    /// Totals counting every budget and every posting exactly once.
    fn totals(
        &self,
        actuals: &BTreeMap<(Account, Currency), Vec<(NaiveDate, Decimal)>>,
        accrued: &BTreeMap<(Account, Currency), Option<Decimal>>,
        types: &AccountTypes,
        from: NaiveDate,
        to: NaiveDate,
        children: bool,
        account_filter: Option<&str>,
    ) -> Vec<BudgetTotal> {
        let pairs: Vec<(Account, Currency)> = self
            .keys_in_force_before(to)
            .into_iter()
            .filter(|(account, _)| passes_account_filter(account.as_str(), account_filter))
            .collect();

        // Accumulated in a map keyed by `(currency, bucket)` — currency first so
        // the sorted output groups a multi-currency report by currency — then
        // handed out as a sorted `Vec` so the published shape carries named
        // fields instead of a tuple whose halves are told apart only by prose.
        let mut acc: BTreeMap<(Currency, Bucket), (Option<Decimal>, Option<Decimal>)> =
            BTreeMap::new();
        for (account, currency) in &pairs {
            let e = acc
                .entry((currency.clone(), Bucket::of(types, account)))
                .or_insert((Some(Decimal::ZERO), Some(Decimal::ZERO)));
            e.0 = e.0.and_then(|sum| {
                accrued
                    .get(&(account.clone(), currency.clone()))
                    .copied()
                    .flatten()
                    .and_then(|seg| sum.checked_add(seg))
            });
        }
        // Each posting counts once, against whichever budgeted accounts cover
        // it, and only from the day one of those budgets existed.
        // One scope per currency, built once, instead of re-filtering `pairs`
        // for every posting account.
        let mut scope_by_currency: BTreeMap<&Currency, BTreeSet<Account>> = BTreeMap::new();
        for (account, currency) in &pairs {
            scope_by_currency
                .entry(currency)
                .or_default()
                .insert(account.clone());
        }
        let empty = BTreeSet::new();
        for ((account, currency), entries) in actuals {
            let scope = scope_by_currency.get(currency).unwrap_or(&empty);
            let Some(start) =
                clip_start(self, scope, account.as_str(), currency.as_str(), children)
            else {
                continue;
            };
            let start = start.max(from);
            let e = acc
                .entry((currency.clone(), Bucket::of(types, account)))
                .or_insert((Some(Decimal::ZERO), Some(Decimal::ZERO)));
            for (_, raw) in entries.iter().filter(|(d, _)| *d >= start) {
                e.1 = e.1.and_then(|sum| {
                    sum.checked_add(normalized_actual(types, account.as_str(), *raw))
                });
            }
        }
        acc.into_iter()
            .map(|((currency, bucket), (budgeted, actual))| BudgetTotal {
                bucket,
                currency,
                budgeted,
                actual,
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BudgetEntry, Interval};
    use rustledger_core::naive_date;

    fn d(y: i32, m: u32, day: u32) -> NaiveDate {
        naive_date(y, m, day).unwrap()
    }

    fn entry(from: NaiveDate, account: &str) -> BudgetEntry {
        BudgetEntry {
            from,
            account: Account::new(account),
            interval: Interval::Month,
            amount: Decimal::from(100),
            currency: Currency::new("USD"),
        }
    }

    #[test]
    fn covers_is_exact_without_children() {
        assert!(covers("Expenses:Food", "Expenses:Food", false));
        assert!(!covers("Expenses:Food", "Expenses:Food:Restaurant", false));
        assert!(!covers("Expenses:Food:Restaurant", "Expenses:Food", false));
        assert!(!covers("Expenses:Food", "Expenses:FoodCourt", false));
    }

    /// With children a budget covers itself and its true subaccounts, and still
    /// NOT a name that merely shares a prefix — the deliberate deviation from
    /// Fava's `startswith`.
    #[test]
    fn covers_is_component_wise_with_children() {
        assert!(covers("Expenses:Food", "Expenses:Food", true));
        assert!(covers("Expenses:Food", "Expenses:Food:Restaurant", true));
        assert!(covers("Expenses:Food", "Expenses:Food:A:B", true));
        assert!(!covers("Expenses:Food", "Expenses:FoodCourt", true));
        assert!(
            !covers("Expenses:Food:Restaurant", "Expenses:Food", true),
            "coverage runs down the tree, never up"
        );
    }

    /// The account filter is a RAW prefix, deliberately unlike `covers`. That
    /// difference is the whole reason both exist, and it was wrong twice while
    /// it lived only in a doc comment.
    #[test]
    fn the_account_filter_is_a_raw_prefix_unlike_coverage() {
        assert!(passes_account_filter("Expenses:Food", None));
        assert!(passes_account_filter(
            "Expenses:Food",
            Some("Expenses:Food")
        ));
        assert!(passes_account_filter("Expenses:Food", Some("Expenses:Foo")));
        assert!(passes_account_filter(
            "Expenses:Food:Sub",
            Some("Expenses:Food")
        ));
        assert!(!passes_account_filter("Expenses:Food", Some("Income")));
        assert!(!passes_account_filter(
            "Expenses:Food",
            Some("Expenses:Food:Sub")
        ));
        // The two predicates MUST disagree on exactly this input.
        assert!(passes_account_filter(
            "Expenses:FoodCourt",
            Some("Expenses:Food")
        ));
        assert!(!covers("Expenses:Food", "Expenses:FoodCourt", true));
    }

    /// The range narrowing must never EXCLUDE a covered account, for ANY pair of
    /// account names — that is the entire correctness condition of the ordered
    /// lookups the comparison was rebuilt on.
    ///
    /// Checked exhaustively against the definition (`covers` over the whole
    /// set) rather than by example, because the failure that already happened
    /// here was invisible by inspection: `'0'` (0x30) and `'-'` (0x2D) sort
    /// BELOW `':'` (0x3A), so a sibling like `Expenses:Food0` lands inside the
    /// parent's byte range and a naive scan stopped at it. The names below are
    /// picked to straddle the `:` boundary from both sides.
    #[test]
    fn the_subtree_range_never_hides_a_covered_account() {
        let names = [
            "Expenses",
            "Expenses:Food",
            "Expenses:Food0",
            "Expenses:Food9",
            "Expenses:Food-Bar",
            "Expenses:Food-",
            "Expenses:FoodCourt",
            "Expenses:Fooda",
            "Expenses:Food:Restaurant",
            "Expenses:Food:Restaurant:Tip",
            "Expenses:Food:0",
            "Expenses:Food:-x",
            "Expenses:Foo",
            "Expenses:Foo:Deep",
            "Income:Salary",
            "A",
            "A:B",
        ];
        let set: BTreeSet<Account> = names.iter().copied().map(Account::new).collect();
        for name in names {
            let account = Account::new(name);
            // What the range yields, once `covers` has had its say.
            let narrowed: Vec<&Account> = subtree_range(&set, &account)
                .filter(|a| covers(account.as_str(), a.as_str(), true))
                .collect();
            // The definition: every account in the set that the budget covers.
            let all: Vec<&Account> = set
                .iter()
                .filter(|a| covers(account.as_str(), a.as_str(), true))
                .collect();
            assert_eq!(
                narrowed, all,
                "subtree_range dropped a covered account under {name}"
            );
        }
    }

    /// The same condition for the spending map, whose keys carry a currency, and
    /// for BOTH `children` settings — the non-children bound is a different
    /// character and has its own way to be wrong.
    #[test]
    fn the_spending_range_never_hides_a_covered_key() {
        let names = [
            "Expenses:Food",
            "Expenses:Food0",
            "Expenses:Food-Bar",
            "Expenses:FoodCourt",
            "Expenses:Food:Restaurant",
            "Expenses:Food:Restaurant:Tip",
            "Expenses:Foo",
        ];
        let mut actuals: BTreeMap<(Account, Currency), Vec<(NaiveDate, Decimal)>> = BTreeMap::new();
        for n in names {
            for c in ["USD", "EUR", ""] {
                actuals.insert(
                    (Account::new(n), Currency::new(c)),
                    vec![(d(2024, 2, 1), Decimal::ONE)],
                );
            }
        }
        for children in [false, true] {
            for n in names {
                let account = Account::new(n);
                let narrowed: Vec<&(Account, Currency)> =
                    covered_range(&actuals, &account, children)
                        .map(|(k, _)| k)
                        .filter(|(a, _)| covers(account.as_str(), a.as_str(), children))
                        .collect();
                let all: Vec<&(Account, Currency)> = actuals
                    .keys()
                    .filter(|(a, _)| covers(account.as_str(), a.as_str(), children))
                    .collect();
                assert_eq!(
                    narrowed, all,
                    "covered_range dropped a covered key under {n} (children={children})"
                );
            }
        }
    }

    /// A total's derived figures behave like a row's. Covered here because the
    /// CLI reaches them through `BudgetRow` and only the FFI calls them
    /// directly — so the crate's own suite never did, and a mutation audit
    /// found all four of these accessors replaceable by a constant.
    #[test]
    fn a_total_derives_remaining_and_used_like_a_row() {
        let total = |budgeted: Option<i64>, actual: Option<i64>| BudgetTotal {
            bucket: Bucket::Typed(AccountTypeKind::Expenses),
            currency: Currency::new("USD"),
            budgeted: budgeted.map(Decimal::from),
            actual: actual.map(Decimal::from),
        };
        let t = total(Some(400), Some(120));
        assert_eq!(t.remaining(), Some(Decimal::from(280)));
        assert!((t.used_fraction().expect("a fraction") - 0.30).abs() < 1e-9);

        // Overspent: remaining goes negative and the fraction passes 1.
        let over = total(Some(100), Some(150));
        assert_eq!(over.remaining(), Some(Decimal::from(-50)));
        assert!((over.used_fraction().expect("a fraction") - 1.5).abs() < 1e-9);

        // An absent half makes the derived figure absent too, rather than
        // treating the unknown as zero and printing an authoritative number.
        assert_eq!(total(None, Some(120)).remaining(), None);
        assert_eq!(total(Some(400), None).remaining(), None);
        assert_eq!(total(Some(400), None).used_fraction(), None);

        // Nothing budgeted is a division by zero — not 0%, and not 100%.
        assert_eq!(total(Some(0), Some(50)).used_fraction(), None);
    }

    /// Classification is by TYPE and config-aware, so a renamed root still
    /// buckets as the type it is — the whole reason this is not the raw root
    /// string it used to be.
    #[test]
    fn a_bucket_classifies_by_type_not_by_root_spelling() {
        let types = AccountTypes::default();
        let of = |a: &str| Bucket::of(&types, &Account::new(a));
        assert_eq!(
            of("Expenses:Food:Sub").kind(),
            Some(AccountTypeKind::Expenses)
        );
        assert_eq!(of("Income:Salary").kind(), Some(AccountTypeKind::Income));
        assert_eq!(
            of("Liabilities:CreditCard").kind(),
            Some(AccountTypeKind::Liabilities)
        );
        assert_eq!(of("Expenses").kind(), Some(AccountTypeKind::Expenses));

        // A ledger that renames its expense root buckets identically — under the
        // old raw-root key this produced a bucket nothing recognized as primary.
        let renamed = AccountTypes {
            expenses: "Depenses".to_string(),
            ..AccountTypes::default()
        };
        assert_eq!(
            Bucket::of(&renamed, &Account::new("Depenses:Food")).kind(),
            Some(AccountTypeKind::Expenses)
        );
        // ...and the ledger's own name comes back for display.
        assert_eq!(renamed.root_name(AccountTypeKind::Expenses), "Depenses");

        // An unclassifiable root stays explicitly unclassified rather than being
        // invented into one of the five.
        let odd = Bucket::of(&types, &Account::new("Weird:Thing"));
        assert_eq!(odd.kind(), None);
        assert_eq!(odd, Bucket::Other(Account::new("Weird")));
    }

    #[test]
    fn normalized_actual_flips_only_credit_normal_accounts() {
        let types = AccountTypes::default();
        let hundred = Decimal::from(100);
        assert_eq!(normalized_actual(&types, "Expenses:Food", hundred), hundred);
        assert_eq!(normalized_actual(&types, "Assets:Cash", hundred), hundred);
        assert_eq!(
            normalized_actual(&types, "Income:Salary", -hundred),
            hundred
        );
        assert_eq!(
            normalized_actual(&types, "Liabilities:Card", -hundred),
            hundred
        );
        assert_eq!(
            normalized_actual(&types, "Equity:Opening", -hundred),
            hundred
        );
    }

    /// Resolved per POSTING ACCOUNT, not per row: taking one minimum for the
    /// whole row let an early child budget drag a parent's window backwards.
    #[test]
    fn clip_start_is_per_posting_account() {
        let budgets = Budgets::new(vec![
            entry(d(2024, 6, 1), "Expenses:Food"),
            entry(d(2024, 1, 1), "Expenses:Food:Restaurant"),
        ]);
        let covered: BTreeSet<Account> = ["Expenses:Food", "Expenses:Food:Restaurant"]
            .into_iter()
            .map(Account::new)
            .collect();
        assert_eq!(
            clip_start(&budgets, &covered, "Expenses:Food", "USD", true),
            Some(d(2024, 6, 1)),
            "a posting on the parent is covered only by the parent's own budget"
        );
        assert_eq!(
            clip_start(&budgets, &covered, "Expenses:Food:Restaurant", "USD", true),
            Some(d(2024, 1, 1)),
            "a posting on the child is covered by both, so the earlier wins"
        );
        assert_eq!(
            clip_start(&budgets, &covered, "Expenses:Rent", "USD", true),
            None
        );
        assert_eq!(
            clip_start(&budgets, &covered, "Expenses:Food", "EUR", true),
            None
        );
    }

    /// The end-to-end shape: a budget, a posting inside the window, and one
    /// before the budget existed. Only the covered spending counts, and the
    /// totals agree with the row.
    #[test]
    fn compare_pairs_budgets_with_the_spending_they_cover() {
        use rustledger_core::{Amount, Posting, Transaction};
        let budgets = Budgets::new(vec![BudgetEntry {
            from: d(2024, 2, 1),
            account: Account::new("Expenses:Food"),
            interval: Interval::Month,
            amount: Decimal::from(400),
            currency: Currency::new("USD"),
        }]);
        let txn = |day, amount: i64| {
            Directive::Transaction(Transaction::new(day, "x").with_synthesized_posting(
                Posting::new("Expenses:Food", Amount::new(Decimal::from(amount), "USD")),
            ))
        };
        let directives = vec![txn(d(2024, 1, 15), 50), txn(d(2024, 2, 10), 120)];
        let cmp = budgets.compare(
            &directives,
            &AccountTypes::default(),
            d(2024, 1, 1),
            d(2024, 3, 1),
            false,
            None,
        );
        assert_eq!(cmp.rows.len(), 1);
        let row = &cmp.rows[0];
        assert_eq!(row.budgeted, Some(Decimal::from(400)), "February only");
        assert_eq!(
            row.actual,
            Some(Decimal::from(120)),
            "the January posting predates the budget"
        );
        assert_eq!(row.remaining(), Some(Decimal::from(280)));
        assert!((row.used_fraction().unwrap() - 0.30).abs() < 1e-9);
        assert_eq!(
            cmp.totals,
            vec![BudgetTotal {
                bucket: Bucket::Typed(AccountTypeKind::Expenses),
                currency: Currency::new("USD"),
                budgeted: Some(Decimal::from(400)),
                actual: Some(Decimal::from(120)),
            }]
        );
    }

    /// A filter that matches nothing yields no rows and no totals — the caller
    /// distinguishes that from "no budgets declared", which it can, because the
    /// index is still there to ask.
    #[test]
    fn compare_honors_the_account_filter() {
        let budgets = Budgets::new(vec![entry(d(2024, 1, 1), "Expenses:Food")]);
        let cmp = budgets.compare(
            &[],
            &AccountTypes::default(),
            d(2024, 1, 1),
            d(2024, 2, 1),
            false,
            Some("Income"),
        );
        assert!(cmp.rows.is_empty() && cmp.totals.is_empty());
        assert!(
            !budgets.is_empty(),
            "the budgets themselves are still there"
        );
    }
}

/// Boundary and coverage tests for the actual-spend half.
///
/// Written from a mutation audit of this module: every decision below had a
/// surviving mutant, meaning no test distinguished it from its neighbor. That is
/// the defect class this feature shipped repeatedly — a window edge or a
/// coverage rule decided one case too wide — so these assert on the edges and on
/// the cases that must NOT match.
#[cfg(test)]
mod boundary_tests {
    use super::*;
    use crate::{BudgetEntry, Interval};
    use rustledger_core::{Amount, Posting, PriceAnnotation, Transaction, naive_date};

    fn d(y: i32, m: u32, day: u32) -> NaiveDate {
        naive_date(y, m, day).unwrap()
    }

    fn budget_of(from: NaiveDate, account: &str, currency: &str, amount: i64) -> BudgetEntry {
        BudgetEntry {
            from,
            account: Account::new(account),
            interval: Interval::Day,
            amount: Decimal::from(amount),
            currency: Currency::new(currency),
        }
    }

    fn spend(day: NaiveDate, account: &str, amount: i64, currency: &str) -> Directive {
        Directive::Transaction(
            Transaction::new(day, "x").with_synthesized_posting(Posting::new(
                account,
                Amount::new(Decimal::from(amount), currency),
            )),
        )
    }

    fn actual_of(budgets: &Budgets, dirs: &[Directive], from: NaiveDate, to: NaiveDate) -> Decimal {
        budgets
            .compare(dirs, &AccountTypes::default(), from, to, false, None)
            .rows
            .first()
            .and_then(|r| r.actual)
            .unwrap_or(Decimal::ZERO)
    }

    /// `[from, to)`: a posting ON `from` counts, one ON `to` does not. Both
    /// halves of that window test had surviving mutants.
    #[test]
    fn the_spend_window_is_half_open() {
        let b = Budgets::new(vec![budget_of(d(2024, 1, 1), "Expenses:Food", "USD", 1)]);
        let on_from = vec![spend(d(2024, 2, 1), "Expenses:Food", 10, "USD")];
        let on_to = vec![spend(d(2024, 3, 1), "Expenses:Food", 10, "USD")];
        let before = vec![spend(d(2024, 1, 31), "Expenses:Food", 10, "USD")];
        let w = (d(2024, 2, 1), d(2024, 3, 1));
        assert_eq!(actual_of(&b, &on_from, w.0, w.1), Decimal::from(10));
        assert_eq!(actual_of(&b, &on_to, w.0, w.1), Decimal::ZERO);
        assert_eq!(actual_of(&b, &before, w.0, w.1), Decimal::ZERO);
    }

    /// A weight in the SAME currency supersedes the units; a weight in ANOTHER
    /// currency is recorded alongside them. Collapsing that guard makes one of
    /// the two wrong.
    #[test]
    fn a_same_currency_weight_supersedes_the_units() {
        let b = Budgets::new(vec![budget_of(d(2024, 1, 1), "Expenses:Fees", "USD", 1)]);
        // `90.00 USD @@ 95.00 USD` spent 95, not 90.
        let same = vec![Directive::Transaction(
            Transaction::new(d(2024, 2, 10), "fee").with_synthesized_posting(
                Posting::new("Expenses:Fees", Amount::new(Decimal::from(90), "USD")).with_price(
                    PriceAnnotation::total(Amount::new(Decimal::from(95), "USD")),
                ),
            ),
        )];
        assert_eq!(
            actual_of(&b, &same, d(2024, 2, 1), d(2024, 3, 1)),
            Decimal::from(95)
        );

        // `90 EUR @ 1.10 USD` moved BOTH currencies: the USD budget sees 99.
        let cross = vec![Directive::Transaction(
            Transaction::new(d(2024, 2, 10), "trip").with_synthesized_posting(
                Posting::new("Expenses:Fees", Amount::new(Decimal::from(90), "EUR")).with_price(
                    PriceAnnotation::unit(Amount::new(
                        Decimal::from(110) / Decimal::from(100),
                        "USD",
                    )),
                ),
            ),
        )];
        assert_eq!(
            actual_of(&b, &cross, d(2024, 2, 1), d(2024, 3, 1)),
            Decimal::from(99)
        );

        // ...and the UNITS side is still recorded, so a EUR budget on the same
        // account sees 90. Collapsing the same-currency guard drops this half
        // while leaving the USD figure above intact, so only this assertion
        // distinguishes them.
        let eur = Budgets::new(vec![budget_of(d(2024, 1, 1), "Expenses:Fees", "EUR", 1)]);
        assert_eq!(
            actual_of(&eur, &cross, d(2024, 2, 1), d(2024, 3, 1)),
            Decimal::from(90)
        );
    }

    /// A row exists only for a budget that matches on ALL THREE of currency,
    /// date and coverage. Relaxing any one invents a row for something nobody
    /// budgeted, or resurrects a budget that starts after the window.
    #[test]
    fn a_child_row_requires_currency_date_and_coverage_together() {
        let b = Budgets::new(vec![
            budget_of(d(2024, 1, 1), "Expenses:Food:Restaurant", "USD", 1),
            budget_of(d(2099, 1, 1), "Expenses:Rent", "USD", 1), // starts after the window
            budget_of(d(2024, 1, 1), "Expenses:Travel", "EUR", 1), // different currency
        ]);
        let cmp = b.compare(
            &[],
            &AccountTypes::default(),
            d(2024, 2, 1),
            d(2024, 3, 1),
            true,
            None,
        );
        let keys: Vec<(&str, &str)> = cmp
            .rows
            .iter()
            .map(|r| (r.account.as_str(), r.currency.as_str()))
            .collect();
        assert_eq!(
            keys,
            vec![
                ("Expenses:Food:Restaurant", "USD"),
                ("Expenses:Travel", "EUR")
            ],
            "the future-dated Rent budget must not produce a row"
        );

        // `b.from < to` is EXCLUSIVE: a budget declared exactly on the window's
        // end is not in force within it. Only a declaration ON the bound
        // separates `<` from `<=`.
        let on_bound = Budgets::new(vec![budget_of(d(2024, 3, 1), "Expenses:Food", "USD", 1)]);
        let cmp = on_bound.compare(
            &[],
            &AccountTypes::default(),
            d(2024, 2, 1),
            d(2024, 3, 1),
            true,
            None,
        );
        assert!(
            cmp.rows.is_empty(),
            "a budget starting on the exclusive end is outside the window"
        );
        let inside = on_bound.compare(
            &[],
            &AccountTypes::default(),
            d(2024, 2, 1),
            d(2024, 3, 2),
            true,
            None,
        );
        assert_eq!(inside.rows.len(), 1, "one day past it, the row exists");
    }

    /// Under `children` a parent aggregates its children's budgets, and only
    /// theirs: not a sibling's, and not another currency's.
    #[test]
    fn a_parent_aggregates_only_what_it_covers() {
        let b = Budgets::new(vec![
            budget_of(d(2024, 1, 1), "Expenses:Food", "USD", 1),
            budget_of(d(2024, 1, 1), "Expenses:Food:Restaurant", "USD", 2),
            budget_of(d(2024, 1, 1), "Expenses:FoodCourt", "USD", 100),
            budget_of(d(2024, 1, 1), "Expenses:Food:Restaurant", "EUR", 50),
        ]);
        let cmp = b.compare(
            &[],
            &AccountTypes::default(),
            d(2024, 2, 1),
            d(2024, 2, 3),
            true,
            None,
        );
        let food = cmp
            .rows
            .iter()
            .find(|r| r.account == "Expenses:Food" && r.currency == "USD")
            .expect("a parent row");
        // Two days of (1 + 2) daily — the prefix-sharing FoodCourt and the EUR
        // child are both excluded.
        assert_eq!(food.budgeted, Some(Decimal::from(6)));
    }

    /// A row counts only spending in its own currency, on accounts it covers.
    #[test]
    fn a_row_counts_only_its_own_currency_and_subtree() {
        let b = Budgets::new(vec![budget_of(d(2024, 1, 1), "Expenses:Food", "USD", 1)]);
        let dirs = vec![
            spend(d(2024, 2, 10), "Expenses:Food", 10, "USD"),
            spend(d(2024, 2, 10), "Expenses:Food", 500, "EUR"),
            spend(d(2024, 2, 10), "Expenses:FoodCourt", 700, "USD"),
            spend(d(2024, 2, 10), "Expenses:Food:Restaurant", 300, "USD"),
        ];
        let cmp = b.compare(
            &dirs,
            &AccountTypes::default(),
            d(2024, 2, 1),
            d(2024, 3, 1),
            false,
            None,
        );
        let row = cmp.rows.first().expect("a row");
        assert_eq!(
            row.actual,
            Some(Decimal::from(10)),
            "EUR, the prefix-sharing account and the child are all excluded"
        );

        // With children the true subaccount joins, and only it.
        let kids = b.compare(
            &dirs,
            &AccountTypes::default(),
            d(2024, 2, 1),
            d(2024, 3, 1),
            true,
            None,
        );
        let row = kids
            .rows
            .iter()
            .find(|r| r.account == "Expenses:Food")
            .expect("a row");
        assert_eq!(row.actual, Some(Decimal::from(310)));
    }
}
