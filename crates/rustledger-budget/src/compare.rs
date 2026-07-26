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

use crate::{Budgets, covers};
use rust_decimal::Decimal;
use rustledger_core::{AccountTypes, Directive, NaiveDate};
use std::collections::BTreeMap;

/// One row of a comparison: an account's budget against its spending.
///
/// `budgeted` and `actual` are `None` when the figure is not representable —
/// only reachable from an absurd declared amount. A clamped number would be
/// wrong by an unbounded factor while looking authoritative, so absence is
/// reported instead and the consumer decides how to show it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BudgetRow {
    /// The budgeted account.
    pub account: String,
    /// The currency this row is denominated in.
    pub currency: String,
    /// Accrued budget over the window.
    pub budgeted: Option<Decimal>,
    /// Spending counted against it, sign-normalized.
    pub actual: Option<Decimal>,
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
        let budgeted = self.budgeted?;
        if budgeted.is_zero() {
            return None;
        }
        let b: f64 = budgeted.try_into().ok()?;
        let a: f64 = self.actual?.try_into().ok()?;
        Some(a / b)
    }
}

/// Whole-comparison totals, keyed by `(currency, account type)`.
///
/// Per TYPE, not per direction: bucketing merely by credit-normality sums a
/// credit-card spending budget into an income target, which is as meaningless as
/// the cross-currency sum the currency key already prevents.
pub type Totals = BTreeMap<(String, String), (Option<Decimal>, Option<Decimal>)>;

/// Budgeted and actual, per row and in total.
#[derive(Clone, Debug, Default)]
pub struct Comparison {
    /// One row per budgeted `(account, currency)`, sorted.
    pub rows: Vec<BudgetRow>,
    /// Totals counting each budget and each posting exactly once.
    ///
    /// Deliberately NOT the sum of `rows`: under `children` a parent row and a
    /// child row overlap by design, so adding the rows double-counts the child.
    pub totals: Totals,
}

/// The account's top-level type, which is how totals are bucketed.
#[must_use]
pub fn account_kind(account: &str) -> String {
    account.split(':').next().unwrap_or(account).to_string()
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

/// The first date on which any budget in `covered` was responsible for spending
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
#[must_use]
pub fn clip_start<'a>(
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
) -> BTreeMap<(String, String), Vec<(NaiveDate, Decimal)>> {
    let mut actuals: BTreeMap<(String, String), Vec<(NaiveDate, Decimal)>> = BTreeMap::new();
    let mut record = |account: &str, currency: &str, date: NaiveDate, amount: Decimal| {
        actuals
            .entry((account.to_string(), currency.to_string()))
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
                    record(p.account.as_str(), &w.currency, txn.date, w.number);
                }
                Some(w) => {
                    record(p.account.as_str(), &units.currency, txn.date, units.number);
                    record(p.account.as_str(), &w.currency, txn.date, w.number);
                }
                None => {
                    record(p.account.as_str(), &units.currency, txn.date, units.number);
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
        let keys: Vec<(String, String)> = if children {
            self.all_keys()
                .into_iter()
                .filter(|(account, currency)| {
                    self.entries().any(|b| {
                        b.currency == *currency && b.from < to && covers(account, &b.account, true)
                    })
                })
                .collect()
        } else {
            self.keys_in_force_before(to)
        };

        let mut rows: Vec<BudgetRow> = keys
            .into_iter()
            .filter(|(account, _)| passes_account_filter(account, account_filter))
            .map(|(account, currency)| {
                let covered: Vec<&str> = if children {
                    let mut all: Vec<&str> = self
                        .entries()
                        .filter(|b| b.currency == currency && covers(&account, &b.account, true))
                        .map(|b| b.account.as_str())
                        .collect();
                    all.sort_unstable();
                    all.dedup();
                    all
                } else {
                    vec![account.as_str()]
                };
                let budgeted: Option<Decimal> = covered
                    .iter()
                    .map(|a| self.accrue(a, &currency, from, to))
                    .try_fold(Decimal::ZERO, |acc, seg| {
                        seg.and_then(|s| acc.checked_add(s))
                    });
                let actual = actuals
                    .iter()
                    .filter(|((a, c), _)| *c == currency && covers(&account, a, children))
                    .flat_map(|((a, _), entries)| {
                        let start =
                            clip_start(self, covered.iter().copied(), a, &currency, children)
                                .unwrap_or(from)
                                .max(from);
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

        let totals = self.totals(&actuals, types, from, to, children, account_filter);
        Comparison { rows, totals }
    }

    /// Totals counting every budget and every posting exactly once.
    fn totals(
        &self,
        actuals: &BTreeMap<(String, String), Vec<(NaiveDate, Decimal)>>,
        types: &AccountTypes,
        from: NaiveDate,
        to: NaiveDate,
        children: bool,
        account_filter: Option<&str>,
    ) -> Totals {
        let pairs: Vec<(String, String)> = self
            .keys_in_force_before(to)
            .into_iter()
            .filter(|(account, _)| passes_account_filter(account, account_filter))
            .collect();

        let mut totals: Totals = BTreeMap::new();
        for (account, currency) in &pairs {
            let e = totals
                .entry((currency.clone(), account_kind(account)))
                .or_insert((Some(Decimal::ZERO), Some(Decimal::ZERO)));
            e.0 = e.0.and_then(|acc| {
                self.accrue(account, currency, from, to)
                    .and_then(|seg| acc.checked_add(seg))
            });
        }
        // Each posting counts once, against whichever budgeted accounts cover
        // it, and only from the day one of those budgets existed.
        for ((account, currency), entries) in actuals {
            let covering = pairs
                .iter()
                .filter(|(_, c)| c == currency)
                .map(|(b, _)| b.as_str());
            let Some(start) = clip_start(self, covering, account, currency, children) else {
                continue;
            };
            let start = start.max(from);
            let e = totals
                .entry((currency.clone(), account_kind(account)))
                .or_insert((Some(Decimal::ZERO), Some(Decimal::ZERO)));
            for (_, raw) in entries.iter().filter(|(d, _)| *d >= start) {
                e.1 =
                    e.1.and_then(|acc| acc.checked_add(normalized_actual(types, account, *raw)));
            }
        }
        totals
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
            account: account.to_string(),
            interval: Interval::Month,
            amount: Decimal::from(100),
            currency: "USD".to_string(),
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

    #[test]
    fn account_kind_is_the_top_level_component() {
        assert_eq!(account_kind("Expenses:Food:Sub"), "Expenses");
        assert_eq!(account_kind("Income:Salary"), "Income");
        assert_eq!(account_kind("Liabilities:CreditCard"), "Liabilities");
        assert_eq!(account_kind("Expenses"), "Expenses");
        assert_eq!(account_kind(""), "");
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
        let covered = ["Expenses:Food", "Expenses:Food:Restaurant"];
        assert_eq!(
            clip_start(&budgets, covered, "Expenses:Food", "USD", true),
            Some(d(2024, 6, 1)),
            "a posting on the parent is covered only by the parent's own budget"
        );
        assert_eq!(
            clip_start(&budgets, covered, "Expenses:Food:Restaurant", "USD", true),
            Some(d(2024, 1, 1)),
            "a posting on the child is covered by both, so the earlier wins"
        );
        assert_eq!(
            clip_start(&budgets, covered, "Expenses:Rent", "USD", true),
            None
        );
        assert_eq!(
            clip_start(&budgets, covered, "Expenses:Food", "EUR", true),
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
            account: "Expenses:Food".to_string(),
            interval: Interval::Month,
            amount: Decimal::from(400),
            currency: "USD".to_string(),
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
            cmp.totals
                .get(&("USD".to_string(), "Expenses".to_string()))
                .copied(),
            Some((Some(Decimal::from(400)), Some(Decimal::from(120))))
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
            account: account.to_string(),
            interval: Interval::Day,
            amount: Decimal::from(amount),
            currency: currency.to_string(),
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
