//! Budgeting for beancount ledgers — the shared model behind `rledger`'s
//! budget reporting.
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
//! A ledger already budgeted for Fava works here unchanged — no new syntax, and
//! the ledger stays the only source of truth.
//!
//! Like [`rustledger_returns`](https://docs.rs/rustledger-returns), this crate
//! deliberately owns only the *model*: reading the directives, the calendar
//! interval arithmetic, and the accrual math. It does no ledger loading, no
//! rendering and no I/O, so every consumer — the CLI `report budget` command,
//! the FFI component, rustfava, the query engine — shares ONE implementation
//! rather than re-deriving supersession, calendar anchoring and pro-rating (the
//! repo's canonical-function discipline). Those rules are subtle enough that two
//! implementations would certainly drift: see the leap-February denominator and
//! the mid-interval supersession split below.
//!
//! # Semantics (matching Fava)
//!
//! - **Per-day accrual, not period matching.** Every day in the half-open range
//!   `[from, to)` accrues `amount / days_in_the_calendar_interval_containing_that_day`.
//!   The denominator is the interval's true calendar length, so a monthly budget
//!   divides by 28/29/30/31 and a yearly one by 365/366. Arbitrary partial
//!   periods therefore pro-rate for free, with no special case.
//! - **Calendar anchoring.** Intervals align to calendar boundaries (month = the
//!   1st, quarter = Jan/Apr/Jul/Oct 1, year = Jan 1, week = ISO Monday), *not* to
//!   the date the directive was written. A budget declared mid-month accrues from
//!   that day on, but each day is still divided by the surrounding calendar month.
//! - **Supersession is per (account, currency).** A later directive replaces an
//!   earlier one for the same account *and currency* from its own date; budgets
//!   in different currencies for one account stay simultaneously active.
//! - **Not retroactive.** A budget applies from its own date onward, so a period
//!   entirely before the first declaration accrues nothing.

mod compare;
pub use compare::{
    BudgetRow, Comparison, Totals, account_kind, clip_start, normalized_actual,
    passes_account_filter,
};

use rust_decimal::Decimal;
use rustledger_core::{CalendarPeriod, Directive, MetaValue, NaiveDate};

/// A budget interval, which fixes both the calendar anchoring and the per-day
/// denominator.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Interval {
    /// One calendar day.
    Day,
    /// An ISO week, starting Monday.
    Week,
    /// A calendar month (28, 29, 30 or 31 days).
    Month,
    /// A calendar quarter, anchored at Jan/Apr/Jul/Oct 1.
    Quarter,
    /// A calendar year (365 or 366 days).
    Year,
}

impl Interval {
    /// Parse an interval keyword.
    ///
    /// Fava accepts ten spellings — both the bare noun and the `-ly` form of each
    /// interval — matched case-insensitively, even though its documentation
    /// advertises only the five `-ly` forms. Accepting all ten keeps ledgers that
    /// rely on the implementation (rather than the docs) working.
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        match s.to_ascii_lowercase().as_str() {
            "day" | "daily" => Some(Self::Day),
            "week" | "weekly" => Some(Self::Week),
            "month" | "monthly" => Some(Self::Month),
            "quarter" | "quarterly" => Some(Self::Quarter),
            "year" | "yearly" => Some(Self::Year),
            _ => None,
        }
    }

    /// The calendar period this interval measures.
    ///
    /// The truncation arithmetic itself lives in
    /// [`rustledger_core::CalendarPeriod`], shared with BQL's `DATE_TRUNC`, so a
    /// weekly budget and `GROUP BY DATE_TRUNC('WEEK', date)` cannot disagree
    /// about where a week starts. This type stays distinct because it also
    /// carries the Fava keyword vocabulary, which is a budget-format concern.
    #[must_use]
    pub const fn period(self) -> CalendarPeriod {
        match self {
            Self::Day => CalendarPeriod::Day,
            Self::Week => CalendarPeriod::Week,
            Self::Month => CalendarPeriod::Month,
            Self::Quarter => CalendarPeriod::Quarter,
            Self::Year => CalendarPeriod::Year,
        }
    }

    /// The first day of the calendar interval containing `day`.
    #[must_use]
    pub fn start_of(self, day: NaiveDate) -> NaiveDate {
        self.period().start_of(day)
    }

    /// The first day of the interval after the one starting at `start`.
    /// `None` when that date is outside the representable range — see
    /// [`CalendarPeriod::next_start`].
    #[must_use]
    pub fn next_start(self, start: NaiveDate) -> Option<NaiveDate> {
        self.period().next_start(start)
    }
}

/// Does a budget on `budgeted` account for spending booked to `posting_account`?
///
/// The single definition of budget COVERAGE, used by row assembly, totals and
/// every diagnostic. They were once separate spellings of this rule, and a
/// change to one silently stopped the totals describing the rows above them.
///
/// Component-aware by design: `Expenses:FoodCourt` is NOT part of
/// `Expenses:Food`, though Fava's `startswith` test says otherwise. Per the
/// project's Python-compatibility policy we match correct behavior, not bugs.
#[must_use]
pub fn covers(budgeted: &str, posting_account: &str, children: bool) -> bool {
    if children {
        rustledger_core::is_subaccount_or_equal(posting_account, budgeted)
    } else {
        posting_account == budgeted
    }
}

/// One `custom "budget"` declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BudgetEntry {
    /// Effective from this date (the directive's own date).
    pub from: NaiveDate,
    /// The budgeted account.
    pub account: String,
    /// The interval the amount is stated over.
    pub interval: Interval,
    /// The budgeted amount per interval.
    pub amount: Decimal,
    /// The currency the amount is stated in.
    pub currency: String,
}

/// A `custom "budget"` directive that could not be read, reported rather than
/// silently ignored.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BudgetError {
    /// The directive's date.
    pub date: NaiveDate,
    /// The account the directive names, when it could be read. `None` for a
    /// directive malformed enough that no account could be identified. Lets a
    /// consumer report only the problems relevant to the accounts it is showing.
    pub account: Option<String>,
    /// What is wrong with it, phrased for a user.
    pub reason: String,
}

/// The account named by a `custom` value, accepting either spelling.
///
/// A quoted string only counts as an account if it looks like one (it contains a
/// `:` component separator), so a genuinely malformed directive still reports as
/// malformed instead of being read as an account named after its own typo.
fn account_name(value: &MetaValue) -> Option<String> {
    match value {
        MetaValue::Account(a) => Some(a.to_string()),
        MetaValue::String(s) if looks_like_account(s) => Some(s.clone()),
        _ => None,
    }
}

/// Is this quoted string actually a valid account name?
///
/// A quoted value is arbitrary user text — accepting it verbatim let a name
/// carrying a newline forge a row in the text report's fixed-width table. The
/// test is [`rustledger_parser::is_valid_account_name`], the CANONICAL rule
/// (it lexes the name and requires it to round-trip as a single account token),
/// not a hand-rolled character check: that function's own documentation records
/// that the validator and loader once each hand-implemented this with different
/// accepted character sets, letting through accounts that could never be parsed
/// back.
fn looks_like_account(s: &str) -> bool {
    rustledger_parser::is_valid_account_name(s)
}

/// Read every `custom "budget"` directive, in effective-date order.
///
/// Malformed entries are returned as errors rather than dropped: a budget that
/// silently does not apply is worse than one that is reported, since the report
/// would otherwise show `0.00` budgeted and look like deliberate under-spend.
#[must_use]
pub fn parse_budgets(directives: &[Directive]) -> (Vec<BudgetEntry>, Vec<BudgetError>) {
    let mut out = Vec::new();
    let mut errors = Vec::new();
    for d in directives {
        let Directive::Custom(c) = d else { continue };
        if c.custom_type != "budget" {
            continue;
        }
        // Shape: <Account> "<interval>" <amount>
        //
        // The account is accepted both as a bare account token and as a quoted
        // string. Fava's own reader is duck-typed (it just takes `values[0]`),
        // and Beancount's `custom` documentation writes its examples with quoted
        // strings, so real Fava-budgeted ledgers contain both spellings; taking
        // only the token would reject a ledger Fava renders fine, which is
        // exactly the compatibility this crate exists to provide.
        // A trailing NOTE is ignored rather than rejected: Fava reads
        // `values[0..2]` and lets a ledger carry one
        // (`... 400.00 USD "groceries only"`). Rejecting the whole directive
        // dropped a real budget AND its matching spend from the report over a
        // comment — the opposite of the compatibility this crate exists for.
        //
        // A trailing NUMBER or AMOUNT is different: `... 400.00 USD 300.00 EUR`
        // and `... 400.00 USD 300.00` are both a user declaring a second figure,
        // and silently keeping the first would drop it with no diagnostic
        // anywhere. Those stay an error, so the user is told which half was lost.
        let parsed = match c.values.as_slice() {
            [
                acct,
                MetaValue::String(interval_raw),
                MetaValue::Amount(amount),
                rest @ ..,
            ] if !rest
                .iter()
                .any(|v| matches!(v, MetaValue::Amount(_) | MetaValue::Number(_))) =>
            {
                account_name(acct).map(|a| (a, interval_raw, amount))
            }
            _ => None,
        };
        let Some((account, interval_raw, amount)) = parsed else {
            errors.push(BudgetError {
                date: c.date,
                account: c.values.first().and_then(account_name),
                reason: "malformed budget directive; expected: \
                     custom \"budget\" <Account> \"<interval>\" <amount> <CCY>"
                    .to_string(),
            });
            continue;
        };
        let Some(interval) = Interval::parse(interval_raw) else {
            errors.push(BudgetError {
                date: c.date,
                account: Some(account.clone()),
                reason: format!(
                    "budget directive has an invalid interval {interval_raw:?} \
                     (use daily, weekly, monthly, quarterly or yearly)"
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
    // Effective-date order, so the "latest in force" scan is a simple walk.
    out.sort_by_key(|e| e.from);
    (out, errors)
}

/// A ledger's budgets, indexed for the queries the accrual needs.
///
/// Supersession, "the next declaration after this date" and "is anything in
/// force" are each needed in several places; keeping the flat list and writing
/// the predicate at every call site is how the two halves of an accrual loop
/// drift apart and start disagreeing about the rate for a segment.
#[derive(Clone, Debug, Default)]
pub struct Budgets {
    /// Sorted by `from`, so a reverse scan finds the entry in force.
    entries: Vec<BudgetEntry>,
}

impl Budgets {
    /// Index a set of declarations.
    ///
    /// `entries` need not be sorted by date — this sorts them. It IS
    /// order-significant in one respect: the sort is stable, and supersession
    /// resolves to the LAST entry on a given date, so two declarations sharing a
    /// date and `(account, currency)` supersede in the order you pass them.
    /// [`Self::from_directives`] passes them in file order, which is what
    /// beancount entry order (and therefore Fava) means by "the later one wins".
    /// A caller assembling entries from a map or a set has no such order and
    /// will get an arbitrary winner; sort or deduplicate before calling.
    #[must_use]
    pub fn new(mut entries: Vec<BudgetEntry>) -> Self {
        entries.sort_by_key(|e| e.from);
        Self { entries }
    }

    /// Read and index a ledger's `custom "budget"` directives.
    #[must_use]
    pub fn from_directives(directives: &[Directive]) -> (Self, Vec<BudgetError>) {
        let (entries, errors) = parse_budgets(directives);
        (Self { entries }, errors)
    }

    /// Every declaration, in effective-date order.
    ///
    /// Returns an iterator rather than a slice deliberately: the storage is a
    /// flat `Vec` today and the lookups here scan it linearly, which is fine for
    /// the handful of budgets a ledger has but not for a consumer with
    /// thousands. Handing out `&[BudgetEntry]` would freeze that representation
    /// on the published API, so re-indexing later — by `(account, currency)`,
    /// say — could not be done without a major version.
    pub fn entries(&self) -> impl ExactSizeIterator<Item = &BudgetEntry> + Clone {
        self.entries.iter()
    }

    /// Whether any budget at all was declared.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The earliest date any budget takes effect.
    #[must_use]
    pub fn earliest(&self) -> Option<NaiveDate> {
        self.entries.iter().map(|e| e.from).min()
    }

    /// Every distinct `(account, currency)` in force before `before`.
    ///
    /// "In force before" excludes budgets declared on or after the window's
    /// exclusive end: a budget written today does not apply to last year.
    #[must_use]
    pub fn keys_in_force_before(&self, before: NaiveDate) -> Vec<(String, String)> {
        let mut keys: Vec<(String, String)> = self
            .entries
            .iter()
            .filter(|e| e.from < before)
            .map(|e| (e.account.clone(), e.currency.clone()))
            .collect();
        keys.sort();
        keys.dedup();
        keys
    }

    /// Every distinct `(account, currency)` ever declared, regardless of date.
    ///
    /// Callers that aggregate across a subtree need this: under a
    /// children-inclusive rule a row is live when any budget it covers is live,
    /// which [`Self::keys_in_force_before`] cannot answer because it only looks
    /// at each account's own declarations.
    #[must_use]
    pub fn all_keys(&self) -> Vec<(String, String)> {
        let mut keys: Vec<(String, String)> = self
            .entries
            .iter()
            .map(|e| (e.account.clone(), e.currency.clone()))
            .collect();
        keys.sort();
        keys.dedup();
        keys
    }

    /// Whether any budget takes effect before `before`.
    #[must_use]
    pub fn any_in_force_before(&self, before: NaiveDate) -> bool {
        self.entries.iter().any(|e| e.from < before)
    }

    /// The budget in force for `(account, currency)` on `day`, if any.
    ///
    /// Supersession is keyed on the pair, not the account alone: a EUR budget and
    /// a USD budget for one account are both live and neither replaces the other.
    #[must_use]
    pub fn in_force(&self, account: &str, currency: &str, day: NaiveDate) -> Option<&BudgetEntry> {
        self.entries
            .iter()
            .rfind(|b| b.account == account && b.currency == currency && b.from <= day)
    }

    /// The first date any budget for `(account, currency)` takes effect.
    ///
    /// Before this date the pair has no budget at all, so spending then is not
    /// spending "against" it — the dual of [`Self::accrue`], which likewise
    /// credits nothing before a budget exists.
    #[must_use]
    pub fn effective_start(&self, account: &str, currency: &str) -> Option<NaiveDate> {
        self.entries
            .iter()
            .filter(|e| e.account == account && e.currency == currency)
            .map(|e| e.from)
            .min()
    }

    /// The date of the next declaration for `(account, currency)` strictly after
    /// `after` — where the accrual rate changes.
    #[must_use]
    pub fn next_change_after(
        &self,
        account: &str,
        currency: &str,
        after: NaiveDate,
    ) -> Option<NaiveDate> {
        self.entries
            .iter()
            .filter(|e| e.account == account && e.currency == currency && e.from > after)
            .map(|e| e.from)
            .min()
    }

    /// Accrue the budgeted amount for one `(account, currency)` over `[from, to)`.
    ///
    /// Conceptually this is Fava's per-day accrual — every day contributes
    /// `amount / days_in_its_calendar_interval` — which is what makes an arbitrary
    /// window pro-rate with no special case. It is evaluated **per contiguous
    /// segment** rather than per day, though, because summing `400/29` twenty-nine
    /// times does not recover exactly `400` in decimal arithmetic: the residue
    /// surfaced as `399.99999999999999999999999997` in machine output. A segment
    /// contributes `amount × days_in_segment / days_in_interval` — multiplying
    /// before dividing, so a fully covered interval is exactly `amount` — which is
    /// mathematically identical to the day-by-day sum but exact at the boundaries
    /// that matter most (a whole month of a monthly budget IS the monthly figure).
    ///
    /// Segments break at whichever comes first: the end of the calendar interval,
    /// the start of a superseding budget, or the end of the window.
    #[must_use]
    /// `None` if the arithmetic leaves `Decimal`'s range, which only an absurd
    /// declared amount can cause. Saturating instead would print a figure wrong
    /// by an unbounded factor as though it were authoritative — a two-month
    /// window and a one-month window both clamping to `Decimal::MAX` look
    /// identical on screen.
    pub fn accrue(
        &self,
        account: &str,
        currency: &str,
        from: NaiveDate,
        to: NaiveDate,
    ) -> Option<Decimal> {
        let next_day = |d: NaiveDate| d.checked_add(jiff::Span::new().days(1)).unwrap_or(d);
        let days_between = |a: NaiveDate, b: NaiveDate| {
            i64::from(a.until((jiff::Unit::Day, b)).map_or(0, |s| s.get_days()))
        };

        let mut total = Decimal::ZERO;
        let mut cursor = from;
        while cursor < to {
            let Some(b) = self.in_force(account, currency, cursor) else {
                // No budget yet in force: skip ahead to the next declaration, or
                // stop if there is none.
                //
                // No `next < to` guard: `next_change_after` returns a date
                // strictly after `cursor`, so a declaration at or past `to`
                // simply ends the loop on the next iteration with the same
                // total. Mutation testing flagged that guard as unkillable,
                // which is how a dead condition announces itself.
                match self.next_change_after(account, currency, cursor) {
                    Some(next) => cursor = next,
                    None => break,
                }
                continue;
            };
            let istart = b.interval.start_of(cursor);
            // The final period at the very end of the representable calendar has
            // no next start, so its length — and therefore its per-day rate — is
            // unknowable. Stop and keep what is already accrued.
            //
            // Propagating `None` here instead threw away the whole total: a
            // window of `--to 9999-12-31` returned nothing for a budget whose
            // accrual to that point was 9,570,000.00, and the caller attributed
            // the absence to `Decimal` overflow, which it was not. Omitting one
            // unmeasurable trailing period from an all-time window is a far
            // smaller lie than discarding every period before it.
            let Some(inext) = b.interval.next_start(istart) else {
                break;
            };
            let mut seg_end = inext.min(to);
            // The next superseding declaration, if it lands inside this segment.
            // `<` and `<=` are indistinguishable here (assigning `seg_end` to a
            // value it already holds changes nothing), so mutation testing
            // reports the comparison as unkillable; the guard itself is NOT
            // dead, because a change beyond `seg_end` must not extend it.
            if let Some(change) = self.next_change_after(account, currency, cursor)
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
            // `> 0` rather than `>= 0`: a zero-day segment contributes exactly
            // zero either way, so the two are indistinguishable by result. The
            // test is kept because skipping the arithmetic entirely is clearer
            // than relying on `0 * amount / days` to vanish.
            if seg_days > 0 {
                let num = Decimal::from(seg_days);
                let den = Decimal::from(interval_days);
                // Multiply-before-divide is what makes a fully covered interval
                // come to exactly `amount`, but the product overflows `Decimal`
                // once the declared amount exceeds about MAX/366 — and a budget
                // amount comes from the ledger, which must never panic the CLI.
                // Fall back to divide-first for those: the residue is irrelevant
                // at that scale, and a slightly inexact number beats an abort.
                let seg = match b.amount.checked_mul(num) {
                    Some(product) => product.checked_div(den)?,
                    // Multiply-before-divide overflows above about MAX/366;
                    // divide-first still answers, less exactly, at that scale.
                    None => b.amount.checked_div(den)?.checked_mul(num)?,
                };
                total = total.checked_add(seg)?;
            }
            cursor = seg_end;
        }
        Some(total)
    }
}

#[cfg(test)]
mod tests;
