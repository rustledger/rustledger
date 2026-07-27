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
mod diagnostics;
pub use compare::{
    Bucket, BudgetRow, BudgetTotal, Comparison, Empty, normalized_actual, passes_account_filter,
};
// The individual diagnostics are deliberately NOT exported. `compare` runs all
// of them and returns the result already filtered and sorted, which is the only
// way a caller can be sure of the same set the CLI and the FFI get. Exposing
// them separately publishes an order to get wrong, a subset to forget, and — in
// `mismatched_currency_errors`' case — an argument no public API can even
// build.

use rust_decimal::Decimal;
use rustledger_core::{Account, CalendarPeriod, Currency, Directive, MetaValue, NaiveDate};
use std::collections::BTreeMap;

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
    ///
    /// Deliberately NOT Fava's boundaries: its `_IntervalQuarter.get_prev`
    /// tests `date.month > i` where it needs `>=`, putting April in Q1, July in
    /// Q2 and October in Q3 (beancount/fava#2318). See
    /// [`rustledger_core::CalendarPeriod`] for the full note.
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

    /// The calendar length, in days, of the interval starting at `start` — the
    /// per-day accrual's denominator. See [`CalendarPeriod::period_days`];
    /// unlike [`Self::next_start`] it is defined for the final period of the
    /// representable calendar too.
    #[must_use]
    pub fn period_days(self, start: NaiveDate) -> i64 {
        self.period().period_days(start)
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
    pub account: Account,
    /// The interval the amount is stated over.
    pub interval: Interval,
    /// The budgeted amount per interval.
    pub amount: Decimal,
    /// The currency the amount is stated in.
    pub currency: Currency,
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
    pub account: Option<Account>,
    /// What is wrong with it, phrased for a user.
    pub reason: String,
}

/// The account named by a `custom` value, accepting either spelling.
///
/// A quoted string only counts as an account if it looks like one (it contains a
/// `:` component separator), so a genuinely malformed directive still reports as
/// malformed instead of being read as an account named after its own typo.
fn account_name(value: &MetaValue) -> Option<Account> {
    match value {
        MetaValue::Account(a) => Some(a.clone()),
        MetaValue::String(s) if looks_like_account(s) => Some(Account::new(s.as_str())),
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

/// What one `custom "budget"` directive turned out to be.
///
/// Three-way because `custom` is beancount's OPEN extension point and the name
/// "budget" is not ours alone. Beancount's own canonical example is
///
/// ```text
/// 2013-05-18 custom "budget" "weekly < 1000.00 USD" 2016-02-28 TRUE 43.03 USD 23
/// ```
///
/// which Python accepts silently, and this repo's fixtures carry both it and
/// `custom "budget" Assets:Bank:Checking 1000.00 USD TRUE "monthly"`. Treating
/// every `custom "budget"` as ours to judge made `rledger check` — and the LSP,
/// and `validateSource` — report ledgers that are valid beancount.
///
/// Separating "did not have our shape" from "had our shape and is wrong" lets
/// each caller pick its own policy without a second reader existing:
/// `rledger check` reports only what it is CONFIDENT about, while
/// `report budget` also reports the doubtful ones, because a user who asked
/// about budgets is owed the news that one could not be read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BudgetRead {
    /// Not addressed to us: another tool's `custom "budget"`, or not a budget
    /// directive at all. Silent on every surface.
    NotABudget,
    /// Ours, and unusable.
    Invalid(BudgetError),
    /// A budget. `note` carries anything worth telling the user about a
    /// directive that was nonetheless USED.
    ///
    /// The distinction from [`Self::Invalid`] is what the reader can still do.
    /// An unusable account or an unknown interval yields no budget, so there is
    /// nothing to keep. A trailing second figure is different: Fava reads the
    /// first three values and ignores the rest, so `... "monthly" 400.00 USD 12`
    /// really is a 400/month budget there. Rejecting it cost the user their
    /// budget AND — because the report shows only budgeted accounts — the
    /// account's entire row, which is a heavier penalty than the mistake.
    Read {
        /// The budget.
        entry: BudgetEntry,
        /// What to tell the user about it, if anything.
        note: Option<BudgetError>,
    },
}

/// Is this `custom "budget"` addressed to US, or to another tool?
///
/// `custom` is beancount's OPEN extension point and the name "budget" is not
/// ours alone, so this question has to be answered ONCE and answered well. It
/// was previously answered in two places with different criteria — a shape
/// match, and a fallback that looked for an account plus an interval — and the
/// two kept disagreeing: tightening one to stop claiming beancount's own
/// documented example loosened the other into claiming an envelope tool's
/// config. One gate, one rule.
///
/// The rule: a real INTERVAL KEYWORD in the interval slot, or an ACCOUNT and an
/// AMOUNT in theirs. Either is strong evidence; neither happens by coincidence
/// in a payload written for something else.
///
/// | directive | verdict |
/// |---|---|
/// | `Expenses:Food "monthly" 400.00 USD` | ours — keyword |
/// | `"Expenses:food" "monthly" 400.00 USD` | ours — keyword; the account is the fault |
/// | `Expenses:Food "fortnight" 400.00 USD` | ours — account + amount; the interval is the fault |
/// | `Expenses:Food 400.00 USD` | ours — account + amount, no room for another schema |
/// | `Expenses:Food "monthly" 400.00` | ours — keyword; the missing currency is the fault |
/// | `"weekly < 1000.00 USD" 2016-02-28 TRUE …` | not ours — beancount's own example |
/// | `Assets:Bank:Checking 1000.00 USD TRUE "monthly"` | not ours — four values is someone else's schema |
/// | `"envelope-groceries" "rollover" 250.00 USD` | not ours — no account, no keyword |
///
/// `<Account> "monthly"` with no amount IS claimed, deliberately: a directive
/// naming itself "budget", naming an account, and using one of Fava's interval
/// keywords has adopted the convention, and telling its author what is missing
/// beats silence.
fn addressed_to_us(c: &rustledger_core::Custom) -> bool {
    let names_interval = matches!(
        c.values.get(1),
        Some(MetaValue::String(s)) if Interval::parse(s).is_some()
    );
    // An account and an amount, in a payload short enough to be Fava's. The
    // amount need not be in slot 2: `custom "budget" Expenses:Food 400.00 USD`
    // is a budget with the interval word forgotten, and requiring the slot made
    // it addressed to nobody — reported by neither `check` nor the report, which
    // then printed "No budgets declared" over a ledger that plainly declares one.
    //
    // The ARITY is what keeps another tool's payload out. Fava reads three
    // values and tolerates a trailing note, so anything longer is a schema of
    // its own: `custom "budget" Assets:Bank:Checking 1000.00 USD TRUE "monthly"`
    // has four and is not ours to judge.
    let account_and_amount = c.values.len() <= 3
        && c.values.first().and_then(account_name).is_some()
        && c.values.iter().any(|v| matches!(v, MetaValue::Amount(_)));
    names_interval || account_and_amount
}

/// Read ONE `custom "budget"` directive.
///
/// Directive-level on purpose: `rustledger-validate` checks budget directives so
/// that `rledger check` and the LSP see a typo'd interval, and it must reach the
/// same verdict as the report. A second reader over there would be the exact
/// re-derivation this repo's canonical-function discipline exists to prevent,
/// and it would drift the first time the accepted shape changed.
#[must_use]
pub fn read_budget(c: &rustledger_core::Custom) -> BudgetRead {
    if c.custom_type != "budget" || !addressed_to_us(c) {
        return BudgetRead::NotABudget;
    }
    // Past the gate this IS a budget, so every remaining fault is ours to
    // report — on `rledger check` as much as in the report. There is no
    // "might be ours" class any more; that class existed only to paper over the
    // two ownership tests disagreeing.
    let [
        first,
        MetaValue::String(interval_raw),
        MetaValue::Amount(amount),
        rest @ ..,
    ] = c.values.as_slice()
    else {
        return BudgetRead::Invalid(BudgetError {
            date: c.date,
            account: c.values.first().and_then(account_name),
            reason: "budget directive not understood; expected: \
                 custom \"budget\" <Account> \"<interval>\" <amount> <CCY>"
                .to_string(),
        });
    };
    let Some(account) = account_name(first) else {
        return BudgetRead::Invalid(BudgetError {
            date: c.date,
            account: None,
            reason: format!(
                "budget directive names {:?}, which is not a valid account name",
                value_text(first)
            ),
        });
    };
    // A trailing NOTE is ignored rather than rejected: Fava reads
    // `values[0..2]` and lets a ledger carry one
    // (`... 400.00 USD "groceries only"`). Rejecting the whole directive
    // dropped a real budget AND its matching spend from the report over a
    // comment — the opposite of the compatibility this crate exists for.
    //
    // A trailing FIGURE is different: `... 400.00 USD 300.00 EUR`,
    // `... 400.00 USD 300.00` and `... 400.00 USD 23` are all a user declaring
    // a second one. `Int` belongs in this list as much as `Number` and
    // `Amount`: a bare `23` parses as `Int`, and leaving it out let exactly that
    // directive be half-read with no warning.
    let second_figure = rest.iter().any(|v| {
        matches!(
            v,
            MetaValue::Amount(_) | MetaValue::Number(_) | MetaValue::Int(_)
        )
    });
    let Some(interval) = Interval::parse(interval_raw) else {
        return BudgetRead::Invalid(BudgetError {
            date: c.date,
            account: Some(account),
            reason: format!(
                "budget directive has an invalid interval {interval_raw:?} \
                 (use daily, weekly, monthly, quarterly or yearly)"
            ),
        });
    };
    let note = second_figure.then(|| BudgetError {
        date: c.date,
        account: Some(account.clone()),
        reason: "budget directive carries a second figure; only the first is \
             read, so write one budget per directive"
            .to_string(),
    });
    BudgetRead::Read {
        entry: BudgetEntry {
            from: c.date,
            account,
            interval,
            amount: amount.number,
            currency: amount.currency.clone(),
        },
        note,
    }
}

/// A `MetaValue` rendered for a diagnostic, without committing to its type.
fn value_text(v: &MetaValue) -> String {
    match v {
        MetaValue::String(s) => s.clone(),
        MetaValue::Account(a) => a.as_str().to_string(),
        MetaValue::Currency(c) => c.as_str().to_string(),
        MetaValue::Number(n) => n.to_string(),
        MetaValue::Int(i) => i.to_string(),
        MetaValue::Bool(b) => b.to_string(),
        MetaValue::Date(d) => d.to_string(),
        MetaValue::Amount(a) => format!("{} {}", a.number, a.currency),
        MetaValue::Tag(t) => t.as_str().to_string(),
        MetaValue::Link(l) => l.as_str().to_string(),
        MetaValue::None => "none".to_string(),
    }
}

/// Read every `custom "budget"` directive, in effective-date order.
///
/// Malformed entries are returned as errors rather than dropped: a budget that
/// silently does not apply is worse than one that is reported, since the report
/// would otherwise show `0.00` budgeted and look like deliberate under-spend.
#[must_use]
pub(crate) fn parse_budgets(directives: &[Directive]) -> (Vec<BudgetEntry>, Vec<BudgetError>) {
    let mut out = Vec::new();
    let mut errors = Vec::new();
    for d in directives {
        let Directive::Custom(c) = d else { continue };
        // Every failure, because there is only one kind: `addressed_to_us`
        // already decided whether the directive is ours, so anything reaching
        // `Invalid` is a budget that could not be read. `check` reports the same
        // set — the report used to be the more talkative of the two, and is not
        // any more.
        match read_budget(c) {
            BudgetRead::Read { entry, note } => {
                out.push(entry);
                errors.extend(note);
            }
            BudgetRead::Invalid(e) => errors.push(e),
            BudgetRead::NotABudget => {}
        }
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
    /// Directives that could not be read, kept WITH the index rather than
    /// handed back separately. They are part of what the ledger said about
    /// budgets, and a caller holding them apart is a caller that can forget to
    /// report them — which is exactly how the FFI came to show a different
    /// warning set from the CLI on one ledger.
    errors: Vec<BudgetError>,
    /// Entry positions per `(account, currency)`, in effective-date order.
    ///
    /// The supersession lookups — [`Self::in_force`] and
    /// [`Self::next_change_after`] — used to scan every declaration in the
    /// ledger. [`Self::accrue`] calls them once per contiguous segment, so a
    /// year of a monthly budget is two dozen full scans PER ACCRUAL, and the
    /// comparison accrues once per (row, covered account). On a ledger
    /// budgeting 1600 accounts that product dominated the whole report.
    /// Indexed, each lookup is a binary search over one account's own history.
    /// NESTED rather than keyed by an `(Account, Currency)` tuple, because a
    /// tuple key cannot be borrowed from a pair of `&str`. With the tuple, every
    /// lookup called `Account::new(account)` — and `InternedStr::new` takes
    /// `impl Into<Arc<str>>`, so from a `&str` that is a fresh HEAP ALLOCATION,
    /// not an interner hit (interning happens in the loader's dedup pass). The
    /// indexes added to remove per-lookup scans were charging a pair of
    /// allocations instead. `Account: Borrow<str>` with a lexicographic `Ord`,
    /// so nested maps take `&str` directly and allocate nothing.
    by_key: BTreeMap<Account, BTreeMap<Currency, Vec<u32>>>,
    /// Earliest `from` per `(account, currency)`, precomputed.
    ///
    /// [`Self::effective_start`] is called once per (row, posting-account) pair
    /// while pairing spending with budgets, and scanning `entries` for each was
    /// the dominant term: on a ledger budgeting 1600 accounts the comparison
    /// spent seconds here. It cannot go stale — `Budgets` is immutable once
    /// built, and both constructors go through [`Self::index`].
    starts: BTreeMap<Account, BTreeMap<Currency, NaiveDate>>,
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
        Self::index(entries)
    }

    /// Build the derived indexes. The ONE place they are computed, so a second
    /// constructor cannot forget one.
    fn index(entries: Vec<BudgetEntry>) -> Self {
        let mut starts: BTreeMap<Account, BTreeMap<Currency, NaiveDate>> = BTreeMap::new();
        let mut by_key: BTreeMap<Account, BTreeMap<Currency, Vec<u32>>> = BTreeMap::new();
        for (i, e) in entries.iter().enumerate() {
            starts
                .entry(e.account.clone())
                .or_default()
                .entry(e.currency.clone())
                .and_modify(|d| *d = (*d).min(e.from))
                .or_insert(e.from);
            // `entries` is sorted by `from` before indexing, so each key's
            // positions come out in effective-date order — which is what makes
            // the binary searches below valid. A ledger cannot hold u32::MAX
            // budget directives.
            if let Ok(i) = u32::try_from(i) {
                by_key
                    .entry(e.account.clone())
                    .or_default()
                    .entry(e.currency.clone())
                    .or_default()
                    .push(i);
            }
        }
        Self {
            entries,
            by_key,
            starts,
            errors: Vec::new(),
        }
    }

    /// The entries for one `(account, currency)`, in effective-date order.
    fn history(&self, account: &str, currency: &str) -> &[u32] {
        self.by_key
            .get(account)
            .and_then(|by_ccy| by_ccy.get(currency))
            .map_or(&[][..], Vec::as_slice)
    }

    /// Read and index a ledger's `custom "budget"` directives.
    #[must_use]
    pub fn from_directives(directives: &[Directive]) -> Self {
        let (entries, errors) = parse_budgets(directives);
        Self {
            errors,
            ..Self::index(entries)
        }
    }

    /// Directives this ledger declared that could not be read.
    #[must_use]
    pub fn errors(&self) -> &[BudgetError] {
        &self.errors
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
    pub fn keys_in_force_before(&self, before: NaiveDate) -> Vec<(Account, Currency)> {
        // Read off `starts`, which is already the deduplicated key set in sorted
        // order with each key's earliest date. Rebuilding it by cloning every
        // entry and sorting was redundant work on a structure that exists.
        self.starts
            .iter()
            .flat_map(|(account, by_ccy)| {
                by_ccy
                    .iter()
                    .filter(|(_, first)| **first < before)
                    .map(move |(currency, _)| (account.clone(), currency.clone()))
            })
            .collect()
    }

    /// Every distinct `(account, currency)` ever declared, regardless of date.
    ///
    /// Callers that aggregate across a subtree need this: under a
    /// children-inclusive rule a row is live when any budget it covers is live,
    /// which [`Self::keys_in_force_before`] cannot answer because it only looks
    /// at each account's own declarations.
    #[must_use]
    pub fn all_keys(&self) -> Vec<(Account, Currency)> {
        self.starts
            .iter()
            .flat_map(|(account, by_ccy)| {
                by_ccy
                    .keys()
                    .map(move |currency| (account.clone(), currency.clone()))
            })
            .collect()
    }

    /// The budget in force for `(account, currency)` on `day`, if any.
    ///
    /// Supersession is keyed on the pair, not the account alone: a EUR budget and
    /// a USD budget for one account are both live and neither replaces the other.
    #[must_use]
    pub fn in_force(&self, account: &str, currency: &str, day: NaiveDate) -> Option<&BudgetEntry> {
        let history = self.history(account, currency);
        // The LAST entry dated on or before `day`. Same answer as a reverse scan
        // of every declaration: supersession resolves to the last entry on a
        // date, and this key's positions are already in that order.
        let at = history.partition_point(|&i| self.entries[i as usize].from <= day);
        history[..at].last().map(|&i| &self.entries[i as usize])
    }

    /// The first date any budget for `(account, currency)` takes effect.
    ///
    /// Before this date the pair has no budget at all, so spending then is not
    /// spending "against" it — the dual of [`Self::accrue`], which likewise
    /// credits nothing before a budget exists.
    #[must_use]
    pub fn effective_start(&self, account: &str, currency: &str) -> Option<NaiveDate> {
        // Indexed, not scanned — see `starts`. Borrowed all the way down: this
        // is called once per (row, posting account) pair and must not allocate.
        self.starts
            .get(account)
            .and_then(|by_ccy| by_ccy.get(currency))
            .copied()
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
        let history = self.history(account, currency);
        let at = history.partition_point(|&i| self.entries[i as usize].from <= after);
        history.get(at).map(|&i| self.entries[i as usize].from)
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
            // The final period of the representable calendar has no representable
            // NEXT start, but `to` is representable and therefore lies inside that
            // period, so the segment simply ends at `to`. Its length — the
            // pro-rata denominator — comes from `period_days`, which is defined
            // there precisely so this case needs no special arithmetic.
            //
            // Two earlier spellings were both wrong. Propagating `None` threw away
            // the whole total, so `--to 9999-12-31` reported nothing for a budget
            // that had accrued 9,570,000.00, and the caller blamed `Decimal`
            // overflow. Breaking out kept the earlier periods but silently dropped
            // the final one: extending the window by a month added 0.00 budget,
            // and a window lying entirely inside that period reported a live
            // budget as `0.00` with no diagnostic — indistinguishable from
            // "nothing was budgeted".
            let mut seg_end = b
                .interval
                .next_start(istart)
                .map_or(to, |inext| inext.min(to));
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
            let interval_days = b.interval.period_days(istart).max(1);
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
