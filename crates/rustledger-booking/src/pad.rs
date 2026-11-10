//! Pad directive processing and transaction reconstruction.
//!
//! This module provides functionality to:
//! - Process pad directives and calculate padding amounts
//! - Generate synthetic transactions representing padding adjustments
//!
//! # Pad Processing
//!
//! A `pad` directive inserts a synthetic transaction between the `pad` date and
//! the next `balance` assertion to make the balance match. The synthetic transaction
//! transfers funds from the source account to the target account.
//!
//! ```beancount
//! 2024-01-01 pad Assets:Bank Equity:Opening-Balances
//! 2024-01-02 balance Assets:Bank 1000.00 USD
//! ```
//!
//! This generates a synthetic transaction (matching Python beancount's format):
//! ```beancount
//! 2024-01-01 P "(Padding inserted for Balance of 1000.00 USD for difference 1000.00 USD)"
//!   Assets:Bank             1000.00 USD
//!   Equity:Opening-Balances -1000.00 USD
//! ```

use rust_decimal::Decimal;
use rustc_hash::{FxHashMap, FxHashSet};
use rustledger_core::{
    Account, Amount, Currency, Directive, NaiveDate, Posting, Spanned, Transaction,
};
use std::ops::Neg;

/// Prefix of the narration carried by every synth pad transaction
/// produced by this crate (the format string used inside the
/// private `create_padding_transaction` constructor).
///
/// Together with [`is_synthesized_pad`], lets consumers distinguish
/// pad-synth transactions from user-written `P`-flag transactions
/// (`P` is a valid user flag in beancount). The narration prefix
/// matches Python beancount's format and is preserved end-to-end
/// through the booking and merge steps.
pub const SYNTH_PAD_NARRATION_PREFIX: &str = "(Padding inserted for Balance of ";

/// Returns `true` iff `txn` is a pad-synth transaction produced by
/// this crate.
///
/// Checks the `P` flag AND the [`SYNTH_PAD_NARRATION_PREFIX`].
/// A bare flag check would conflate user-written `P`-flag
/// transactions with synth pads.
#[must_use]
pub fn is_synthesized_pad(txn: &Transaction) -> bool {
    txn.flag == 'P'
        && txn
            .narration
            .as_str()
            .starts_with(SYNTH_PAD_NARRATION_PREFIX)
}

/// Result of processing pad directives.
///
/// This holds only what `process_pads` *derives* from the input: the
/// synthesized padding transactions and any errors. It deliberately
/// does NOT echo the input directives back — the caller already owns
/// that slice, so cloning it into the result was pure waste on every
/// call (a full deep-clone of the directive stream the caller then
/// discarded). Callers that want the source merged with the synth
/// transactions for balance math should use [`merge_with_padding`].
#[derive(Debug, Clone)]
pub struct PadResult {
    /// Synthetic padding transactions generated.
    pub padding_transactions: Vec<Transaction>,
    /// Where each of [`Self::padding_transactions`] came from, in the same
    /// order: the `pad` that produced it and the `balance` it satisfies.
    /// Beancount gives a padding entry the `pad`'s source location and its
    /// postings the `balance`'s, so a query reports both (#2825).
    pub padding_origins: Vec<PadOrigin>,
    /// Any errors encountered during pad processing.
    pub errors: Vec<PadError>,
}

/// The directives a padding transaction came from: indices into the slice
/// [`process_pads`] was given.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PadOrigin {
    /// The `pad` directive that produced the transaction.
    pub pad: usize,
    /// The `balance` assertion the transaction satisfies.
    pub balance: usize,
}

/// Error during pad processing.
#[derive(Debug, Clone)]
pub struct PadError {
    /// Date of the error.
    pub date: NaiveDate,
    /// Error message.
    pub message: String,
    /// Account involved.
    pub account: Option<rustledger_core::Account>,
}

impl PadError {
    /// Create a new pad error.
    pub fn new(date: NaiveDate, message: impl Into<String>) -> Self {
        Self {
            date,
            message: message.into(),
            account: None,
        }
    }

    /// Add account context.
    pub fn with_account(mut self, account: impl Into<rustledger_core::Account>) -> Self {
        self.account = Some(account.into());
        self
    }
}

/// Multiplier beancount applies to a `balance`'s inferred tolerance: twice
/// the `tolerance_multiplier` option (`beancount/ops/balance.py`,
/// `get_balance_tolerance`).
const BALANCE_TOLERANCE_MULTIPLIER: Decimal = Decimal::TWO;

/// The tolerance a `balance` assertion of `expected` is checked with.
///
/// A `pad` measures its difference against it too: this is beancount's
/// `get_balance_tolerance`, which both its balance check and its `pad`
/// plugin call.
///
/// - `explicit`: the `~ tolerance` written on the directive, which always
///   wins.
/// - `tolerance_multiplier`: the `tolerance_multiplier` option (default
///   0.5, [`crate::DEFAULT_TOLERANCE_MULTIPLIER`]).
///
/// Otherwise the tolerance is `tolerance_multiplier * 2` units of the
/// asserted amount's last digit, and zero for an integer amount, which must
/// match exactly.
///
/// CANONICAL: the balance check in `rustledger-validate` and [`plan_pads`]
/// both call this, so a difference a pad leaves alone is one the check
/// passes (#2901).
#[must_use]
pub fn balance_tolerance(
    expected: Decimal,
    explicit: Option<Decimal>,
    tolerance_multiplier: Decimal,
) -> Decimal {
    if let Some(t) = explicit {
        return t;
    }
    let scale = expected.scale();
    if scale > 0 {
        tolerance_multiplier * BALANCE_TOLERANCE_MULTIPLIER * Decimal::new(1, scale)
    } else {
        Decimal::ZERO
    }
}

/// The pad rule, beancount's `pad` plugin (`beancount/ops/pad.py`).
///
/// Each account with a `pad` is a pad group, walked on its own:
///
/// - A group sees the balances on its account AND on its sub-accounts. Each
///   is compared against the group's own running amount: the real postings
///   of the account and its sub-accounts, plus the padding this group has
///   inserted (beancount's `pad_balance`). Another group's padding is no
///   part of it, whether it went into a sub-account or came out of the
///   group's account as that pad's source (#2901).
/// - The pad a balance can use is the group's latest `pad` before it (its
///   `active_pad`). A pad superseded by a later one is never used again, and
///   comes out unused if it never padded.
/// - A balance in a currency uses up that currency for the group until the
///   next `pad` (`padded_lots`), whatever its difference, and so does a
///   balance on a sub-account: `pad A`, `balance A:B 30` (held),
///   `balance A 100` pads nothing and fails the second balance.
/// - A pad inserts padding only for a difference beyond the balance's
///   tolerance ([`balance_tolerance`]). A pad that never inserts padding is
///   an `Unused Pad entry`, even if a balance reached it.
///
/// The padding goes into the group's account, whichever account the balance
/// is on. [`plan_pads`] is its one caller, and walks the ledger in booking
/// order, so the pads a group has seen when a balance comes are the ones
/// before it (a same-date `pad` sorts after the `balance`, #2150).
#[derive(Debug, Default)]
struct PadTracker {
    /// The pad groups, by account.
    groups: FxHashMap<Account, PadGroup>,
    /// Every `pad`, in walk order.
    pads: Vec<TrackedPad>,
}

/// One account's pads (one of beancount's per-account walks).
#[derive(Debug, Default)]
struct PadGroup {
    /// The active pad, an index into [`PadTracker::pads`].
    active: Option<usize>,
    /// Currencies a balance has asserted since the active pad
    /// (`padded_lots`): they are compared, not padded.
    padded_lots: FxHashSet<Currency>,
    /// The units of the real postings to the account and its sub-accounts,
    /// per currency, kept running as beancount keeps `pad_balance`: seeded
    /// once when the group's first `pad` comes, then moved by each posting
    /// (`PadTracker::post`). Summing the subtree at every balance instead
    /// made a parent pad with balances on its sub-accounts quadratic.
    real: Totals,
    /// Currencies whose running `real` total left the representable range
    /// (#1863). Their amount is summed from the inventories when needed.
    real_overflowed: FxHashSet<Currency>,
    /// The padding this group has inserted, per currency.
    padded: Totals,
}

/// A `pad` known to a [`PadTracker`].
#[derive(Debug)]
struct TrackedPad {
    date: NaiveDate,
    target: Account,
    source_account: Account,
    /// The pad's index in the input.
    index: usize,
    /// Whether this pad inserted padding for at least one balance.
    used: bool,
}

/// What a pad group does for a balance.
enum PadAction {
    /// Nothing is padded: the group has no active pad open to the currency,
    /// or the difference is within the balance's tolerance. The currency is
    /// used up all the same.
    Compare,
    /// Pad this amount into the group's account, and its negation out of the
    /// active pad's source.
    Pad(Decimal),
    /// The group's amount, or the difference, cannot be represented: nothing
    /// is padded, and the caller reports it (#1863).
    Unrepresentable,
}

impl PadTracker {
    /// A `pad` into `target` from `source_account`: the group's active pad
    /// from now on, with every currency open to padding again. `seed` gives
    /// the account's and its sub-accounts' real units so far, read only when
    /// this is the account's first `pad`.
    fn add(
        &mut self,
        target: &Account,
        date: NaiveDate,
        source_account: Account,
        index: usize,
        seed: impl FnOnce() -> (Totals, FxHashSet<Currency>),
    ) {
        let group = self.groups.entry(target.clone()).or_insert_with(|| {
            let (real, real_overflowed) = seed();
            PadGroup {
                real,
                real_overflowed,
                ..PadGroup::default()
            }
        });
        group.active = Some(self.pads.len());
        group.padded_lots.clear();
        self.pads.push(TrackedPad {
            date,
            target: target.clone(),
            source_account,
            index,
            used: false,
        });
    }

    /// The prefixes of `account` that can name a group: its ancestors,
    /// outermost first, then the account itself.
    fn prefixes(account: &str) -> impl Iterator<Item = &str> {
        account
            .match_indices(':')
            .map(|(at, _)| &account[..at])
            .chain(std::iter::once(account))
    }

    /// A real posting of `number` `currency` to `account`: every group it
    /// falls in (the account's own and its ancestors') moves by it. O(depth).
    fn post(&mut self, account: &Account, currency: &Currency, number: Decimal) {
        if self.groups.is_empty() {
            return;
        }
        for prefix in Self::prefixes(account.as_str()) {
            if let Some(group) = self.groups.get_mut(prefix)
                && !group.real_overflowed.contains(currency)
                && add_units(&mut group.real, currency, number).is_err()
            {
                group.real_overflowed.insert(currency.clone());
            }
        }
    }

    /// The groups a `balance` on `account` belongs to: its own account's and
    /// its ancestors', outermost first (beancount walks the groups in sorted
    /// order).
    fn groups_of(&self, account: &Account) -> Vec<Account> {
        if self.groups.is_empty() {
            return Vec::new();
        }
        Self::prefixes(account.as_str())
            .filter_map(|prefix| self.groups.get_key_value(prefix).map(|(k, _)| k.clone()))
            .collect()
    }

    /// Apply the rule for the group of `group_account` to a `balance` of
    /// `asserted`, checked with `tolerance`. `summed` sums the units of the
    /// currency in the group's account and its sub-accounts from the
    /// inventories (`None` when they cannot be represented); it is called
    /// only when the group's running total of the currency left range.
    ///
    /// Returns what to do, the active pad when the group can pad, and the
    /// group's units before any padding for this balance (its real units and
    /// its own earlier padding, per currency: beancount's `pad_balance`).
    fn balance(
        &mut self,
        group_account: &Account,
        asserted: &Amount,
        tolerance: Decimal,
        summed: impl FnOnce() -> Option<Decimal>,
    ) -> (PadAction, Option<(&TrackedPad, Vec<Amount>)>) {
        let Some(group) = self.groups.get_mut(group_account) else {
            return (PadAction::Compare, None);
        };
        let currency = &asserted.currency;
        // The currency is used up whatever comes of this balance.
        let fresh = group.padded_lots.insert(currency.clone());
        let Some(active) = group.active.filter(|_| fresh) else {
            return (PadAction::Compare, None);
        };
        let real = if group.real_overflowed.contains(currency) {
            summed()
        } else {
            Some(units_of(&group.real, currency))
        };
        let own_padding = units_of(&group.padded, currency);
        let mut held = Vec::new();
        let action = match real
            .and_then(|r| r.checked_add(own_padding))
            .and_then(|current| asserted.number.checked_sub(current))
        {
            None => PadAction::Unrepresentable,
            Some(difference) if difference.abs() <= tolerance => PadAction::Compare,
            Some(difference) => {
                held = held_units(group);
                if add_units(&mut group.padded, currency, difference).is_err() {
                    PadAction::Unrepresentable
                } else {
                    self.pads[active].used = true;
                    PadAction::Pad(difference)
                }
            }
        };
        (action, Some((&self.pads[active], held)))
    }

    /// Take back `difference` of `currency` from the padding of
    /// `group_account`'s group: padding [`Self::balance`] planned that could
    /// not be applied. It restores a total that existed a moment ago, so it
    /// cannot overflow.
    fn retract(&mut self, group_account: &Account, currency: &Currency, difference: Decimal) {
        if let Some(group) = self.groups.get_mut(group_account) {
            drop(add_units(&mut group.padded, currency, -difference));
        }
    }
}

/// What `group` holds, per currency: its real units and its own padding
/// (beancount's `pad_balance`), for the "pad an entry with cost" message. A
/// currency whose total cannot be represented is left out: the message is
/// all it is for.
fn held_units(group: &PadGroup) -> Vec<Amount> {
    let mut held: Totals = group
        .real
        .iter()
        .filter(|(c, _)| !group.real_overflowed.contains(c))
        .cloned()
        .collect();
    for (currency, number) in &group.padded {
        if add_units(&mut held, currency, *number).is_err() {
            held.retain(|(c, _)| c != currency);
        }
    }
    held.into_iter()
        .map(|(currency, number)| Amount::new(number, currency))
        .collect()
}

/// The units of `currency` in `totals`.
fn units_of(totals: &Totals, currency: &Currency) -> Decimal {
    totals
        .iter()
        .find(|(c, _)| c == currency)
        .map_or(Decimal::ZERO, |(_, n)| *n)
}

/// Add `number` `currency` to `totals`. A total that would leave the
/// representable range is left as it was and reported (#1863).
fn add_units(
    totals: &mut Totals,
    currency: &Currency,
    number: Decimal,
) -> Result<(), rustledger_core::OverflowError> {
    if let Some((_, total)) = totals.iter_mut().find(|(c, _)| c == currency) {
        *total = total
            .checked_add(number)
            .ok_or_else(|| rustledger_core::OverflowError {
                currency: currency.clone(),
            })?;
    } else {
        totals.push((currency.clone(), number));
    }
    Ok(())
}

/// The padding beancount inserts for a ledger, from [`plan_pads`].
///
/// This is the one pad computation. [`process_pads`] turns it into the
/// synthesized padding transactions the loader's balance view, BQL and the
/// reports read, and `rustledger-validate`'s balance check computes it over
/// its own stream and adds it to its booked inventories as its walk reaches
/// each `pad`, dated at the pad as beancount dates its padding entry. Given
/// the same stream the two pad the same amounts from the same pads at the
/// same place; what can still differ is the inventories each then compares
/// against, which the `pad_parity_test` drift guard in `rustledger-validate`
/// covers.
#[derive(Debug, Clone, Default)]
pub struct PadPlan {
    /// The padding to insert, in the order of the balances it satisfies.
    pub paddings: Vec<PlannedPadding>,
    /// The pads that inserted no padding (`Unused Pad entry`), in walk order.
    pub unused: Vec<UnusedPad>,
    /// Pad amounts that could not be computed or applied (#1863), each with
    /// the index of the balance it was for: no padding is planned for them.
    pub failed: Vec<(usize, PadError)>,
    /// Running balances that left the representable range on a posting. The
    /// validator reports these itself, from its own inventories.
    pub inventory_errors: Vec<PadError>,
}

/// One padding entry of a [`PadPlan`]: `units` into `target`, their
/// negation out of `source`, dated at the pad, as beancount dates its
/// padding entry.
#[derive(Debug, Clone)]
pub struct PlannedPadding {
    /// The `pad` and the `balance` it satisfies.
    pub origin: PadOrigin,
    /// The pad's date.
    pub date: NaiveDate,
    /// The account padded: the pad's account. The balance is on it or on
    /// one of its sub-accounts.
    pub target: Account,
    /// The account the padding is taken from.
    pub source: Account,
    /// The padding, in the balance's currency.
    pub units: Amount,
    /// The balance's asserted amount.
    pub asserted: Amount,
    /// What the pad group held before this padding, per currency: the real
    /// units of `target` and its sub-accounts and the group's own earlier
    /// padding (beancount's `pad_balance`). Units only; the validator adds
    /// the lots held at cost from its booked inventories for the "pad an
    /// entry with cost" message.
    pub held: Vec<Amount>,
}

/// A `pad` that inserted no padding.
#[derive(Debug, Clone)]
pub struct UnusedPad {
    /// Its index in the input.
    pub pad: usize,
    /// Its date.
    pub date: NaiveDate,
    /// Its target account.
    pub target: Account,
}

/// Compute the padding for `sorted`, beancount's rule.
///
/// `sorted` must be in booking order ([`rustledger_core::booking_sort_key`]),
/// each directive with its index in the caller's input (the indices
/// [`PadOrigin`] and [`UnusedPad`] report). `tolerance_multiplier` is the
/// ledger's `tolerance_multiplier` option, which a balance's tolerance
/// derives from ([`balance_tolerance`]).
///
/// Inventories track every account a posting names, opened or not, as
/// beancount's padding reads every posting: tracking only opened accounts
/// dropped an unopened target's own postings and padded it by the wrong
/// amount (#2896). They hold real postings only: each pad group counts its
/// own padding on top, and no other group's (the private `PadTracker`,
/// which is the rule).
pub fn plan_pads<'a, I>(sorted: I, tolerance_multiplier: Decimal) -> PadPlan
where
    I: IntoIterator<Item = (usize, &'a Directive)>,
{
    let mut inventories = PadInventories::default();
    let mut pads = PadTracker::default();
    let mut plan = PadPlan::default();

    for (index, directive) in sorted {
        match directive {
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    if let Some(units) = posting.amount() {
                        // A running balance that leaves range makes every pad
                        // measured against it wrong, so report it here rather
                        // than pad from a clamped total (#1863).
                        match inventories.add(&posting.account, &units.currency, units.number) {
                            Ok(()) => pads.post(&posting.account, &units.currency, units.number),
                            Err(e) => {
                                plan.inventory_errors.push(
                                    PadError::new(txn.date, e.to_string())
                                        .with_account(posting.account.clone()),
                                );
                            }
                        }
                    }
                }
            }

            Directive::Pad(pad) => {
                pads.add(
                    &pad.account,
                    pad.date,
                    pad.source_account.clone(),
                    index,
                    || inventories.subtree_all(&pad.account),
                );
            }

            Directive::Balance(bal) => {
                let tolerance =
                    balance_tolerance(bal.amount.number, bal.tolerance, tolerance_multiplier);
                // Every group the balance is in: its account's and its
                // ancestors'. Each measures its own account AND sub-accounts,
                // as the balance check sums them.
                for group in pads.groups_of(&bal.account) {
                    let (action, pad) = pads.balance(&group, &bal.amount, tolerance, || {
                        inventories.subtree_units(&group, &bal.amount.currency)
                    });
                    let (difference, pad) = match (action, pad) {
                        (PadAction::Pad(difference), Some((pad, held))) => (
                            difference,
                            (
                                pad.index,
                                pad.date,
                                pad.target.clone(),
                                pad.source_account.clone(),
                                held,
                            ),
                        ),
                        // A pad amount that cannot be represented must not be
                        // clamped: the synthetic transaction it produces is
                        // written into the ledger as if the user had entered
                        // it (#1863).
                        (PadAction::Unrepresentable, _) => {
                            plan.failed.push((
                                index,
                                PadError::new(
                                    bal.date,
                                    format!(
                                        "cannot compute the pad amount for {group}: the {} \
                                         balance exceeds the representable range (±7.9e28)",
                                        bal.amount.currency
                                    ),
                                ),
                            ));
                            continue;
                        }
                        _ => continue,
                    };
                    let (pad_index, pad_date, target, source, held) = pad;
                    let currency = &bal.amount.currency;
                    // The padding must also fit each account it posts to, as
                    // the ledger sums it (its real postings and all the
                    // padding into or out of it): a padding entry that
                    // overflows its source must not be written out (#1863).
                    // Both halves land, or neither: the group's own padding
                    // is taken back if the source half cannot.
                    let applied = inventories
                        .pad(&target, currency, difference)
                        .and_then(|()| {
                            inventories
                                .pad(&source, currency, -difference)
                                .inspect_err(|_| {
                                    // Restores a total that existed a moment
                                    // ago, so it cannot overflow.
                                    drop(inventories.pad(&target, currency, -difference));
                                })
                        });
                    if let Err(e) = applied {
                        pads.retract(&group, currency, difference);
                        plan.failed
                            .push((index, PadError::new(bal.date, e.to_string())));
                        continue;
                    }
                    plan.paddings.push(PlannedPadding {
                        origin: PadOrigin {
                            pad: pad_index,
                            balance: index,
                        },
                        date: pad_date,
                        target,
                        source,
                        units: Amount::new(difference, currency),
                        asserted: bal.amount.clone(),
                        held,
                    });
                }
            }

            _ => {}
        }
    }

    plan.unused = pads
        .pads
        .into_iter()
        .filter(|p| !p.used)
        .map(|p| UnusedPad {
            pad: p.index,
            date: p.date,
            target: p.target,
        })
        .collect();
    plan.unused.sort_by_key(|u| u.pad);
    plan
}

/// Process pad directives and generate synthetic transactions.
///
/// The padding is [`plan_pads`]'s, as a synthesized transaction per
/// padding entry, dated at the pad.
///
/// # Arguments
///
/// * `directives` - The directives to process. Order does not matter:
///   `process_pads` sorts a view of them by date internally before
///   applying pad math.
/// * `tolerance_multiplier` - The ledger's `tolerance_multiplier` option
///   ([`crate::DEFAULT_TOLERANCE_MULTIPLIER`] when the caller has no
///   options): a difference within a balance's tolerance is not padded
///   ([`balance_tolerance`]).
///
/// # Returns
///
/// A `PadResult` containing:
/// - The synthetic padding transactions derived from the input
/// - Any errors encountered
///
/// The input directives are NOT echoed back in the result; the caller
/// already owns them. To get the source merged with the synth
/// transactions, use [`merge_with_padding`].
///
/// `rustledger-validate` applies [`plan_pads`] output to its own booked
/// inventories in its walk, at the pad (see [`PadPlan`]).
pub fn process_pads(directives: &[Directive], tolerance_multiplier: Decimal) -> PadResult {
    let mut sorted: Vec<(usize, &Directive)> = directives.iter().enumerate().collect();
    // Sort by the canonical booking key, not by date alone. Date-only left
    // same-date directives in source order, so a `pad` written above the
    // `balance` it targets was processed first and the balance consumed it --
    // synthesizing a padding transaction beancount does not (#2150). The key
    // puts Balance before Pad, so that balance is seen first and the pad ends
    // up with nothing to satisfy.
    sorted.sort_by_key(|(_, d)| rustledger_core::booking_sort_key(d));
    let plan = plan_pads(sorted, tolerance_multiplier);

    let mut padding_transactions = Vec::with_capacity(plan.paddings.len());
    let mut padding_origins = Vec::with_capacity(plan.paddings.len());
    for p in &plan.paddings {
        padding_transactions.push(create_padding_transaction(
            p.date,
            &p.target,
            &p.source,
            p.units.clone(),
            &p.asserted, // target balance for narration
        ));
        padding_origins.push(p.origin);
    }

    let mut errors = plan.inventory_errors;
    errors.extend(plan.failed.into_iter().map(|(_, e)| e));
    // Unused pads (beancount's `Unused Pad entry`).
    errors.extend(plan.unused.into_iter().map(|u| {
        PadError::new(
            u.date,
            format!(
                "Pad directive for account {} has no corresponding balance assertion",
                u.target
            ),
        )
        .with_account(u.target)
    }));

    PadResult {
        padding_transactions,
        padding_origins,
        errors,
    }
}

/// The running totals [`plan_pads`] measures pads against: for every account
/// a posting names, its units per currency from real postings (no padding:
/// each pad group adds its own, `PadTracker`), with the lexical prefix index
/// a subtree sum needs.
///
/// Units only, not an [`rustledger_core::Inventory`]: a pad reads nothing but
/// the units of one currency. Beancount's "Attempt to pad an entry with
/// cost" check (`ops/pad.py`, any remaining lot at cost in the padded
/// currency) needs lots, so the validator makes it from its booked
/// inventories, at each balance a [`PlannedPadding`] was planned for.
#[derive(Debug, Default)]
struct PadInventories {
    by_account: AccountTotals,
    /// The keys of `by_account`, sorted, kept in lockstep (keys are never
    /// removed), for [`rustledger_core::for_each_strict_subaccount`].
    index: std::collections::BTreeSet<Account>,
    /// The padding into or out of each account, every pad group's, kept
    /// apart from `by_account`: a group measures real postings and its own
    /// padding only, while the ledger holds them all, which is what an entry
    /// must fit ([`Self::pad`]).
    padded: FxHashMap<Account, Totals>,
}

/// One account's units per currency.
type Totals = smallvec::SmallVec<[(Currency, Decimal); 2]>;

/// The totals of each account. A newtype so that every read goes through
/// [`Self::get`] or iteration (`for (account, totals) in &by_account`), both
/// of which a test counts: whatever walk a subtree sum does, each account it
/// reads is counted where it is read
/// (`test_plan_pads_sums_each_balance_over_its_subtree_only`).
#[derive(Debug, Default)]
struct AccountTotals(FxHashMap<Account, Totals>);

impl AccountTotals {
    /// The totals of `account`, counted as one account read.
    fn get(&self, account: &Account) -> Option<&Totals> {
        #[cfg(test)]
        tests::ACCOUNTS_READ.with(|n| n.set(n.get() + 1));
        self.0.get(account)
    }
}

/// Iterating reads every account, each counted. Nothing here iterates: this
/// is what a scan would go through, so the test sees one.
impl<'a> IntoIterator for &'a AccountTotals {
    type Item = (&'a Account, &'a Totals);
    type IntoIter = Box<dyn Iterator<Item = Self::Item> + 'a>;

    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.0.iter().inspect(|_| {
            #[cfg(test)]
            tests::ACCOUNTS_READ.with(|n| n.set(n.get() + 1));
        }))
    }
}

impl PadInventories {
    /// Add `number` `currency` to `account`, created on first use. A total
    /// that would leave the representable range is left as it was and
    /// reported (#1863).
    ///
    /// This is a plain `checked_add` on the running total. It does not apply
    /// `Inventory::add`'s near-ceiling check (#2554), so a total the
    /// validator's booked inventory refuses can still be accepted here.
    fn add(
        &mut self,
        account: &Account,
        currency: &Currency,
        number: Decimal,
    ) -> Result<(), rustledger_core::OverflowError> {
        // One lookup; the key clone is a reference-count bump (`Account` is
        // interned).
        let totals = match self.by_account.0.entry(account.clone()) {
            std::collections::hash_map::Entry::Occupied(totals) => totals.into_mut(),
            std::collections::hash_map::Entry::Vacant(slot) => {
                self.index.insert(account.clone());
                slot.insert(Totals::new())
            }
        };
        add_units(totals, currency, number)
    }

    /// Record `number` `currency` of padding into `account` (out of it when
    /// negative), if the account's total in the ledger, its real postings
    /// and all its padding, stays representable; otherwise nothing changes
    /// and the overflow is reported (#1863).
    ///
    /// One account, not a subtree: its real total is read directly, not
    /// counted as a subtree read.
    fn pad(
        &mut self,
        account: &Account,
        currency: &Currency,
        number: Decimal,
    ) -> Result<(), rustledger_core::OverflowError> {
        let real = self
            .by_account
            .0
            .get(account)
            .map_or(Decimal::ZERO, |totals| units_of(totals, currency));
        let padded = self.padded.entry(account.clone()).or_default();
        let fits = real
            .checked_add(units_of(padded, currency))
            .and_then(|total| total.checked_add(number))
            .is_some();
        if !fits {
            return Err(rustledger_core::OverflowError {
                currency: currency.clone(),
            });
        }
        add_units(padded, currency, number)
    }

    /// The units of every currency in `account` and its sub-accounts, and the
    /// currencies whose sum leaves the representable range (#1863): the seed
    /// of a pad group's running total, read once per group.
    fn subtree_all(&self, account: &Account) -> (Totals, FxHashSet<Currency>) {
        let mut sum = Totals::new();
        let mut overflowed = FxHashSet::default();
        let mut add = |totals: &Totals| {
            for (currency, units) in totals {
                if !overflowed.contains(currency) && add_units(&mut sum, currency, *units).is_err()
                {
                    overflowed.insert(currency.clone());
                }
            }
        };
        if let Some(totals) = self.by_account.get(account) {
            add(totals);
        }
        rustledger_core::for_each_strict_subaccount(&self.index, account.as_str(), |sub| {
            if let Some(totals) = self.by_account.get(sub) {
                add(totals);
            }
        });
        (sum, overflowed)
    }

    /// The units of `currency` in `account` and its sub-accounts, as a
    /// `balance` assertion sums them (beancount includes sub-accounts), or
    /// `None` when the sum leaves the representable range (#1863).
    ///
    /// O(log A + subtree) through the prefix index. Summing over a scan of
    /// every account ([`rustledger_core::sum_account_and_subaccounts`]) made
    /// `rledger check`, BQL and the reports quadratic in a ledger with many
    /// padded balances.
    fn subtree_units(&self, account: &Account, currency: &Currency) -> Option<Decimal> {
        let mut total = Some(Decimal::ZERO);
        let mut add = |totals: &Totals| {
            if let Some((_, units)) = totals.iter().find(|(c, _)| c == currency) {
                total = total.and_then(|t| t.checked_add(*units));
            }
        };
        if let Some(totals) = self.by_account.get(account) {
            add(totals);
        }
        rustledger_core::for_each_strict_subaccount(&self.index, account.as_str(), |sub| {
            if let Some(totals) = self.by_account.get(sub) {
                add(totals);
            }
        });
        total
    }
}

/// Create a synthetic padding transaction.
///
/// The narration format matches Python beancount:
/// `(Padding inserted for Balance of {balance} for difference {difference})`
fn create_padding_transaction(
    date: NaiveDate,
    target_account: &str,
    source_account: &str,
    difference: Amount,
    balance: &Amount,
) -> Transaction {
    let narration = format!(
        "{prefix}{bal_num} {bal_cur} for difference {diff_num} {diff_cur})",
        prefix = SYNTH_PAD_NARRATION_PREFIX,
        bal_num = balance.number,
        bal_cur = balance.currency,
        diff_num = difference.number,
        diff_cur = difference.currency,
    );
    Transaction::new(date, &narration)
        .with_flag('P')
        .with_synthesized_posting(Posting::new(target_account, difference.clone()))
        .with_synthesized_posting(Posting::new(source_account, difference.neg()))
}

/// Merge original directives with padding transactions, maintaining date order.
///
/// Keeps the original pad directives and adds the synthesized
/// transactions alongside them. Use this when downstream
/// consumers want both views: `Pad` directives for source-faithful queries
/// (e.g., BQL `WHERE type = 'pad'`) and the synth transactions for inventory
/// math. `tolerance_multiplier` is [`process_pads`]'.
///
/// # Sort ordering on date ties
///
/// Synth transactions carry the pad's date, not the balance's date. When a
/// pad precedes its balance by at least a day, the synth must appear BEFORE
/// that balance so any consumer checking assertions mid-stream sees the
/// padded inventory. This is achieved by prepending the synth list to the
/// original directives before the stable sort: synths land at the front of
/// their date-group, originals follow.
///
/// A pad and the balance it targets on the SAME date produce no synth at
/// all. beancount checks a balance at the start of the day, so it is ordered
/// ahead of a same-date pad and consumes nothing; the pad is reported unused.
/// This doc previously called that pairing "legal in beancount" and required
/// the synth to precede the balance -- which is what produced a padding
/// transaction beancount does not, leaving the account richer by the
/// difference while our own validator called the pad unused (#2150).
///
/// # Errors are discarded
///
/// [`process_pads`] can emit `PadError`s (e.g., unused-pad warnings).
/// `merge_with_padding` discards them by design: those diagnostics are the
/// validator's responsibility (`E2003`). If you need them, call
/// [`process_pads`] directly and inspect `result.errors`.
///
/// # Not idempotent
///
/// Re-running `merge_with_padding` on its own output double-counts pad
/// effects because the original `Pad` directives survive and `process_pads`
/// re-applies them against an inventory that already includes the prior
/// synth. A `debug_assert!` guards against this in dev builds.
pub fn merge_with_padding(
    directives: &[Directive],
    tolerance_multiplier: Decimal,
) -> Vec<Directive> {
    merge_with_padding_owned(directives.to_vec(), tolerance_multiplier)
}

/// [`merge_with_padding`] for a caller that already owns its directives.
///
/// Exists so consumers holding an owned `Vec` need not clone it a second time
/// just to reach the canonical placement rule. `Ledger::balance_view` used to
/// inline the merge for exactly that reason, and the copy drifted the moment
/// the rule changed — this is the same saving without the duplicate.
#[must_use]
pub fn merge_with_padding_owned(
    directives: Vec<Directive>,
    tolerance_multiplier: Decimal,
) -> Vec<Directive> {
    // Idempotence: input that already contains synth pad transactions has
    // been merged before (e.g. an embedder queries entries it loaded via
    // load-full, which merges pads — rustledger#1712). Re-running would
    // double-count pad effects, so return the input unchanged instead.
    if directives
        .iter()
        .any(|d| matches!(d, Directive::Transaction(t) if is_synthesized_pad(t)))
    {
        return directives;
    }

    let result = process_pads(&directives, tolerance_multiplier);

    let mut merged: Vec<Directive> = directives;
    merged.sort_by_key(rustledger_core::Directive::date);

    for txn in result.padding_transactions {
        let insert_at = pad_insertion_index(merged.iter(), txn.date);
        merged.insert(insert_at, Directive::Transaction(txn));
    }

    merged
}

/// Where a synthesized padding transaction dated `date` belongs in an
/// already date-sorted directive stream.
///
/// The rule: at the END of its date group.
///
/// That is what stops the synth displacing UNRELATED same-date directives.
/// Prepending it to the whole date group did that: on
/// `ledger2beancount/tests_balance-assertion.beancount` a 2019-01-29 pad for
/// `Assets:Test6` jumped ahead of an unrelated 2019-01-29 transaction for
/// `Assets:Test5`, and every running balance from that row on was 500.00 USD
/// out relative to bean-query.
///
/// # No same-date-Balance special case
///
/// This used to return the index of the first same-date `Balance`, to put a
/// synth ahead of a balance sharing the pad's date. Such a pad no longer
/// synthesizes at all -- the balance is checked first, so the pad is unused
/// (#2150) -- which left the arm firing only for an UNRELATED same-date
/// balance, where it put the synth ahead of the whole date group and
/// contradicted the Balance-before-Pad order the same change established
/// (#2188).
///
/// A pad serving a LATER balance still precedes it, by date alone; no special
/// case is needed for that, which
/// `test_merge_with_padding_earlier_pad_still_synthesizes_before_balance`
/// pins.
///
/// # Where this still differs from bean-query
///
/// Verified against beancount 3.2.3. With a pad, an unrelated same-date
/// balance, and the target balance later, both tools now order the date group
/// `balance, pad, transaction`.
///
/// They part company when the pad's date also carries a `note`, `price` or
/// `close`. beancount sorts by `(date, type_priority, lineno)` with
/// Transaction, Pad, Note and Price sharing priority 0, so the synth lands
/// next to its `pad` by line number:
///
/// ```text
/// bean-query   balance pad transaction note price close
/// rustledger   balance pad note price close transaction
/// ```
///
/// This is the general type-grouping difference of #2149, not a pad-specific
/// rule, and it is cosmetic: notes, prices and closes carry no postings, so
/// no balance moves. Placing the synth next to its pad instead would fix the
/// cosmetic case and break the load-bearing one -- our type sort puts Pad
/// before Transaction, so the synth would jump ahead of an unrelated same-date
/// transaction and shift every running balance after it, which is exactly the
/// regression described above.
///
/// This is the single source of truth for pad placement. It is `pub` because
/// the rule has three consumers with three different element types —
/// [`merge_with_padding_owned`] over `Directive`,
/// [`merge_with_padding_spanned`] over [`Spanned<Directive>`], and
/// `rustledger-ffi-wasi`'s `expand_pads` over `(Directive, tag)` pairs, which
/// carries parallel provenance tags and so cannot call either merge. All three
/// once open-coded the rule; two of the copies were still prepending when this
/// one changed. Compute the index here rather than re-deriving it.
///
/// Cost: one insert per synth into an already-sorted vector, so O(n x k) for
/// k pads rather than a single O(n log n) pass. `pad` is used sparingly by
/// construction — one per account per period — and callers early-return on a
/// ledger with none; the heaviest file in the compat corpus carries 12. If a
/// ledger ever arrives with pads in the thousands, merge the (date-sorted)
/// synths in one pass instead.
#[must_use]
pub fn pad_insertion_index<'a, I>(sorted: I, date: NaiveDate) -> usize
where
    I: IntoIterator<Item = &'a Directive>,
{
    let mut end_of_group = 0;
    for (index, directive) in sorted.into_iter().enumerate() {
        if directive.date() <= date {
            end_of_group = index + 1;
        }
    }
    end_of_group
}

/// Span-preserving variant of [`merge_with_padding`].
///
/// Identical merge behavior (and the same `tolerance_multiplier`), but the
/// input/output keep each directive's
/// [`Spanned`] wrapper so downstream consumers (e.g. BQL's `filename`/`lineno`
/// columns) can resolve real source locations. A pad-synthesized transaction
/// is located where beancount locates it (#2825): the transaction at its
/// `pad` directive (beancount copies the pad's metadata onto the entry, so
/// `#entries` reports the pad's line) and each of its postings at the
/// `balance` assertion it satisfies (bean-query's postings table reports
/// that line). Both come from [`PadResult::padding_origins`].
///
/// # Not idempotent
///
/// Same caveat as [`merge_with_padding`]: re-running on its own output
/// double-counts pad effects.
#[must_use]
pub fn merge_with_padding_spanned(
    directives: &[Spanned<Directive>],
    tolerance_multiplier: Decimal,
) -> Vec<Spanned<Directive>> {
    let plain: Vec<Directive> = directives.iter().map(|s| s.value.clone()).collect();
    debug_assert!(
        !plain
            .iter()
            .any(|d| matches!(d, Directive::Transaction(t) if is_synthesized_pad(t))),
        "merge_with_padding_spanned called on input that already contains synth pad transactions; \
         re-running would double-count pad effects",
    );

    let result = process_pads(&plain, tolerance_multiplier);

    // Placement via the shared [`pad_insertion_index`]; located at the pad and
    // the balance it came from, as beancount locates them.
    let mut merged: Vec<Spanned<Directive>> = directives.to_vec();
    merged.sort_by_key(|s| s.value.date());

    for (mut txn, origin) in result
        .padding_transactions
        .into_iter()
        .zip(result.padding_origins)
    {
        let pad = &directives[origin.pad];
        let balance = &directives[origin.balance];
        for posting in &mut txn.postings {
            posting.span = balance.span;
            posting.file_id = balance.file_id;
        }
        let insert_at = pad_insertion_index(merged.iter().map(|s| &s.value), txn.date);
        merged.insert(
            insert_at,
            Spanned {
                value: Directive::Transaction(txn),
                span: pad.span,
                file_id: pad.file_id,
            },
        );
    }

    merged
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DEFAULT_TOLERANCE_MULTIPLIER;
    use rust_decimal_macros::dec;
    use rustledger_core::{Balance, Open, Pad};

    std::thread_local! {
        /// Accounts `PadInventories` has read (`AccountTotals`) on this
        /// thread, for `test_plan_pads_sums_each_balance_over_its_subtree_only`.
        pub(super) static ACCOUNTS_READ: std::cell::Cell<usize> =
            const { std::cell::Cell::new(0) };
    }

    /// Each padded balance is measured over its own subtree, not over every
    /// account: with `n` accounts each holding a transaction, a pad and a
    /// balance, the pad computation reads `n` accounts, where a scan per
    /// balance reads `n * n` and made `rledger check` quadratic (40k such
    /// accounts took 46 s). Accounts are counted where they are read
    /// (`AccountTotals`), not where they match, so a scan that adds only the
    /// matching accounts fails too: verified with `subtree_units` rewritten
    /// as `for (a, totals) in &self.by_account { if is_subaccount_or_equal(..)
    /// { add(totals) } }`.
    #[test]
    fn test_plan_pads_sums_each_balance_over_its_subtree_only() {
        let n = 2_000;
        let mut directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:B")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:O")),
        ];
        for i in 0..n {
            let account = format!("Assets:A{i:05}");
            directives.push(Directive::Open(Open::new(date(2024, 1, 1), &account)));
            directives.push(transfer(date(2024, 1, 2), &account, dec!(1)));
            directives.push(Directive::Pad(Pad::new(
                date(2024, 1, 3),
                &account,
                "Equity:O",
            )));
            directives.push(balance(date(2024, 1, 5), &account, dec!(10)));
        }
        ACCOUNTS_READ.with(|c| c.set(0));
        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);
        let summed = ACCOUNTS_READ.with(std::cell::Cell::get);
        assert_eq!(result.padding_transactions.len(), n);
        assert!(result.errors.is_empty(), "{:?}", result.errors);
        assert_eq!(summed, n, "each balance reads only its own account");
    }

    /// A pad on a parent with balances on its sub-accounts reads the subtree
    /// once, when the group's first `pad` comes, not at every balance: each
    /// group keeps a running total, as beancount keeps `pad_balance`. With
    /// `n` sub-accounts, a daily `pad` on the parent and a balance on the
    /// next sub-account the day after, summing the subtree per balance reads
    /// `n * (n + 1)` accounts (#2901 review: 10k sub-accounts took 3 s of
    /// CPU where main took 0.36 s).
    #[test]
    fn test_plan_pads_parent_pad_reads_its_subtree_once() {
        let n: u32 = 400;
        let mut directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:B")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:O")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:P")),
        ];
        for i in 0..n {
            let account = format!("Assets:P:C{i:05}");
            directives.push(Directive::Open(Open::new(date(2024, 1, 1), &account)));
            directives.push(transfer(date(2024, 1, 1), &account, dec!(1.00)));
        }
        let mut day = date(2024, 1, 1);
        for i in 0..n {
            let account = format!("Assets:P:C{i:05}");
            day = day.tomorrow().expect("in range");
            directives.push(Directive::Pad(Pad::new(day, "Assets:P", "Equity:O")));
            day = day.tomorrow().expect("in range");
            // A different amount each time, so every balance pads.
            directives.push(balance(day, &account, Decimal::from(i + 2)));
        }
        ACCOUNTS_READ.with(|c| c.set(0));
        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);
        let read = ACCOUNTS_READ.with(std::cell::Cell::get);
        assert_eq!(result.padding_transactions.len(), n as usize);
        assert_eq!(
            read,
            n as usize + 1,
            "the parent's subtree is read once, when its first pad comes"
        );
    }

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        rustledger_core::naive_date(year, month, day).unwrap()
    }

    #[test]
    fn test_process_pads_basic() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        assert!(result.errors.is_empty());
        assert_eq!(result.padding_transactions.len(), 1);

        let txn = &result.padding_transactions[0];
        assert_eq!(txn.date, date(2024, 1, 1));
        assert_eq!(txn.postings.len(), 2);

        // Check target posting
        assert_eq!(txn.postings[0].account, "Assets:Bank");
        assert_eq!(
            txn.postings[0].amount(),
            Some(&Amount::new(dec!(1000.00), "USD"))
        );

        // Check source posting
        assert_eq!(txn.postings[1].account, "Equity:Opening");
        assert_eq!(
            txn.postings[1].amount(),
            Some(&Amount::new(dec!(-1000.00), "USD"))
        );
    }

    #[test]
    fn test_process_pads_with_existing_balance() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 5), "Deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(500.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-500.00), "USD"),
                    )),
            ),
            Directive::Pad(Pad::new(date(2024, 1, 10), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 15),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        assert!(result.errors.is_empty());
        assert_eq!(result.padding_transactions.len(), 1);

        let txn = &result.padding_transactions[0];
        // Should pad 500.00 (1000 target - 500 existing)
        assert_eq!(
            txn.postings[0].amount(),
            Some(&Amount::new(dec!(500.00), "USD"))
        );
    }

    #[test]
    fn test_process_pads_sums_subaccounts_for_nonleaf_target() {
        // A pad targeting a NON-LEAF account must measure the current balance the
        // same way the balance assertion does — summing the account AND its
        // sub-accounts (beancount semantic, verified against bean-check). Here the
        // balance lives entirely in the sub-account `Assets:Bank:Checking`, so the
        // pad to `Assets:Bank` must be 100 - 50 = 50, NOT 100 (the old leaf-only
        // bug, which then tripped the sub-account-summing Late validator).
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank:Checking")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 5), "Deposit into sub-account")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank:Checking",
                        Amount::new(dec!(50.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-50.00), "USD"),
                    )),
            ),
            Directive::Pad(Pad::new(date(2024, 1, 10), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 15),
                "Assets:Bank",
                Amount::new(dec!(100.00), "USD"),
            )),
        ];

        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        assert!(result.errors.is_empty());
        assert_eq!(result.padding_transactions.len(), 1);
        // 100 target - 50 already held in the sub-account = 50.
        assert_eq!(
            result.padding_transactions[0].postings[0].amount(),
            Some(&Amount::new(dec!(50.00), "USD")),
            "pad on a non-leaf account must sum sub-accounts (was leaf-only)"
        );
    }

    #[test]
    fn test_process_pads_negative_adjustment() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 5), "Big deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(2000.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-2000.00), "USD"),
                    )),
            ),
            Directive::Pad(Pad::new(date(2024, 1, 10), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 15),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        assert!(result.errors.is_empty());
        assert_eq!(result.padding_transactions.len(), 1);

        let txn = &result.padding_transactions[0];
        // Should pad -1000.00 (1000 target - 2000 existing)
        assert_eq!(
            txn.postings[0].amount(),
            Some(&Amount::new(dec!(-1000.00), "USD"))
        );
    }

    #[test]
    fn test_process_pads_no_difference() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Open(Open::new(date(2024, 1, 1), "Income:Salary")),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 5), "Exact deposit")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(1000.00), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Income:Salary",
                        Amount::new(dec!(-1000.00), "USD"),
                    )),
            ),
            Directive::Pad(Pad::new(date(2024, 1, 10), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 15),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        // No padding transaction needed when balance already matches, so the
        // pad is unused, as bean-check reports it (`Unused Pad entry`).
        assert!(result.padding_transactions.is_empty());
        assert_eq!(result.errors.len(), 1, "{:?}", result.errors);
        assert!(
            result.errors[0]
                .message
                .contains("no corresponding balance")
        );
    }

    #[test]
    fn test_process_pads_unused_pad() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            // Pad without balance assertion
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
        ];

        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        assert_eq!(result.errors.len(), 1);
        assert!(
            result.errors[0]
                .message
                .contains("no corresponding balance")
        );
    }

    /// A transaction moving `number` USD from `Assets:B` into `account`.
    fn transfer(on: NaiveDate, account: &str, number: Decimal) -> Directive {
        Directive::Transaction(
            Transaction::new(on, "t")
                .with_synthesized_posting(Posting::new(account, Amount::new(number, "USD")))
                .with_synthesized_posting(Posting::new("Assets:B", Amount::new(-number, "USD"))),
        )
    }

    fn balance(on: NaiveDate, account: &str, number: Decimal) -> Directive {
        Directive::Balance(Balance::new(on, account, Amount::new(number, "USD")))
    }

    /// The padding amounts `process_pads` synthesizes into `Assets:A`, and its
    /// unused-pad count.
    fn padding_and_unused(directives: &[Directive]) -> (Vec<Decimal>, usize) {
        let result = process_pads(directives, DEFAULT_TOLERANCE_MULTIPLIER);
        let amounts = result
            .padding_transactions
            .iter()
            .map(|t| {
                let p = &t.postings[0];
                assert_eq!(p.account.as_str(), "Assets:A");
                p.amount().expect("padding has units").number
            })
            .collect();
        let unused = result
            .errors
            .iter()
            .filter(|e| e.message.contains("no corresponding balance"))
            .count();
        assert_eq!(unused, result.errors.len(), "{:?}", result.errors);
        (amounts, unused)
    }

    /// An unopened target's own postings count, as beancount's padding reads
    /// every posting: bean-query 3.2.3 shows target 100, source -130 (#2896).
    /// Opened later or never, the same.
    #[test]
    fn test_process_pads_counts_an_unopened_targets_postings() {
        for open in [None, Some(date(2024, 2, 1))] {
            let mut directives = vec![
                Directive::Open(Open::new(date(2024, 1, 1), "Equity:O")),
                Directive::Open(Open::new(date(2024, 1, 1), "Assets:B")),
                Directive::Pad(Pad::new(date(2024, 1, 2), "Assets:A", "Equity:O")),
                transfer(date(2024, 1, 3), "Assets:A", dec!(-30)),
                balance(date(2024, 1, 5), "Assets:A", dec!(100)),
            ];
            directives.extend(open.map(|d| Directive::Open(Open::new(d, "Assets:A"))));
            assert_eq!(
                padding_and_unused(&directives),
                (vec![dec!(130)], 0),
                "{open:?}"
            );
        }
    }

    /// An unopened target whose postings already reach the balance is not
    /// padded, and the pad is unused, as bean-check 3.2.3 reports (#2896).
    #[test]
    fn test_process_pads_does_not_pad_a_satisfied_unopened_target() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:O")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:B")),
            Directive::Pad(Pad::new(date(2024, 1, 2), "Assets:A", "Equity:O")),
            transfer(date(2024, 1, 3), "Assets:A", dec!(100)),
            balance(date(2024, 1, 5), "Assets:A", dec!(100)),
        ];
        assert_eq!(padding_and_unused(&directives), (vec![], 1));
    }

    /// A balance with a zero difference uses up the pad's currency: the next
    /// balance in it is not padded, and the pad is unused (bean-check 3.2.3:
    /// `Unused Pad entry`, then `Balance failed` on the second balance).
    #[test]
    fn test_process_pads_zero_difference_uses_up_the_currency() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:O")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:A")),
            Directive::Pad(Pad::new(date(2024, 1, 2), "Assets:A", "Equity:O")),
            balance(date(2024, 1, 3), "Assets:A", dec!(0)),
            balance(date(2024, 1, 5), "Assets:A", dec!(10)),
        ];
        assert_eq!(padding_and_unused(&directives), (vec![], 1));
    }

    /// A pad superseded by a later one is never used, and is unused; the
    /// later one pads once (bean-check 3.2.3: `Unused Pad entry` on the first
    /// pad, `Balance failed` on the second balance).
    #[test]
    fn test_process_pads_superseded_pad_is_unused() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:O")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:A")),
            Directive::Pad(Pad::new(date(2024, 1, 9), "Assets:A", "Equity:O")),
            Directive::Pad(Pad::new(date(2024, 1, 10), "Assets:A", "Equity:O")),
            balance(date(2024, 1, 11), "Assets:A", dec!(100)),
            balance(date(2024, 1, 12), "Assets:A", dec!(200)),
        ];
        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);
        assert_eq!(result.padding_origins.len(), 1);
        assert_eq!(result.padding_origins[0].pad, 3, "the later pad pads");
        assert_eq!(padding_and_unused(&directives), (vec![dec!(100)], 1));
    }

    #[test]
    fn test_merge_with_padding() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let merged = merge_with_padding(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        // Should have: 2 opens + 1 pad + 1 balance + 1 synthetic = 5
        assert_eq!(merged.len(), 5);

        // Pad should still be there
        let has_pad = merged.iter().any(|d| matches!(d, Directive::Pad(_)));
        assert!(has_pad, "Pad should be preserved");

        // Should also have the synthetic transaction
        let txn_count = merged
            .iter()
            .filter(|d| matches!(d, Directive::Transaction(_)))
            .count();
        assert_eq!(txn_count, 1);
    }

    #[test]
    fn test_is_synthesized_pad_recognizes_synth() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000), "USD"),
            )),
        ];
        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);
        let synth = result.padding_transactions.into_iter().next().unwrap();
        assert!(
            is_synthesized_pad(&synth),
            "synth pad transaction must be detected by is_synthesized_pad",
        );
    }

    #[test]
    fn test_is_synthesized_pad_rejects_user_p_flag() {
        // A user-written `P`-flag transaction with arbitrary narration
        // must NOT be classified as a synth pad. `P` is a valid user
        // flag in beancount; bare flag-checking would conflate them.
        let user_p = Transaction::new(date(2024, 1, 1), "user-authored P-flag txn")
            .with_flag('P')
            .with_synthesized_posting(Posting::new("Assets:Bank", Amount::new(dec!(100), "USD")));
        assert!(
            !is_synthesized_pad(&user_p),
            "user-written P-flag transaction must not be classified as synth",
        );
    }

    #[test]
    fn test_merge_with_padding_synth_does_not_displace_unrelated_same_date_entry() {
        // A pad whose balance lands on a LATER date must not jump ahead of an
        // unrelated transaction sharing the pad's date. Prepending synths to
        // the whole date group did exactly that, and every running balance
        // from that row on was off by the padding amount.
        //
        // The synth belongs at the END of its date group, which is where
        // bean-query puts it relative to same-date transactions.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Other")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            // Unrelated transaction, same date as the pad below.
            Directive::Transaction(
                Transaction::new(date(2024, 1, 2), "unrelated")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Other",
                        Amount::new(dec!(10), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Equity:Opening",
                        Amount::new(dec!(-10), "USD"),
                    )),
            ),
            Directive::Pad(Pad::new(date(2024, 1, 2), "Assets:Bank", "Equity:Opening")),
            // Balance is on a LATER date, so there is no same-date Balance.
            Directive::Balance(Balance::new(
                date(2024, 1, 3),
                "Assets:Bank",
                Amount::new(dec!(1000), "USD"),
            )),
        ];

        let merged = merge_with_padding(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        let synth_idx = merged
            .iter()
            .position(|d| matches!(d, Directive::Transaction(t) if is_synthesized_pad(t)))
            .expect("synth present");
        let unrelated_idx = merged
            .iter()
            .position(
                |d| matches!(d, Directive::Transaction(t) if t.narration.as_ref() == "unrelated"),
            )
            .expect("unrelated txn present");
        assert!(
            unrelated_idx < synth_idx,
            "unrelated same-date txn (idx {unrelated_idx}) must precede the synth (idx {synth_idx})",
        );
    }

    #[test]
    fn test_merge_with_padding_synth_follows_an_unrelated_same_date_balance() {
        // The case #2188 was filed for. `pad_insertion_index` used to return
        // the index of the first same-date `Balance`, which put the synth at
        // the FRONT of the date group whenever any unrelated balance shared
        // the pad's date -- ahead of the balance, the pad, and everything
        // else.
        //
        // Verified against beancount 3.2.3 on this exact shape: bean-query
        // reports the 2024-06-10 group as `balance pad transaction`. Before
        // the fix we reported `transaction balance pad`.
        //
        // The balance is on an account the pad does not touch, so it neither
        // consumes the pad nor is affected by it; only the ordering moved.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:A")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:B")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 6, 10), "Assets:A", "Equity:Opening")),
            // UNRELATED account, sharing the pad's date.
            Directive::Balance(Balance::new(
                date(2024, 6, 10),
                "Assets:B",
                Amount::new(dec!(0), "USD"),
            )),
            // The pad's own target, on a later date.
            Directive::Balance(Balance::new(
                date(2024, 6, 15),
                "Assets:A",
                Amount::new(dec!(100), "USD"),
            )),
        ];

        // Sorted the way the loader sorts before merging: `merge_with_padding`
        // only stable-sorts by DATE, so feeding it parse order would leave the
        // group as `pad, balance` and test a stream the pipeline never
        // produces. The type priority (Balance 2 before Pad 3) comes from
        // here.
        let mut directives = directives;
        rustledger_core::sort_directives(&mut directives);
        let merged = merge_with_padding(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        let group: Vec<&Directive> = merged
            .iter()
            .filter(|d| d.date() == date(2024, 6, 10))
            .collect();
        let shape: Vec<&str> = group
            .iter()
            .map(|d| match d {
                Directive::Balance(_) => "balance",
                Directive::Pad(_) => "pad",
                Directive::Transaction(_) => "transaction",
                _ => "other",
            })
            .collect();
        assert_eq!(
            shape,
            vec!["balance", "pad", "transaction"],
            "the synth belongs at the END of its date group, after an \
             unrelated same-date balance (bean-query agrees)",
        );
    }

    #[test]
    fn test_merge_with_padding_spanned_places_the_synth_like_the_plain_merge() {
        // The THIRD consumer of `pad_insertion_index`, and the one with no
        // test of its own until #2188. The rule's own docs record that two of
        // its three copies were still prepending the last time it changed, so
        // each consumer is pinned separately rather than trusting that they
        // share a function today.
        //
        // Asserted against the plain merge rather than a hardcoded shape: the
        // point is that the two agree, so a future change to one is caught
        // even if it moves both tests' expected order.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:A")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:B")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 6, 10), "Assets:A", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 6, 10),
                "Assets:B",
                Amount::new(dec!(0), "USD"),
            )),
            Directive::Balance(Balance::new(
                date(2024, 6, 15),
                "Assets:A",
                Amount::new(dec!(100), "USD"),
            )),
        ];
        let mut directives = directives;
        rustledger_core::sort_directives(&mut directives);

        let spanned: Vec<Spanned<Directive>> = directives
            .iter()
            .cloned()
            .map(|d| Spanned::new(d, rustledger_core::Span::new(0, 1)))
            .collect();

        let plain = merge_with_padding(&directives, DEFAULT_TOLERANCE_MULTIPLIER);
        let merged = merge_with_padding_spanned(&spanned, DEFAULT_TOLERANCE_MULTIPLIER);

        let shape = |ds: &[Directive]| -> Vec<&'static str> {
            ds.iter()
                .filter(|d| d.date() == date(2024, 6, 10))
                .map(|d| match d {
                    Directive::Balance(_) => "balance",
                    Directive::Pad(_) => "pad",
                    Directive::Transaction(_) => "transaction",
                    _ => "other",
                })
                .collect()
        };
        let spanned_plain: Vec<Directive> = merged.iter().map(|s| s.value.clone()).collect();
        assert_eq!(
            shape(&spanned_plain),
            shape(&plain),
            "the spanned merge must place a synth exactly where the plain one does",
        );
        assert_eq!(
            shape(&spanned_plain),
            vec!["balance", "pad", "transaction"],
            "and that placement is the end of the date group",
        );
    }

    #[test]
    fn test_merge_with_padding_same_date_pad_balance_synthesizes_nothing() {
        // A pad and the balance it targets on the SAME date produce NO synth.
        // beancount checks a balance at the start of the day, so it is ordered
        // ahead of a same-date pad and consumes nothing; the pad is reported
        // "Unused Pad entry" and the account keeps its real figure (#2150).
        //
        // This test previously asserted the opposite -- that a synth exists and
        // precedes the Balance -- which is what let the bug through. On the
        // fixture below beancount reports 40.00 for the account where we
        // reported 100.00, and our own validator called the pad unused in the
        // same run that booked it.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 2), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000), "USD"),
            )),
        ];

        let merged = merge_with_padding(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        assert!(
            !merged
                .iter()
                .any(|d| matches!(d, Directive::Transaction(t) if is_synthesized_pad(t))),
            "a same-date pad+balance must synthesize nothing; beancount leaves \
             the pad unused"
        );
        // The Pad itself survives, so `WHERE type = 'pad'` audits still see it.
        assert!(merged.iter().any(|d| matches!(d, Directive::Pad(_))));
    }

    #[test]
    fn test_pad_after_a_same_date_balance_still_serves_a_later_balance() {
        // A pad written after a balance on the same date is NOT consumed by
        // that balance -- it stays pending and satisfies the next one. Found
        // while reviewing #2150, and it was broken worse than the reported
        // case: the account came back with no balance at all and `check`
        // reported nothing, on a ledger bean-check accepts silently.
        //
        // Under the old Pad-before-Balance order the same-date balance ate the
        // pad, leaving the later assertion with nothing.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:A")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:O")),
            Directive::Balance(Balance::new(
                date(2024, 6, 15),
                "Assets:A",
                Amount::new(dec!(0), "USD"),
            )),
            Directive::Pad(Pad::new(date(2024, 6, 15), "Assets:A", "Equity:O")),
            Directive::Balance(Balance::new(
                date(2024, 7, 1),
                "Assets:A",
                Amount::new(dec!(50), "USD"),
            )),
        ];

        let merged = merge_with_padding(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        let synths = merged
            .iter()
            .filter(|d| matches!(d, Directive::Transaction(t) if is_synthesized_pad(t)))
            .count();
        assert_eq!(
            synths, 1,
            "the pad must satisfy the LATER balance, producing exactly one synth"
        );
    }

    #[test]
    fn test_merge_with_padding_earlier_pad_still_synthesizes_before_balance() {
        // The day-earlier case is the one that DOES pad, and the synth still
        // has to precede the balance so a mid-stream assertion check sees the
        // padded inventory. That ordering guarantee is what the old same-date
        // test was really protecting; it belongs here, where a synth exists.
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 2), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 3),
                "Assets:Bank",
                Amount::new(dec!(1000), "USD"),
            )),
        ];

        let merged = merge_with_padding(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        let synth_idx = merged
            .iter()
            .position(|d| matches!(d, Directive::Transaction(t) if is_synthesized_pad(t)))
            .expect("an earlier pad must still synthesize");
        let balance_idx = merged
            .iter()
            .position(|d| matches!(d, Directive::Balance(_)))
            .expect("balance present");
        assert!(
            synth_idx < balance_idx,
            "synth (idx {synth_idx}) must precede the Balance (idx {balance_idx})",
        );
    }

    #[test]
    fn test_merge_with_padding_is_idempotent() {
        // Re-merging already-merged input must be a no-op, not a
        // double-count (and not an abort): embedders legitimately feed
        // load-full output — which is already merged — back into
        // query/window ops (rustledger#1712).
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000), "USD"),
            )),
        ];
        let merged_once = merge_with_padding(&directives, DEFAULT_TOLERANCE_MULTIPLIER);
        let merged_twice = merge_with_padding(&merged_once, DEFAULT_TOLERANCE_MULTIPLIER);
        assert_eq!(merged_once.len(), merged_twice.len());
    }

    #[test]
    fn test_padding_transaction_has_p_flag() {
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000.00), "USD"),
            )),
        ];

        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        assert_eq!(result.padding_transactions.len(), 1);
        assert_eq!(result.padding_transactions[0].flag, 'P');
    }

    #[test]
    fn test_process_pads_multiple_currencies() {
        // From basic.beancount:
        // 2007-12-30 pad  Assets:Cash  Equity:Opening-Balances
        // 2007-12-31 balance  Assets:Cash  200 CAD
        // 2007-12-31 balance  Assets:Cash  300 USD
        //
        // A single pad should generate padding for BOTH currencies
        let directives = vec![
            Directive::Open(Open::new(date(2007, 1, 1), "Assets:Cash")),
            Directive::Open(Open::new(date(2007, 1, 1), "Equity:Opening")),
            Directive::Pad(Pad::new(
                date(2007, 12, 30),
                "Assets:Cash",
                "Equity:Opening",
            )),
            Directive::Balance(Balance::new(
                date(2007, 12, 31),
                "Assets:Cash",
                Amount::new(dec!(200), "CAD"),
            )),
            Directive::Balance(Balance::new(
                date(2007, 12, 31),
                "Assets:Cash",
                Amount::new(dec!(300), "USD"),
            )),
        ];

        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        assert!(result.errors.is_empty(), "Should have no errors");
        assert_eq!(
            result.padding_transactions.len(),
            2,
            "Should generate TWO padding transactions (one per currency)"
        );

        // Check that we have both currencies padded
        let currencies: Vec<_> = result
            .padding_transactions
            .iter()
            .filter_map(|txn| txn.postings.first())
            .filter_map(|p| p.amount())
            .map(|a| a.currency.as_str())
            .collect();

        assert!(currencies.contains(&"CAD"), "Should pad CAD");
        assert!(currencies.contains(&"USD"), "Should pad USD");
    }

    #[test]
    fn test_process_pads_transaction_after_balance_ends_pad() {
        // Once a transaction affects the account after the balance assertions,
        // the pad should no longer apply to later balance assertions
        let directives = vec![
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Open(Open::new(date(2024, 1, 1), "Equity:Opening")),
            Directive::Open(Open::new(date(2024, 1, 1), "Expenses:Food")),
            Directive::Pad(Pad::new(date(2024, 1, 1), "Assets:Bank", "Equity:Opening")),
            Directive::Balance(Balance::new(
                date(2024, 1, 2),
                "Assets:Bank",
                Amount::new(dec!(1000), "USD"),
            )),
            // Transaction after balance - this "consumes" the pad
            Directive::Transaction(
                Transaction::new(date(2024, 1, 3), "Spending")
                    .with_synthesized_posting(Posting::new(
                        "Assets:Bank",
                        Amount::new(dec!(-100), "USD"),
                    ))
                    .with_synthesized_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(100), "USD"),
                    )),
            ),
            // This balance should NOT use the pad (too late)
            Directive::Balance(Balance::new(
                date(2024, 1, 5),
                "Assets:Bank",
                Amount::new(dec!(900), "USD"),
            )),
        ];

        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);

        // Should only generate one padding transaction (for the first balance)
        assert_eq!(result.padding_transactions.len(), 1);
        assert_eq!(
            result.padding_transactions[0]
                .postings
                .first()
                .and_then(|p| p.amount())
                .map(|a| a.number),
            Some(dec!(1000))
        );
    }

    /// A difference within the balance's tolerance is not padded, and the
    /// tolerance follows the ledger's `tolerance_multiplier`: `100.004`
    /// against `balance 100.00` is within 0.5 * 2 * 0.01 = 0.01, as in
    /// beancount (`Unused Pad entry`), and beyond a multiplier of 0 (#2901).
    #[test]
    fn test_process_pads_within_the_balance_tolerance_pads_nothing() {
        let directives = vec![
            transfer(date(2024, 1, 2), "Assets:A", dec!(100.004)),
            Directive::Pad(Pad::new(date(2024, 1, 3), "Assets:A", "Equity:O")),
            balance(date(2024, 1, 10), "Assets:A", dec!(100.00)),
        ];
        let result = process_pads(&directives, DEFAULT_TOLERANCE_MULTIPLIER);
        assert!(result.padding_transactions.is_empty());
        assert_eq!(result.errors.len(), 1, "{:?}", result.errors);
        assert!(
            result.errors[0]
                .message
                .contains("no corresponding balance")
        );

        let strict = process_pads(&directives, Decimal::ZERO);
        assert_eq!(strict.padding_transactions.len(), 1);
        assert_eq!(
            strict.padding_transactions[0].postings[0]
                .amount()
                .map(|a| a.number),
            Some(dec!(-0.004))
        );
        assert!(strict.errors.is_empty(), "{:?}", strict.errors);
    }
}

#[cfg(test)]
mod tolerance_tests {
    use super::*;
    use rust_decimal_macros::dec;

    /// Default `tolerance_multiplier` from `ValidationOptions::default()`
    /// (also the loader's default via `Options::new()`).
    fn default_mul() -> Decimal {
        dec!(0.5)
    }

    #[test]
    fn explicit_tolerance_always_wins() {
        // Even an absurdly-small / absurdly-large explicit tolerance
        // overrides the scale-derived default. This is the
        // contract `~ tolerance` on a Balance directive provides.
        assert_eq!(
            balance_tolerance(dec!(100.00), Some(dec!(0.001)), default_mul()),
            dec!(0.001)
        );
        assert_eq!(
            balance_tolerance(dec!(100.00), Some(dec!(50)), default_mul()),
            dec!(50)
        );
    }

    #[test]
    fn integer_amount_requires_exact_match() {
        // scale == 0 means the asserted amount has no decimal places.
        // Python beancount requires an exact match in that case; the
        // helper returns ZERO to make `difference > 0` strict.
        assert_eq!(
            balance_tolerance(dec!(100), None, default_mul()),
            Decimal::ZERO
        );
    }

    #[test]
    fn two_decimal_amount_uses_default_quantum() {
        // For `100.00 USD` with the default multiplier 0.5:
        //   tolerance = 0.5 * 2 * 0.01 = 0.01
        // This is the Beancount-spec rule the LSP and the validator
        // both depend on; if this changes, every balance assertion
        // shifts pass/fail.
        assert_eq!(
            balance_tolerance(dec!(100.00), None, default_mul()),
            dec!(0.01)
        );
    }

    #[test]
    fn higher_precision_scales_down() {
        // 4 decimal places: tolerance = 0.5 * 2 * 0.0001 = 0.0001
        assert_eq!(
            balance_tolerance(dec!(100.0000), None, default_mul()),
            dec!(0.0001)
        );
    }

    #[test]
    fn multiplier_one_doubles_default() {
        // File overrides `option "inferred_tolerance_multiplier" "1.0"`:
        //   tolerance = 1.0 * 2 * 0.01 = 0.02
        assert_eq!(balance_tolerance(dec!(100.00), None, dec!(1.0)), dec!(0.02));
    }

    #[test]
    fn multiplier_zero_forces_strict_match() {
        // `option "inferred_tolerance_multiplier" "0.0"` is the
        // canonical way to force strict equality on a decimal
        // amount. The helper must yield zero so the validator emits
        // a diagnostic on any rounding drift.
        assert_eq!(
            balance_tolerance(dec!(100.00), None, dec!(0.0)),
            Decimal::ZERO
        );
    }

    #[test]
    fn negative_amount_uses_same_scale_logic() {
        // Tolerance is sign-independent (the validator applies it
        // against `(actual - expected).abs()`), but the helper does
        // not flip sign on negative expected: scale() is unsigned.
        assert_eq!(
            balance_tolerance(dec!(-100.00), None, default_mul()),
            dec!(0.01)
        );
    }
}
