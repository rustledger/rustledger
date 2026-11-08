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
    Account, Amount, Currency, Directive, Inventory, NaiveDate, Position, Posting, Spanned,
    Transaction,
};
use std::collections::HashMap;
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

/// The pad rule: which `pad` a `balance` uses, and whether that pad is used
/// at all. Beancount's `pad` plugin (`beancount/ops/pad.py`), per target
/// account:
///
/// - The pad a balance can use is the latest one dated strictly before it
///   (its `active_pad`). An earlier pad that a later one superseded is never
///   used again, and comes out unused if it never padded.
/// - A balance in a currency uses up that currency for the pads before it,
///   whatever its difference (its `padded_lots`, reset by each new pad): a
///   later balance in the same currency is compared, not padded, until
///   another `pad` comes. So `pad`, `balance 0`, `balance 10` pads nothing
///   and fails the second balance.
/// - A pad is used only when it inserts padding, a non-zero difference.
///   Otherwise it is an `Unused Pad entry`, even if a balance reached it.
///
/// This is the one implementation of that rule, shared by [`process_pads`]
/// (the synthesized padding transactions the loader's balance view, BQL and
/// the reports read) and `rustledger-validate`'s balance check, which pads
/// its own booked inventories inline in its walk
/// (`validators::balance::validate_balance_late`). Each keeps its own
/// inventories and hands [`Self::balance`] the target's current amount, so
/// what the rule decides cannot differ between them; the
/// `pad_parity_test` drift guard in `rustledger-validate` compares the two
/// end to end.
///
/// The payload `P` is what the caller needs back about a pad: its index in
/// the input for [`process_pads`], its source location for the validator.
#[derive(Debug, Clone)]
pub struct PadTracker<P> {
    targets: FxHashMap<Account, Vec<TrackedPad<P>>>,
}

impl<P> Default for PadTracker<P> {
    fn default() -> Self {
        Self {
            targets: FxHashMap::default(),
        }
    }
}

/// A `pad` known to a [`PadTracker`].
#[derive(Debug, Clone)]
pub struct TrackedPad<P> {
    /// The pad's date.
    pub date: NaiveDate,
    /// The account the padding is taken from.
    pub source_account: Account,
    /// The caller's data for this pad.
    pub payload: P,
    /// Whether this pad inserted padding for at least one balance.
    used: bool,
    /// Currencies a balance after this pad has asserted (beancount's
    /// `padded_lots`): this pad pads none of them again.
    reached: FxHashSet<Currency>,
}

impl<P> TrackedPad<P> {
    /// Whether this pad inserted padding for at least one balance. A pad that
    /// never did is an `Unused Pad entry`.
    #[must_use]
    pub const fn is_used(&self) -> bool {
        self.used
    }
}

/// What a balance does with its account's pad, from [`PadTracker::balance`].
#[derive(Debug)]
pub struct PadStep<'a, P> {
    /// The dates of the pads this balance is the first in its currency to
    /// reach, oldest first. More than one means two pads stand before the
    /// balance; it uses only the last, and the others are unused.
    pub contenders: Vec<NaiveDate>,
    /// The pad the balance uses: the latest of the contenders.
    pub pad: &'a TrackedPad<P>,
    /// What the pad does.
    pub action: PadAction,
}

/// What a pad does for a balance (see [`PadStep`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PadAction {
    /// The account already holds the asserted amount: nothing is padded, and
    /// the currency is used up all the same.
    Satisfied,
    /// Pad this amount into the target, and its negation out of the source.
    Pad(Decimal),
    /// The target's amount, or the difference, cannot be represented: nothing
    /// is padded, and the caller reports it (#1863).
    Unrepresentable,
}

impl<P> PadTracker<P> {
    /// Register a `pad` into `target` from `source_account`.
    pub fn add(&mut self, target: &Account, date: NaiveDate, source_account: Account, payload: P) {
        let pads = self.targets.entry(target.clone()).or_default();
        // Kept in date order, so the last pad dated before a balance is its
        // active pad whatever order the caller registers them in. Equal dates
        // keep registration order.
        let at = pads.partition_point(|p| p.date <= date);
        pads.insert(
            at,
            TrackedPad {
                date,
                source_account,
                payload,
                used: false,
                reached: FxHashSet::default(),
            },
        );
    }

    /// Apply the rule to a `balance` of `asserted` `currency` on `account`
    /// dated `date`.
    ///
    /// `current` gives the account's amount of the currency, its
    /// sub-accounts included, as the balance check sums it (`None` when it
    /// cannot be represented). It is called only when a pad applies.
    ///
    /// Returns `None` when no pad applies, and the balance is compared
    /// against the inventory as it stands. Otherwise the balance has been
    /// recorded against the pads (the currency is used up for every
    /// contender, and the pad is marked used if it pads), and the caller
    /// applies [`PadStep::action`] and does not compare.
    pub fn balance(
        &mut self,
        account: &Account,
        date: NaiveDate,
        asserted: &Amount,
        current: impl FnOnce() -> Option<Decimal>,
    ) -> Option<PadStep<'_, P>> {
        let pads = self.targets.get_mut(account)?;
        let before = pads.partition_point(|p| p.date < date);
        let active = before.checked_sub(1)?;
        if pads[active].reached.contains(&asserted.currency) {
            // The active pad already served this currency: compare.
            return None;
        }
        // Every balance marks all the pads before it, so in a walk in date
        // order (both callers walk in booking order) the pads that have
        // reached the currency are a prefix: walk back from the active pad to
        // the first one that has, rather than over every pad.
        let mut contenders = Vec::new();
        for pad in pads[..before].iter_mut().rev() {
            if pad.reached.contains(&asserted.currency) {
                break;
            }
            pad.reached.insert(asserted.currency.clone());
            contenders.push(pad.date);
        }
        contenders.reverse();
        let action = match current().and_then(|c| asserted.number.checked_sub(c)) {
            None => PadAction::Unrepresentable,
            Some(difference) if difference.is_zero() => PadAction::Satisfied,
            Some(difference) => {
                pads[active].used = true;
                PadAction::Pad(difference)
            }
        };
        Some(PadStep {
            contenders,
            pad: &pads[active],
            action,
        })
    }

    /// The pads that never padded (`Unused Pad entry`), with their target.
    pub fn unused(&self) -> impl Iterator<Item = (&Account, &TrackedPad<P>)> {
        self.targets
            .iter()
            .flat_map(|(target, pads)| pads.iter().map(move |pad| (target, pad)))
            .filter(|(_, pad)| !pad.used)
    }
}

/// Process pad directives and generate synthetic transactions.
///
/// This function:
/// 1. Tracks account inventories: every account a posting names, opened or
///    not, as beancount's padding reads every posting
/// 2. When a pad is encountered, registers it with the [`PadTracker`]
/// 3. When a balance assertion is encountered for an account with a pad,
///    applies the tracker's rule, and generates a synthetic transaction to
///    make the balance match when it pads
///
/// # Arguments
///
/// * `directives` - The directives to process. Order does not matter:
///   `process_pads` sorts a view of them by date internally before
///   applying pad math.
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
/// `rustledger-validate` pads its own booked inventories inline in its
/// walk rather than calling this, but through the same [`PadTracker`], so
/// the two cannot disagree on which pad a balance uses or by how much.
pub fn process_pads(directives: &[Directive]) -> PadResult {
    let num_directives = directives.len();
    let mut inventories: HashMap<rustledger_core::Account, Inventory> =
        HashMap::with_capacity(num_directives.min(16));
    let mut pads: PadTracker<usize> = PadTracker::default();
    let mut padding_transactions = Vec::with_capacity(num_directives.min(16));
    let mut padding_origins = Vec::with_capacity(num_directives.min(16));
    let mut errors = Vec::with_capacity(4);

    let mut sorted: Vec<(usize, &Directive)> = directives.iter().enumerate().collect();
    // Sort by the canonical booking key, not by date alone. Date-only left
    // same-date directives in source order, so a `pad` written above the
    // `balance` it targets was processed first and the balance consumed it --
    // synthesizing a padding transaction beancount does not (#2150). The key
    // puts Balance before Pad, so that balance is seen first and the pad ends
    // up with nothing to satisfy.
    sorted.sort_by_key(|(_, d)| rustledger_core::booking_sort_key(d));

    for (index, directive) in sorted {
        match directive {
            Directive::Transaction(txn) => {
                // Update inventories. Every account counts, opened or not:
                // beancount's padding sums every posting to the target, so
                // tracking only opened accounts dropped an unopened target's
                // own postings and padded it by the wrong amount (#2896).
                for posting in &txn.postings {
                    if let Some(units) = posting.amount() {
                        let inv = account_inventory(&mut inventories, &posting.account);
                        let position =
                            Position::from_posting(units, posting.cost.as_deref(), txn.date);
                        // A running balance that leaves range makes every pad
                        // measured against it wrong, so report it here rather
                        // than pad from a clamped total (#1863).
                        if let Err(e) = inv.add(position) {
                            errors.push(
                                PadError::new(txn.date, e.to_string())
                                    .with_account(posting.account.clone()),
                            );
                        }
                    }
                }
            }

            Directive::Pad(pad) => {
                pads.add(&pad.account, pad.date, pad.source_account.clone(), index);
            }

            Directive::Balance(bal) => {
                // The balance assertion this pad targets sums the account AND
                // its sub-accounts (beancount semantic, verified against
                // bean-check), so the pad difference is measured the same way.
                let Some(step) = pads.balance(&bal.account, bal.date, &bal.amount, || {
                    rustledger_core::sum_account_and_subaccounts(
                        inventories.iter(),
                        bal.account.as_str(),
                        &bal.amount.currency,
                    )
                }) else {
                    continue;
                };
                let difference = match step.action {
                    PadAction::Satisfied => continue,
                    // A pad amount that cannot be represented must not be
                    // clamped — the synthetic transaction it produces is
                    // written into the ledger as if the user had entered it
                    // (#1863).
                    PadAction::Unrepresentable => {
                        errors.push(PadError::new(
                            bal.date,
                            format!(
                                "cannot compute the pad amount for {}: the {} balance exceeds \
                                 the representable range (±7.9e28)",
                                bal.account, bal.amount.currency
                            ),
                        ));
                        continue;
                    }
                    PadAction::Pad(difference) => difference,
                };
                let pad = step.pad;

                // Generate synthetic transaction
                let pad_txn = create_padding_transaction(
                    pad.date,
                    &bal.account,
                    &pad.source_account,
                    Amount::new(difference, &bal.amount.currency),
                    &bal.amount, // target balance for narration
                );

                // Apply to inventories. `difference` was just derived from
                // these same balances, so an overflow here means the pad
                // target itself is out of range, so report it rather than pad
                // to a clamped figure.
                //
                // A pad is two halves of one entry, so it applies as a unit:
                // if the source overflows after the target succeeded, the
                // target is UNDONE. Leaving it applied would credit the
                // target without debiting the source while emitting no
                // synthetic transaction, so the inventories and the directive
                // list would disagree, and a later assertion on the target
                // could pass off a pad that never happened. The undo is always
                // representable: it restores a total that existed a moment
                // ago. Both halves land whatever the accounts' state, as
                // beancount's padding entry posts to both.
                let currency = &bal.amount.currency;
                let mut apply = |account, number| {
                    account_inventory(&mut inventories, account)
                        .add(Position::simple(Amount::new(number, currency)))
                };
                if let Err(e) = apply(&bal.account, difference) {
                    errors.push(PadError::new(bal.date, e.to_string()));
                    continue;
                }
                if let Err(e) = apply(&pad.source_account, -difference) {
                    drop(apply(&bal.account, -difference));
                    errors.push(PadError::new(bal.date, e.to_string()));
                    continue;
                }

                padding_transactions.push(pad_txn);
                padding_origins.push(PadOrigin {
                    pad: pad.payload,
                    balance: index,
                });
            }

            _ => {}
        }
    }

    // Check for unused pads (pad without corresponding balance)
    for (account, pad) in pads.unused() {
        errors.push(
            PadError::new(
                pad.date,
                format!(
                    "Pad directive for account {account} has no corresponding balance assertion"
                ),
            )
            .with_account(account.clone()),
        );
    }

    PadResult {
        padding_transactions,
        padding_origins,
        errors,
    }
}

/// The inventory of `account`, created empty on first use. Looks up before
/// inserting so the common case clones no account name.
fn account_inventory<'a>(
    inventories: &'a mut HashMap<Account, Inventory>,
    account: &Account,
) -> &'a mut Inventory {
    if !inventories.contains_key(account) {
        inventories.insert(account.clone(), Inventory::new());
    }
    inventories
        .get_mut(account)
        .expect("the inventory was inserted just above")
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
/// math.
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
pub fn merge_with_padding(directives: &[Directive]) -> Vec<Directive> {
    merge_with_padding_owned(directives.to_vec())
}

/// [`merge_with_padding`] for a caller that already owns its directives.
///
/// Exists so consumers holding an owned `Vec` need not clone it a second time
/// just to reach the canonical placement rule. `Ledger::balance_view` used to
/// inline the merge for exactly that reason, and the copy drifted the moment
/// the rule changed — this is the same saving without the duplicate.
#[must_use]
pub fn merge_with_padding_owned(directives: Vec<Directive>) -> Vec<Directive> {
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

    let result = process_pads(&directives);

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
/// Identical merge behavior, but the input/output keep each directive's
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
pub fn merge_with_padding_spanned(directives: &[Spanned<Directive>]) -> Vec<Spanned<Directive>> {
    let plain: Vec<Directive> = directives.iter().map(|s| s.value.clone()).collect();
    debug_assert!(
        !plain
            .iter()
            .any(|d| matches!(d, Directive::Transaction(t) if is_synthesized_pad(t))),
        "merge_with_padding_spanned called on input that already contains synth pad transactions; \
         re-running would double-count pad effects",
    );

    let result = process_pads(&plain);

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
    use rust_decimal_macros::dec;
    use rustledger_core::{Balance, Open, Pad};

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

        let result = process_pads(&directives);

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

        let result = process_pads(&directives);

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

        let result = process_pads(&directives);

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

        let result = process_pads(&directives);

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

        let result = process_pads(&directives);

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

        let result = process_pads(&directives);

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
        let result = process_pads(directives);
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
        let result = process_pads(&directives);
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

        let merged = merge_with_padding(&directives);

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
        let result = process_pads(&directives);
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

        let merged = merge_with_padding(&directives);

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
        let merged = merge_with_padding(&directives);

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

        let plain = merge_with_padding(&directives);
        let merged = merge_with_padding_spanned(&spanned);

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

        let merged = merge_with_padding(&directives);

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

        let merged = merge_with_padding(&directives);

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

        let merged = merge_with_padding(&directives);

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
        let merged_once = merge_with_padding(&directives);
        let merged_twice = merge_with_padding(&merged_once);
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

        let result = process_pads(&directives);

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

        let result = process_pads(&directives);

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

        let result = process_pads(&directives);

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
}
