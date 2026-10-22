//! Transaction validation.

use rust_decimal::Decimal;
use rustc_hash::FxHashMap;
use rustledger_core::{Amount, BookingMethod, Inventory, NaiveDate, Posting, Transaction};

use super::helpers::push_account_not_open;
use crate::error::{ErrorCode, ValidationError};
use crate::{AccountState, LedgerState, PendingPostingError, ValidationOptions};

/// Early-phase transaction validation — runs on pre-booking directives.
///
/// Reports the structural checks that need the pre-booking shape (posting
/// count, multiple elided amounts, negative costs). Account errors on the
/// postings — presence (E1001) and the open/close dates — are judged
/// against the provisional pre-plugin table and HELD under the
/// transaction's source identity (`location`), not reported: the late
/// phase judges every posting it sees against the post-plugin accounts and
/// drops the held errors, so only a posting late never sees (booking
/// dropped it, or booking refused its transaction) is reported from here.
/// See `LedgerState::pending_posting_errors`.
///
/// Currency-constraint checking (which calls `posting.amount()`) is
/// deliberately deferred to the late phase, since elided postings have
/// `units: None` here.
pub fn validate_transaction_early(
    state: &mut LedgerState,
    txn: &Transaction,
    location: Option<(rustledger_parser::Span, u16)>,
    errors: &mut Vec<ValidationError>,
) {
    if !validate_transaction_structure(txn, errors) {
        return;
    }
    // Only a transaction with a real source identity can be matched up in
    // late. A synthesized one shares the `(SYNTHESIZED_FILE_ID, Span::ZERO)`
    // sentinel and an unspanned caller has no identity; both hand late the
    // same list (no booking or plugins in between), so late covers them.
    let Some((span, file_id)) = location else {
        return;
    };
    if file_id == rustledger_core::SYNTHESIZED_FILE_ID {
        return;
    }
    let mut held = Vec::new();
    for (i, posting) in txn.postings.iter().enumerate() {
        let mut found = Vec::new();
        match state.early_accounts.get(&posting.account) {
            Some(&(opened, closed)) => {
                lifecycle_errors(txn, posting, opened, closed, &mut found);
            }
            None => push_account_not_open(state, &posting.account, txn.date, "Account", &mut found),
        }
        // One judgment per account per transaction, as late makes.
        if !found.is_empty() && !first_posting_to_account(txn, i) {
            continue;
        }
        for mut error in found {
            error.span = Some(span);
            error.file_id = Some(file_id);
            held.push(PendingPostingError {
                posting: (posting.file_id, posting.span),
                account: posting.account.clone(),
                // Booking can drop any posting whose amount it has to
                // interpolate: fully elided, or a currency with no number.
                elided: posting.amount().is_none(),
                error,
            });
        }
    }
    if !held.is_empty() {
        state
            .pending_posting_errors
            .entry((file_id, span))
            .or_default()
            .extend(held);
    }
}

/// Late-phase transaction validation — runs on post-booking, post-plugin
/// directives.
///
/// The authority on every posting it sees: account presence (E1001), the
/// open/close dates, and the currency constraint, against the accounts the
/// post-plugin stream opened. Then the balance residual and the inventory
/// updates (lot matching, capital gains).
pub fn validate_transaction_late(
    state: &mut LedgerState,
    txn: &Transaction,
    location: Option<(rustledger_parser::Span, u16)>,
    errors: &mut Vec<ValidationError>,
) {
    for (i, posting) in txn.postings.iter().enumerate() {
        // Presence and the open/close dates are judged once per account per
        // transaction, as beancount does (it checks the set of accounts an
        // entry references). Booking can split one posting into several to
        // the same account (a reduction across lots, an elided posting
        // absorbing two currencies), which must not multiply the error.
        //
        // The duplicate check runs only once an error was found, so the
        // clean path pays nothing for it.
        let before = errors.len();
        let account_state = state.accounts.get(&posting.account);
        match account_state {
            Some(account_state) => validate_account_lifecycle(txn, posting, account_state, errors),
            None => push_account_not_open(state, &posting.account, txn.date, "Account", errors),
        }
        if errors.len() > before && !first_posting_to_account(txn, i) {
            errors.truncate(before);
        }
        if let Some(account_state) = account_state {
            validate_posting_currency(state, txn, posting, account_state, errors);
        }
    }

    // The early phase's held judgments of this transaction's postings: late
    // just judged every posting still here, so drop them — except an elided
    // posting booking removed (a zero-value interpolation), which only early
    // saw. That is the elided-zero-to-unopened-account case beancount misses
    // (#877), which rustledger reports on purpose.
    //
    // A posting is "removed" when no posting here carries its source
    // identity or its account. The account half matters when the identity
    // is gone for another reason: the Python plugin bridge does not carry
    // posting spans, so after a Python plugin no posting has its identity,
    // and a posting still naming the account was just judged above. (A
    // Python plugin that RENAMES an elided posting therefore still gets the
    // old name reported, as before #2648; a native plugin keeps the
    // posting's identity, so its renames are clean.)
    if let Some((span, file_id)) = location
        && !state.pending_posting_errors.is_empty()
        && let Some(held) = state.pending_posting_errors.remove(&(file_id, span))
    {
        for pending in held {
            if pending.elided
                && !txn
                    .postings
                    .iter()
                    .any(|p| (p.file_id, p.span) == pending.posting || p.account == pending.account)
            {
                errors.push(pending.error);
            }
        }
    }

    // Compute tolerances and check transaction balance.
    let tolerances = calculate_tolerances(txn, &state.options);
    validate_transaction_balance(txn, &tolerances, errors);

    // Update inventories with booking validation
    update_inventories(state, txn, errors);
}

/// Whether `txn.postings[i]` is the first posting in `txn` to its account.
/// A scan of the earlier postings: transactions have a handful, and this
/// allocates nothing.
fn first_posting_to_account(txn: &Transaction, i: usize) -> bool {
    let account = &txn.postings[i].account;
    !txn.postings[..i].iter().any(|p| &p.account == account)
}

/// Validate transaction structure.
/// Returns false if validation should stop (no postings to validate).
///
/// Note: Python beancount allows transactions with zero postings (metadata-only transactions).
/// Single-posting transactions are allowed structurally but will fail balance checking.
pub fn validate_transaction_structure(
    txn: &Transaction,
    errors: &mut Vec<ValidationError>,
) -> bool {
    if txn.postings.is_empty() {
        // Python beancount allows transactions with no postings (metadata-only).
        // No error, but skip further validation since there's nothing to validate.
        return false;
    }

    // Warn about single posting (structurally valid but will fail balance check).
    // Skip if the single posting has an explicit zero-cost spec — this indicates
    // the counterpart was interpolated to zero and removed during booking,
    // matching Python beancount behavior.
    let is_zero_cost_single = txn.postings.len() == 1
        && txn.postings[0].cost.as_ref().is_some_and(|c| {
            // Either per-unit or total carrying zero counts.
            c.number.is_some_and(|cn| {
                cn.per_unit().is_some_and(|n| n.is_zero())
                    || cn.total().is_some_and(|n| n.is_zero())
            })
        });
    if txn.postings.len() == 1 && !is_zero_cost_single {
        errors.push(ValidationError::new(
            ErrorCode::SinglePosting,
            "Transaction has only one posting".to_string(),
            txn.date,
        ));
    }

    // Check for multiple missing amounts per currency (E3002).
    //
    // Interpolation solves one unknown per currency group, so two elided
    // postings are only ambiguous when they compete for the SAME residual.
    // The grouping comes from `rustledger_booking::elided_unknown_groups` --
    // the same function `interpolate` solves by -- rather than being re-derived
    // here. It cannot be eyeballed from the posting: a per-unit cost or price
    // redenominates the weight, so `HOOL {300.00 USD}` is an unknown in USD,
    // not in HOOL (#1911).
    //
    // This block previously grouped by the units currency and then summed
    // across every group, rejecting two elided postings that were in different
    // currencies entirely (#1914). The grouping was also never populated: the
    // hint used `as_amount()`, which is `None` for exactly the partial-units
    // postings the rule is about, so everything landed in one bucket.
    {
        let groups = rustledger_booking::elided_unknown_groups(txn);
        let mut per_currency: FxHashMap<&rustledger_core::Currency, u32> = FxHashMap::default();
        let mut unassigned = 0_u32;
        for (_, group) in &groups {
            match group {
                rustledger_booking::UnknownGroup::Currency(c) => {
                    *per_currency.entry(c).or_default() += 1;
                }
                rustledger_booking::UnknownGroup::Unassigned => unassigned += 1,
            }
        }

        // A fully-elided posting has no currency of its own, so it can absorb
        // any residual -- including one another unknown is already claiming.
        // Beancount refuses the combination outright ("CategorizationError"),
        // and so do we: more than one unknown in play alongside one is
        // ambiguous no matter which currencies the others sit in.
        let ambiguous = if unassigned > 0 {
            groups.len() > 1
        } else {
            per_currency.values().any(|&n| n > 1)
        };

        if ambiguous {
            let detail = per_currency
                .iter()
                .filter(|&(_, &n)| n > 1)
                .map(|(c, n)| format!("{n} in {c}"))
                .collect::<Vec<_>>()
                .join(", ");
            let message = if detail.is_empty() {
                format!(
                    "Transaction has {} postings with missing amounts; at most one is allowed \
                     when any of them has no currency to interpolate in",
                    groups.len()
                )
            } else {
                format!(
                    "Transaction has multiple postings with missing amounts in the same \
                     currency ({detail}); at most one per currency is allowed"
                )
            };
            errors.push(ValidationError::new(
                ErrorCode::MultipleInterpolation,
                message,
                txn.date,
            ));
        }
    }

    // Check for negative cost amounts. One error per posting, even
    // when the spec is `PerUnitFromTotal` and carries both halves: by
    // `BookedCost`'s invariant `per_unit * |units| = total`, the two
    // values share sign, so reporting both would be two errors for
    // one underlying problem. Prefer the user-written value
    // (`total` for `PerUnitFromTotal`, since that's the literal
    // `{{ total }}` the user typed and what they can fix). Fall back
    // to per-unit for raw `PerUnit` specs.
    for posting in &txn.postings {
        if let Some(cost) = &posting.cost
            && let Some(cn) = cost.number
        {
            // Read-only destructure: the `BookedCost { total: value, .. }`
            // pattern pulls the user-written `total` out for the negative
            // check, but does NOT construct a new `BookedCost`. Do not
            // copy this pattern to *build* a `BookedCost` — that would
            // bypass the consistency invariant enforced by
            // `BookedCost::new` / `try_new`.
            // Compound carries two independently-signed components; take
            // the first negative one (per-unit checked first) so the
            // diagnostic names the offending part.
            let (label, value) = match cn {
                rustledger_core::CostNumber::PerUnit { value } => ("per-unit", value),
                rustledger_core::CostNumber::Total { value }
                | rustledger_core::CostNumber::PerUnitFromTotal(rustledger_core::BookedCost {
                    total: value,
                    ..
                }) => ("total", value),
                rustledger_core::CostNumber::Compound { per_unit, total } => {
                    if per_unit < Decimal::ZERO {
                        ("per-unit", per_unit)
                    } else {
                        ("total", total)
                    }
                }
            };
            if value < Decimal::ZERO {
                let units_str = posting.amount().map_or_else(
                    || "?".to_string(),
                    |a| format!("{} {}", a.number, a.currency),
                );
                let cost_currency = cost.currency.as_ref().map_or("?", |c| c.as_str());
                errors.push(ValidationError::new(
                    ErrorCode::NegativeCost,
                    format!(
                        "Cost is negative: {label} cost ({value} {cost_currency}) for {units_str} in posting to {}",
                        posting.account
                    ),
                    txn.date,
                ));
            }
        }
    }

    true
}

/// Validate that an account is open at transaction time and not closed.
pub fn validate_account_lifecycle(
    txn: &Transaction,
    posting: &Posting,
    account_state: &AccountState,
    errors: &mut Vec<ValidationError>,
) {
    lifecycle_errors(
        txn,
        posting,
        account_state.opened,
        account_state.closed,
        errors,
    );
}

/// The open/close date check behind [`validate_account_lifecycle`], on bare
/// dates so the early phase's provisional table can share it.
fn lifecycle_errors(
    txn: &Transaction,
    posting: &Posting,
    opened: NaiveDate,
    closed: Option<NaiveDate>,
    errors: &mut Vec<ValidationError>,
) {
    if txn.date < opened {
        errors.push(ValidationError::new(
            ErrorCode::AccountNotOpen,
            format!(
                "Account {} used on {} but not opened until {}",
                posting.account, txn.date, opened
            ),
            txn.date,
        ));
    }

    // A posting ON the close date is allowed: beancount walks the entries in
    // booking order, where a `close` sorts after every transaction of its
    // day, so the account is still active for them. Both phases register
    // every close before walking the transactions, so the order has to be
    // expressed as the date comparison: strictly after.
    if let Some(closed) = closed
        && txn.date > closed
    {
        errors.push(ValidationError::new(
            ErrorCode::AccountClosed,
            format!(
                "Posting to inactive account {} on {} (closed on {})",
                posting.account, txn.date, closed
            ),
            txn.date,
        ));
    }
}

/// Validate currency constraints and commodity declarations for a posting.
pub fn validate_posting_currency(
    state: &LedgerState,
    txn: &Transaction,
    posting: &Posting,
    account_state: &AccountState,
    errors: &mut Vec<ValidationError>,
) {
    let Some(units) = posting.amount() else {
        return;
    };

    // Check currency constraints
    if !account_state.currencies.is_empty() && !account_state.currencies.contains(&units.currency) {
        errors.push(ValidationError::new(
            ErrorCode::CurrencyNotAllowed,
            format!(
                "Invalid currency {} not allowed in account {}",
                units.currency, posting.account
            ),
            txn.date,
        ));
    }

    // Check commodity declaration
    if state.options.require_commodities && !state.commodities.contains(&units.currency) {
        errors.push(ValidationError::new(
            ErrorCode::UndeclaredCurrency,
            format!("Currency {} not declared", units.currency),
            txn.date,
        ));
    }
}

/// Validate that the transaction balances within tolerance.
///
/// Tolerance is calculated per-currency based on:
/// 1. The quantum (precision) of amounts in postings
/// 2. Cost-based tolerance when `infer_tolerance_from_cost` is enabled:
///    each cost or price contributes
///    `min(units_quantum * tolerance_multiplier * number, 0.5)`, summed per
///    currency (see [`rustledger_booking::transaction_tolerances`])
pub fn validate_transaction_balance(
    txn: &Transaction,
    tolerances: &FxHashMap<rustledger_core::Currency, Decimal>,
    errors: &mut Vec<ValidationError>,
) {
    // Skip balance checking if there are any empty cost specs (e.g., `{}`).
    // Empty cost specs will have their cost filled in by lot matching during booking,
    // and if there's no matching lot, that error will be reported separately.
    // This matches Python beancount behavior where booking runs before balance checking.
    let has_empty_cost_spec = txn.postings.iter().any(|p| {
        if let Some(cost) = &p.cost {
            cost.number.is_none()
        } else {
            false
        }
    });
    if has_empty_cost_spec {
        return;
    }

    // Same rule, other cause: a posting whose units interpolation never filled
    // in. The residual of a half-filled transaction is an artifact of the
    // failure, not a fact about the user's file — reporting it sends them
    // hunting for an imbalance that would not exist once the real error is
    // fixed.
    //
    // Unreachable from `rledger check`, whose pipeline books BEFORE Late
    // validation and drops failed transactions (`run_booking`'s
    // `failed_indices`), so every posting it sees is filled. The LSP used to
    // validate transactions whose booking failed, and without this reported
    // "does not balance: residual 1e29 USD" where `check` reported that the
    // posting amount could not be computed at all (#1863). It now leaves
    // them out of Late validation as `check` does (#2510), so this guard is
    // reached only by callers that validate an unbooked ledger.
    //
    // Returning silently is right ONLY because something else has already
    // spoken: `check` reports the booking error, and the LSP surfaces it
    // directly (`ErrorCode::for_booking_failure`). One case is not covered — a
    // post-booking plugin that emits a posting with no units. Nothing in-tree
    // does, and the plugin wire format permitting it is the deeper problem,
    // but such a transaction would now pass silently where it previously drew
    // a (misleading) E3001. Fixing it properly means the caller telling this
    // validator whether booking succeeded, rather than it inferring from the
    // postings.
    if txn.postings.iter().any(|p| p.amount().is_none()) {
        return;
    }

    // Fast path: use rust_decimal first. If ALL residuals are exactly zero,
    // the transaction definitely balances — skip the expensive BigDecimal
    // calculation. We only skip on exact zero (not "within tolerance")
    // because Decimal arithmetic can lose precision during cost/price
    // multiplication, potentially under-reporting a non-zero residual.
    // `None` = the fast tier's arithmetic left `rust_decimal`'s range, so it
    // has no opinion; fall through to the exact tier rather than skipping.
    // Short-circuiting on `None` here would pass an arbitrarily unbalanced
    // transaction (#1863).
    let all_zero = rustledger_booking::calculate_residual(txn)
        .is_some_and(|residuals| residuals.values().all(|r| *r == Decimal::ZERO));

    if all_zero {
        return;
    }

    // Slow path: use arbitrary-precision arithmetic for edge cases where
    // Decimal's 28-digit precision causes false positives.
    let residuals = rustledger_booking::calculate_residual_precise(txn);

    for (currency, residual) in &residuals {
        // Get the tolerance for this currency, defaulting to 0 (exact balance).
        // Python beancount uses 0 as default when no posting contributes decimal
        // precision for a currency (all integer amounts → exact balance required).
        let tolerance: bigdecimal::BigDecimal = tolerances
            .get(currency)
            .map(|d| {
                use std::str::FromStr;
                bigdecimal::BigDecimal::from_str(&d.to_string()).unwrap_or_default()
            })
            .unwrap_or_default();

        if residual.abs() > tolerance {
            errors.push(ValidationError::new(
                ErrorCode::TransactionUnbalanced,
                format!("Transaction does not balance: residual {residual} {currency}"),
                txn.date,
            ));
        }
    }
}
/// Calculate per-currency balance tolerances for a transaction.
///
/// Thin wrapper over the canonical
/// [`rustledger_booking::transaction_tolerances`], wiring in the
/// ledger-driven knobs from [`ValidationOptions`]. The semantics live in
/// `rustledger-booking` so every consumer (validator, embedders) shares one
/// implementation.
#[must_use]
pub fn calculate_tolerances(
    txn: &Transaction,
    options: &ValidationOptions,
) -> FxHashMap<rustledger_core::Currency, Decimal> {
    rustledger_booking::transaction_tolerances(
        txn,
        &rustledger_booking::ToleranceOptions {
            multiplier: options.tolerance_multiplier,
            infer_from_cost: options.infer_tolerance_from_cost,
            defaults: &options.inferred_tolerance_default,
        },
    )
}

/// Update inventories with booking validation for each posting.
///
/// Reductions are applied in textual order and augmentations after all of
/// them, the same walk as `BookingEngine::apply` (#2368). Booking classifies
/// each posting against the inventory as it stood before the transaction,
/// threaded with earlier REDUCTIONS only, so an augmentation earlier in the
/// transaction never turns a later posting into a reduction. Adding it first
/// would make `+10 X {100}` then `-20 X {100}` reduce 20 from 10 and fail,
/// where booking (and beancount) open a short of 10. The walk in
/// `BookingEngine::apply` documents the reasoning; change one and change the
/// other.
pub fn update_inventories(
    state: &mut LedgerState,
    txn: &Transaction,
    errors: &mut Vec<ValidationError>,
) {
    let any_cost = txn.postings.iter().any(|p| p.cost.is_some());
    let mut deferred: smallvec::SmallVec<[(&Posting, &Amount); 8]> = smallvec::SmallVec::new();
    for posting in &txn.postings {
        let Some(units) = posting.amount() else {
            continue;
        };
        let Some(inv) = state.inventories.get_mut(&posting.account) else {
            continue;
        };

        let booking_method = state
            .accounts
            .get(&posting.account)
            .map(|a| a.booking)
            .unwrap_or_default();

        // Reduction vs augmentation — the SAME decision the booking engine makes,
        // now via the single `Inventory::is_booking_reduction` source: a cost-bearing
        // opposite-sign position reduces, and under `option "booking_method" "NONE"`
        // (issue #1182) every posting is an augmentation. Sharing it means this
        // validator pass and `BookingEngine::apply` can't drift, and the #1182 gate
        // lives in one place instead of being maintained in both crates.
        let is_reduction = inv.is_booking_reduction(units, posting.cost.as_deref(), booking_method);

        if is_reduction {
            process_inventory_reduction(inv, posting, units, booking_method, txn, errors);
        } else if !any_cost {
            // No cost spec anywhere, so nothing can reduce and textual order
            // is `book`'s order; saves the second map lookup. Not for a
            // cost-less posting in general: `AVERAGE` pools cost-less
            // positions too, so adding one ahead of a sale moves its basis.
            add_posting(inv, posting, units, txn, errors);
        } else {
            deferred.push((posting, units));
        }
    }

    for (posting, units) in deferred {
        if let Some(inv) = state.inventories.get_mut(&posting.account) {
            add_posting(inv, posting, units, txn, errors);
        }
    }
}

/// Add `posting` to `inv`, reporting an overflow as a validation error.
fn add_posting(
    inv: &mut Inventory,
    posting: &Posting,
    units: &Amount,
    txn: &Transaction,
    errors: &mut Vec<ValidationError>,
) {
    if let Err(e) = process_inventory_addition(inv, posting, units, txn) {
        errors.push(
            ValidationError::new(
                ErrorCode::ArithmeticOverflow,
                rustledger_core::BookingError::Overflow(e.clone())
                    .with_account(posting.account.clone())
                    .to_string(),
                txn.date,
            )
            .with_context(format!("currency: {}", e.currency)),
        );
    }
}

/// Process an inventory reduction (selling/removing units).
///
/// On pre-booked directives (the normal pipeline), every reduction posting has
/// a fully-resolved cost spec, so `inv.reduce()` is a trivial exact match.
///
/// If the cost spec has no cost amount (booking failed or wasn't run), we skip
/// inventory processing entirely — booking already reported the error, and
/// re-running lot matching here would either double-report or diverge from the
/// booking engine's decisions.
pub fn process_inventory_reduction(
    inv: &mut Inventory,
    posting: &Posting,
    units: &Amount,
    booking_method: BookingMethod,
    txn: &Transaction,
    errors: &mut Vec<ValidationError>,
) {
    // Skip reductions whose cost spec has no cost amount (e.g., `{}`, `{2024-01-15}`,
    // `{"lot1"}`). These are unbooked postings where either:
    //   - Booking wasn't run (standalone validation), or
    //   - Booking failed and already reported the error (normal pipeline).
    // If booking succeeded, it would have filled in a per-unit cost
    // from the matched lot. Re-running lot matching here would
    // double-report or diverge from the booking engine's decisions.
    // This mirrors `validate_transaction_balance`, which also skips
    // balance checking when a posting has an unresolved cost.
    if let Some(cost) = &posting.cost
        && cost.number.is_none()
    {
        return;
    }

    match inv.reduce(units, posting.cost.as_deref(), booking_method) {
        Ok(_) => {}
        Err(err) => {
            // On pre-booked directives, reduce() with a fully-specified cost
            // should not fail. If it does, report the error — this catches
            // bugs in the booking engine or standalone validation without booking.
            // Code from the canonical mapping (shared with the LSP); only the
            // CONTEXT string is local, since it draws on this posting.
            let code = ErrorCode::for_booking_error(&err);
            let context = match &err {
                rustledger_core::BookingError::InsufficientUnits { .. } => {
                    format!("currency: {}", units.currency)
                }
                rustledger_core::BookingError::AmbiguousMatch { .. } => {
                    "Specify cost, date, or label to disambiguate".to_string()
                }
                rustledger_core::BookingError::NoMatchingLot { .. }
                | rustledger_core::BookingError::CurrencyMismatch { .. }
                | rustledger_core::BookingError::MergeMismatch { .. }
                | rustledger_core::BookingError::MergeSpecMismatch { .. }
                | rustledger_core::BookingError::AverageSpecMismatch { .. }
                | rustledger_core::BookingError::AverageSpecDateOrLabel { .. } => {
                    format!("cost spec: {:?}", posting.cost)
                }
                rustledger_core::BookingError::Overflow(e) => {
                    format!("currency: {}", e.currency)
                }
            };
            errors.push(
                ValidationError::new(
                    code,
                    format!("{}", err.with_account(posting.account.clone())),
                    txn.date,
                )
                .with_context(context),
            );
        }
    }
}

/// Process an inventory addition (buying/adding units).
///
/// # Errors
///
/// [`rustledger_core::OverflowError`] when the account's running total leaves
/// `rust_decimal`'s range (#1863).
pub fn process_inventory_addition(
    inv: &mut Inventory,
    posting: &Posting,
    units: &Amount,
    txn: &Transaction,
) -> Result<(), rustledger_core::OverflowError> {
    let position =
        rustledger_core::Position::from_posting(units, posting.cost.as_deref(), txn.date);

    inv.add(position)
}

#[cfg(test)]
mod tolerance_tests {
    //! Direct unit tests for `calculate_tolerances` (#1309 cluster 3).
    //! The semantics now live in `rustledger_booking::transaction_tolerances`;
    //! these tests exercise the full path through the `ValidationOptions`
    //! wrapper, pinning the tolerance arithmetic and the per-currency
    //! default/floor logic against drift on either side.
    use super::*;
    use rust_decimal_macros::dec;

    fn cur(s: &str) -> rustledger_core::Currency {
        rustledger_core::Currency::from(s)
    }

    fn mk_txn(postings: Vec<Posting>) -> Transaction {
        let mut t = Transaction::new(rustledger_core::naive_date(2024, 1, 1).unwrap(), "t");
        for p in postings {
            t = t.with_synthesized_posting(p);
        }
        t
    }

    #[test]
    fn decimal_quantum_reflects_scale() {
        assert_eq!(
            rustledger_booking::decimal_quantum(dec!(100.00)),
            dec!(0.01)
        ); // scale 2
        assert_eq!(
            rustledger_booking::decimal_quantum(dec!(10.436)),
            dec!(0.001)
        ); // scale 3
        assert_eq!(rustledger_booking::decimal_quantum(dec!(5)), dec!(1)); // scale 0 -> ONE
    }

    #[test]
    fn tolerance_base_is_quantum_times_multiplier_max() {
        // 10.00 USD -> 0.01 * 0.5 = 0.005; 5.000 USD -> 0.001 * 0.5 = 0.0005;
        // per-currency max = 0.005. An integer (scale-0) amount contributes
        // nothing, so CAD gets no tolerance entry at all.
        let t = calculate_tolerances(
            &mk_txn(vec![
                Posting::new("Assets:A", Amount::new(dec!(10.00), "USD")),
                Posting::new("Assets:B", Amount::new(dec!(5.000), "USD")),
                Posting::new("Assets:C", Amount::new(dec!(100), "CAD")),
            ]),
            &ValidationOptions::default(),
        );
        assert_eq!(t.get(&cur("USD")), Some(&dec!(0.005)));
        assert!(
            !t.contains_key(&cur("CAD")),
            "integer-only currency gets no tolerance"
        );
        assert_eq!(t.len(), 1);
    }

    #[test]
    fn tolerance_cost_inferred_is_units_quantum_times_mult_times_cost() {
        // infer_from_cost: 10.00 STK {2.00 USD}
        //   units_quantum 0.01 * 0.5 = 0.005; * cost_per_unit 2.00 = 0.01.
        let opts = ValidationOptions {
            infer_tolerance_from_cost: true,
            ..ValidationOptions::default()
        };
        let p = Posting::new("Assets:Stock", Amount::new(dec!(10.00), "STK")).with_cost(
            rustledger_core::CostSpec::empty()
                .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(2.00) })
                .with_currency("USD"),
        );
        let t = calculate_tolerances(&mk_txn(vec![p]), &opts);
        // USD from the cost; STK from the units-quantum base (0.01 * 0.5).
        // Assert the whole map so an unexpected/missing entry is caught.
        assert_eq!(t.get(&cur("USD")), Some(&dec!(0.01)));
        assert_eq!(t.get(&cur("STK")), Some(&dec!(0.005)));
        assert_eq!(t.len(), 2);
    }

    #[test]
    fn tolerance_price_inferred_is_units_quantum_times_mult_times_price() {
        // Price inference (still gated by `infer_tolerance_from_cost`):
        // 10.00 STK @ 3.00 USD -> USD 0.005 * 3.00 = 0.015; STK keeps its
        // 0.01 * 0.5 = 0.005 units-quantum base.
        let opts = ValidationOptions {
            infer_tolerance_from_cost: true,
            ..ValidationOptions::default()
        };
        let p = Posting::new("Assets:Stock", Amount::new(dec!(10.00), "STK")).with_price(
            rustledger_core::PriceAnnotation::unit(Amount::new(dec!(3.00), "USD")),
        );
        let t = calculate_tolerances(&mk_txn(vec![p]), &opts);
        assert_eq!(t.get(&cur("USD")), Some(&dec!(0.015)));
        assert_eq!(t.get(&cur("STK")), Some(&dec!(0.005)));
        assert_eq!(t.len(), 2);
    }

    #[test]
    fn tolerance_per_currency_default_acts_as_floor() {
        // Default 0.1 for USD exceeds the computed 0.005 -> floor wins.
        let mut opts = ValidationOptions::default();
        opts.inferred_tolerance_default
            .insert("USD".to_string(), dec!(0.1));
        let t = calculate_tolerances(
            &mk_txn(vec![Posting::new(
                "Assets:A",
                Amount::new(dec!(10.00), "USD"),
            )]),
            &opts,
        );
        assert_eq!(t.get(&cur("USD")), Some(&dec!(0.1)));
        assert_eq!(t.len(), 1, "only the USD currency should appear");
    }

    /// #2685: `*` is beancount's fallback for a currency with no tolerance,
    /// not a floor: it reaches integer-only USD but leaves cents-written USD
    /// at its inferred 0.005.
    #[test]
    fn tolerance_wildcard_default_is_the_fallback_for_currencies_without_one() {
        let mut opts = ValidationOptions::default();
        opts.inferred_tolerance_default
            .insert("*".to_string(), dec!(0.2));
        let t = calculate_tolerances(
            &mk_txn(vec![Posting::new("Assets:A", Amount::new(dec!(10), "USD"))]),
            &opts,
        );
        assert_eq!(t.get(&cur("USD")), Some(&dec!(0.2)));
        assert_eq!(t.len(), 1, "only the USD currency should appear");
        let t = calculate_tolerances(
            &mk_txn(vec![Posting::new(
                "Assets:A",
                Amount::new(dec!(10.00), "USD"),
            )]),
            &opts,
        );
        assert_eq!(t.get(&cur("USD")), Some(&dec!(0.005)));
    }

    /// #2554 pinned the `Decimal::MAX` clamp of a cost/price tolerance past
    /// the range here: 22 prices of `MAX` gave a true USD tolerance of
    /// `22 x 0.05 x MAX = 1.1 MAX`. Since #2717 each contribution is capped
    /// at beancount's `MAXIMUM_TOLERANCE`, so the tolerance is `22 x 0.5 =
    /// 11`, exactly, end to end through the balance validator, whose residual
    /// is EXACT and can itself pass `MAX`:
    /// - a residual of 11 passes, and one of 11.1 fails;
    /// - residuals of `0.5 MAX`, `MAX` and past `MAX` all fail.
    #[test]
    fn the_capped_tolerance_never_passes_an_imbalance_the_true_one_fails() {
        let max = Decimal::MAX;
        let opts = ValidationOptions {
            infer_tolerance_from_cost: true,
            ..ValidationOptions::default()
        };
        let unbalanced = |cash: &[Decimal]| {
            let mut postings: Vec<Posting> = (0..22)
                .map(|i| {
                    let units = if i % 2 == 0 { dec!(0.1) } else { dec!(-0.1) };
                    Posting::new("Assets:Stock", Amount::new(units, "CORP")).with_price(
                        rustledger_core::PriceAnnotation::unit(Amount::new(max, "USD")),
                    )
                })
                .collect();
            for &n in cash {
                postings.push(Posting::new("Assets:Cash", Amount::new(n, "USD")));
            }
            let txn = mk_txn(postings);
            let tolerances = calculate_tolerances(&txn, &opts);
            assert_eq!(
                tolerances.get(&cur("USD")),
                Some(&dec!(11)),
                "22 capped 0.5s"
            );
            let mut errors = Vec::new();
            validate_transaction_balance(&txn, &tolerances, &mut errors);
            errors
                .iter()
                .filter(|e| e.code == ErrorCode::TransactionUnbalanced)
                .count()
        };
        let half = Decimal::from_str_exact("39614081257132168796771975167").unwrap();
        let twentieth = Decimal::from_str_exact("3961408125713216879677197517").unwrap();
        assert_eq!(unbalanced(&[dec!(11)]), 0, "within the capped sum");
        assert_eq!(unbalanced(&[dec!(11.1)]), 1, "past the capped sum");
        assert_eq!(unbalanced(&[half]), 1, "0.5 MAX");
        assert_eq!(unbalanced(&[max]), 1, "MAX");
        assert_eq!(unbalanced(&[max, twentieth]), 1, "past MAX");
    }
}

#[cfg(test)]
mod validator_comparison_tests {
    //! #1309 follow-up: kill the comparison-operator mutants in the
    //! structure / lifecycle / balance validators (the survivors in
    //! transaction.rs outside `calculate_tolerances`). Each test pins a
    //! boundary case so a `<`/`>` -> `<=`/`>=`/`==` mutation flips an
    //! observable error.
    use super::*;
    use crate::AccountState;
    use rust_decimal_macros::dec;

    fn d(y: i32, m: u32, day: u32) -> rustledger_core::NaiveDate {
        rustledger_core::naive_date(y, m, day).unwrap()
    }

    fn acct(opened: rustledger_core::NaiveDate) -> AccountState {
        AccountState {
            opened,
            closed: None,
            currencies: rustc_hash::FxHashSet::default(),
            booking: BookingMethod::default(),
        }
    }

    fn has(errs: &[ValidationError], code: ErrorCode) -> bool {
        errs.iter().any(|e| e.code == code)
    }

    // ---- validate_account_lifecycle: `txn.date < account_state.opened`

    #[test]
    fn lifecycle_posting_on_open_date_is_allowed() {
        // date == opened must NOT error. Kills `<` -> `<=` and `<` -> `==`
        // (both flag the open-date posting that the correct `<` allows).
        let a = acct(d(2024, 1, 1));
        let p = Posting::new("Assets:A", Amount::new(dec!(1), "USD"));
        let txn = Transaction::new(d(2024, 1, 1), "on open date");
        let mut errs = Vec::new();
        validate_account_lifecycle(&txn, &p, &a, &mut errs);
        assert!(
            !has(&errs, ErrorCode::AccountNotOpen),
            "a posting on the open date must be allowed: {errs:?}"
        );
    }

    #[test]
    fn lifecycle_posting_before_open_errors() {
        // date < opened must error. Kills `<` -> `==` (which would not flag
        // a strictly-before-open date).
        let a = acct(d(2024, 1, 10));
        let p = Posting::new("Assets:A", Amount::new(dec!(1), "USD"));
        let txn = Transaction::new(d(2024, 1, 1), "before open");
        let mut errs = Vec::new();
        validate_account_lifecycle(&txn, &p, &a, &mut errs);
        assert!(
            has(&errs, ErrorCode::AccountNotOpen),
            "a posting before the open date must error: {errs:?}"
        );
    }

    // ---- validate_transaction_balance: `residual.abs() > tolerance`

    fn usd_tol(t: Decimal) -> FxHashMap<rustledger_core::Currency, Decimal> {
        let mut m = FxHashMap::default();
        m.insert(rustledger_core::Currency::from("USD"), t);
        m
    }

    #[test]
    fn balance_residual_equal_to_tolerance_is_ok() {
        // residual exactly == tolerance must NOT error. Kills `>` -> `>=`.
        let txn = Transaction::new(d(2024, 1, 1), "edge")
            .with_synthesized_posting(Posting::new("Assets:A", Amount::new(dec!(0.01), "USD")));
        let mut errs = Vec::new();
        validate_transaction_balance(&txn, &usd_tol(dec!(0.01)), &mut errs);
        assert!(
            !has(&errs, ErrorCode::TransactionUnbalanced),
            "a residual exactly at tolerance must pass: {errs:?}"
        );
    }

    #[test]
    fn balance_residual_above_tolerance_errors() {
        let txn = Transaction::new(d(2024, 1, 1), "unbalanced")
            .with_synthesized_posting(Posting::new("Assets:A", Amount::new(dec!(0.02), "USD")));
        let mut errs = Vec::new();
        validate_transaction_balance(&txn, &usd_tol(dec!(0.01)), &mut errs);
        assert!(
            has(&errs, ErrorCode::TransactionUnbalanced),
            "a residual above tolerance must error: {errs:?}"
        );
    }

    // ---- validate_transaction_structure: `value < Decimal::ZERO` (cost)

    fn cost_posting(cost: Decimal) -> Posting {
        Posting::new("Assets:Stock", Amount::new(dec!(10), "STK")).with_cost(
            rustledger_core::CostSpec::empty()
                .with_number(rustledger_core::CostNumber::PerUnit { value: cost })
                .with_currency("USD"),
        )
    }

    #[test]
    fn structure_zero_cost_is_not_negative() {
        // A zero cost must NOT raise NegativeCost. Kills `<` -> `<=`.
        let txn = Transaction::new(d(2024, 1, 1), "zero cost")
            .with_synthesized_posting(cost_posting(dec!(0)));
        let mut errs = Vec::new();
        validate_transaction_structure(&txn, &mut errs);
        assert!(
            !has(&errs, ErrorCode::NegativeCost),
            "a zero cost is not negative: {errs:?}"
        );
    }

    #[test]
    fn structure_negative_cost_errors() {
        let txn = Transaction::new(d(2024, 1, 1), "neg cost")
            .with_synthesized_posting(cost_posting(dec!(-5)));
        let mut errs = Vec::new();
        validate_transaction_structure(&txn, &mut errs);
        assert!(
            has(&errs, ErrorCode::NegativeCost),
            "a negative cost must error: {errs:?}"
        );
    }
}
