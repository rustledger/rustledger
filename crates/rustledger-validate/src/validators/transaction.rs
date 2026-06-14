//! Transaction validation.

use rust_decimal::Decimal;
use rustc_hash::FxHashMap;
use rustledger_core::{Amount, BookingMethod, Inventory, Posting, ReductionScope, Transaction};
use std::collections::HashMap;

use crate::error::{ErrorCode, ValidationError};
use crate::{AccountState, LedgerState, ValidationOptions};

/// Validate a Transaction directive.
/// Early-phase transaction validation — runs on pre-booking directives.
///
/// Includes only checks that don't require booked amounts:
/// structure (posting count), account-presence (E1001), and
/// account-lifecycle (used-before-open / used-after-close).
///
/// Currency-constraint checking (which calls `posting.amount()`) is
/// deliberately deferred to the late phase, since elided postings have
/// `units: None` here.
pub fn validate_transaction_early(
    state: &LedgerState,
    txn: &Transaction,
    errors: &mut Vec<ValidationError>,
) {
    if !validate_transaction_structure(txn, errors) {
        return;
    }
    // Inline the presence + lifecycle subset of `validate_posting_accounts`
    // here — we don't want to run the currency check yet (deferred to late
    // phase so it sees filled units).
    for posting in &txn.postings {
        match state.accounts.get(&posting.account) {
            Some(account_state) => {
                validate_account_lifecycle(txn, posting, account_state, errors);
            }
            None => {
                errors.push(ValidationError::new(
                    ErrorCode::AccountNotOpen,
                    format!("Account {} was never opened", posting.account),
                    txn.date,
                ));
            }
        }
    }
}

/// Late-phase transaction validation — runs on post-booking directives.
///
/// Includes checks that need filled-in amounts: currency-constraint
/// enforcement on filled postings, tolerance calculation, balance
/// residual, and inventory updates (lot matching, capital gains).
pub fn validate_transaction_late(
    state: &mut LedgerState,
    txn: &Transaction,
    errors: &mut Vec<ValidationError>,
) {
    // Currency-constraint checks on filled postings. These need to run
    // late because they call `posting.amount()`, which is `None` for
    // elided postings until booking fills them in.
    //
    // Account-presence (E1001) already ran in the early phase; we
    // deliberately don't re-emit here, but we still need the account
    // state to enforce currency constraints — so skip the check rather
    // than re-flagging unopened accounts.
    for posting in &txn.postings {
        if let Some(account_state) = state.accounts.get(&posting.account) {
            validate_posting_currency(state, txn, posting, account_state, errors);
        }
    }

    // Compute tolerances and check transaction balance.
    let tolerances = calculate_tolerances(txn, &state.options);
    validate_transaction_balance(txn, &tolerances, errors);

    // Update inventories with booking validation
    update_inventories(state, txn, errors);
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
    // If >1 posting is missing an amount for the same currency, interpolation
    // is ambiguous. We detect this by looking at postings where `amount()` is
    // None AND the posting has no units at all (fully elided amount).
    {
        let mut missing_count: FxHashMap<Option<&rustledger_core::Currency>, u32> =
            FxHashMap::default();
        for posting in &txn.postings {
            if posting.amount().is_none() {
                // Group by the currency hint from partial units, or None for fully elided
                let currency = posting
                    .units
                    .as_ref()
                    .and_then(|u| u.as_amount())
                    .map(|a| &a.currency);
                *missing_count.entry(currency).or_default() += 1;
            }
        }
        // If any group has >1 missing, or there are multiple groups of missing amounts
        let total_missing: u32 = missing_count.values().sum();
        if total_missing > 1 {
            errors.push(ValidationError::new(
                ErrorCode::MultipleInterpolation,
                format!(
                    "Transaction has {total_missing} postings with missing amounts; at most one is allowed"
                ),
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
            let (label, value) = match cn {
                rustledger_core::CostNumber::PerUnit { value } => ("per-unit", value),
                rustledger_core::CostNumber::Total { value }
                | rustledger_core::CostNumber::PerUnitFromTotal(rustledger_core::BookedCost {
                    total: value,
                    ..
                }) => ("total", value),
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
    if txn.date < account_state.opened {
        errors.push(ValidationError::new(
            ErrorCode::AccountNotOpen,
            format!(
                "Account {} used on {} but not opened until {}",
                posting.account, txn.date, account_state.opened
            ),
            txn.date,
        ));
    }

    if let Some(closed) = account_state.closed
        && txn.date >= closed
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
///    `tolerance = units_quantum * cost_per_unit * tolerance_multiplier`
pub fn validate_transaction_balance(
    txn: &Transaction,
    tolerances: &HashMap<rustledger_core::Currency, Decimal>,
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

    // Fast path: use rust_decimal first. If ALL residuals are exactly zero,
    // the transaction definitely balances — skip the expensive BigDecimal
    // calculation. We only skip on exact zero (not "within tolerance")
    // because Decimal arithmetic can lose precision during cost/price
    // multiplication, potentially under-reporting a non-zero residual.
    let fast_residuals = rustledger_booking::calculate_residual(txn);
    let all_zero = fast_residuals
        .values()
        .all(|residual| *residual == Decimal::ZERO);

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

/// Calculate the quantum (smallest unit) of a decimal number based on its precision.
/// For example: 10.436 has quantum 0.001, 100.00 has quantum 0.01
pub fn decimal_quantum(value: Decimal) -> Decimal {
    let scale = value.scale();
    if scale == 0 {
        Decimal::ONE
    } else {
        Decimal::new(1, scale)
    }
}

/// Calculate per-currency tolerances for a transaction.
///
/// When `infer_tolerance_from_cost` is enabled, for each posting with a cost:
///   `tolerance = units_quantum * cost_per_unit * tolerance_multiplier`
///
/// The tolerance for each cost currency is the maximum of all such values
/// computed from postings with costs in that currency.
pub fn calculate_tolerances(
    txn: &Transaction,
    options: &ValidationOptions,
) -> HashMap<rustledger_core::Currency, Decimal> {
    // Pre-allocate for typical case (1-2 currencies)
    let mut tolerances: HashMap<rustledger_core::Currency, Decimal> =
        HashMap::with_capacity(txn.postings.len().min(4));

    // Default tolerance based on quantum of amounts in postings.
    // Only amounts with decimal places contribute (Python's `if expo < 0:` guard).
    // Integer amounts (scale=0) don't contribute — if all amounts for a currency
    // are integers, the tolerance for that currency stays at 0 (exact balance required).
    for posting in &txn.postings {
        if let Some(units) = posting.amount()
            && units.number.scale() > 0
        {
            let quantum = decimal_quantum(units.number);
            // Use half the quantum as base tolerance (like Python beancount)
            let base_tolerance = quantum * options.tolerance_multiplier;

            tolerances
                .entry(units.currency.clone())
                .and_modify(|t| *t = (*t).max(base_tolerance))
                .or_insert(base_tolerance);
        }
    }

    // Calculate cost-inferred tolerance if enabled.
    // In Python, cost/price tolerance is only computed for postings where units
    // have decimal places (expo < 0). The cost tolerance is ACCUMULATED (summed)
    // across postings, then max'd with the existing tolerance per currency.
    if options.infer_tolerance_from_cost {
        // Accumulated cost/price tolerances per currency
        let mut cost_tolerances: HashMap<rustledger_core::Currency, Decimal> = HashMap::new();

        for posting in &txn.postings {
            if let Some(units) = posting.amount() {
                // Only process postings with decimal amounts (Python: if expo < 0)
                if units.number.scale() == 0 {
                    continue;
                }
                let units_quantum = decimal_quantum(units.number);
                let tolerance = units_quantum * options.tolerance_multiplier;

                // Cost contribution — only per-unit cost feeds into
                // tolerance inference. `PerUnitFromTotal` and `PerUnit`
                // both expose a per-unit value via `per_unit()`.
                if let Some(cost_spec) = &posting.cost
                    && let Some(cost_per_unit) = cost_spec.number.and_then(|cn| cn.per_unit())
                    && let Some(cost_currency) = &cost_spec.currency
                {
                    let cost_tolerance = tolerance * cost_per_unit;
                    *cost_tolerances.entry(cost_currency.clone()).or_default() += cost_tolerance;
                }

                // Price contribution: only complete amounts contribute
                // (incomplete/empty price annotations are filled in by
                // interpolation later). `kind` (Unit vs Total) doesn't
                // change the tolerance math here — both use `tolerance *
                // price_amt.number`.
                if let Some(price) = &posting.price
                    && let Some(price_amt) = price
                        .amount
                        .as_ref()
                        .and_then(rustledger_core::IncompleteAmount::as_amount)
                {
                    let price_tolerance = tolerance * price_amt.number;
                    *cost_tolerances
                        .entry(price_amt.currency.clone())
                        .or_default() += price_tolerance;
                }
            }
        }

        // Merge cost tolerances: take max of existing and cost-inferred
        for (currency, cost_tol) in cost_tolerances {
            tolerances
                .entry(currency)
                .and_modify(|t| *t = (*t).max(cost_tol))
                .or_insert(cost_tol);
        }
    }

    // Apply per-currency default tolerances from `inferred_tolerance_default` option.
    // These act as a floor: if the computed tolerance for a currency is less than the
    // default, the default is used. The special key "*" applies to all currencies.
    if !options.inferred_tolerance_default.is_empty() {
        // Apply the wildcard default first (if any)
        if let Some(wildcard_default) = options.inferred_tolerance_default.get("*") {
            // Apply wildcard to all currencies that appear in the transaction
            for posting in &txn.postings {
                if let Some(units) = posting.amount() {
                    tolerances
                        .entry(units.currency.clone())
                        .and_modify(|t| *t = (*t).max(*wildcard_default))
                        .or_insert(*wildcard_default);
                }
            }
        }

        // Apply per-currency defaults (overrides wildcard for specific currencies)
        for (currency_str, default_tol) in &options.inferred_tolerance_default {
            if currency_str == "*" {
                continue;
            }
            let currency = rustledger_core::Currency::from(currency_str.as_str());
            tolerances
                .entry(currency)
                .and_modify(|t| *t = (*t).max(*default_tol))
                .or_insert(*default_tol);
        }
    }

    tolerances
}

/// Update inventories with booking validation for each posting.
pub fn update_inventories(
    state: &mut LedgerState,
    txn: &Transaction,
    errors: &mut Vec<ValidationError>,
) {
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

        // Use the same reduction detection as the booking engine: a posting
        // reduces inventory when the inventory has cost-bearing positions with
        // the opposite sign for the same currency. Simple (no-cost) positions
        // are ignored. This correctly handles sell-to-open (selling into empty
        // inventory) as an augmentation, not a reduction.
        //
        // Under `option "booking_method" "NONE"` (issue #1182), every
        // posting is an augmentation — NONE accumulates positions
        // without lot matching. Mirrors the parallel guards in
        // `rustledger-booking::book::book` and `BookingEngine::apply`.
        // Without this gate, the validator's independent lot-matching
        // pass would re-raise the ambiguous/no-matching-lot errors
        // the booker just decided to skip.
        let is_reduction = booking_method != BookingMethod::None
            && posting.cost.is_some()
            && inv.is_reduced_by(units, ReductionScope::CostBearingOnly);

        if is_reduction {
            process_inventory_reduction(inv, posting, units, booking_method, txn, errors);
        } else {
            process_inventory_addition(inv, posting, units, txn);
        }
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

    match inv.reduce(units, posting.cost.as_ref(), booking_method) {
        Ok(_) => {}
        Err(err) => {
            // On pre-booked directives, reduce() with a fully-specified cost
            // should not fail. If it does, report the error — this catches
            // bugs in the booking engine or standalone validation without booking.
            let (code, context) = match &err {
                rustledger_core::BookingError::InsufficientUnits { .. } => (
                    ErrorCode::InsufficientUnits,
                    format!("currency: {}", units.currency),
                ),
                rustledger_core::BookingError::AmbiguousMatch { .. } => (
                    ErrorCode::AmbiguousLotMatch,
                    "Specify cost, date, or label to disambiguate".to_string(),
                ),
                rustledger_core::BookingError::NoMatchingLot { .. }
                | rustledger_core::BookingError::CurrencyMismatch { .. } => (
                    ErrorCode::NoMatchingLot,
                    format!("cost spec: {:?}", posting.cost),
                ),
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
pub fn process_inventory_addition(
    inv: &mut Inventory,
    posting: &Posting,
    units: &Amount,
    txn: &Transaction,
) {
    let position = if let Some(cost_spec) = &posting.cost {
        if let Some(cost) = cost_spec.resolve(units.number, txn.date) {
            rustledger_core::Position::with_cost(units.clone(), cost)
        } else {
            rustledger_core::Position::simple(units.clone())
        }
    } else {
        rustledger_core::Position::simple(units.clone())
    };

    inv.add(position);
}

#[cfg(test)]
mod tolerance_tests {
    //! Direct unit tests for `decimal_quantum` and `calculate_tolerances`
    //! (#1309 cluster 3). The file had no tests, so the tolerance
    //! arithmetic and the per-currency default/floor logic went
    //! unasserted.
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
        assert_eq!(decimal_quantum(dec!(100.00)), dec!(0.01)); // scale 2
        assert_eq!(decimal_quantum(dec!(10.436)), dec!(0.001)); // scale 3
        assert_eq!(decimal_quantum(dec!(5)), dec!(1)); // scale 0 -> ONE
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

    #[test]
    fn tolerance_wildcard_default_applies_to_all_currencies() {
        let mut opts = ValidationOptions::default();
        opts.inferred_tolerance_default
            .insert("*".to_string(), dec!(0.2));
        let t = calculate_tolerances(
            &mk_txn(vec![Posting::new(
                "Assets:A",
                Amount::new(dec!(10.00), "USD"),
            )]),
            &opts,
        );
        assert_eq!(t.get(&cur("USD")), Some(&dec!(0.2)));
        assert_eq!(t.len(), 1, "only the USD currency should appear");
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

    fn usd_tol(t: Decimal) -> HashMap<rustledger_core::Currency, Decimal> {
        let mut m = HashMap::new();
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
