//! Beancount booking engine with interpolation.
//!
//! This crate provides:
//! - Transaction interpolation (filling in missing amounts)
//! - Transaction balancing verification
//! - Tolerance calculation
//!
//! # Interpolation
//!
//! When a transaction has exactly one posting per currency without an amount,
//! that amount can be calculated to make the transaction balance.
//!
//! ```ignore
//! use rustledger_booking::interpolate;
//!
//! // Transaction with one missing amount
//! // 2024-01-15 * "Groceries"
//! //   Expenses:Food  50.00 USD
//! //   Assets:Cash               <- amount inferred as -50.00 USD
//! ```

#![forbid(unsafe_code)]
#![warn(missing_docs)]

mod book;
mod interpolate;
mod pad;

pub use book::{
    BookedTransaction, BookingEngine, BookingError, CapitalGain, LedgerBookResult, book,
    book_transactions,
};
pub use interpolate::{
    InterpolationError, InterpolationResult, UnknownGroup, elided_unknown_groups, interpolate,
    interpolate_with_tolerance_map, interpolate_with_tolerances,
};
pub use pad::{
    PadError, PadResult, SYNTH_PAD_NARRATION_PREFIX, is_synthesized_pad, merge_with_padding,
    merge_with_padding_owned, merge_with_padding_spanned, pad_insertion_index, process_pads,
};

use bigdecimal::BigDecimal;
use rust_decimal::Decimal;
use rust_decimal::prelude::Signed;
use rustc_hash::FxHashMap;
use rustledger_core::{Amount, Currency, IncompleteAmount, Transaction};

/// Option knobs for [`transaction_tolerances`], mirroring the ledger options
/// that drive tolerance inference (`tolerance_multiplier`,
/// `infer_tolerance_from_cost`, `inferred_tolerance_default`).
#[derive(Debug, Clone)]
pub struct ToleranceOptions<'a> {
    /// Multiplier applied to each amount's quantum (beancount default 0.5).
    pub multiplier: Decimal,
    /// Whether per-unit costs and prices feed the tolerance (accumulated,
    /// then max'd per currency), per `option "infer_tolerance_from_cost"`.
    pub infer_from_cost: bool,
    /// Per-currency tolerance floors from `option "inferred_tolerance_default"`;
    /// the key `"*"` is a wildcard floor applied to every currency that
    /// appears as a posting UNIT currency in the transaction (a currency
    /// present only via cost/price inference gets no wildcard floor,
    /// though a named per-currency default still reaches it) — behavior
    /// inherited verbatim from the validator.
    pub defaults: &'a FxHashMap<String, Decimal>,
}

/// Owned counterpart of [`ToleranceOptions`].
///
/// For holders that outlive any one borrow — the booking engine carries one
/// across a whole ledger so every transaction it interpolates rounds against
/// the ledger's own knobs.
#[derive(Debug, Clone)]
pub struct TolerancePolicy {
    /// See [`ToleranceOptions::multiplier`].
    pub multiplier: Decimal,
    /// See [`ToleranceOptions::infer_from_cost`].
    pub infer_from_cost: bool,
    /// See [`ToleranceOptions::defaults`].
    pub defaults: FxHashMap<String, Decimal>,
}

impl Default for TolerancePolicy {
    /// Beancount's defaults: `inferred_tolerance_multiplier` 0.5,
    /// `infer_tolerance_from_cost` false, no `inferred_tolerance_default`.
    ///
    /// Written by hand rather than derived on purpose. A derived `Default`
    /// would give `multiplier: 0`, which reads downstream as "this currency
    /// has no tolerance" and would silently switch off both the balance
    /// check's slack and interpolation's quantization.
    fn default() -> Self {
        Self {
            multiplier: Decimal::new(5, 1),
            infer_from_cost: false,
            defaults: FxHashMap::default(),
        }
    }
}

impl TolerancePolicy {
    /// Borrowed view, for passing to [`transaction_tolerances`].
    #[must_use]
    pub const fn options(&self) -> ToleranceOptions<'_> {
        ToleranceOptions {
            multiplier: self.multiplier,
            infer_from_cost: self.infer_from_cost,
            defaults: &self.defaults,
        }
    }
}

/// Calculate the quantum (smallest unit) of a decimal number based on its precision.
/// For example: 10.436 has quantum 0.001, 100.00 has quantum 0.01
#[must_use]
pub fn decimal_quantum(value: Decimal) -> Decimal {
    let scale = value.scale();
    if scale == 0 {
        Decimal::ONE
    } else {
        Decimal::new(1, scale)
    }
}

/// Calculate per-currency balance tolerances for a transaction — the
/// canonical tolerance semantics used by the validation pipeline.
///
/// This is the tolerance model that decides whether a transaction balances
/// (beancount's `infer_tolerance_from_quantum`): each posting amount with
/// decimal places contributes `quantum(amount) x multiplier`, max'd per
/// currency; integer amounts contribute nothing (exact balance required).
///
/// When `infer_tolerance_from_cost` is enabled, each posting with a
/// per-unit cost (or price) contributes
/// `units_quantum * cost_per_unit * multiplier`; these contributions are
/// ACCUMULATED (summed) per cost currency across the transaction's
/// postings, and the accumulated value is then max'd against the base
/// quantum tolerance for that currency. (The doc used to claim the
/// per-posting maximum — the implementation, moved verbatim from the
/// validator, has always summed.)
#[must_use]
pub fn transaction_tolerances(
    txn: &Transaction,
    opts: &ToleranceOptions<'_>,
) -> FxHashMap<rustledger_core::Currency, Decimal> {
    // Pre-allocate for typical case (1-2 currencies)
    let mut tolerances: FxHashMap<rustledger_core::Currency, Decimal> =
        FxHashMap::with_capacity_and_hasher(txn.postings.len().min(4), Default::default());

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
            let base_tolerance = quantum * opts.multiplier;

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
    if opts.infer_from_cost {
        // Accumulated cost/price tolerances per currency
        let mut cost_tolerances: FxHashMap<rustledger_core::Currency, Decimal> =
            FxHashMap::with_capacity_and_hasher(txn.postings.len().min(4), Default::default());

        for posting in &txn.postings {
            if let Some(units) = posting.amount() {
                // Only process postings with decimal amounts (Python: if expo < 0)
                if units.number.scale() == 0 {
                    continue;
                }
                let units_quantum = decimal_quantum(units.number);
                let tolerance = units_quantum * opts.multiplier;

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
    // default, the default is used. The special key "*" floors every currency that
    // appears as a posting UNIT currency (not currencies present only via
    // cost/price inference — named defaults below reach those too).
    if !opts.defaults.is_empty() {
        // Apply the wildcard default first (if any)
        if let Some(wildcard_default) = opts.defaults.get("*") {
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
        for (currency_str, default_tol) in opts.defaults {
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

/// Calculate the tolerance for a bare set of amounts (low-level primitive).
///
/// Tolerance is the maximum of all individual amount tolerances, using each
/// amount's fixed [`Amount::inferred_tolerance`]. This is **not** the
/// pipeline's transaction-balancing tolerance: it ignores the ledger options
/// (`tolerance_multiplier`, `infer_tolerance_from_cost`,
/// `inferred_tolerance_default`). For the semantics that decide whether a
/// transaction balances, use [`transaction_tolerances`].
#[must_use]
pub fn calculate_tolerance(amounts: &[&Amount]) -> FxHashMap<Currency, Decimal> {
    // Pre-allocate for typical case (1-3 currencies per transaction)
    let mut tolerances: FxHashMap<Currency, Decimal> =
        FxHashMap::with_capacity_and_hasher(amounts.len().min(4), Default::default());

    for amount in amounts {
        let tol = amount.inferred_tolerance();
        tolerances
            .entry(amount.currency.clone())
            .and_modify(|t| *t = (*t).max(tol))
            .or_insert(tol);
    }

    tolerances
}

/// Extract the currency named in a posting's price annotation, if any.
///
/// Returns the currency on `IncompleteAmount::Complete`. `CurrencyOnly`,
/// `NumberOnly`, and the bare-sigil form (`amount: None`) all return
/// `None` — they're shapes where the currency is either missing or
/// supplied later by interpolation. `kind` (Unit vs Total) is irrelevant
/// at this layer.
#[must_use]
pub(crate) fn price_currency_of(posting: &rustledger_core::Posting) -> Option<Currency> {
    posting
        .price
        .as_ref()
        .and_then(|p| p.amount.as_ref())
        .and_then(IncompleteAmount::as_amount)
        .map(|a| a.currency.clone())
}

/// Infer the cost currency from other postings in the transaction.
///
/// Python beancount infers cost currency from simple postings (those without
/// cost specs) when a cost is specified without a currency like `{100}`.
///
/// Currency inference follows this priority:
/// 1. An explicit currency in the cost specification itself (handled by the caller).
/// 2. A price annotation on a simple posting (the price currency takes precedence).
/// 3. The currency of other simple postings (units or currency-only amounts).
/// 4. The currency from a cost spec (e.g., `{0 USD}` for zero-cost items).
#[must_use]
pub(crate) fn infer_cost_currency_from_postings(transaction: &Transaction) -> Option<Currency> {
    // First pass: look for simple postings (no cost spec) - these take priority
    for posting in &transaction.postings {
        // Skip postings with cost specs in first pass
        if posting.cost.is_some() {
            continue;
        }

        // Get the currency from this posting's units
        if let Some(units) = &posting.units {
            match units {
                IncompleteAmount::Complete(amount) => {
                    // If this posting has a price annotation, the "real" currency
                    // is the price currency, not the units currency
                    if let Some(c) = price_currency_of(posting) {
                        return Some(c);
                    }
                    // Simple posting - use its currency
                    return Some(amount.currency.clone());
                }
                IncompleteAmount::CurrencyOnly(currency) => {
                    return Some(currency.clone());
                }
                IncompleteAmount::NumberOnly(_) => {}
            }
        }
    }

    // Second pass: look for cost spec currencies (e.g., `{0 USD}`)
    // This handles zero-cost postings where the cost currency should be used
    for posting in &transaction.postings {
        if let Some(cost) = &posting.cost
            && let Some(currency) = &cost.currency
        {
            return Some(currency.clone());
        }
    }

    None
}

/// Numeric backend for the posting-weight engine. `Decimal` is the fast path;
/// `BigDecimal` the arbitrary-precision path used near the `rust_decimal`
/// 28-digit ceiling. Both implement this trait so the balance-weight ladder
/// (cost-spec resolution + price formula) lives in exactly ONE place
/// ([`residual_weight`]): a new `CostNumber` variant or a sign fix then forces a
/// compile error / change at a single site instead of silently drifting between
/// the fast and precise residual functions.
///
/// `abs`/`signum` are taken on the source `Decimal` (exact — they add no
/// digits); only the *multiplications* run in `D`, so `D = BigDecimal`
/// reproduces the precise path's arithmetic byte-for-byte.
/// Arithmetic is CHECKED, not saturating. `rust_decimal` has a hard 96-bit
/// magnitude ceiling (~7.9e28) whose `+`/`*` panic on overflow, and clamping
/// instead is not an option here: `Decimal::MIN == -Decimal::MAX` exactly, so a
/// clamped debit and a clamped credit cancel to a residual of *precisely zero*
/// and the transaction certifies as balanced (PR #1890 shipped that and was
/// closed — a ledger off by 1e40 passed `rledger check`). So `D = Decimal`
/// reports "cannot represent" and the caller escalates to `D = BigDecimal`,
/// which has no ceiling and gives Python beancount's answer exactly.
trait WeightNum: Clone + Default {
    fn from_decimal(d: Decimal) -> Self;
    /// `None` when the product is outside this backend's range.
    fn checked_mul(self, rhs: Self) -> Option<Self>;
    /// `None` when the sum is outside this backend's range.
    fn checked_add(self, rhs: Self) -> Option<Self>;
}

impl WeightNum for Decimal {
    fn from_decimal(d: Decimal) -> Self {
        d
    }
    fn checked_mul(self, rhs: Self) -> Option<Self> {
        Self::checked_mul(self, rhs)
    }
    fn checked_add(self, rhs: Self) -> Option<Self> {
        Self::checked_add(self, rhs)
    }
}

impl WeightNum for BigDecimal {
    fn from_decimal(d: Decimal) -> Self {
        to_big(d)
    }
    // Arbitrary precision and unbounded magnitude: these never fail, which is
    // what makes BigDecimal a sound escalation target for the Decimal tier.
    fn checked_mul(self, rhs: Self) -> Option<Self> {
        Some(self * rhs)
    }
    fn checked_add(self, rhs: Self) -> Option<Self> {
        Some(self + rhs)
    }
}

/// Resolve the currency a posting's cost weight is denominated in: the explicit
/// cost currency, else the price currency, else `infer_currency()` (called
/// lazily — only when the first two are absent). Returns `None` if the posting
/// has no cost spec or no currency can be determined.
#[must_use]
pub(crate) fn cost_currency_of(
    posting: &rustledger_core::Posting,
    infer_currency: impl FnOnce() -> Option<Currency>,
) -> Option<Currency> {
    let cost_spec = posting.cost.as_ref()?;
    cost_spec
        .currency
        .clone()
        .or_else(|| price_currency_of(posting))
        .or_else(infer_currency)
}

/// The canonical per-posting **cost** weight contribution — the single
/// `CostNumber` ladder shared by [`residual_weight`] and `interpolate` (so the
/// "cost beats price" weight rule and a future `CostNumber` variant live in one
/// place rather than drifting between balance-checking and interpolation).
///
/// Returns `None` for a posting with no cost spec, an empty `{}` spec (no
/// determinable number), or when no cost currency resolves. `interpolate`
/// instantiates this at `Decimal`.
/// The weight arithmetic left this backend's range. Distinct from `Ok(None)`,
/// which means the posting legitimately contributes no cost weight.
struct Overflow;

fn cost_weight<D: WeightNum>(
    posting: &rustledger_core::Posting,
    units: &Amount,
    infer_currency: impl FnOnce() -> Option<Currency>,
) -> Result<Option<(Currency, D)>, Overflow> {
    let Some(cost_spec) = posting.cost.as_ref() else {
        return Ok(None);
    };
    // Match the number FIRST so an empty `{}` spec short-circuits without
    // resolving (and possibly inferring) the cost currency.
    let Some(number) = cost_spec.number.as_ref() else {
        return Ok(None);
    };
    let weight = cost_number_weight_generic::<D>(units.number, number).ok_or(Overflow)?;
    let Some(cost_curr) = cost_currency_of(posting, infer_currency) else {
        return Ok(None);
    };
    Ok(Some((cost_curr, weight)))
}

/// The `CostNumber`-variant weight arithmetic, generic over the numeric
/// backend — the single implementation behind [`cost_number_weight`] and
/// [`cost_weight`]. A new `CostNumber` variant forces a change HERE and
/// nowhere else.
fn cost_number_weight_generic<D: WeightNum>(
    units_number: Decimal,
    number: &rustledger_core::CostNumber,
) -> Option<D> {
    let signum = units_number.signum();
    // `PerUnitFromTotal` and `Total` both carry a preserved total — using it
    // avoids the division-then-multiplication precision loss of recomputing from
    // `per_unit`. `PerUnit` goes through multiplication.
    match *number {
        rustledger_core::CostNumber::Total { value: total } => {
            D::from_decimal(total).checked_mul(D::from_decimal(signum))
        }
        rustledger_core::CostNumber::PerUnitFromTotal(b) => {
            D::from_decimal(b.total).checked_mul(D::from_decimal(signum))
        }
        rustledger_core::CostNumber::PerUnit { value: per_unit } => {
            D::from_decimal(units_number).checked_mul(D::from_decimal(per_unit))
        }
        // Compound `{a # b}` (beancount compound_amount): the cost totals
        // `N*a + b`, so the weight is the per-unit product (sign embedded
        // in `units`) plus the signed lump total (#1700).
        //
        // DELIBERATE DIVERGENCE FROM PYTHON — see #1943.
        //
        // We compute the weight from what the author WROTE. beancount instead
        // treats a `#` cost spec as incomplete and SOLVES it from the residual,
        // discarding the written number when the two disagree:
        //
        //   10 AAPL {# 9.95 USD} against -9.95 USD    both -> 0.995   (agree)
        //   10 AAPL {# 9.95 USD} against -19.90 USD   beancount -> 1.990
        //                                             ours      -> 0.995, E3001
        //   20 AAPL {45.23 # USD} against -45.23 USD  beancount -> 2.2615
        //                                             ours      -> 45.23,  E3001
        //
        // In the second row the user typed a total of 9.95 and beancount books
        // 19.90. Silently replacing a cost basis is the failure an accounting
        // tool should least want: it propagates into capital gains and every
        // cost-denominated report with nothing to indicate it. E3001 instead
        // says the file is inconsistent, which is true and actionable.
        //
        // The cost of the deviation: we reject three `parser-lima` fixtures
        // beancount accepts. No real-world file in the compat corpus hits it.
        // Registered in `KNOWN_POSTING_DIVERGENCES` (scripts/compat-values.py)
        // so the oracle does not re-report it, and pinned by
        // `compound_cost_uses_the_written_numbers` below.
        rustledger_core::CostNumber::Compound { per_unit, total } => {
            let w = D::from_decimal(units_number).checked_mul(D::from_decimal(per_unit))?;
            w.checked_add(D::from_decimal(total).checked_mul(D::from_decimal(signum))?)
        }
    }
}

/// The canonical weight of a cost number: what `units_number` of a posting
/// with this cost spec contributes to the transaction balance, in the cost
/// currency (Beancount's "weight" of a costed posting).
///
/// This is the exact arithmetic the balance validator's residual uses —
/// `Total`/`PerUnitFromTotal` take the preserved total (sign following
/// units), avoiding the division-then-multiplication precision loss of
/// recomputing from `per_unit` (#1106/#1113); `Compound {a # b}` totals
/// `N·a + b` (#1700). Consumers surfacing a per-posting weight (BQL `weight`
/// column, `currency_accounts` grouping) MUST use this rather than re-derive
/// the ladder, or they drift from `rledger check` on those shapes.
///
/// Returns `None` when the weight is outside `rust_decimal`'s ~7.9e28 range.
/// Callers that need an answer regardless must recompute in `BigDecimal` (as
/// the balance validator does); callers that merely display a weight should
/// omit it rather than substitute a clamped figure, which would be reported as
/// exact.
///
/// Deliberately checked rather than saturating: `Decimal::MIN` is exactly
/// `-Decimal::MAX`, so clamped opposite-sign weights cancel to a residual of
/// zero and an unbalanced transaction certifies as balanced (#1863).
#[must_use]
pub fn cost_number_weight(
    units_number: Decimal,
    number: &rustledger_core::CostNumber,
) -> Option<Decimal> {
    cost_number_weight_generic::<Decimal>(units_number, number)
}

/// The canonical weight of a price annotation: what `units_number` of a
/// posting priced `@`/`@@` contributes to the transaction balance, in the
/// price currency.
///
/// `@` (per-unit): `|units| × price × sign(units)`. `@@` (total): the price
/// is a positive magnitude in the source, so the weight is
/// `price × sign(units)` — credit-side postings flip to `−price`
/// (issue #1052). Zero units weigh zero for both kinds. Same single-source
/// rule as [`cost_number_weight`], including its `None`-on-overflow contract.
#[must_use]
pub fn price_weight(
    units_number: Decimal,
    price_number: Decimal,
    kind: rustledger_core::PriceKind,
) -> Option<Decimal> {
    price_weight_generic::<Decimal>(units_number, price_number, kind)
}

/// The canonical weight of a whole posting: the amount, **in the currency the
/// posting contributes to the transaction balance**, that this posting is worth.
///
/// This is the *ladder* that selects between the two weight arithmetics
/// ([`cost_number_weight`] and [`price_weight`]), matching Beancount — cost
/// beats price:
///
/// - a cost spec with both a number and an explicit currency → cost weight, in
///   the cost currency;
/// - else a complete price annotation → price weight, in the price currency;
/// - else the units themselves, in the units currency.
///
/// `None` for a posting whose units are unresolved (elided, pre-interpolation).
///
/// Consumers that surface a per-posting weight — the BQL `weight` column, the
/// budget report's actual-spend accrual — MUST call this rather than re-derive
/// the ladder, so they cannot drift from each other.
///
/// # This is NOT byte-for-byte the `rledger check` rule
///
/// [`calculate_residual`]'s `residual_weight` is the balance validator's rule
/// and differs in two places, both of which only matter for cost specs:
///
/// - a cost spec with a number but NO explicit currency: the residual infers
///   the cost currency from the transaction's other postings
///   (`infer_cost_currency_from_postings`); this function falls through to the
///   price branch instead;
/// - a bare `{}` with no determinable number: the residual contributes NOTHING
///   and deliberately refuses to fall through to a price annotation, because
///   the canonical weight of a cost-tracked posting is `units × cost`, not
///   `units × price` (issue #1026); this function does fall through.
///
/// Aligning the two would change BQL `weight` results, so it is deliberately
/// left alone here — but do not describe this as "the rule `check` uses".
///
/// Also `None` when the weight leaves `rust_decimal`'s range: BQL's `weight`
/// column and the budget report render this figure directly, and a clamped
/// number displayed as an exact total is worse than a blank cell.
#[must_use]
pub fn posting_weight(posting: &rustledger_core::Posting) -> Option<Amount> {
    let units = posting.amount()?;
    if let Some(cost_spec) = &posting.cost
        && let Some(number) = &cost_spec.number
        && let Some(currency) = cost_spec.currency.clone()
    {
        return Some(Amount::new(
            cost_number_weight(units.number, number)?,
            currency,
        ));
    }
    if let Some(price_ann) = &posting.price
        && let Some(price_amt) = price_ann.amount()
    {
        return Some(Amount::new(
            price_weight(units.number, price_amt.number, price_ann.kind)?,
            price_amt.currency.clone(),
        ));
    }
    Some(units.clone())
}

/// The price-annotation weight arithmetic, generic over the numeric backend —
/// the single implementation behind [`price_weight`] and [`residual_weight`].
///
/// The expanded `abs * price * signum` form (rather than `units * price`) is
/// kept so `D = Decimal` and `D = BigDecimal` reproduce the pre-refactor
/// residual arithmetic exactly.
fn price_weight_generic<D: WeightNum>(
    units_number: Decimal,
    price_number: Decimal,
    kind: rustledger_core::PriceKind,
) -> Option<D> {
    let signum = units_number.signum();
    match kind {
        rustledger_core::PriceKind::Unit => D::from_decimal(units_number.abs())
            .checked_mul(D::from_decimal(price_number))?
            .checked_mul(D::from_decimal(signum)),
        rustledger_core::PriceKind::Total => {
            D::from_decimal(price_number).checked_mul(D::from_decimal(signum))
        }
    }
}

/// The canonical per-posting balance weight, summed per currency, generic over
/// the numeric backend. Single source of truth for [`calculate_residual`] and
/// [`calculate_residual_precise`].
///
/// DELIBERATELY not the same rule as [`posting_weight`], which serves BQL's
/// `weight` column and the budget report. That one infers a cost number with no
/// currency and refuses to let a bare `{}` fall through to a price; this one
/// does neither, because #1026 turns on it — aligning the two flips E3001
/// pass/fail for every ledger containing a bare-cost-plus-price posting. See
/// `posting_weight`'s docs for the other half of this pair. Revisit only if
/// #1026 is settled such that one rule can serve both.
///
/// Weight rule (Beancount): a cost spec puts the weight in the cost currency
/// (`cost` beats `price`); else a price annotation puts it in the price
/// currency; else the weight is the units themselves.
fn residual_weight<D: WeightNum>(transaction: &Transaction) -> Option<FxHashMap<Currency, D>> {
    // Pre-allocate for typical case (1-2 currencies per transaction)
    let mut residuals: FxHashMap<Currency, D> =
        FxHashMap::with_capacity_and_hasher(transaction.postings.len().min(4), Default::default());

    // Lazily compute inferred currency only when needed (most transactions don't need it)
    let mut inferred_cost_currency: Option<Option<Currency>> = None;
    let get_inferred_currency = |cache: &mut Option<Option<Currency>>| -> Option<Currency> {
        cache
            .get_or_insert_with(|| infer_cost_currency_from_postings(transaction))
            .clone()
    };

    for posting in &transaction.postings {
        // Only process complete amounts
        let Some(IncompleteAmount::Complete(units)) = &posting.units else {
            continue;
        };

        // Accumulate `amount` into `currency`'s running residual, or bail out
        // of the whole computation if the sum leaves `D`'s range.
        macro_rules! accumulate {
            ($currency:expr, $amount:expr) => {{
                let slot = residuals.entry($currency).or_default();
                *slot = std::mem::take(slot).checked_add($amount)?;
            }};
        }

        // Determine the "weight" of this posting for balance purposes.
        let cost_contribution = cost_weight::<D>(posting, units, || {
            get_inferred_currency(&mut inferred_cost_currency)
        })
        .ok()?;

        if let Some((currency, amount)) = cost_contribution {
            // Cost-based posting: weight is in the cost currency
            accumulate!(currency, amount);
        } else if posting.cost.is_some() {
            // Cost spec exists but has no determinable cost number
            // (e.g., empty `{}`). The CANONICAL weight of a cost-tracked
            // posting is `units × cost`, NOT `units × price` — even if a
            // price annotation is present. Falling through to the price
            // branch would silently produce a balanced residual using
            // the wrong weight (issue #1026). Skip contribution; the
            // booking pass will resolve via lot matching, and the
            // interpolation rule (in `interpolate.rs`) accounts for
            // this posting as one cost-unknown for its currency group.
        } else if let Some(price) = &posting.price {
            // Price annotation: converts units to the price currency.
            if let Some(amt) = price.amount.as_ref().and_then(IncompleteAmount::as_amount) {
                let signed = price_weight_generic::<D>(units.number, amt.number, price.kind)?;
                accumulate!(amt.currency.clone(), signed);
            } else {
                // Incomplete or bare-sigil price annotation — can't
                // calculate a price-currency conversion, fall back to units.
                accumulate!(units.currency.clone(), D::from_decimal(units.number));
            }
        } else {
            // Simple posting: weight is just the units
            accumulate!(units.currency.clone(), D::from_decimal(units.number));
        }
    }

    Some(residuals)
}

/// Calculate the residual (imbalance) of a transaction.
///
/// Returns a map of currency -> residual amount.
/// A balanced transaction has all residuals within tolerance.
///
/// # TLA+ Specification
///
/// Implements balance checking from `DoubleEntry.tla`:
/// - Invariant: `TransactionsBalance` - For every transaction, `sum(postings) = 0`
/// - Each currency is checked independently
/// - A non-zero residual indicates a violation of double-entry bookkeeping
///
/// See: `spec/tla/DoubleEntry.tla`
#[must_use]
// clippy::implicit_hasher still fires for a concrete `FxBuildHasher` (it wants
// the fn generic over `S: BuildHasher`); the explicit fast hasher is the point.
#[allow(clippy::implicit_hasher)]
/// Returns `None` when the residual arithmetic leaves `rust_decimal`'s ~7.9e28
/// range. `None` means "unknown", NOT "balanced" — a caller must escalate to
/// [`calculate_residual_precise`], which cannot fail. Treating `None` as an
/// empty map would certify an arbitrarily unbalanced transaction as clean.
pub fn calculate_residual(transaction: &Transaction) -> Option<FxHashMap<Currency, Decimal>> {
    residual_weight::<Decimal>(transaction)
}

/// Convert a `rust_decimal::Decimal` to `BigDecimal` for arbitrary-precision arithmetic.
///
/// Individual `Decimal` values are representable exactly (≤28 significant digits).
/// The precision loss only occurs during arithmetic, so converting before operations
/// preserves full precision.
fn to_big(d: Decimal) -> BigDecimal {
    use std::str::FromStr;
    // rust_decimal Display is exact; BigDecimal FromStr handles any decimal string
    BigDecimal::from_str(&d.to_string()).expect("Decimal always produces valid decimal string")
}

/// Calculate the residual of a transaction using arbitrary-precision arithmetic.
///
/// This mirrors [`calculate_residual`] but uses `BigDecimal` to avoid precision loss
/// when amounts have near-28-digit precision. `rust_decimal` is limited to 28-29
/// significant digits; this function handles arbitrary precision correctly.
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn calculate_residual_precise(transaction: &Transaction) -> FxHashMap<Currency, BigDecimal> {
    // `BigDecimal`'s `WeightNum` ops are total, so `residual_weight` cannot
    // return `None` here. This is the property that makes the Decimal tier's
    // `None` recoverable rather than fatal.
    residual_weight::<BigDecimal>(transaction)
        .expect("BigDecimal arithmetic is unbounded and cannot overflow")
}

/// Check if a transaction is balanced within the given tolerances
/// (low-level primitive).
///
/// The caller supplies the tolerance map. The validation pipeline does not
/// call this: it computes tolerances via [`transaction_tolerances`] and
/// escalates non-zero residuals to [`calculate_residual_precise`] (the
/// two-tier check from #1240). Pair this with [`transaction_tolerances`] —
/// not [`calculate_tolerance`] — if you need pipeline-equivalent balancing.
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn is_balanced(transaction: &Transaction, tolerances: &FxHashMap<Currency, Decimal>) -> bool {
    // Overflow in the fast tier means this tier has no answer, NOT that the
    // transaction is unbalanced: accumulation is order-dependent, so postings
    // of `[+7e28, +7e28, -7e28, -7e28]` overflow the running sum even though
    // they total exactly zero. Returning `false` is therefore a conservative
    // under-approximation — it can report a balanced transaction as unbalanced,
    // never the reverse.
    //
    // Acceptable only because this is a low-level primitive that the pipeline
    // does not use (see the doc above): `validate_transaction_balance`
    // escalates to `calculate_residual_precise`, which has no ceiling and gets
    // the exact answer. A caller who needs that must do the same rather than
    // trust this `false`.
    let Some(residuals) = calculate_residual(transaction) else {
        return false;
    };

    for (currency, residual) in residuals {
        let tolerance = tolerances.get(&currency).copied().unwrap_or(Decimal::ZERO); // Default 0 (exact balance for integer-only currencies)

        if residual.abs() > tolerance {
            return false;
        }
    }

    true
}

/// Normalize total prices (`@@`) to per-unit prices (`@`) on a transaction.
///
/// This converts a `PriceAnnotation` with `PriceKind::Total` to one with
/// `PriceKind::Unit` by dividing
/// the total price by the number of units. This should be called AFTER validation
/// (balance checking) to preserve exact total prices for precise residual calculation.
///
/// Matches Python beancount behavior where `@@` is converted to `@`.
pub fn normalize_prices(txn: &mut Transaction) {
    use rustledger_core::{PriceAnnotation, PriceKind};

    for posting in &mut txn.postings {
        if let (Some(IncompleteAmount::Complete(units)), Some(price)) =
            (&posting.units, &posting.price)
            && price.kind == PriceKind::Total
        {
            let normalized = match price.amount.as_ref().and_then(IncompleteAmount::as_amount) {
                Some(total_amount) if !units.number.is_zero() => {
                    let per_unit = total_amount.number / units.number.abs();
                    Some(PriceAnnotation::unit(Amount::new(
                        per_unit,
                        &total_amount.currency,
                    )))
                }
                Some(_) => None, // units.number is zero — leave alone
                None => {
                    // Empty (`@@` with no amount) — Total → Unit sigil swap.
                    // `total_incomplete` with no complete amount cannot be
                    // normalized because we don't have a number to divide.
                    if price.amount.is_none() {
                        Some(PriceAnnotation::unit_empty())
                    } else {
                        None
                    }
                }
            };
            if let Some(normalized_price) = normalized {
                posting.price = Some(normalized_price);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{CostSpec, IncompleteAmount, NaiveDate, Posting, PriceAnnotation};

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        rustledger_core::naive_date(year, month, day).unwrap()
    }

    // =========================================================================
    // cost_number_weight / price_weight — the public single-source arithmetic
    // =========================================================================

    #[test]
    fn cost_number_weight_covers_all_variants() {
        use rustledger_core::{BookedCost, CostNumber};
        // PerUnit: units × per_unit.
        assert_eq!(
            cost_number_weight(dec!(10), &CostNumber::PerUnit { value: dec!(5.00) }),
            Some(dec!(50.00)),
        );
        // Total: preserved total, sign following units.
        assert_eq!(
            cost_number_weight(
                dec!(3),
                &CostNumber::Total {
                    value: dec!(100.00)
                }
            ),
            Some(dec!(100.00)),
        );
        assert_eq!(
            cost_number_weight(
                dec!(-3),
                &CostNumber::Total {
                    value: dec!(100.00)
                }
            ),
            Some(dec!(-100.00)),
        );
        // PerUnitFromTotal: the preserved total EXACTLY — not per_unit × units,
        // which for 100/3 would give 99.99999... at the 28-digit ceiling.
        let booked = CostNumber::PerUnitFromTotal(BookedCost {
            per_unit: dec!(100.00) / dec!(3),
            total: dec!(100.00),
        });
        assert_eq!(cost_number_weight(dec!(3), &booked), Some(dec!(100.00)));
        assert_eq!(cost_number_weight(dec!(-3), &booked), Some(dec!(-100.00)));
        // Compound {a # b}: N·a + b, lump signed with units (#1700).
        let compound = CostNumber::Compound {
            per_unit: dec!(5.00),
            total: dec!(10.00),
        };
        assert_eq!(cost_number_weight(dec!(10), &compound), Some(dec!(60.00)));
        assert_eq!(cost_number_weight(dec!(-10), &compound), Some(dec!(-60.00)));
    }

    /// #1943: a compound `{a # b}` cost weighs what the AUTHOR WROTE.
    ///
    /// Deliberately stricter than Python. beancount treats a `#` spec as
    /// incomplete and solves it from the residual, so `{# 9.95 USD}` on 10
    /// units against -19.90 cash books a per-unit cost of 1.990 — discarding
    /// the 9.95 the user typed. We weigh the written total and let the balance
    /// validator report the inconsistency as E3001.
    ///
    /// Pinned here because the divergence is easy to "fix" by accident: making
    /// the weight follow the residual would make three parser-lima fixtures
    /// pass and would silently reintroduce cost bases the user never wrote.
    #[test]
    fn compound_cost_uses_the_written_numbers() {
        use rust_decimal_macros::dec;
        use rustledger_core::CostNumber;
        // `{# 9.95}` — per-unit 0, total 9.95, 10 units.
        assert_eq!(
            cost_number_weight(
                dec!(10),
                &CostNumber::Compound {
                    per_unit: dec!(0),
                    total: dec!(9.95),
                }
            ),
            Some(dec!(9.95)),
            "the weight is the WRITTEN total, not one solved from the residual",
        );
        // `{45.23 # }` — per-unit 45.23, total 0, 20 units.
        assert_eq!(
            cost_number_weight(
                dec!(20),
                &CostNumber::Compound {
                    per_unit: dec!(45.23),
                    total: dec!(0),
                }
            ),
            Some(dec!(904.60)),
            "a written per-unit stays per-unit; beancount would divide by units",
        );
    }

    #[test]
    fn price_weight_unit_and_total_signs() {
        use rustledger_core::PriceKind;
        // `@` per-unit: units × price, sign through units.
        assert_eq!(
            price_weight(dec!(10), dec!(1.50), PriceKind::Unit),
            Some(dec!(15.00)),
        );
        assert_eq!(
            price_weight(dec!(-10), dec!(1.50), PriceKind::Unit),
            Some(dec!(-15.00)),
        );
        // `@@` total: positive magnitude in source, sign follows units —
        // the #1052 credit-side flip.
        assert_eq!(
            price_weight(dec!(10), dec!(15.00), PriceKind::Total),
            Some(dec!(15.00)),
        );
        assert_eq!(
            price_weight(dec!(-10), dec!(15.00), PriceKind::Total),
            Some(dec!(-15.00)),
        );
        // Zero units weigh zero for both kinds.
        assert_eq!(
            price_weight(dec!(0), dec!(15.00), PriceKind::Total),
            Some(dec!(0))
        );
    }

    // =========================================================================
    // Basic residual tests (existing)
    // =========================================================================

    #[test]
    fn test_calculate_residual_balanced() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-50.00), "USD"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    #[test]
    fn test_calculate_residual_unbalanced() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-45.00), "USD"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        assert_eq!(residual.get("USD"), Some(&dec!(5.00)));
    }

    #[test]
    fn test_is_balanced() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-50.00), "USD"),
            ));

        let tolerances = calculate_tolerance(&[
            &Amount::new(dec!(50.00), "USD"),
            &Amount::new(dec!(-50.00), "USD"),
        ]);

        assert!(is_balanced(&txn, &tolerances));
    }

    #[test]
    fn test_is_balanced_within_tolerance() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.004), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-50.00), "USD"),
            ));

        let tolerances = calculate_tolerance(&[
            &Amount::new(dec!(50.004), "USD"),
            &Amount::new(dec!(-50.00), "USD"),
        ]);

        // 0.004 is within tolerance of 0.005 (scale 2 -> 0.005)
        assert!(is_balanced(&txn, &tolerances));
    }

    #[test]
    fn test_is_balanced_detects_imbalance() {
        // Mutation guard (#1238): the existing is_balanced tests only
        // assert the TRUE (balanced) cases, so replacing the whole body
        // with `true` survived the suite — the balance check could be
        // wholly broken and no test would notice. Assert the FALSE case.
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-49.00), "USD"),
            ));
        // Residual is 1.00 USD against zero tolerance — clearly unbalanced.
        let mut tolerances = FxHashMap::default();
        tolerances.insert(Currency::from("USD"), Decimal::ZERO);
        assert!(
            !is_balanced(&txn, &tolerances),
            "a 1.00 USD residual with zero tolerance must be detected as unbalanced"
        );
    }

    #[test]
    fn test_is_balanced_at_exact_tolerance_boundary() {
        // Mutation guard (#1238): the comparison is `residual.abs() >
        // tolerance`, so a residual EXACTLY at the tolerance is balanced
        // (strict greater-than). This kills the `>`->`>=` and `>`->`==`
        // mutants, both of which would wrongly reject the boundary case.
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.01), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-50.00), "USD"),
            ));
        // Residual 0.01 exactly equals the tolerance: balanced under `>`.
        let mut tolerances = FxHashMap::default();
        tolerances.insert(Currency::from("USD"), dec!(0.01));
        assert!(
            is_balanced(&txn, &tolerances),
            "a residual exactly at the tolerance must be treated as balanced"
        );
    }

    #[test]
    fn test_calculate_tolerance() {
        let amounts = [
            Amount::new(dec!(100), "USD"),    // scale 0 -> tol 0.5
            Amount::new(dec!(50.00), "USD"),  // scale 2 -> tol 0.005
            Amount::new(dec!(25.000), "EUR"), // scale 3 -> tol 0.0005
        ];

        let refs: Vec<&Amount> = amounts.iter().collect();
        let tolerances = calculate_tolerance(&refs);

        // USD should use the max tolerance (0.5 from scale 0)
        assert_eq!(tolerances.get("USD"), Some(&dec!(0.5)));
        assert_eq!(tolerances.get("EUR"), Some(&dec!(0.0005)));
    }

    // =========================================================================
    // Cost-based residual tests
    // =========================================================================

    /// Test residual calculation with per-unit cost.
    /// Buy 10 AAPL at $150 each = $1500 total cost in USD.
    #[test]
    fn test_calculate_residual_with_per_unit_cost() {
        let txn = Transaction::new(date(2024, 1, 15), "Buy stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit {
                            value: dec!(150.00),
                        })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-1500.00), "USD"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Cost posting contributes 10 * 150 = 1500 USD
        // Cash posting contributes -1500 USD
        // Residual should be 0
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
        // AAPL should not appear in residuals (cost converts to USD)
        assert_eq!(residual.get("AAPL"), None);
    }

    /// Fitness function: the fast (`Decimal`) and precise (`BigDecimal`) residual
    /// paths now share one generic engine ([`residual_weight`]), so they must
    /// produce equal residuals per currency. Guards against a future
    /// re-specialization of one path drifting from the other. Exercises every
    /// weight arm in a single transaction.
    #[test]
    fn fast_and_precise_residual_agree_across_weight_arms() {
        use std::str::FromStr;

        let txn = Transaction::new(date(2024, 1, 15), "Every weight arm")
            // per-unit cost
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(150.00) })
                        .with_currency("USD"),
                ),
            )
            // total cost, negative units
            .with_synthesized_posting(
                Posting::new("Assets:Bond", Amount::new(dec!(-3), "BOND")).with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::Total { value: dec!(450.00) })
                        .with_currency("USD"),
                ),
            )
            // unit price
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(-100.00), "USD"))
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(0.85), "EUR"))),
            )
            // total price
            .with_synthesized_posting(
                Posting::new("Assets:GBP", Amount::new(dec!(20.00), "GBP"))
                    .with_price(PriceAnnotation::total(Amount::new(dec!(26.00), "EUR"))),
            )
            // simple
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-12.34), "USD")));

        let fast = calculate_residual(&txn).expect("fixture fits in Decimal");
        let precise = calculate_residual_precise(&txn);

        assert_eq!(
            fast.len(),
            precise.len(),
            "fast {fast:?} and precise {precise:?} cover different currency sets"
        );
        for (currency, fval) in &fast {
            let pval = precise.get(currency).expect("currency present in precise");
            // Compare via the precise value's string form parsed back to Decimal
            // (exact for these values) — avoids BigDecimal scale-sensitive `==`.
            let pval_as_dec = Decimal::from_str(&pval.to_string()).unwrap();
            assert_eq!(
                *fval, pval_as_dec,
                "fast and precise residual disagree for {currency}: {fval} vs {pval}"
            );
        }
    }

    /// Test residual calculation with total cost.
    /// Buy 10 AAPL with total cost of $1500.
    #[test]
    fn test_calculate_residual_with_total_cost() {
        let txn = Transaction::new(date(2024, 1, 15), "Buy stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::Total {
                            value: dec!(1500.00),
                        })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-1500.00), "USD"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Total cost posting contributes 1500 * signum(10) = 1500 USD
        // Cash posting contributes -1500 USD
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test residual calculation with total cost and negative units (sell).
    #[test]
    fn test_calculate_residual_with_total_cost_negative_units() {
        let txn = Transaction::new(date(2024, 1, 15), "Sell stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "AAPL")).with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::Total {
                            value: dec!(1500.00),
                        })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(1500.00), "USD"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Total cost with negative units: 1500 * signum(-10) = -1500 USD
        // Cash posting contributes +1500 USD
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test cost spec without amount/currency falls back to units.
    #[test]
    fn test_calculate_residual_cost_without_amount_skips() {
        // When a posting has an empty cost spec (e.g., `{}`) and no price annotation,
        // it doesn't contribute to the residual because the cost will be determined
        // by lot matching during booking. This matches Python beancount behavior.
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL"))
                    .with_cost(CostSpec::empty()), // Empty cost spec - doesn't contribute
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-10), "AAPL")));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Empty cost spec posting doesn't contribute, only the second posting does
        assert_eq!(residual.get("AAPL"), Some(&dec!(-10)));
    }

    /// Issue #1026: when an empty cost spec is paired with a price
    /// annotation (`{} @ price`), the residual computation must NOT
    /// fall through to using the price as the posting's weight. The
    /// canonical weight of a cost-tracked posting is `units × cost`,
    /// not `units × price`. Pre-fix, this branch produced a balanced
    /// residual using the wrong weight; the htsec compat fixture (and
    /// the interpolate.rs caller chain) was the visible victim.
    ///
    /// Pinned here at the lib.rs level so a future revert of the
    /// branch reordering would fail this test directly, independent
    /// of the interpolate.rs end-to-end tests.
    #[test]
    fn test_calculate_residual_empty_cost_spec_with_price_skips_not_uses_price() {
        let txn = Transaction::new(date(2024, 1, 15), "Sale, empty cost + price")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "HOOL"))
                    .with_cost(CostSpec::empty())
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(150),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(1500), "USD")));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Pre-fix: residual[USD] = 0 (price-as-weight contributed
        // -1500, cancelling cash's +1500).
        // Post-fix: residual[USD] = +1500 (cost-unknown skipped, only
        // cash contributes; the residual stays open for booking-pass
        // lot matching to resolve via cost basis).
        assert_eq!(residual.get("USD"), Some(&dec!(1500)));
    }

    /// Companion to the previous test for the `BigDecimal` variant.
    /// Same fix, same semantics.
    #[test]
    fn test_calculate_residual_precise_empty_cost_spec_with_price_skips_not_uses_price() {
        use bigdecimal::BigDecimal;
        use std::str::FromStr;

        let txn = Transaction::new(date(2024, 1, 15), "Sale, empty cost + price")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "HOOL"))
                    .with_cost(CostSpec::empty())
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(150),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(1500), "USD")));

        let residual = calculate_residual_precise(&txn);
        assert_eq!(
            residual.get("USD"),
            Some(&BigDecimal::from_str("1500").unwrap())
        );
    }

    // =========================================================================
    // Price annotation residual tests
    // =========================================================================

    /// Test residual with per-unit price annotation (@).
    /// -100 USD @ 0.85 EUR means we're converting 100 USD to EUR at 0.85 rate.
    #[test]
    fn test_calculate_residual_with_unit_price() {
        let txn = Transaction::new(date(2024, 1, 15), "Currency exchange")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(-100.00), "USD"))
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(0.85), "EUR"))),
            )
            .with_synthesized_posting(Posting::new("Assets:EUR", Amount::new(dec!(85.00), "EUR")));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Price posting: |-100| * 0.85 * signum(-100) = -85 EUR
        // EUR posting: +85 EUR
        // Total: 0 EUR
        assert_eq!(residual.get("EUR"), Some(&dec!(0)));
        // USD should not appear (converted to EUR)
        assert_eq!(residual.get("USD"), None);
    }

    /// Test residual with total price annotation (@@).
    #[test]
    fn test_calculate_residual_with_total_price() {
        let txn = Transaction::new(date(2024, 1, 15), "Currency exchange")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(-100.00), "USD"))
                    .with_price(PriceAnnotation::total(Amount::new(dec!(85.00), "EUR"))),
            )
            .with_synthesized_posting(Posting::new("Assets:EUR", Amount::new(dec!(85.00), "EUR")));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Total price: 85 * signum(-100) = -85 EUR
        // EUR posting: +85 EUR
        assert_eq!(residual.get("EUR"), Some(&dec!(0)));
    }

    /// Test residual with positive units and unit price.
    #[test]
    fn test_calculate_residual_with_unit_price_positive() {
        let txn = Transaction::new(date(2024, 1, 15), "Buy EUR")
            .with_synthesized_posting(
                Posting::new("Assets:EUR", Amount::new(dec!(85.00), "EUR"))
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(1.18), "USD"))),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:USD",
                Amount::new(dec!(-100.30), "USD"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Price posting: |85| * 1.18 * signum(85) = 100.30 USD
        // USD posting: -100.30 USD
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test `UnitIncomplete` price annotation with complete amount.
    #[test]
    fn test_calculate_residual_unit_incomplete_with_amount() {
        let txn = Transaction::new(date(2024, 1, 15), "Exchange")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(-100.00), "USD")).with_price(
                    PriceAnnotation::unit_incomplete(IncompleteAmount::Complete(Amount::new(
                        dec!(0.85),
                        "EUR",
                    ))),
                ),
            )
            .with_synthesized_posting(Posting::new("Assets:EUR", Amount::new(dec!(85.00), "EUR")));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        assert_eq!(residual.get("EUR"), Some(&dec!(0)));
    }

    /// Test `TotalIncomplete` price annotation with complete amount.
    #[test]
    fn test_calculate_residual_total_incomplete_with_amount() {
        let txn = Transaction::new(date(2024, 1, 15), "Exchange")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(-100.00), "USD")).with_price(
                    PriceAnnotation::total_incomplete(IncompleteAmount::Complete(Amount::new(
                        dec!(85.00),
                        "EUR",
                    ))),
                ),
            )
            .with_synthesized_posting(Posting::new("Assets:EUR", Amount::new(dec!(85.00), "EUR")));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        assert_eq!(residual.get("EUR"), Some(&dec!(0)));
    }

    /// Test `UnitIncomplete` without amount falls back to units.
    #[test]
    fn test_calculate_residual_unit_incomplete_no_amount_fallback() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(100.00), "USD")).with_price(
                    PriceAnnotation::unit_incomplete(IncompleteAmount::NumberOnly(dec!(0.85))),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:USD",
                Amount::new(dec!(-100.00), "USD"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Falls back to units since no currency in incomplete amount
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test `TotalIncomplete` without amount falls back to units.
    #[test]
    fn test_calculate_residual_total_incomplete_no_amount_fallback() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(100.00), "USD")).with_price(
                    PriceAnnotation::total_incomplete(IncompleteAmount::NumberOnly(dec!(85.00))),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:USD",
                Amount::new(dec!(-100.00), "USD"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test `UnitEmpty` price annotation falls back to units.
    #[test]
    fn test_calculate_residual_unit_empty_fallback() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(100.00), "USD"))
                    .with_price(PriceAnnotation::unit_empty()),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:USD",
                Amount::new(dec!(-100.00), "USD"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Falls back to units
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test `TotalEmpty` price annotation falls back to units.
    #[test]
    fn test_calculate_residual_total_empty_fallback() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:USD", Amount::new(dec!(100.00), "USD"))
                    .with_price(PriceAnnotation::total_empty()),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:USD",
                Amount::new(dec!(-100.00), "USD"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    // =========================================================================
    // Mixed and edge case tests
    // =========================================================================

    /// Test transaction with both cost and regular postings.
    #[test]
    fn test_calculate_residual_mixed_cost_and_simple() {
        let txn = Transaction::new(date(2024, 1, 15), "Buy with fee")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit {
                            value: dec!(150.00),
                        })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Expenses:Fees",
                Amount::new(dec!(10.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-1510.00), "USD"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // 10 * 150 + 10 - 1510 = 0
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test sell with cost basis and capital gains.
    #[test]
    fn test_calculate_residual_sell_with_gains() {
        let txn = Transaction::new(date(2024, 6, 15), "Sell stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "AAPL"))
                    .with_cost(
                        CostSpec::empty()
                            .with_number(rustledger_core::CostNumber::PerUnit {
                                value: dec!(150.00),
                            })
                            .with_currency("USD"),
                    )
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(175.00), "USD"))),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(1750.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Income:CapitalGains",
                Amount::new(dec!(-250.00), "USD"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Stock posting with cost: -10 * 150 = -1500 USD (cost takes precedence)
        // Cash: +1750 USD
        // Gains: -250 USD
        // Total: -1500 + 1750 - 250 = 0
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test multi-currency transaction with costs.
    #[test]
    fn test_calculate_residual_multi_currency_with_cost() {
        let txn = Transaction::new(date(2024, 1, 15), "Multi-currency")
            .with_synthesized_posting(
                Posting::new("Assets:Stock:US", Amount::new(dec!(10), "AAPL")).with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit {
                            value: dec!(150.00),
                        })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(
                Posting::new("Assets:Stock:EU", Amount::new(dec!(5), "SAP")).with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit {
                            value: dec!(100.00),
                        })
                        .with_currency("EUR"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash:USD",
                Amount::new(dec!(-1500.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash:EUR",
                Amount::new(dec!(-500.00), "EUR"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
        assert_eq!(residual.get("EUR"), Some(&dec!(0)));
    }

    /// Test that incomplete units (auto postings) are skipped.
    #[test]
    fn test_calculate_residual_skips_incomplete_units() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash")); // No units

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Only the complete posting is counted
        assert_eq!(residual.get("USD"), Some(&dec!(50.00)));
    }

    // =========================================================================
    // Cost currency inference tests (issue #203)
    // =========================================================================

    /// Test cost currency is inferred from other postings.
    /// This is the exact case from issue #203.
    #[test]
    fn test_calculate_residual_infers_cost_currency_from_other_posting() {
        // 2026-01-01 * "Opening balance"
        //   Assets:Vanguard:IRA:Trad:VFIFX  10 VFIFX {100}
        //   Equity:Opening-Balances      -1000 USD
        //
        // Python beancount infers the cost currency as USD from the second posting.
        let txn = Transaction::new(date(2026, 1, 1), "Opening balance")
            .with_synthesized_posting(
                Posting::new(
                    "Assets:Vanguard:IRA:Trad:VFIFX",
                    Amount::new(dec!(10), "VFIFX"),
                )
                .with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(100) }),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Equity:Opening-Balances",
                Amount::new(dec!(-1000), "USD"),
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Cost posting should contribute 10 * 100 = 1000 USD (inferred from other posting)
        // Equity posting contributes -1000 USD
        // Residual should be 0
        assert_eq!(
            residual.get("USD"),
            Some(&dec!(0)),
            "Should balance when cost currency is inferred from other posting"
        );
        // VFIFX should not appear in residuals
        assert_eq!(residual.get("VFIFX"), None);
    }

    /// Test cost currency inference with total cost.
    #[test]
    fn test_calculate_residual_infers_cost_currency_total_cost() {
        // 10 VFIFX {{1000}} with -1000 USD posting
        let txn = Transaction::new(date(2026, 1, 1), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "VFIFX")).with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::Total { value: dec!(1000) }),
                ),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1000), "USD")));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        assert_eq!(residual.get("USD"), Some(&dec!(0)));
    }

    /// Test that explicit cost currency takes precedence over inference.
    #[test]
    fn test_calculate_residual_explicit_cost_currency_takes_precedence() {
        // If cost has explicit currency, don't infer from other postings
        let txn = Transaction::new(date(2026, 1, 1), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL")).with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(100) })
                        .with_currency("EUR"), // Explicit EUR
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-1000), "USD"), // USD posting
            ));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Should use EUR (explicit) not USD (from other posting)
        assert_eq!(residual.get("EUR"), Some(&dec!(1000)));
        assert_eq!(residual.get("USD"), Some(&dec!(-1000)));
    }

    /// Test that price annotation takes precedence over other posting inference.
    #[test]
    fn test_calculate_residual_price_annotation_takes_precedence() {
        // If cost has price annotation, use that currency
        let txn = Transaction::new(date(2026, 1, 1), "Test")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "AAPL"))
                    .with_cost(
                        CostSpec::empty()
                            .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(100) }),
                    )
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(105), "EUR"))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1000), "USD")));

        let residual = calculate_residual(&txn).expect("fixture fits in Decimal");
        // Should use EUR (from price annotation) not USD (from other posting)
        assert_eq!(residual.get("EUR"), Some(&dec!(1000)));
        assert_eq!(residual.get("USD"), Some(&dec!(-1000)));
    }

    // =========================================================================
    // infer_cost_currency_from_postings tests
    // =========================================================================

    /// Test that cost spec currency is used as fallback when no simple postings exist.
    #[test]
    fn test_infer_cost_currency_from_cost_spec() {
        // Transaction with only cost-spec posting - should get currency from cost spec
        let txn = Transaction::new(date(2022, 4, 16), "Free tokens")
            .with_synthesized_posting(
                Posting::new("Assets:Crypto", Amount::new(dec!(100), "TOKEN")).with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(0) })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Income:Bonus"));

        let inferred = infer_cost_currency_from_postings(&txn);
        assert_eq!(inferred.as_deref(), Some("USD"));
    }

    /// Test that simple posting currency takes precedence over cost spec currency.
    #[test]
    fn test_infer_cost_currency_simple_takes_precedence() {
        // Transaction with both simple posting and cost spec - simple should win
        let txn = Transaction::new(date(2022, 4, 16), "Trade")
            .with_synthesized_posting(
                Posting::new("Assets:Crypto", Amount::new(dec!(100), "TOKEN")).with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(10) })
                        .with_currency("EUR"),
                ),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-1000), "USD")));

        let inferred = infer_cost_currency_from_postings(&txn);
        // Should get USD from the simple posting, not EUR from cost spec
        assert_eq!(inferred.as_deref(), Some("USD"));
    }

    /// Test that zero-cost spec currency is still used for inference.
    #[test]
    fn test_infer_cost_currency_zero_cost() {
        // Zero cost should still provide the currency
        let txn = Transaction::new(date(2022, 4, 16), "Airdrop")
            .with_synthesized_posting(
                Posting::new("Assets:Crypto", Amount::new(dec!(1000), "SHIB")).with_cost(
                    CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(0) })
                        .with_currency("JPY"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Income:Airdrop"));

        let inferred = infer_cost_currency_from_postings(&txn);
        assert_eq!(inferred.as_deref(), Some("JPY"));
    }
}
