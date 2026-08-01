//! Transaction interpolation.
//!
//! Fills in missing posting amounts to balance transactions.

use rust_decimal::Decimal;
use rust_decimal::prelude::Signed;
use rustledger_core::{
    Amount, BookedCost, CostNumber, CostSpec, Currency, IncompleteAmount, Transaction,
};
use std::collections::HashMap;
use thiserror::Error;

/// Errors that can occur during interpolation.
#[derive(Debug, Clone, Error)]
pub enum InterpolationError {
    /// Multiple unknowns in the same currency group, where an unknown is
    /// either a posting with a missing amount or a posting with an empty
    /// cost spec (`{}`) whose cost-basis weight is deferred to booking-
    /// time lot matching. Bean-check enforces "at most one unknown per
    /// currency group" — see issue #1026 for the cost-spec extension.
    ///
    /// The variant name `MultipleMissing` is kept for API stability;
    /// "missing amounts" in the error message is a slight overgeneral
    /// (the count includes cost-unknowns, not just missing amounts), but
    /// the field semantics are correct.
    #[error(
        "multiple postings missing amounts or with unresolved cost specs for currency {currency} ({count} unknowns)"
    )]
    MultipleMissing {
        /// The currency group with too many unknowns.
        currency: Currency,
        /// Total count of unknowns: missing-amount postings plus
        /// empty-cost-spec postings whose weight is deferred to
        /// booking-time lot matching.
        count: usize,
    },
    /// The residual-solved cost for an empty `{}` augmentation came out
    /// negative — beancount rejects this ("Cost is negative") rather than
    /// booking a negative-cost lot (#1705 edge e14).
    #[error(
        "inferred cost for {currency} posting is negative ({per_unit} per unit); \
         a lot cannot be acquired at a negative cost"
    )]
    NegativeInferredCost {
        /// The cost currency the negative value was solved in.
        currency: Currency,
        /// The (negative) solved per-unit value.
        per_unit: Decimal,
    },
    /// An empty `{}` cost spec names no currency and the transaction's
    /// other postings span more than one currency, so the cost currency
    /// (and therefore the residual to solve from) is ambiguous — beancount
    /// rejects this ("Failed to categorize posting") (#1705 edge e15).
    #[error(
        "cannot infer the cost currency for the {{}} cost spec: candidates \
         {candidates}; name it explicitly (e.g. {{EUR}})"
    )]
    AmbiguousInferredCostCurrency {
        /// Comma-joined candidate currencies observed.
        candidates: String,
    },

    /// A posting's units number is missing and cannot be recovered from the
    /// balance, because the posting's weight does not vary with that number
    /// (#1911). The cases are enumerated on the private `UnitsWeight` classifier
    /// in this module: a total cost or price, a zero factor, an empty `{}` spec,
    /// a compound cost, and a cost with no units currency to write into.
    ///
    /// Reported rather than left unfilled: `validate_transaction_balance` skips
    /// a transaction that still has an unfilled posting, so staying silent here
    /// would accept an unbalanced transaction.
    #[error("cannot interpolate the units number for the {account} posting: {reason}")]
    UnsolvableUnits {
        /// The account of the posting whose units could not be solved.
        account: rustledger_core::Account,
        /// Why the balance does not determine the number.
        reason: &'static str,
    },

    /// A bare price sigil (`@` / `@@` with no amount) asks for the price to be
    /// computed, but no single currency stands out to compute it in (#1915).
    #[error(
        "cannot tell which currency the bare price on the {account} posting should be \
         computed in; write the price currency (e.g. `@ 1.20 USD`)"
    )]
    AmbiguousBarePriceCurrency {
        /// The account of the posting carrying the bare sigil.
        account: rustledger_core::Account,
    },

    /// A bare price sigil cannot be answered from the balance for a reason
    /// other than an ambiguous currency (#1915).
    #[error("cannot compute the price for the {account} posting: {reason}")]
    UnsolvablePrice {
        /// The account of the posting carrying the bare sigil.
        account: rustledger_core::Account,
        /// Why the balance does not determine the price.
        reason: &'static str,
    },

    /// Solving a bare price sigil from the residual gives a negative price
    /// (#1915). Refused for the same reason as [`Self::NegativeInferredCost`]:
    /// the balance is asking for something that is not a price.
    #[error(
        "the price of the {account} posting would have to be {price} {currency} to \
         balance this transaction, and a negative price is not meaningful; check the \
         signs of the other postings"
    )]
    NegativeInferredPrice {
        /// The account of the posting carrying the bare sigil.
        account: rustledger_core::Account,
        /// The currency the price was solved in.
        currency: Currency,
        /// The (negative) solved price.
        price: Decimal,
    },

    /// Cannot infer currency for a posting.
    #[error("cannot infer currency for posting to account {account}")]
    CannotInferCurrency {
        /// The account of the posting.
        account: rustledger_core::Account,
    },

    /// Transaction does not balance after interpolation.
    #[error("transaction does not balance: residual {residual} {currency}")]
    DoesNotBalance {
        /// The unbalanced currency.
        currency: Currency,
        /// The residual amount.
        residual: Decimal,
    },

    /// The weight arithmetic left `rust_decimal`'s ~7.9e28 range, so the
    /// amount to interpolate cannot be represented (#1863).
    ///
    /// This is reported rather than clamped because an interpolated amount is
    /// WRITTEN INTO the posting and then flows to every report, BQL result and
    /// balance check as if the user had typed it. A saturated value there is a
    /// fabricated figure presented as the user's own data.
    #[error(
        "amounts in this transaction exceed the {} range, so the {currency} \
         posting amount cannot be computed; split the transaction, or \
         denominate it in larger units (thousands, millions) so the number \
         is smaller",
        "±7.9e28"
    )]
    Unrepresentable {
        /// The currency group whose arithmetic left the range.
        currency: Currency,
    },
}

/// Result of interpolation.
#[derive(Debug, Clone)]
pub struct InterpolationResult {
    /// The interpolated transaction.
    pub transaction: Transaction,
    /// Which posting indices were filled in.
    pub filled_indices: Vec<usize>,
    /// Residuals after interpolation (should all be near zero).
    pub residuals: HashMap<Currency, Decimal>,
}

/// Add `amount` into `currency`'s running residual.
///
/// On overflow the currency is recorded in `unrepresentable` and its running
/// total is left untouched, rather than panicking (#1863) or aborting outright.
///
/// The distinction matters: a residual that cannot be represented is only
/// FATAL when interpolation must actually solve an amount from it — that
/// amount would be written into the posting as if the user had typed it. When
/// there is nothing to solve (no elided posting AND no unresolved `{}` cost
/// spec — see the gate after the posting loop), the balance validator
/// recomputes the residual in `BigDecimal` and reports the exact imbalance,
/// matching Python beancount, whose `decimal` context has no magnitude
/// ceiling. Aborting here would replace that precise diagnostic with a vaguer
/// one.
fn accumulate_residual(
    residuals: &mut HashMap<Currency, Decimal>,
    unrepresentable: &mut std::collections::HashSet<Currency>,
    currency: &Currency,
    amount: Decimal,
) {
    let slot = residuals.entry(currency.clone()).or_default();
    match slot.checked_add(amount) {
        Some(v) => *slot = v,
        None => {
            unrepresentable.insert(currency.clone());
        }
    }
}

/// Round an interpolated amount to match existing scale, but never round
/// a non-zero residual to zero (that would leave the transaction unbalanced).
fn round_interpolated(residual: Decimal, existing_scale: Option<u32>) -> Decimal {
    let interpolated = -residual;
    if let Some(scale) = existing_scale {
        let rounded = interpolated.round_dp(scale);
        // If rounding would make non-zero residual into zero, preserve precision
        if rounded.is_zero() && !residual.is_zero() {
            interpolated
        } else {
            rounded
        }
    } else {
        interpolated
    }
}

/// How a units-missing posting's balance weight depends on the number we are
/// about to solve for.
///
/// The number is recovered from a residual, so the question is always "which
/// currency's residual, and scaled by what?". For a plain posting the weight
/// IS the units, and the answer is the units currency's residual unchanged.
/// For a posting carrying a cost or price the weight is `units × multiplier`
/// denominated in the cost/price currency, so the number is that currency's
/// residual DIVIDED by the multiplier, written back in the posting's own units
/// currency (#1911).
///
/// This mirrors the weight ladder in [`crate::cost_weight`] /
/// [`crate::cost_number_weight_generic`] — inverted. A new `CostNumber` variant
/// must be classified here as well as given a weight there; the `_ =>` arm
/// below fails closed (refuse to solve) rather than guessing a multiplier.
enum UnitsWeight {
    /// `weight = units`, in the posting's own units currency: a plain posting,
    /// or one whose price annotation is too incomplete to convert (matching the
    /// "fall back to units" arm of the complete-units branch).
    Units,
    /// `weight = units × multiplier`, in `currency`. Only ever constructed with
    /// a NON-ZERO multiplier, which is what makes the inverting division safe.
    Scaled {
        /// The currency the weight lands in, whose residual we solve from.
        currency: Currency,
        /// The non-zero per-unit factor.
        multiplier: Decimal,
    },
    /// The weight does not depend on the units number, so no number can be
    /// recovered from any residual. Carries the user-facing explanation.
    ///
    /// A total cost (`{{600 USD}}`) or total price (`@@ 600 USD`) contributes a
    /// CONSTANT weight — every units number balances equally, so the input is
    /// genuinely ambiguous rather than merely hard. A zero per-unit factor
    /// collapses the weight to zero for the same reason. An empty `{}` spec has
    /// no number to divide by, and a compound `{a # b}` weight
    /// (`units×a + b×signum(units)`) admits two roots; we refuse rather than
    /// pick one.
    ///
    /// Python beancount does not diagnose these — it crashes: `TypeError: bad
    /// operand type for abs(): 'type'` on a total or zero cost, and
    /// `AssertionError: Internal error; residual currency different than
    /// missing currency` on a zero price. We report
    /// [`InterpolationError::UnsolvableUnits`] instead.
    ///
    /// This MUST be an error and not a silent skip: `validate_transaction_balance`
    /// deliberately returns without checking a transaction that still has an
    /// unfilled posting, on the documented assumption that interpolation already
    /// reported the real failure. Leaving one unfilled and quiet would accept an
    /// unbalanced transaction outright.
    Undetermined {
        /// Why no number can be recovered, phrased for the ledger author.
        reason: &'static str,
    },
}

/// Classify how `posting`'s weight scales with its (missing) units number.
fn units_weight(
    posting: &rustledger_core::Posting,
    infer_currency: impl FnOnce() -> Option<Currency>,
) -> UnitsWeight {
    // Cost beats price, exactly as in `cost_weight`: a posting with both
    // annotations weighs at cost, so the price is not what we invert.
    if let Some(cost_spec) = posting.cost.as_ref() {
        return match cost_spec.number {
            Some(CostNumber::PerUnit { value }) if !value.is_zero() => {
                match crate::cost_currency_of(posting, infer_currency) {
                    Some(currency) => UnitsWeight::Scaled {
                        currency,
                        multiplier: value,
                    },
                    // A per-unit cost whose currency we cannot name gives us a
                    // multiplier but no residual to apply it to.
                    None => UnitsWeight::Undetermined {
                        reason: "the cost currency cannot be determined, so there is no \
                                 residual to solve from; name it explicitly (e.g. `{300.00 USD}`)",
                    },
                }
            }
            Some(CostNumber::PerUnit { .. }) => UnitsWeight::Undetermined {
                reason: "a zero per-unit cost makes every units number weigh zero, \
                         so the balance cannot single one out",
            },
            Some(CostNumber::Total { .. } | CostNumber::PerUnitFromTotal(_)) => {
                UnitsWeight::Undetermined {
                    reason: "a total cost `{{...}}` contributes the same weight whatever the \
                             units are, so the balance cannot single one out; write the cost \
                             per unit (`{...}`) or state the units",
                }
            }
            Some(CostNumber::Compound { .. }) => UnitsWeight::Undetermined {
                reason: "a compound cost `{a # b}` can balance at two different \
                         units numbers, one positive and one negative",
            },
            None => UnitsWeight::Undetermined {
                reason: "an empty cost spec `{}` has no cost number to solve against, \
                         and its own value is not known until lot matching",
            },
        };
    }

    if let Some(price) = posting.price.as_ref() {
        let Some(price_amt) = price.amount.as_ref().and_then(IncompleteAmount::as_amount) else {
            // A bare `@` sigil is itself a request to compute the price
            // (#1915). Together with a missing units number that is two
            // unknowns on one posting, and one residual cannot determine both.
            return UnitsWeight::Undetermined {
                reason: "the units number and the price are both missing, and a single \
                         residual cannot determine two unknowns; write one of them",
            };
        };
        return match price.kind {
            rustledger_core::PriceKind::Unit if !price_amt.number.is_zero() => {
                UnitsWeight::Scaled {
                    currency: price_amt.currency.clone(),
                    multiplier: price_amt.number,
                }
            }
            rustledger_core::PriceKind::Unit => UnitsWeight::Undetermined {
                reason: "a zero per-unit price makes every units number weigh zero, \
                         so the balance cannot single one out",
            },
            rustledger_core::PriceKind::Total => UnitsWeight::Undetermined {
                reason: "a total price `@@ ...` contributes the same weight whatever the \
                         units are, so the balance cannot single one out; write the price \
                         per unit (`@ ...`) or state the units",
            },
        };
    }

    UnitsWeight::Units
}

/// The price currency the author WROTE, whether or not they also wrote a
/// number: both `@ 1.20 USD` and `@ USD` say USD.
///
/// Deliberately wider than [`crate::price_currency_of`], which reads only a
/// COMPLETE price amount and so cannot see `@ USD` at all. That is the right
/// reading where a price's numeric contribution is what matters, but here the
/// question is "which currency does this posting's weight land in", and
/// `@ USD` answers it perfectly well. Using the narrow one made a posting
/// priced `@ USD` offer its UNITS currency as a candidate instead.
fn declared_price_currency(posting: &rustledger_core::Posting) -> Option<Currency> {
    posting
        .price
        .as_ref()
        .and_then(|p| p.amount.as_ref())
        .and_then(|amount| match amount {
            IncompleteAmount::Complete(amount) => Some(amount.currency.clone()),
            IncompleteAmount::CurrencyOnly(currency) => Some(currency.clone()),
            IncompleteAmount::NumberOnly(_) => None,
        })
}

/// The currency a bare price sigil resolves in.
///
/// **A declared currency always wins.** `@ USD` (the form beancount's own
/// parser docs call "recommended") states the answer's currency and leaves only
/// the number to compute, so there is nothing to infer and nothing we are
/// entitled to override. Inferring anyway would let `100.00 USD @ CAD` against
/// `-50.00 EUR` be written back as `@ 0.50 EUR` — substituting a currency the
/// author did not write, which is the same fabrication this module refuses
/// everywhere else.
///
/// Only a fully bare `@` / `@@` needs inference, and then the answer is the
/// currency the transaction is out of balance in: that is the residual the
/// posting has to cancel.
///
/// When nothing is known yet (every other posting is itself an unknown, so all
/// residuals are zero) fall back to the currencies the other postings are
/// denominated in. That is what lets the count rule name a group and say
/// "two unknowns in USD" rather than failing with something vaguer.
///
/// `None` when no single currency stands out, in either pass.
fn bare_price_currency(
    txn: &Transaction,
    self_index: usize,
    residuals: &HashMap<Currency, Decimal>,
) -> Option<Currency> {
    if let Some(declared) = declared_price_currency(&txn.postings[self_index]) {
        return Some(declared);
    }

    let candidates: Vec<&Currency> = residuals
        .iter()
        .filter(|(_, value)| !value.is_zero())
        .map(|(currency, _)| currency)
        .collect();

    if candidates.is_empty() {
        // The other postings' WEIGHT currencies, not their units currencies:
        // this posting has to cancel what they contribute to the balance, and
        // a price annotation redenominates that. `? CAD @ 1.2 USD` weighs in
        // USD, so a bare sigil facing it resolves in USD too — reading CAD off
        // its units would put the two unknowns in different groups and hide a
        // genuine ambiguity.
        let mut weights: Vec<Currency> = Vec::new();
        for (i, posting) in txn.postings.iter().enumerate() {
            if i == self_index {
                continue;
            }
            // Cost beats price beats units, the same ladder the residual scan
            // walks. A cost-bearing posting weighs in its COST currency, so
            // `HOOL {300.00 USD}` offers USD and never HOOL; reading the
            // commodity off its units would put this sigil in a different
            // group from a posting it actually competes with, and downgrade a
            // "too many unknowns in USD" into a bare imbalance report. When a
            // `{}` spec names no currency there is no candidate to offer, so
            // contribute none rather than guess.
            let currency = if posting.cost.is_some() {
                crate::cost_currency_of(posting, || None)
            } else {
                declared_price_currency(posting).or_else(|| match &posting.units {
                    Some(IncompleteAmount::Complete(amount)) => Some(amount.currency.clone()),
                    Some(IncompleteAmount::CurrencyOnly(currency)) => Some(currency.clone()),
                    _ => None,
                })
            };
            if let Some(currency) = currency
                && !weights.contains(&currency)
            {
                weights.push(currency);
            }
        }
        return match weights.as_slice() {
            [only] => Some(only.clone()),
            _ => None,
        };
    }

    match candidates.as_slice() {
        [only] => Some((*only).clone()),
        _ => None,
    }
}

/// Which residual an elided posting's unknown will be solved from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnknownGroup {
    /// Solved from this currency's residual. For a posting carrying a per-unit
    /// cost or price this is the COST/PRICE currency, not the units currency
    /// (#1911) — that is the whole reason this cannot be eyeballed from the
    /// posting's units.
    Currency(Currency),
    /// A fully-elided posting (`Assets:Cash` with no amount at all). Which
    /// currency it absorbs is not knowable until the residuals are, so
    /// interpolation assigns it late — and may split it across several
    /// currencies.
    Unassigned,
}

/// The currency group each of `txn`'s elided postings will be solved in.
///
/// **Canonical grouping.** [`interpolate`] solves per this grouping, and
/// `rustledger-validate`'s E3002 check enforces "at most one unknown per group"
/// against it. Both go through the same private `units_weight` classifier in
/// this module, so the rule cannot drift
/// between the pre-booking diagnostic and the solver that actually runs
/// (#1914 — the validator previously grouped by the posting's own units
/// currency, then summed across groups anyway, and rejected two elided
/// postings that were in different currencies entirely).
///
/// Postings with a complete amount are omitted, as are shapes that
/// [`interpolate`] refuses outright ([`InterpolationError::UnsolvableUnits`]):
/// those get a precise message naming the offending annotation, which a
/// generic "too many unknowns" would only obscure.
///
/// Bare price sigils (`@` / `@@` with no amount) are also omitted, even though
/// they ARE unknowns for the same one-per-group rule (#1915). Which group they
/// fall in depends on the residuals, which this function deliberately does not
/// compute — reproducing that here would be a second implementation of the
/// grouping, the drift this function exists to prevent. `interpolate` reports
/// them instead, one phase later.
#[must_use]
pub fn elided_unknown_groups(txn: &Transaction) -> Vec<(usize, UnknownGroup)> {
    let mut inferred_cost_currency: Option<Option<Currency>> = None;
    let mut groups = Vec::new();

    for (i, posting) in txn.postings.iter().enumerate() {
        match &posting.units {
            // Nothing to solve.
            Some(IncompleteAmount::Complete(_)) => {}
            Some(IncompleteAmount::CurrencyOnly(units_currency)) => {
                match units_weight(posting, || {
                    inferred_cost_currency
                        .get_or_insert_with(|| crate::infer_cost_currency_from_postings(txn))
                        .clone()
                }) {
                    UnitsWeight::Units => {
                        groups.push((i, UnknownGroup::Currency(units_currency.clone())));
                    }
                    UnitsWeight::Scaled { currency, .. } => {
                        groups.push((i, UnknownGroup::Currency(currency)));
                    }
                    UnitsWeight::Undetermined { .. } => {}
                }
            }
            // Never an unknown for this rule. The number is written, so such a
            // posting contributes a KNOWN weight once its currency is read off
            // the balance; it does not compete for a residual the way an elided
            // posting does (#1920). With a cost or price present the currency is
            // unknowable and `interpolate` refuses outright, which again is not
            // this rule's business.
            Some(IncompleteAmount::NumberOnly(_)) => {}
            // A cost spec here is refused by `interpolate` (no commodity to
            // write the solved number in), so it is not grouped.
            None => {
                if posting.cost.is_none() {
                    groups.push((i, UnknownGroup::Unassigned));
                }
            }
        }
    }

    groups
}

/// Interpolate missing amounts in a transaction.
///
/// This function:
/// 1. Identifies postings with missing amounts
/// 2. For each currency, calculates the residual
/// 3. Fills in the missing amount to balance
///
/// # Rules
///
/// - At most one posting per currency can have a missing amount
/// - If a posting has a cost spec with a currency, that currency is used
/// - Otherwise, the posting gets the residual that makes the transaction balance
///
/// # TLA+ Specification
///
/// Implements invariants from `Interpolation.tla` (post-#1030 redesign for
/// N postings + multi-currency + cost-unknowns):
/// - `AtMostOneUnknownPerCurrency`: For each currency group, at most one
///   posting may be "unknown" — either a missing amount (counts toward
///   the units currency) or an empty cost spec like `{}` (counts toward
///   the cost currency, since the cost-basis weight is unresolved until
///   booking-pass lot matching). Returns `MultipleMissing` if violated.
/// - `CompleteImpliesValidated`: Interpolation only completes the
///   transaction when the validation rule holds.
///
/// The spec models the structural validation rule, not the residual
/// arithmetic that produces filled amounts — see `Interpolation.tla`'s
/// header for the scope rationale.
///
/// See: `spec/tla/Interpolation.tla`
///
/// # Example
///
/// ```ignore
/// let txn = Transaction::new(date, "Test")
///     .with_synthesized_posting(Posting::new("Expenses:Food", Amount::new(dec!(50.00), "USD")))
///     .with_synthesized_posting(Posting::auto("Assets:Cash"));
///
/// let result = interpolate(&txn)?;
/// // Assets:Cash now has -50.00 USD
/// ```
pub fn interpolate(transaction: &Transaction) -> Result<InterpolationResult, InterpolationError> {
    // Clone the transaction for modification
    let mut result = transaction.clone();
    let mut filled_indices = Vec::new();

    // Lazily compute inferred currency only when needed (most transactions don't need it)
    let mut inferred_cost_currency: Option<Option<Currency>> = None;
    let get_inferred_currency = |cache: &mut Option<Option<Currency>>| -> Option<Currency> {
        cache
            .get_or_insert_with(|| crate::infer_cost_currency_from_postings(transaction))
            .clone()
    };

    // Calculate initial residuals from postings with amounts
    // Pre-allocate for typical case (1-2 currencies per transaction)
    let num_postings = transaction.postings.len();
    let mut residuals: HashMap<Currency, Decimal> = HashMap::with_capacity(num_postings.min(4));
    // Currencies whose running residual left `rust_decimal`'s range (#1863).
    let mut unrepresentable: std::collections::HashSet<Currency> = std::collections::HashSet::new();
    let mut missing_by_currency: HashMap<Currency, Vec<usize>> = HashMap::with_capacity(2);
    let mut unassigned_missing: Vec<usize> = Vec::with_capacity(2);

    // Track maximum scale (decimal places) per currency for rounding interpolated amounts.
    //
    // Matches Python beancount's `infer_tolerances` rule: only NON-INTEGER posting
    // units contribute to the per-currency tolerance/precision. Integer amounts
    // ("1 CAD" commission, "1 CSU" share count) do NOT contribute — they don't
    // tell us anything about that currency's display precision.
    //
    // Cost spec scales are deliberately NOT included. With Python's default
    // `infer_tolerance_from_cost = False`, cost annotations don't influence the
    // residual quantization either. The natural Decimal arithmetic that flows
    // through `cost_amount = units × per_unit` preserves whatever scale the
    // operands carry, so a transaction with no non-integer posting units in a
    // given currency simply doesn't get a quantization step (the residual is
    // rendered at its natural scale).
    //
    // - #333 (`1 CSU {2800.01 CAD}` + `1 CAD` commission + missing CAD):
    //   no non-integer CAD posting units in this transaction; residual
    //   passes through unrounded at its natural scale, which is 2dp from
    //   the explicit cost literal `{2800.01}` flowing through
    //   `cost_amount = units × per_unit`.
    // - #251 (`70.538 ABC {100 USD}` + missing posting): no non-integer
    //   USD posting units; residual = `70.538 × 100 = 7053.800` (scale 3
    //   from the rust_decimal multiplication), preserved naturally.
    // - #1107 (`-1.763 STOCK {}` lot-matched against high-precision per_unit):
    //   the cash side `336.73 USD` gives USD scale=2; the residual gets
    //   quantized to 2dp instead of inheriting the lot's derived 26-digit
    //   per_unit precision.
    let mut max_scale_by_currency: HashMap<Currency, u32> = HashMap::with_capacity(4);

    // Per-currency count of postings whose WEIGHT contribution is unknown even
    // though their units are written out. Two shapes qualify:
    //
    // - an empty cost spec (`{}`), whose cost basis is not known until booking
    //   resolves the lot match (issue #1026). Without counting these, rledger
    //   would silently fall back to the price annotation and accept
    //   transactions with more unknowns than the interpolation rule allows.
    // - a bare price sigil (`@` / `@@` with no amount), whose price is solved
    //   from the residual further down (#1915).
    //
    // Each is one unknown for interpolation accounting, added to the
    // per-currency total alongside missing-amount postings.
    let mut weight_unknowns_by_currency: HashMap<Currency, usize> = HashMap::with_capacity(2);

    // Augmenting `{}` postings whose per-unit cost beancount infers from the
    // balance residual (issue #1705): `(posting index, cost currency, units)`.
    // Only empty-`{}`, price-less postings qualify — a reduction's `{}` is
    // already cost-filled by the booking pass (so it never reaches the empty
    // branch below), and a priced `{}` defers to booking-time lot matching.
    // Each is solved post-loop, but only when it is the SOLE unknown in its
    // cost currency group (else the group already errored on the count rule).
    let mut inferable_cost: Vec<(usize, Currency, Decimal)> = Vec::new();

    // Postings carrying a bare price sigil (`@` / `@@` with no amount), whose
    // price is solved from the residual once the currency is known (#1915):
    // `(posting index, units, sigil kind)`. Cost-bearing postings never appear
    // here — cost beats price, so their sigil does not affect the balance.
    let mut bare_price: Vec<(usize, Amount, rustledger_core::PriceKind)> = Vec::new();

    // Postings priced `@ 1.20` — price number written, price currency elided.
    // Only the currency is inferred; the number is kept verbatim:
    // `(posting index, units, sigil kind, price number)`.
    let mut price_number_known: Vec<(usize, Amount, rustledger_core::PriceKind, Decimal)> =
        Vec::new();
    // Postings written as a number with the currency elided (`120.00`), whose
    // units currency is read off the balance while the number itself is kept
    // verbatim (#1920): `(posting index, number)`. Distinct from
    // `unassigned_missing`, which has no number either and is SOLVED from the
    // residual; conflating the two overwrote the author's number.
    let mut number_only: Vec<(usize, Decimal)> = Vec::new();

    // Units-missing postings whose weight is `units × multiplier` in some other
    // currency (a per-unit cost or price): `index -> (units currency, factor)`.
    // Their entry in `missing_by_currency` is keyed by the WEIGHT currency, so
    // the fill step needs this to divide back out and to name the commodity it
    // writes (#1911). Empty for every posting that weighs at its own units,
    // which is the overwhelming majority — `HashMap::new` does not allocate.
    let mut scaled_missing: HashMap<usize, (Currency, Decimal)> = HashMap::new();

    for (i, posting) in transaction.postings.iter().enumerate() {
        match &posting.units {
            Some(IncompleteAmount::Complete(amount)) => {
                // Track scale (decimal places) for rounding interpolated amounts.
                // Skip integer (scale==0) amounts — matches Python's
                // `infer_tolerances`, which ignores integer posting.units
                // since they don't reflect intentional currency precision.
                let scale = amount.number.scale();
                if scale > 0 {
                    max_scale_by_currency
                        .entry(amount.currency.clone())
                        .and_modify(|s| *s = (*s).max(scale))
                        .or_insert(scale);
                }

                // Determine the "weight" of this posting for balance purposes.
                // The cost weight goes through the shared `cost_weight` engine —
                // the SAME `CostNumber` ladder `calculate_residual` uses — so
                // interpolation and the balance residual can no longer disagree
                // (the rule: cost beats price; else price; else units).
                let Ok(cost_contribution) = crate::cost_weight::<Decimal>(posting, amount, || {
                    get_inferred_currency(&mut inferred_cost_currency)
                }) else {
                    // This posting's weight is out of range. Mark the
                    // currency the weight WOULD have been denominated in —
                    // marking `amount.currency` instead would leave the
                    // cost currency's residual quietly short by this
                    // posting while looking representable (#1863).
                    let weight_currency = crate::cost_currency_of(posting, || {
                        get_inferred_currency(&mut inferred_cost_currency)
                    })
                    .unwrap_or_else(|| amount.currency.clone());
                    unrepresentable.insert(weight_currency);
                    // `continue`, NOT `None`: falling through would reach
                    // the `posting.cost.is_some()` branch and be counted as
                    // an empty-`{}` cost unknown, turning an arithmetic
                    // problem into a spurious #1026 "multiple unknowns".
                    continue;
                };

                if let Some((currency, cost_amount)) = cost_contribution {
                    // Cost-based posting: weight is in the cost currency.
                    // Cost spec scales are intentionally NOT tracked in
                    // `max_scale_by_currency` — see its declaration for the
                    // rationale (Python beancount with default
                    // `infer_tolerance_from_cost = False`).
                    accumulate_residual(
                        &mut residuals,
                        &mut unrepresentable,
                        &currency,
                        cost_amount,
                    );
                } else if posting.cost.is_some() {
                    // Cost spec exists but has no determinable cost number (e.g.,
                    // an empty `{}` spec where the lot's cost will be filled by
                    // booking-time lot matching). The WEIGHT of this posting is
                    // the cost basis × units, NOT the price × units — so we must
                    // not fall through to the price branch below and use price
                    // as a substitute (that's what happened pre-#1026 fix and
                    // produced silent acceptance of unsolvable transactions).
                    //
                    // Track this as one unknown for the cost currency. The
                    // post-loop check then enforces the "at most one unknown
                    // per currency group" rule that bean-check enforces.
                    let cost_currency = crate::cost_currency_of(posting, || {
                        get_inferred_currency(&mut inferred_cost_currency)
                    });
                    if let Some(curr) = cost_currency {
                        *weight_unknowns_by_currency.entry(curr.clone()).or_default() += 1;
                        // An empty `{}` reaching here is an augmentation (a
                        // reduction's `{}` is filled by the booking pass
                        // first). Beancount infers its per-unit cost from the
                        // residual — INCLUDING when a price annotation is
                        // present, and even when the two disagree (verified
                        // against bean-check 3.2.3: `{} @ 0.90` with a 0.95
                        // residual books {0.95}; the price feeds implicit
                        // price directives only). #1705 edges e07/e16.
                        //
                        // The cost currency must be unambiguous when the spec
                        // does not name one: with candidates from more than
                        // one non-cost posting, beancount fails to categorize
                        // the posting (edge e15).
                        if posting.cost.as_ref().is_some_and(|c| c.currency.is_none()) {
                            // Candidates are currencies of COMPLETE cost-less
                            // postings, excluding any currency that already
                            // has its own missing-amount posting: that group
                            // owns its unknown, so the {} cannot also belong
                            // to it (the per-group at-most-one rule) — which
                            // is what disambiguates "cost-unknown in USD +
                            // missing amount in EUR" (fine, disjoint groups)
                            // from two complete foreign currencies (e15,
                            // beancount: "Failed to categorize").
                            let mut complete: Vec<String> = Vec::new();
                            let mut incomplete: Vec<String> = Vec::new();
                            for p in &transaction.postings {
                                if p.cost.is_some() {
                                    continue;
                                }
                                let curr_of = crate::price_currency_of(p).or_else(|| {
                                    p.units.as_ref().and_then(|u| match u {
                                        IncompleteAmount::Complete(a) => Some(a.currency.clone()),
                                        IncompleteAmount::CurrencyOnly(c) => Some(c.clone()),
                                        IncompleteAmount::NumberOnly(_) => None,
                                    })
                                });
                                let complete_units =
                                    matches!(p.units.as_ref(), Some(IncompleteAmount::Complete(_)));
                                if let Some(c) = curr_of {
                                    if complete_units {
                                        complete.push(c.as_str().to_owned());
                                    } else {
                                        incomplete.push(c.as_str().to_owned());
                                    }
                                }
                            }
                            // A fully-unassigned missing posting (no currency
                            // context at all) makes the whole transaction
                            // reject via the post-scan unassigned+cost-unknown
                            // check with a more specific diagnosis — defer to
                            // it rather than reporting ambiguity.
                            let has_unassigned = transaction.postings.iter().any(|p| {
                                p.cost.is_none()
                                    && crate::price_currency_of(p).is_none()
                                    && !matches!(
                                        p.units.as_ref(),
                                        Some(
                                            IncompleteAmount::Complete(_)
                                                | IncompleteAmount::CurrencyOnly(_)
                                        )
                                    )
                            });
                            let mut candidates: Vec<String> = complete
                                .into_iter()
                                .filter(|c| !incomplete.contains(c))
                                .collect();
                            candidates.sort_unstable();
                            candidates.dedup();
                            if !has_unassigned && candidates.len() > 1 {
                                return Err(InterpolationError::AmbiguousInferredCostCurrency {
                                    candidates: candidates.join(", "),
                                });
                            }
                        }
                        inferable_cost.push((i, curr, amount.number));
                    }
                } else if let Some(price) = &posting.price {
                    // Price annotation: converts units to price currency.
                    // Scale tracking: per-unit prices are multipliers, so we
                    // do NOT track their scale. Total prices are explicit
                    // amounts, so we DO track theirs (non-integer scale
                    // only — an integer `@@ 1 USD` shouldn't quantize an
                    // elided same-currency residual to whole units).
                    if let Some(price_amt) =
                        price.amount.as_ref().and_then(IncompleteAmount::as_amount)
                    {
                        let (curr, signed) = match price.kind {
                            rustledger_core::PriceKind::Unit => (
                                price_amt.currency.clone(),
                                if let Some(v) = amount.number.abs().checked_mul(price_amt.number) {
                                    // `* signum` is exact: signum is -1, 0 or
                                    // 1, and `-Decimal::MIN == Decimal::MAX`
                                    // is representable, so only the price
                                    // product above can leave the range.
                                    v * amount.number.signum()
                                } else {
                                    unrepresentable.insert(price_amt.currency.clone());
                                    continue;
                                },
                            ),
                            rustledger_core::PriceKind::Total => {
                                let scale = price_amt.number.scale();
                                if scale > 0 {
                                    max_scale_by_currency
                                        .entry(price_amt.currency.clone())
                                        .and_modify(|s| *s = (*s).max(scale))
                                        .or_insert(scale);
                                }
                                (
                                    price_amt.currency.clone(),
                                    // Exact for the same reason as the
                                    // per-unit branch: multiplying by a signum
                                    // cannot leave the range.
                                    price_amt.number * amount.number.signum(),
                                )
                            }
                        };
                        accumulate_residual(&mut residuals, &mut unrepresentable, &curr, signed);
                    } else if let Some(IncompleteAmount::NumberOnly(price_number)) =
                        price.amount.as_ref()
                    {
                        // `@ 1.20` — the price NUMBER is written and only its
                        // currency is elided. The number is data, so keep it and
                        // infer just the currency, exactly as the units path does
                        // for a bare `120.00`. Treating this as a sigil overwrote
                        // the author's rate with whatever balanced the books.
                        price_number_known.push((i, amount.clone(), price.kind, *price_number));
                    } else {
                        // A bare `@` / `@@` sigil, or `@ USD`: the NUMBER is to be
                        // computed, so this posting's weight is unknown rather than
                        // "the units" (#1915). Contributing the units here would
                        // both answer the request with silence and let an
                        // unbalanced transaction look balanced.
                        //
                        // Reached only when the posting has no cost spec (the cost
                        // branches come first), which is right: cost beats price,
                        // so alongside a cost the sigil is inert — it feeds implicit
                        // price directives and never the balance.
                        bare_price.push((i, amount.clone(), price.kind));
                    }
                } else {
                    // Simple posting: weight is just the units
                    accumulate_residual(
                        &mut residuals,
                        &mut unrepresentable,
                        &amount.currency,
                        amount.number,
                    );
                }
            }
            Some(IncompleteAmount::CurrencyOnly(units_currency)) => {
                // Currency known, number to be interpolated. The number comes
                // from the residual of whichever currency this posting's WEIGHT
                // lands in — the units currency only when no cost or price
                // redenominates it (#1911).
                match units_weight(posting, || {
                    get_inferred_currency(&mut inferred_cost_currency)
                }) {
                    UnitsWeight::Units => {
                        missing_by_currency
                            .entry(units_currency.clone())
                            .or_default()
                            .push(i);
                    }
                    UnitsWeight::Scaled {
                        currency,
                        multiplier,
                    } => {
                        scaled_missing.insert(i, (units_currency.clone(), multiplier));
                        missing_by_currency.entry(currency).or_default().push(i);
                    }
                    UnitsWeight::Undetermined { reason } => {
                        // Unconditionally unsolvable: the multiplier is a
                        // property of this posting alone, so no other posting
                        // can rescue it and there is nothing to gain by
                        // deferring the report.
                        return Err(InterpolationError::UnsolvableUnits {
                            account: posting.account.clone(),
                            reason,
                        });
                    }
                }
            }
            Some(IncompleteAmount::NumberOnly(number)) => {
                // The number is written and only the currency is elided, so the
                // author's number must survive: it is data, not something to
                // solve for (#1920).
                //
                // A cost or price names ITS OWN currency, never the commodity
                // being counted: `10 {300.00 USD}` is ten of something, and
                // nothing in the transaction says what. Refuse rather than
                // guess, which is what beancount does too
                // ("Failed to categorize posting").
                if posting.cost.is_some() || posting.price.is_some() {
                    return Err(InterpolationError::CannotInferCurrency {
                        account: posting.account.clone(),
                    });
                }
                number_only.push((i, *number));
            }
            None => {
                // No units at all. A cost spec names the COST currency, never
                // the commodity being bought, so there is nothing to denominate
                // a solved number in. Filling the cost currency here fabricated
                // a lot: a bare `{300.00 USD}` became `600.00 USD {300.00 USD}`
                // and the resulting imbalance was reported as an invented
                // `179400.0000 USD`. Python beancount refuses the shape
                // ("CategorizationError"); we count it as an unsolvable unknown
                // so the user gets a balance error instead of fiction.
                if posting.cost.is_some() {
                    return Err(InterpolationError::UnsolvableUnits {
                        account: posting.account.clone(),
                        reason: "a cost spec names the cost currency, not the commodity being \
                                 bought, so there is no currency to write the solved number in; \
                                 state the commodity (e.g. `HOOL {300.00 USD}`)",
                    });
                }
                // Can't determine currency yet
                unassigned_missing.push(i);
            }
        }
    }

    // An out-of-range residual (#1863) is fatal ONLY if this transaction has
    // something to interpolate: the solved amount is written into the posting
    // and thereafter indistinguishable from user input, so it must never be
    // derived from a total we could not compute. With nothing to solve, we
    // return normally and the balance validator recomputes the residual in
    // `BigDecimal` and reports the exact imbalance — strictly more useful than
    // failing here, and what Python beancount prints.
    if !unrepresentable.is_empty()
        && (!missing_by_currency.is_empty()
            || !weight_unknowns_by_currency.is_empty()
            || !unassigned_missing.is_empty())
    {
        // Deterministic choice of currency for the message.
        let mut names: Vec<&Currency> = unrepresentable.iter().collect();
        names.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        return Err(InterpolationError::Unrepresentable {
            currency: (*names.first().expect("non-empty")).clone(),
        });
    }
    // Nothing was solved, so hand back no residual for those currencies rather
    // than the partial sum we stopped accumulating — a wrong number in a
    // public field is exactly the failure mode this fix exists to remove.
    for currency in &unrepresentable {
        residuals.remove(currency);
    }

    // Resolve which currency each bare price sigil answers in, and register it
    // as an unknown there BEFORE the count rule below — a posting whose price
    // is still to be computed contributes an unknown weight to that currency
    // exactly as an empty `{}` cost spec does (#1915).
    // Give each number-with-no-currency posting its currency, keeping the
    // number the author wrote (#1920). The currency is the one the transaction
    // is out of balance in, which is the only thing that can identify it.
    //
    // Runs BEFORE the bare-price resolution below, because these postings
    // contribute a KNOWN weight and a sigil should see the residual that is
    // actually left over once they have.
    for (idx, number) in number_only {
        let mut nonzero = residuals.iter().filter(|(_, value)| !value.is_zero());
        let currency = match (nonzero.next(), nonzero.next()) {
            (Some((currency, _)), None) => currency.clone(),
            // Nothing to read the currency off, or more than one candidate.
            _ => {
                return Err(InterpolationError::CannotInferCurrency {
                    account: transaction.postings[idx].account.clone(),
                });
            }
        };
        result.postings[idx].units =
            Some(IncompleteAmount::Complete(Amount::new(number, &currency)));
        filled_indices.push(idx);
        // The blanket unrepresentable gate ran further up, so guard here too:
        // an overflow at this point would otherwise leave a partial residual in
        // a public field while we have already written units into the posting.
        accumulate_residual(&mut residuals, &mut unrepresentable, &currency, number);
        if unrepresentable.contains(&currency) {
            return Err(InterpolationError::Unrepresentable { currency });
        }
    }

    // Give each `@ 1.20` its price currency, keeping the number. Runs BEFORE the
    // bare-sigil resolution below, because these postings contribute a KNOWN
    // weight once denominated and a sigil should see what is actually left over.
    for (idx, units, kind, price_number) in price_number_known {
        let Some(currency) = bare_price_currency(transaction, idx, &residuals) else {
            return Err(InterpolationError::AmbiguousBarePriceCurrency {
                account: transaction.postings[idx].account.clone(),
            });
        };
        let Some(weight) = crate::price_weight(units.number, price_number, kind) else {
            return Err(InterpolationError::Unrepresentable { currency });
        };
        result.postings[idx].price = Some(rustledger_core::PriceAnnotation {
            kind,
            amount: Some(IncompleteAmount::Complete(Amount::new(
                price_number,
                &currency,
            ))),
        });
        accumulate_residual(&mut residuals, &mut unrepresentable, &currency, weight);
        if unrepresentable.contains(&currency) {
            return Err(InterpolationError::Unrepresentable { currency });
        }
    }

    let mut bare_price_solved: Vec<(usize, Amount, rustledger_core::PriceKind, Currency)> =
        Vec::with_capacity(bare_price.len());
    for (idx, units, kind) in bare_price {
        let Some(currency) = bare_price_currency(transaction, idx, &residuals) else {
            return Err(InterpolationError::AmbiguousBarePriceCurrency {
                account: transaction.postings[idx].account.clone(),
            });
        };
        *weight_unknowns_by_currency
            .entry(currency.clone())
            .or_default() += 1;
        bare_price_solved.push((idx, units, kind, currency));
    }

    // Check for multiple unknowns in the same currency group. An "unknown"
    // is a missing-amount posting, a posting with an empty cost spec (whose
    // cost-basis weight is unknown until booking resolves the lot match), or
    // a posting whose price is still to be computed from a bare sigil.
    // Bean-check enforces "at most one unknown per currency group" — see
    // issue #1026.
    //
    // Iterate currencies in sorted order so the error message is
    // deterministic for the same input. HashMap iteration order is
    // unspecified, so picking "the first failing currency" without
    // sorting would produce non-reproducible test output.
    let mut currencies_with_unknowns: Vec<&Currency> = missing_by_currency
        .keys()
        .chain(weight_unknowns_by_currency.keys())
        .collect();
    currencies_with_unknowns.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    currencies_with_unknowns.dedup();
    for currency in currencies_with_unknowns {
        let missing_count = missing_by_currency
            .get(currency)
            .map_or(0, std::vec::Vec::len);
        let weight_unknown_count = weight_unknowns_by_currency
            .get(currency)
            .copied()
            .unwrap_or(0);
        let total = missing_count + weight_unknown_count;
        if total > 1 {
            return Err(InterpolationError::MultipleMissing {
                currency: currency.clone(),
                count: total,
            });
        }
    }

    // Same rule extended to "would-be" landing currencies for unassigned
    // missing postings: an unassigned-missing posting absorbs residuals
    // across all non-zero currencies at fill time, so it could land in
    // any currency including one with a cost-unknown.
    //
    // Empirically verified against bean-check (issue #1026): bean-check
    // rejects ANY combination of unassigned-missing + cost-unknown, even
    // when the unassigned would semantically prefer a different currency.
    // The reason is that an unassigned posting's currency assignment is
    // determined post-hoc from non-zero residuals, and cost-unknowns
    // contribute an unknown amount to their currency's residual — so the
    // landing currency could always be the cost-unknown's currency. To
    // require the user to make the absorber's currency explicit, reject.
    //
    // Pick the lexicographically-smallest cost-unknown currency for the
    // error so the message is reproducible across runs.
    if !unassigned_missing.is_empty() {
        let mut weight_unknown_keys: Vec<&Currency> = weight_unknowns_by_currency.keys().collect();
        weight_unknown_keys.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        if let Some(curr) = weight_unknown_keys.first() {
            let count = weight_unknowns_by_currency.get(*curr).copied().unwrap_or(0);
            return Err(InterpolationError::MultipleMissing {
                currency: (*curr).clone(),
                count: count + unassigned_missing.len(),
            });
        }
    }

    // Infer the per-unit cost of augmenting `{}` postings from the residual
    // (issue #1705). Beancount books first, then interpolates the single
    // remaining unknown; an augmenting lot written `1000 USD {}` with one
    // balancing cash leg has its cost inferred from that leg (`-900 EUR` →
    // 0.90 EUR/unit). rledger left such a lot with no cost basis, which also
    // broke later reductions of it (the `{}` reduction could no longer match a
    // cost-bearing lot, surfacing as a spurious "2 unknowns" error).
    //
    // Runs BEFORE missing-amount filling so a filled cost balances its
    // currency before any elided amount absorbs that currency's residual. Each
    // entry is guaranteed the sole unknown in its cost currency group: the
    // count-rule check above rejected any group with >1 unknown, and the
    // unassigned-missing check rejected any unassigned + cost-unknown combo.
    for (idx, currency, units_number) in inferable_cost {
        if units_number.is_zero() {
            continue; // BookedCost is undefined for zero units.
        }
        let residual = residuals.get(&currency).copied().unwrap_or(Decimal::ZERO);
        // The posting's cost weight must cancel the residual. For
        // `PerUnitFromTotal` the weight is `total * signum(units)`, so pick
        // `total = -residual * signum(units)` and `per_unit = total / |units|`.
        let signum = units_number.signum();
        let total = -residual * signum;
        let per_unit = total / units_number.abs();
        if per_unit < Decimal::ZERO {
            // Beancount: "Cost is negative" — a lot cannot be acquired at a
            // negative cost (#1705 edge e14).
            return Err(InterpolationError::NegativeInferredCost { currency, per_unit });
        }

        let existing = result.postings[idx]
            .cost
            .take()
            .unwrap_or_else(CostSpec::empty);
        result.postings[idx].cost = Some(CostSpec {
            number: Some(CostNumber::PerUnitFromTotal(BookedCost::new(
                per_unit,
                total,
                units_number,
            ))),
            currency: Some(currency.clone()),
            date: existing.date.or(Some(transaction.date)),
            label: existing.label,
            merge: existing.merge,
        });
        // Fold the now-known cost weight into the residual so downstream
        // missing-amount solving sees a balanced cost currency.
        *residuals.entry(currency).or_default() += total * signum;
    }

    // Answer each bare price sigil from the residual it has to cancel (#1915).
    //
    // Runs beside the `{}` cost inference above and for the same reason: the
    // solved weight has to land in the residual before any elided amount
    // absorbs that currency. Each entry is guaranteed the sole unknown in its
    // currency — the count rule rejected any group with more.
    //
    // `@` weighs `units × price` and `@@` weighs `total × signum(units)`, so
    // invert each accordingly. NOT what Python beancount computes: it solves
    // the MAGNITUDE, `|residual| / |units|`, which happens to balance only when
    // the other side is opposite-signed. On `IncompleteInputs.PriceMissing`
    // (`100.00 USD @` against a POSITIVE `120.00 CAD`) it fills `@1.2 CAD` and
    // then reports the 240 CAD imbalance it just created. The value that would
    // balance there is -1.2, and a negative price is not a price, so the honest
    // answer is to refuse and say why.
    for (idx, units, kind, currency) in bare_price_solved {
        let residual = residuals.get(&currency).copied().unwrap_or(Decimal::ZERO);

        if units.number.is_zero() {
            // Zero units weigh nothing at any price, so the balance says
            // nothing about this price. Harmless when the books already
            // balance; otherwise the sigil cannot be the thing that fixes them.
            if residual.is_zero() {
                continue;
            }
            // The currency IS known here; what fails is the arithmetic, so do
            // not send the user off to write a price currency they already
            // have (or that would not help).
            return Err(InterpolationError::UnsolvablePrice {
                account: transaction.postings[idx].account.clone(),
                reason: "the posting has zero units, so no price gives it any weight, \
                         and the transaction does not balance without one",
            });
        }

        // Nothing to cancel in this currency, so the balance determines nothing
        // and the honest answer is to leave the sigil unanswered. Reachable when
        // the author DECLARED a price currency (`@ CAD`) that no other posting
        // touches: writing the `@ 0 CAD` the arithmetic implies would put a
        // fabricated rate in the ledger, and the real problem — the currency
        // that actually fails to balance — is reported by the balance validator,
        // which still runs because the units here are complete.
        if residual.is_zero() {
            continue;
        }

        let (solved, weight) = match kind {
            rustledger_core::PriceKind::Unit => {
                let Some(price) = (-residual).checked_div(units.number) else {
                    return Err(InterpolationError::Unrepresentable { currency });
                };
                let Some(weight) = crate::price_weight(units.number, price, kind) else {
                    return Err(InterpolationError::Unrepresentable { currency });
                };
                (price, weight)
            }
            rustledger_core::PriceKind::Total => {
                // `weight = total × signum(units)`, and signum is ±1 here, so
                // multiplying inverts it exactly.
                let total = -residual * units.number.signum();
                let Some(weight) = crate::price_weight(units.number, total, kind) else {
                    return Err(InterpolationError::Unrepresentable { currency });
                };
                (total, weight)
            }
        };

        if solved < Decimal::ZERO {
            return Err(InterpolationError::NegativeInferredPrice {
                account: transaction.postings[idx].account.clone(),
                currency,
                price: solved,
            });
        }

        result.postings[idx].price = Some(rustledger_core::PriceAnnotation {
            kind,
            amount: Some(IncompleteAmount::Complete(Amount::new(solved, &currency))),
        });
        *residuals.entry(currency).or_default() += weight;
    }

    // Fill in known-currency missing postings
    for (weight_currency, indices) in missing_by_currency {
        let idx = indices[0];
        let residual = residuals
            .get(&weight_currency)
            .copied()
            .unwrap_or(Decimal::ZERO);

        // `scaled_missing` is empty unless a cost or price redenominates this
        // posting's weight, so the common path below is the original one: the
        // residual is the number, in the currency it was keyed under.
        let Some((units_currency, multiplier)) = scaled_missing.remove(&idx) else {
            let interpolated = round_interpolated(
                residual,
                max_scale_by_currency.get(&weight_currency).copied(),
            );
            result.postings[idx].units = Some(IncompleteAmount::Complete(Amount::new(
                interpolated,
                &weight_currency,
            )));
            filled_indices.push(idx);
            // Reflect the actual interpolated amount (rounding may have moved it).
            *residuals.entry(weight_currency).or_default() += interpolated;
            continue;
        };

        // `weight = units × multiplier`, so invert: the number is the weight
        // currency's residual divided by the factor, but quantized against the
        // UNITS currency's observed scale — that is the currency it is written
        // in. Beancount agrees on both halves: `HOOL {300.00 USD}` against
        // `-600.00 USD` yields a bare `2 HOOL`, and gains a `.00` only once
        // some other posting establishes a HOOL scale.
        let Some(quotient) = residual.checked_div(multiplier) else {
            return Err(InterpolationError::Unrepresentable {
                currency: weight_currency,
            });
        };
        let interpolated = round_interpolated(
            quotient,
            max_scale_by_currency.get(&units_currency).copied(),
        );

        result.postings[idx].units = Some(IncompleteAmount::Complete(Amount::new(
            interpolated,
            &units_currency,
        )));
        filled_indices.push(idx);

        // Fold back the WEIGHT the posting now contributes — the solved number
        // scaled back up, not the number itself.
        let Some(weight) = interpolated.checked_mul(multiplier) else {
            return Err(InterpolationError::Unrepresentable {
                currency: weight_currency,
            });
        };
        *residuals.entry(weight_currency).or_default() += weight;
    }

    // Handle unassigned missing postings
    // Each one absorbs one or more currencies' residuals
    if !unassigned_missing.is_empty() {
        // Get currencies with non-zero residuals
        let non_zero_residuals: Vec<(Currency, Decimal)> = residuals
            .iter()
            .filter(|&(_, v)| !v.is_zero())
            .map(|(k, v)| (k.clone(), *v))
            .collect();

        // Special case: single missing posting with multiple currencies
        // This is multi-currency interpolation - split into multiple postings
        if unassigned_missing.len() == 1 && non_zero_residuals.len() > 1 {
            let idx = unassigned_missing[0];
            let original_posting = &transaction.postings[idx];

            // Fill the first currency into the original posting
            let (first_currency, first_residual) = &non_zero_residuals[0];
            let interpolated = round_interpolated(
                *first_residual,
                max_scale_by_currency.get(first_currency).copied(),
            );
            result.postings[idx].units = Some(IncompleteAmount::Complete(Amount::new(
                interpolated,
                first_currency,
            )));
            filled_indices.push(idx);
            *residuals.entry(first_currency.clone()).or_default() += interpolated;

            // Add new postings for remaining currencies
            for (currency, residual) in non_zero_residuals.iter().skip(1) {
                let mut new_posting = original_posting.clone();
                let interpolated =
                    round_interpolated(*residual, max_scale_by_currency.get(currency).copied());
                new_posting.units = Some(IncompleteAmount::Complete(Amount::new(
                    interpolated,
                    currency,
                )));
                result.postings.push(new_posting);
                filled_indices.push(result.postings.len() - 1);
                *residuals.entry(currency.clone()).or_default() += interpolated;
            }
        } else {
            // Check for ambiguous elision: more unassigned missing postings than
            // available residual currencies means multiple postings would all be
            // assigned to the same currency, which is ambiguous and an error.
            if unassigned_missing.len() > non_zero_residuals.len() && !non_zero_residuals.is_empty()
            {
                let (currency, _) = &non_zero_residuals[0];
                return Err(InterpolationError::MultipleMissing {
                    currency: currency.clone(),
                    count: unassigned_missing.len(),
                });
            }

            // Standard case: assign one currency per missing posting
            for (i, idx) in unassigned_missing.iter().enumerate() {
                if i < non_zero_residuals.len() {
                    let (currency, residual) = &non_zero_residuals[i];
                    let interpolated =
                        round_interpolated(*residual, max_scale_by_currency.get(currency).copied());
                    result.postings[*idx].units = Some(IncompleteAmount::Complete(Amount::new(
                        interpolated,
                        currency,
                    )));
                    filled_indices.push(*idx);
                    *residuals.entry(currency.clone()).or_default() += interpolated;
                } else if !non_zero_residuals.is_empty() {
                    // Use the first currency
                    let (currency, _) = &non_zero_residuals[0];
                    result.postings[*idx].units =
                        Some(IncompleteAmount::Complete(Amount::zero(currency)));
                    filled_indices.push(*idx);
                } else if let Some(currency) = get_inferred_currency(&mut inferred_cost_currency) {
                    // No residuals but we can infer currency from cost basis
                    // This handles balanced cost-basis transactions like:
                    //   Assets:Crypto  100 USDC {1.0 USD}
                    //   Assets:Cash   -100 USD
                    //   Income:Trading  ; <- infer 0 USD from cost basis
                    result.postings[*idx].units =
                        Some(IncompleteAmount::Complete(Amount::zero(&currency)));
                    filled_indices.push(*idx);
                } else {
                    // No residuals and cannot infer currency
                    return Err(InterpolationError::CannotInferCurrency {
                        account: transaction.postings[*idx].account.clone(),
                    });
                }
            }
        }
    }

    // Prune postings that were filled with zero amounts. Python
    // beancount drops these from its rendered output too — they
    // contribute nothing to the transaction balance and would just
    // clutter BQL / JSON / format output.
    //
    // The historical concern (#877) was that pre-validation pruning
    // hid `E1001 Account X was never opened` errors on elided
    // postings to unopened accounts. The loader pipeline now runs an
    // EARLY validation phase before booking (see
    // `rustledger_validate::Phase::Early` and the "Python Compatibility
    // Policy" section in CLAUDE.md), so account-presence checks fire
    // BEFORE we reach this prune step. That's a deliberate divergence
    // from Python — Python silently accepts these references; rledger
    // catches them. Tested by `test_zero_interpolated_posting_keeps_e1001_*`
    // in `rustledger-loader`.
    //
    // Iterate in reverse so indices stay valid as we remove.
    let mut indices_to_remove: Vec<usize> = filled_indices
        .iter()
        .filter(|&&idx| {
            result.postings.get(idx).is_some_and(|p| {
                p.units
                    .as_ref()
                    .and_then(|u| u.as_amount())
                    .is_some_and(|a| a.number.is_zero())
            })
        })
        .copied()
        .collect();
    indices_to_remove.sort_unstable_by(|a, b| b.cmp(a));

    for idx in &indices_to_remove {
        result.postings.remove(*idx);
    }

    // Drop the removed indices from filled_indices and shift the
    // surviving ones down to reflect the new posting positions.
    let final_filled_indices: Vec<usize> = filled_indices
        .into_iter()
        .filter(|idx| !indices_to_remove.contains(idx))
        .map(|idx| {
            let adjustment = indices_to_remove.iter().filter(|&&r| r < idx).count();
            idx - adjustment
        })
        .collect();

    // Return the residuals we've been tracking incrementally
    // (no need to recalculate - we've updated residuals as we filled amounts)
    Ok(InterpolationResult {
        transaction: result,
        filled_indices: final_filled_indices,
        residuals,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;
    use rustledger_core::{NaiveDate, Posting};

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        rustledger_core::naive_date(year, month, day).unwrap()
    }

    /// Helper to get the complete amount from a posting.
    fn get_amount(posting: &rustledger_core::Posting) -> Option<&Amount> {
        posting.units.as_ref().and_then(|u| u.as_amount())
    }

    #[test]
    fn test_interpolate_simple() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).unwrap();

        assert_eq!(result.filled_indices, vec![1]);

        let filled = &result.transaction.postings[1];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.number, dec!(-50.00));
        assert_eq!(amount.currency, "USD");
    }

    #[test]
    fn test_interpolate_multiple_postings() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(30.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Expenses:Drink",
                Amount::new(dec!(20.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).unwrap();

        let filled = &result.transaction.postings[2];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.number, dec!(-50.00));
    }

    #[test]
    fn test_interpolate_no_missing() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-50.00), "USD"),
            ));

        let result = interpolate(&txn).unwrap();

        assert!(result.filled_indices.is_empty());
    }

    #[test]
    fn test_interpolate_multiple_currencies() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Expenses:Travel",
                Amount::new(dec!(100.00), "EUR"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Cash:USD",
                Amount::new(dec!(-50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash:EUR"));

        let result = interpolate(&txn).unwrap();

        let filled = &result.transaction.postings[3];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.number, dec!(-100.00));
        assert_eq!(amount.currency, "EUR");
    }

    #[test]
    fn test_interpolate_error_multiple_missing_same_currency() {
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash"))
            .with_synthesized_posting(Posting::auto("Assets:Bank"));

        // Multiple unassigned missing postings with a single residual currency
        // is ambiguous and should return MultipleMissing error.
        let result = interpolate(&txn);
        assert!(
            matches!(result, Err(InterpolationError::MultipleMissing { .. })),
            "expected MultipleMissing error, got: {result:?}"
        );
    }

    #[test]
    fn test_interpolate_multiple_missing_different_currencies_ok() {
        // Two elided postings but two residual currencies - each gets one
        let txn = Transaction::new(date(2024, 1, 15), "Multi-currency")
            .with_synthesized_posting(Posting::new("Assets:USD", Amount::new(dec!(100.00), "USD")))
            .with_synthesized_posting(Posting::new("Assets:EUR", Amount::new(dec!(85.00), "EUR")))
            .with_synthesized_posting(Posting::auto("Liabilities:CreditCard"))
            .with_synthesized_posting(Posting::auto("Equity:Exchange"));

        // Two unassigned missing, two non-zero residuals - this is unambiguous
        let result = interpolate(&txn);
        assert!(
            result.is_ok(),
            "expected success for different-currency elision, got: {result:?}"
        );
    }

    #[test]
    fn test_interpolate_with_per_unit_cost() {
        // 2015-10-02 *
        //   Assets:Stock   10 HOOL {100.00 USD}
        //   Assets:Cash
        //
        // Expected: Assets:Cash should be interpolated to -1000.00 USD
        let txn = Transaction::new(date(2015, 10, 2), "Buy stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit {
                            value: dec!(100.00),
                        })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // Check that the cash posting was filled
        assert_eq!(result.filled_indices, vec![1]);

        // Check the interpolated amount
        let filled = &result.transaction.postings[1];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(
            amount.currency, "USD",
            "should be USD (cost currency), not HOOL"
        );
        assert_eq!(
            amount.number,
            dec!(-1000.00),
            "should be -1000 USD (10 * 100)"
        );

        // Verify the transaction balances
        let residual = result
            .residuals
            .get("USD")
            .copied()
            .unwrap_or(Decimal::ZERO);
        assert!(
            residual.abs() < dec!(0.01),
            "USD residual should be ~0, got {residual}"
        );
        // There should be NO HOOL residual
        assert!(
            !result.residuals.contains_key("HOOL"),
            "should not have HOOL residual"
        );
    }

    /// Agreement fitness function: interpolation and balance-checking now share
    /// the `cost_weight` engine, so after interpolation the *independent* public
    /// [`crate::calculate_residual`] must see the result as balanced — across
    /// cost AND price weights. If interpolation computed a posting using a
    /// different weight than the residual does, this would surface a non-zero
    /// residual.
    #[test]
    fn test_interpolated_weights_agree_with_calculate_residual() {
        // Total-cost stock + unit-priced FX leg, both weighing in USD; the auto
        // cash posting must absorb the USD residual exactly.
        let txn = Transaction::new(date(2015, 10, 2), "Mixed cost and price")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::Total {
                            value: dec!(1500.00),
                        })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(
                Posting::new("Assets:EUR", Amount::new(dec!(-200.00), "EUR")).with_price(
                    rustledger_core::PriceAnnotation::unit(Amount::new(dec!(1.10), "USD")),
                ),
            )
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // The independent residual engine (sharing cost_weight) sees balance.
        for (currency, value) in
            crate::calculate_residual(&result.transaction).expect("fixture fits in Decimal")
        {
            assert!(
                value.abs() < dec!(0.0001),
                "interpolated result not balanced per calculate_residual: {value} {currency}"
            );
        }
    }

    #[test]
    fn test_interpolate_with_total_cost() {
        // 2015-10-02 *
        //   Assets:Stock   10 HOOL {{1000.00 USD}}
        //   Assets:Cash
        //
        // Expected: Assets:Cash should be interpolated to -1000.00 USD
        let txn = Transaction::new(date(2015, 10, 2), "Buy stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::Total {
                            value: dec!(1000.00),
                        })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        let filled = &result.transaction.postings[1];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.currency, "USD");
        assert_eq!(amount.number, dec!(-1000.00));
    }

    #[test]
    fn test_interpolate_stock_purchase_with_commission() {
        // From beancount starter.beancount:
        // 2013-02-03 * "Bought some stock"
        //   Assets:Stock         8 HOOL {701.20 USD}
        //   Expenses:Commission  7.95 USD
        //   Assets:Cash
        //
        // Expected: Cash = -(8 * 701.20 + 7.95) = -5617.55 USD
        let txn = Transaction::new(date(2013, 2, 3), "Bought some stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(8), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit {
                            value: dec!(701.20),
                        })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Expenses:Commission",
                Amount::new(dec!(7.95), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        let filled = &result.transaction.postings[2];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.currency, "USD");
        // 8 * 701.20 = 5609.60, plus 7.95 commission = 5617.55
        assert_eq!(amount.number, dec!(-5617.55));
    }

    #[test]
    fn test_interpolate_stock_sale_with_cost_and_price() {
        // Selling stock at a different price than cost basis
        // 2015-10-02 *
        //   Assets:Stock   -10 HOOL {100.00 USD} @ 120.00 USD
        //   Assets:Cash
        //   Income:Gains
        //
        // The sale is at cost (for booking), but price is 120 USD
        // Weight: -10 * 100 = -1000 USD (at cost)
        // Cash should receive: 10 * 120 = 1200 USD (at price)
        // Gains: -200 USD
        let txn = Transaction::new(date(2015, 10, 2), "Sell stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "HOOL"))
                    .with_cost(
                        rustledger_core::CostSpec::empty()
                            .with_number(rustledger_core::CostNumber::PerUnit {
                                value: dec!(100.00),
                            })
                            .with_currency("USD"),
                    )
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(120.00),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(1200.00), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Income:Gains"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        let filled = &result.transaction.postings[2];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.currency, "USD");
        // Gains = cost - proceeds = 1000 - 1200 = -200 (income is negative)
        assert_eq!(amount.number, dec!(-200.00));
    }

    #[test]
    fn test_interpolate_balanced_with_cost_no_interpolation_needed() {
        // When all amounts are provided, no interpolation needed
        // 2015-10-02 *
        //   Assets:Stock   10 HOOL {100.00 USD}
        //   Assets:Cash   -1000.00 USD
        let txn = Transaction::new(date(2015, 10, 2), "Buy stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit {
                            value: dec!(100.00),
                        })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-1000.00), "USD"),
            ));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // No postings should be filled
        assert!(result.filled_indices.is_empty());

        // Transaction should balance
        let residual = result
            .residuals
            .get("USD")
            .copied()
            .unwrap_or(Decimal::ZERO);
        assert!(residual.abs() < dec!(0.01));
    }

    #[test]
    fn test_interpolate_negative_cost_units_sale() {
        // Selling stock (negative units) with cost
        // 2015-10-02 *
        //   Assets:Stock   -5 HOOL {100.00 USD}
        //   Assets:Cash
        //
        // Expected: Cash = 500.00 USD (proceeds from sale at cost)
        let txn = Transaction::new(date(2015, 10, 2), "Sell stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-5), "HOOL")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit {
                            value: dec!(100.00),
                        })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        let filled = &result.transaction.postings[1];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.currency, "USD");
        assert_eq!(amount.number, dec!(500.00)); // Positive (receiving cash)
    }

    // =========================================================================
    // Multi-currency interpolation tests
    // =========================================================================

    #[test]
    fn test_interpolate_multi_currency_single_elided() {
        // Test case from basic.beancount:
        // 2008-04-02 * "Gilbert paid back for iPhone"
        //   Assets:Cash                            440.00 CAD
        //   Assets:AccountsReceivable             -431.92 USD
        //   Assets:Cash
        //
        // Expected: The elided Assets:Cash becomes TWO postings:
        //   Assets:Cash: -440.00 CAD
        //   Assets:Cash: 431.92 USD
        let txn = Transaction::new(date(2008, 4, 2), "Gilbert paid back for iPhone")
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(440.00), "CAD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:AccountsReceivable",
                Amount::new(dec!(-431.92), "USD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // Should now have 4 postings (original 3 + 1 added for second currency)
        assert_eq!(
            result.transaction.postings.len(),
            4,
            "should split elided posting into 2"
        );

        // Check that all residuals are zero
        for (currency, residual) in &result.residuals {
            assert!(
                residual.abs() < dec!(0.01),
                "{currency} residual should be ~0, got {residual}"
            );
        }

        // Verify the amounts (order may vary based on HashMap iteration)
        let mut found_cad = false;
        let mut found_usd = false;
        for posting in &result.transaction.postings {
            if let Some(amount) = get_amount(posting)
                && posting.account.as_str() == "Assets:Cash"
            {
                if amount.currency == "CAD" && amount.number == dec!(-440.00) {
                    found_cad = true;
                } else if amount.currency == "USD" && amount.number == dec!(431.92) {
                    found_usd = true;
                }
            }
        }
        assert!(found_cad, "should have -440.00 CAD posting");
        assert!(found_usd, "should have 431.92 USD posting");
    }

    #[test]
    fn test_interpolate_multi_currency_three_currencies() {
        // Three currencies with one elided posting
        let txn = Transaction::new(date(2024, 1, 15), "Multi-currency test")
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(100), "USD")))
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(200), "EUR")))
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(300), "GBP")))
            .with_synthesized_posting(Posting::auto("Equity:Opening"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // Should now have 6 postings (original 4 + 2 added)
        assert_eq!(result.transaction.postings.len(), 6);

        // All residuals should be zero
        for (currency, residual) in &result.residuals {
            assert!(
                residual.abs() < dec!(0.01),
                "{currency} residual should be ~0, got {residual}"
            );
        }
    }

    // =========================================================================
    // Cost currency inference tests (issue #203)
    // =========================================================================

    /// Test interpolation with cost currency inferred from other postings.
    /// This is the exact case from issue #203.
    #[test]
    fn test_interpolate_cost_currency_inferred_from_other_posting() {
        // 2026-01-01 * "Opening balance"
        //   Assets:Vanguard:IRA:Trad:VFIFX  10 VFIFX {100}
        //   Equity:Opening-Balances
        //
        // The cost currency should be inferred, and the elided posting should
        // be filled with -1000 USD.
        let txn = Transaction::new(date(2026, 1, 1), "Opening balance")
            .with_synthesized_posting(
                Posting::new(
                    "Assets:Vanguard:IRA:Trad:VFIFX",
                    Amount::new(dec!(10), "VFIFX"),
                )
                .with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(100) }),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Equity:Opening-Balances",
                Amount::new(dec!(-1000), "USD"),
            ));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // Transaction should balance
        let residual = result
            .residuals
            .get("USD")
            .copied()
            .unwrap_or(Decimal::ZERO);
        assert!(
            residual.abs() < dec!(0.01),
            "USD residual should be ~0, got {residual}"
        );
    }

    /// Test interpolation where the cash posting is elided.
    #[test]
    fn test_interpolate_cost_currency_inferred_elided_cash() {
        // Like issue #203 but with elided cash posting:
        // 2026-01-01 * "Opening balance"
        //   Assets:Vanguard:IRA:Trad:VFIFX  10 VFIFX {100}
        //   Equity:Opening-Balances  -1000 USD
        //
        // Both postings are complete, should just balance.
        let txn = Transaction::new(date(2026, 1, 1), "Opening balance")
            .with_synthesized_posting(
                Posting::new(
                    "Assets:Vanguard:IRA:Trad:VFIFX",
                    Amount::new(dec!(10), "VFIFX"),
                )
                .with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(100) }),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Equity:Opening-Balances",
                Amount::new(dec!(-1000), "USD"),
            ));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // No postings filled since both are complete
        assert!(result.filled_indices.is_empty());

        // Should balance
        let residual = result
            .residuals
            .get("USD")
            .copied()
            .unwrap_or(Decimal::ZERO);
        assert!(
            residual.abs() < dec!(0.01),
            "USD residual should be ~0, got {residual}"
        );
    }

    // =========================================================================
    // Interpolation rounding tests (issue #268)
    // =========================================================================

    /// Test that interpolated amounts are rounded to match the precision of other amounts.
    /// This matches Python beancount's behavior where interpolated amounts use the same
    /// quantum (decimal places) as other amounts in the same currency.
    ///
    /// Issue: <https://github.com/rustledger/rustledger/issues/268>
    #[test]
    fn test_interpolate_rounds_to_quantum() {
        // From issue #268:
        // 2026-01-02 * "..."
        //   Assets:Cash
        //   Assets:Abc                    12.3340 ABC {140.02 USD, 2025-01-01}
        //   Expenses:Abc                    -0.01 USD
        //
        // Cost: 12.3340 * 140.02 = 1727.006680 USD
        // Python rounds Cash to -1727.00 (2 decimal places from -0.01 USD)
        // Residual: 1727.006680 - 0.01 - 1727.00 = -0.003320 USD (within 0.005 tolerance)
        let txn = Transaction::new(date(2026, 1, 2), "Test")
            .with_synthesized_posting(Posting::auto("Assets:Cash"))
            .with_synthesized_posting(
                Posting::new("Assets:Abc", Amount::new(dec!(12.3340), "ABC")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit {
                            value: dec!(140.02),
                        })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Expenses:Abc",
                Amount::new(dec!(-0.01), "USD"),
            ));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // Check that Cash was filled
        assert_eq!(result.filled_indices, vec![0]);

        // The interpolated amount should be rounded to 2 decimal places
        // (matching the -0.01 USD in Expenses:Abc)
        let filled = &result.transaction.postings[0];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.currency, "USD");
        assert_eq!(
            amount.number,
            dec!(-1727.00),
            "should be -1727.00 USD (rounded to 2 decimal places)"
        );

        // The residual should be non-zero but small (within tolerance)
        let residual = result
            .residuals
            .get("USD")
            .copied()
            .unwrap_or(Decimal::ZERO);
        assert_eq!(
            residual,
            dec!(-0.003320),
            "residual should be -0.003320 USD"
        );
    }

    /// Test that interpolation uses the maximum scale when multiple amounts have different scales.
    #[test]
    fn test_interpolate_uses_max_scale() {
        // When we have amounts with different scales, use the maximum.
        // 0.1 USD (scale 1) and 0.001 USD (scale 3) -> interpolate to scale 3
        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_synthesized_posting(Posting::new("Expenses:A", Amount::new(dec!(0.1), "USD")))
            .with_synthesized_posting(Posting::new("Expenses:B", Amount::new(dec!(0.001), "USD")))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        let filled = &result.transaction.postings[2];
        let amount = get_amount(filled).expect("should have amount");

        // The amount is exactly -0.101, which fits in 3 decimal places
        assert_eq!(amount.number, dec!(-0.101));
        // Scale should be 3 (the maximum of 1 and 3)
        assert_eq!(amount.number.scale(), 3);
    }

    /// Test that cost spec scale is used when other postings have lower scale.
    ///
    /// Issue: <https://github.com/rustledger/rustledger/issues/333>
    ///
    /// When a transaction has:
    /// - A cost spec with decimal places (e.g., {2800.01 CAD})
    /// - Other postings with fewer decimal places (e.g., 1 CAD)
    ///
    /// The interpolated amount should use the cost spec's scale, not the
    /// lower scale from other postings.
    #[test]
    fn test_interpolate_cost_scale_preserved() {
        // From issue #333:
        // 2026-01-19 * "Buy stock"
        //   Assets:Stock  1 CSU { 2800.01 CAD }
        //   Expenses:Commission  1 CAD
        //   Assets:Cash
        //
        // Cost: 1 * 2800.01 = 2800.01 CAD (scale 2)
        // Commission: 1 CAD (scale 0)
        // Without fix: Cash rounds to -2801.00 (scale 0), leaving 0.01 residual
        // With fix: Cash is -2801.01 (scale 2), transaction balances
        let txn = Transaction::new(date(2026, 1, 19), "Buy stock")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(1), "CSU")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit {
                            value: dec!(2800.01),
                        })
                        .with_currency("CAD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Expenses:Commission",
                Amount::new(dec!(1), "CAD"),
            ))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        // Check that Cash was filled
        assert_eq!(result.filled_indices, vec![2]);

        // The interpolated amount should be -2801.01 (scale 2 from cost spec)
        let filled = &result.transaction.postings[2];
        let amount = get_amount(filled).expect("should have amount");
        assert_eq!(amount.currency, "CAD");
        assert_eq!(
            amount.number,
            dec!(-2801.01),
            "should be -2801.01 CAD (preserving cost spec precision)"
        );

        // Transaction should balance (no residual)
        let residual = result
            .residuals
            .get("CAD")
            .copied()
            .unwrap_or(Decimal::ZERO);
        assert!(
            residual.is_zero(),
            "CAD residual should be 0, got {residual}"
        );
    }

    // =========================================================================
    // Currency inference from cost basis tests
    // =========================================================================

    /// Test that zero-amount postings are removed when transaction balances perfectly.
    /// Zero-amount interpolated postings are pruned by booking.
    ///
    /// When a transaction with cost basis balances to zero (cost equals
    /// cash), the elided counterpart fills with 0 and gets dropped from
    /// the booked output — matches Python beancount's display behavior.
    /// The #877 invariant (catching E1001 on the elided posting's
    /// account) is preserved by running the loader's early-phase
    /// account validator BEFORE booking; see `rustledger-validate`'s
    /// `Phase::Early` and `test_zero_interpolated_posting_keeps_e1001_on_unopened_account`
    /// in `rustledger-loader/tests/loader_test.rs` for the
    /// end-to-end coverage.
    ///
    /// Example:
    /// ```beancount
    /// Assets:Crypto    100 USDC {1.0 USD, 2022-04-16}
    /// Assets:Cash     -100 USD
    /// Income:Trading   ; <- fills to 0 USD, pruned
    /// ```
    #[test]
    fn test_interpolate_balanced_cost_prunes_zero_posting() {
        let txn = Transaction::new(date(2022, 4, 16), "Trade")
            .with_synthesized_posting(
                Posting::new("Assets:Crypto", Amount::new(dec!(100), "USDC")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(1.0) })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-100), "USD")))
            .with_synthesized_posting(Posting::auto("Income:Trading"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        assert!(
            result.filled_indices.is_empty(),
            "zero-amount filled posting should have been pruned"
        );
        assert_eq!(
            result.transaction.postings.len(),
            2,
            "Income:Trading filled to 0 USD should be pruned"
        );
        assert!(
            !result
                .transaction
                .postings
                .iter()
                .any(|p| p.account.as_str() == "Income:Trading"),
            "Income:Trading should not be in postings after pruning"
        );
    }

    /// Zero-cost basis: empty posting fills to 0 and is pruned.
    ///
    /// Example:
    /// ```beancount
    /// Assets:Crypto    100 TOKEN {0 USD}
    /// Income:Bonus     ; <- fills to 0 USD, pruned
    /// ```
    #[test]
    fn test_interpolate_zero_cost_prunes_zero_posting() {
        let txn = Transaction::new(date(2022, 4, 16), "Free tokens")
            .with_synthesized_posting(
                Posting::new("Assets:Crypto", Amount::new(dec!(100), "TOKEN")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::PerUnit { value: dec!(0) })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Income:Bonus"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        assert!(
            result.filled_indices.is_empty(),
            "zero-amount filled posting should have been pruned"
        );
        assert_eq!(result.transaction.postings.len(), 1);
    }

    /// Zero total cost: empty posting fills to 0 and is pruned.
    ///
    /// Example:
    /// ```beancount
    /// Assets:Crypto    100 TOKEN {{0 USD}}
    /// Income:Bonus     ; <- fills to 0 USD, pruned
    /// ```
    #[test]
    fn test_interpolate_zero_total_cost_prunes_zero_posting() {
        let txn = Transaction::new(date(2022, 4, 16), "Free tokens")
            .with_synthesized_posting(
                Posting::new("Assets:Crypto", Amount::new(dec!(100), "TOKEN")).with_cost(
                    rustledger_core::CostSpec::empty()
                        .with_number(rustledger_core::CostNumber::Total { value: dec!(0) })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::auto("Income:Bonus"));

        let result = interpolate(&txn).expect("interpolation should succeed");

        assert!(
            result.filled_indices.is_empty(),
            "zero-amount filled posting should have been pruned"
        );
        assert_eq!(result.transaction.postings.len(), 1);
    }

    // ─── Issue #1026: empty cost spec + missing posting in same group ───
    //
    // bean-check rejects with "Too many missing numbers for currency
    // group 'CCY'" when a transaction has both:
    //   1. A posting with empty cost spec `{}` (cost-basis weight unknown
    //      until booking-pass lot matching).
    //   2. Another posting in the same currency group missing its amount.
    //
    // Pre-fix, rledger silently used the price annotation as the
    // posting's weight when cost was unknown, producing a balanced
    // residual and accepting the transaction.

    /// Minimal repro from #1026's body: position with `{} @ price` plus
    /// missing-amount Income:PnL must error.
    #[test]
    fn test_interpolate_empty_cost_spec_with_missing_amount_errors() {
        use rustledger_core::CostSpec;

        let txn = Transaction::new(date(2022, 1, 12), "sell what was never bought")
            .with_synthesized_posting(
                Posting::new(
                    "Assets:Htsec:Positions",
                    Amount::new(dec!(-13000.00), "SH513050"),
                )
                .with_cost(CostSpec::empty()) // empty `{}` — unknown cost
                .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                    dec!(1.300),
                    "CNY",
                ))),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Htsec:Cash",
                Amount::new(dec!(16900.00), "CNY"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Htsec:Cash",
                Amount::new(dec!(-0.85), "CNY"),
            ))
            .with_synthesized_posting(Posting::new(
                "Expenses:Htsec:Commission",
                Amount::new(dec!(0.85), "CNY"),
            ))
            .with_synthesized_posting(Posting::auto("Income:Htsec:PnL"));

        let result = interpolate(&txn);
        assert!(
            matches!(result, Err(InterpolationError::MultipleMissing { .. })),
            "expected MultipleMissing error from empty cost spec + missing posting; got {result:?}"
        );
        if let Err(InterpolationError::MultipleMissing { currency, count }) = result {
            assert_eq!(currency.as_str(), "CNY");
            assert!(
                count >= 2,
                "expected count >= 2 unknowns in CNY group, got {count}"
            );
        }
    }

    /// Empty cost spec by itself (no other missing posting) is OK — the
    /// booking pass will resolve the lot match. Pre- and post-fix should
    /// agree.
    #[test]
    fn test_interpolate_empty_cost_spec_alone_ok() {
        use rustledger_core::CostSpec;

        let txn = Transaction::new(date(2022, 1, 12), "Sell HOOL")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "HOOL"))
                    .with_cost(CostSpec::empty())
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(150),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(1500), "USD")));

        let result = interpolate(&txn);
        assert!(
            result.is_ok(),
            "single empty cost spec with no missing postings should succeed; got {result:?}"
        );
    }

    /// Two empty cost specs in the same currency group: two cost-unknowns
    /// in one group, no missing-amount postings needed → still errors.
    #[test]
    fn test_interpolate_two_empty_cost_specs_same_currency_errors() {
        use rustledger_core::CostSpec;

        let txn = Transaction::new(date(2022, 1, 12), "Two unknown-cost sells")
            .with_synthesized_posting(
                Posting::new("Assets:StockA", Amount::new(dec!(-10), "AAPL"))
                    .with_cost(CostSpec::empty())
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(150),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(
                Posting::new("Assets:StockB", Amount::new(dec!(-5), "GOOG"))
                    .with_cost(CostSpec::empty())
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(2000),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(11500), "USD")));

        let result = interpolate(&txn);
        assert!(
            matches!(result, Err(InterpolationError::MultipleMissing { .. })),
            "two empty cost specs in same currency should error; got {result:?}"
        );
    }

    /// Issue #1705: an augmenting `{}` posting with one balancing leg has
    /// its per-unit cost inferred from the residual (like beancount), not
    /// left with an empty cost basis. `1000 USD {}` + `-900 EUR` → the lot
    /// is booked at 0.90 EUR/unit.
    #[test]
    fn test_interpolate_augmenting_empty_cost_inferred_from_residual() {
        use rustledger_core::{CostNumber, CostSpec};

        let txn = Transaction::new(date(2024, 1, 2), "buy USD")
            .with_synthesized_posting(
                Posting::new("Assets:Broker", Amount::new(dec!(1000), "USD"))
                    .with_cost(CostSpec::empty()), // augmenting `{}` — no price
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(-900), "EUR")));

        let result = interpolate(&txn).expect("augmenting `{}` should interpolate its cost");
        let cost = result.transaction.postings[0]
            .cost
            .as_ref()
            .expect("cost spec should be present");
        assert_eq!(cost.currency.as_deref(), Some("EUR"));
        match cost.number {
            Some(CostNumber::PerUnitFromTotal(b)) => {
                assert_eq!(b.per_unit, dec!(0.90), "per-unit cost");
                assert_eq!(b.total, dec!(900), "preserved total");
            }
            other => panic!("expected PerUnitFromTotal, got {other:?}"),
        }
        // Cost currency now balances.
        assert_eq!(
            result
                .residuals
                .get("EUR")
                .copied()
                .unwrap_or(Decimal::ZERO),
            Decimal::ZERO
        );
    }

    /// Cost-unknown in one currency + missing-amount posting in a
    /// DIFFERENT currency: should succeed. The two unknowns belong to
    /// disjoint currency groups, so the rule is satisfied per-group.
    /// Verifies the rule check is per-currency, not global.
    #[test]
    fn test_interpolate_empty_cost_spec_with_missing_in_different_currency_ok() {
        use rustledger_core::CostSpec;

        let txn = Transaction::new(date(2022, 1, 12), "Sale + currency-known absorber")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "HOOL"))
                    .with_cost(CostSpec::empty()) // cost-unknown in USD
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(150),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(1500), "USD")))
            .with_synthesized_posting(Posting::new("Expenses:Fee", Amount::new(dec!(5), "EUR")))
            .with_synthesized_posting(Posting {
                // Missing amount, currency known via CurrencyOnly: lands in EUR.
                units: Some(IncompleteAmount::CurrencyOnly("EUR".into())),
                ..Posting::auto("Income:Misc")
            });

        let result = interpolate(&txn);
        assert!(
            result.is_ok(),
            "cost-unknown in USD + missing-amount in EUR should succeed (disjoint groups); \
             got {result:?}"
        );
    }

    /// Issue #1107: an interpolated residual must not inherit the high
    /// scale of a derived per-unit cost (which can be 26+ digits from
    /// `total / units` division). Python beancount quantizes the
    /// residual to currency precision derived from explicit posting
    /// units, not cost spec scales.
    ///
    /// Repro: a sell with explicit high-precision per-unit cost. Pre-fix,
    /// the cost scale (5) merged into `max_scale_by_currency[USD]`,
    /// rounding the residual to 5dp (`-36.72498`). Post-fix, only the
    /// `336.73 USD` cash side contributes to USD precision (scale=2), so
    /// the residual is `-36.72` (matches bean-query exactly).
    #[test]
    fn test_interpolate_residual_ignores_cost_spec_scale() {
        use rustledger_core::CostSpec;

        let cost_spec = CostSpec {
            number: Some(rustledger_core::CostNumber::PerUnit {
                value: dec!(170.16734),
            }),
            currency: Some(Currency::from("USD")),
            date: None,
            label: None,
            merge: false,
        };

        let txn = Transaction::new(date(2016, 2, 12), "Sell")
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(336.73), "USD"),
            ))
            .with_synthesized_posting(
                Posting::new("Assets:Brokerage", Amount::new(dec!(-1.763), "STOCK"))
                    .with_cost(cost_spec)
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(191.00),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::auto("Income:Capital-Gains"));

        let result = interpolate(&txn).expect("interpolation should succeed");
        let filled = &result.transaction.postings[2];
        let amount = get_amount(filled).expect("Income should have amount");

        assert_eq!(
            amount.currency.as_str(),
            "USD",
            "residual currency should be USD"
        );
        assert_eq!(
            amount.number.scale(),
            2,
            "residual scale must be 2 (USD precision from `336.73 USD`), \
             not 5 (from cost spec). Pre-fix this was 5. (#1107)"
        );
        assert_eq!(
            amount.number,
            dec!(-36.72),
            "residual value should match bean-query exactly (#1107). \
             Was -36.72498 before fix."
        );
    }

    /// End-to-end #1107 repro through the booking pass — this is the
    /// path that actually surfaces in real ledgers, where the booking
    /// engine derives a 26+ digit per-unit cost from `{{total}} / units`
    /// (or lot-matches a `{}` sell against such a derived cost) and
    /// previously propagated that scale into the interpolated residual.
    ///
    /// Concretely models the healthequity fixture pattern: buy with
    /// `{{total}}` total cost, sell with `{}` lot-match. After booking,
    /// the sell's filled `CostSpec` carries the high-scale `per_unit` from
    /// the division — and interpolation must STILL round the missing
    /// Income residual to USD's 2dp (no posting-unit-scale cost-scale
    /// contamination).
    #[test]
    fn test_interpolate_residual_after_booking_total_cost_division() {
        use crate::book::BookingEngine;
        use rustledger_core::{Cost, CostSpec, IncompleteAmount, PriceAnnotation};

        // Buy: 1.763 STOCK {{300.00 USD}} → booking derives
        // per_unit = 300.00 / 1.763 = ~170.16449... at 26-digit scale.
        let buy = Transaction::new(date(2016, 1, 1), "Buy")
            .with_synthesized_posting(
                Posting::new("Assets:Brokerage", Amount::new(dec!(1.763), "STOCK")).with_cost(
                    CostSpec {
                        number: Some(rustledger_core::CostNumber::Total {
                            value: dec!(300.00),
                        }),
                        currency: Some(Currency::from("USD")),
                        date: None,
                        label: None,
                        merge: false,
                    },
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-300.00), "USD"),
            ));

        // Sell: -1.763 STOCK {} @ 191.00 USD — empty cost spec; booking
        // lot-matches against the previous buy, filling the high-scale
        // derived per_unit. Income is missing, must be interpolated.
        let sell = Transaction::new(date(2016, 2, 12), "Sell")
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(336.73), "USD"),
            ))
            .with_synthesized_posting(
                Posting::new("Assets:Brokerage", Amount::new(dec!(-1.763), "STOCK"))
                    .with_cost(CostSpec::empty())
                    .with_price(PriceAnnotation::unit(Amount::new(dec!(191.00), "USD"))),
            )
            .with_synthesized_posting(Posting::auto("Income:Capital-Gains"));

        let mut engine = BookingEngine::new();
        engine.apply(&buy).expect("fixture fits in Decimal");

        // book_and_interpolate handles the empty `{}` lot match AND
        // runs interpolation on the booked transaction. The Income
        // residual must end up at USD's 2dp scale — pre-fix this
        // inherited the lot's derived 26-digit per_unit scale.
        let result = engine
            .book_and_interpolate(&sell)
            .expect("booking+interpolation should succeed");

        let income = &result.transaction.postings[2];
        let amount = get_amount(income).expect("Income should have an amount after interpolation");

        assert_eq!(amount.currency.as_str(), "USD");
        assert!(
            amount.number.scale() <= 2,
            "residual scale must be ≤ 2 (USD's tracked precision), \
             not inherited from the lot's high-scale derived per_unit. \
             Got scale={} number={}",
            amount.number.scale(),
            amount.number
        );

        // Use `_ = Cost::new` to keep the import live without an
        // unrelated unused-import warning if the test grows.
        let _ = Cost::new(dec!(1), "USD");
        let _: Option<IncompleteAmount> = None;
    }

    /// UNASSIGNED missing posting (no currency context) instead of a
    /// currency-known one. bean-check rejects this because the
    /// unassigned could absorb residuals across all currencies including
    /// the cost-unknown's; the rejection is conservative-by-design.
    /// Pins the empirically-verified bean-check parity (#1026 review).
    #[test]
    fn test_interpolate_empty_cost_spec_with_unassigned_in_different_currency_errors() {
        use rustledger_core::CostSpec;

        let txn = Transaction::new(date(2022, 1, 12), "Sale + unassigned absorber")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(-10), "HOOL"))
                    .with_cost(CostSpec::empty())
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(150),
                        "USD",
                    ))),
            )
            .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(dec!(1500), "USD")))
            .with_synthesized_posting(Posting::new("Expenses:Fee", Amount::new(dec!(5), "EUR")))
            .with_synthesized_posting(Posting::auto("Income:Misc"));

        let result = interpolate(&txn);
        assert!(
            matches!(result, Err(InterpolationError::MultipleMissing { .. })),
            "cost-unknown + unassigned-missing must error even when in different \
             currencies (bean-check parity); got {result:?}"
        );
    }

    // ---- #1309 cluster 2: residual / price arithmetic ----------------
    // Exact-value assertions on the residual math so the surviving
    // mutants (cost/price `*`, residual `+=`, the multi-currency split
    // guard and index math) are killed.

    #[test]
    fn interpolate_unit_price_is_units_times_price() {
        // 10 STK @ 3 USD → the elided cash leg is -30 USD.
        let txn = Transaction::new(date(2024, 1, 1), "Buy")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "STK")).with_price(
                    rustledger_core::PriceAnnotation::unit(Amount::new(dec!(3), "USD")),
                ),
            )
            .with_synthesized_posting(Posting::auto("Assets:Cash"));
        let r = interpolate(&txn).expect("interpolation should succeed");
        let cash = get_amount(&r.transaction.postings[1]).expect("filled");
        assert_eq!(cash.currency, "USD");
        assert_eq!(cash.number, dec!(-30)); // kills `abs * price` and `* signum -> +`
    }

    #[test]
    fn interpolate_total_price_is_total() {
        // 10 STK @@ 30 USD → elided cash -30 USD.
        let txn = Transaction::new(date(2024, 1, 1), "Buy")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(10), "STK")).with_price(
                    rustledger_core::PriceAnnotation::total(Amount::new(dec!(30), "USD")),
                ),
            )
            .with_synthesized_posting(Posting::auto("Assets:Cash"));
        let r = interpolate(&txn).expect("interpolation should succeed");
        let cash = get_amount(&r.transaction.postings[1]).expect("filled");
        assert_eq!(cash.number, dec!(-30)); // kills total-price `* signum -> +`
        assert_eq!(cash.currency, "USD"); // right magnitude in the right currency
    }

    #[test]
    fn interpolate_three_posting_residual_sum() {
        // 100 USD + 25 USD + elided → cash -125 USD.
        let txn = Transaction::new(date(2024, 1, 1), "Split")
            .with_synthesized_posting(Posting::new("Expenses:A", Amount::new(dec!(100), "USD")))
            .with_synthesized_posting(Posting::new("Expenses:B", Amount::new(dec!(25), "USD")))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));
        let r = interpolate(&txn).expect("interpolation should succeed");
        let cash = get_amount(&r.transaction.postings[2]).expect("filled");
        assert_eq!(cash.number, dec!(-125)); // kills residual `+= -> -=`/`*=`
    }

    #[test]
    fn interpolate_single_elided_splits_two_currencies() {
        // One auto posting absorbs two currency residuals → two filled
        // postings (-100 USD, -50 EUR). Exercises the multi-currency
        // split path's guard and `len() - 1` index push.
        let txn = Transaction::new(date(2024, 1, 1), "FX")
            .with_synthesized_posting(Posting::new("Assets:USD", Amount::new(dec!(100), "USD")))
            .with_synthesized_posting(Posting::new("Assets:EUR", Amount::new(dec!(50), "EUR")))
            .with_synthesized_posting(Posting::auto("Equity:Balance"));
        let r = interpolate(&txn).expect("interpolation should succeed");
        let filled: Vec<Amount> = r
            .filled_indices
            .iter()
            .map(|&i| {
                get_amount(&r.transaction.postings[i])
                    .expect("filled")
                    .clone()
            })
            .collect();
        assert_eq!(filled.len(), 2, "one elided posting should split into two");
        assert!(
            filled
                .iter()
                .any(|a| a.currency == "USD" && a.number == dec!(-100))
        );
        assert!(
            filled
                .iter()
                .any(|a| a.currency == "EUR" && a.number == dec!(-50))
        );
    }

    #[test]
    fn interpolate_post_fill_residual_returns_to_zero() {
        // After filling the elided leg, the tracked residual must return
        // to zero (kills the post-fill `residual += interpolated` mutants:
        // `-=` → 2R, `*=` → R·interpolated).
        let txn = Transaction::new(date(2024, 1, 1), "Split")
            .with_synthesized_posting(Posting::new("Expenses:A", Amount::new(dec!(100), "USD")))
            .with_synthesized_posting(Posting::new("Expenses:B", Amount::new(dec!(25), "USD")))
            .with_synthesized_posting(Posting::auto("Assets:Cash"));
        let r = interpolate(&txn).expect("interpolation should succeed");
        assert_eq!(
            r.residuals.get("USD").copied(),
            Some(dec!(0)),
            "residual must be exactly zero after the elided leg is filled"
        );
    }

    #[test]
    fn interpolate_preserves_subcent_residual() {
        // Explicit USD legs net to zero; a 0.001 USD per-unit price
        // contribution leaves a sub-cent residual. The currency's tracked
        // scale is 2 (from the 1.00 USD legs), so naively rounding the
        // -0.001 fill to 0.00 would silently leave the txn unbalanced.
        // `round_interpolated` must keep full precision — kills the
        // `!residual.is_zero()` guard.
        let txn = Transaction::new(date(2024, 1, 1), "subcent")
            .with_synthesized_posting(Posting::new("Assets:A", Amount::new(dec!(1.00), "USD")))
            .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(-1.00), "USD")))
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(1), "STK")).with_price(
                    rustledger_core::PriceAnnotation::unit(Amount::new(dec!(0.001), "USD")),
                ),
            )
            .with_synthesized_posting(Posting::auto("Assets:Cash"));
        let r = interpolate(&txn).expect("interpolation should succeed");
        let cash = r
            .filled_indices
            .iter()
            .map(|&i| get_amount(&r.transaction.postings[i]).expect("filled"))
            .find(|a| a.currency == "USD")
            .expect("a USD fill");
        assert_eq!(
            cash.number,
            dec!(-0.001),
            "sub-cent residual must be preserved, not rounded to zero"
        );
    }

    #[test]
    fn interpolate_currency_only_fill_zeroes_residual() {
        // A CurrencyOnly elided leg (`Assets:Cash USD`, number missing)
        // is filled via the known-currency path; the post-fill residual
        // must return to zero (kills that path's `residual += interpolated`).
        let txn = Transaction::new(date(2024, 1, 1), "currency-only")
            .with_synthesized_posting(Posting::new("Expenses:X", Amount::new(dec!(100), "USD")))
            .with_synthesized_posting(Posting::with_incomplete(
                "Assets:Cash",
                IncompleteAmount::CurrencyOnly("USD".into()),
            ));
        let r = interpolate(&txn).expect("interpolation should succeed");
        let cash = get_amount(&r.transaction.postings[1]).expect("filled");
        assert_eq!(cash.number, dec!(-100));
        assert_eq!(r.residuals.get("USD").copied(), Some(dec!(0)));
    }

    #[test]
    fn interpolate_number_only_with_a_price_is_refused() {
        // A NumberOnly leg (`-100`, currency missing) carrying `@ 1 USD`.
        //
        // This used to assert that the leg contributed `-100` to the USD
        // residual, treating the PRICE currency as the units currency. It is
        // not: `-100 @ 1 USD` is minus one hundred of something, and nothing
        // in the transaction says what. Python beancount refuses the same
        // input with "Could not resolve units currency" (#1920).
        //
        // The unit multiplier of 1 is what made the old behavior look
        // harmless here; at any other price the residual was wrong as well.
        let txn = Transaction::new(date(2024, 1, 1), "number-only")
            .with_synthesized_posting(Posting::new("Expenses:X", Amount::new(dec!(100), "USD")))
            .with_synthesized_posting(
                Posting::with_incomplete("Assets:Cash", IncompleteAmount::NumberOnly(dec!(-100)))
                    .with_price(rustledger_core::PriceAnnotation::unit(Amount::new(
                        dec!(1),
                        "USD",
                    ))),
            );
        match interpolate(&txn) {
            Err(InterpolationError::CannotInferCurrency { account }) => {
                assert_eq!(account.as_str(), "Assets:Cash");
            }
            other => panic!("expected CannotInferCurrency, got {other:?}"),
        }
    }

    // ---- #1911: solving a missing units NUMBER when the units CURRENCY is
    // known but a cost or price redenominates the posting's weight ----

    /// `Assets:A  HOOL {300.00 USD}` — units currency written, number elided.
    fn units_currency_only(account: &str, currency: &str) -> Posting {
        Posting {
            units: Some(IncompleteAmount::CurrencyOnly(currency.into())),
            ..Posting::auto(account)
        }
    }

    fn per_unit_cost(value: Decimal, currency: &str) -> CostSpec {
        CostSpec::empty()
            .with_number(CostNumber::PerUnit { value })
            .with_currency(currency)
    }

    /// The `IncompleteInputs.UnitsMissingNumberWithCost` vector: the number is
    /// `residual / cost_per_unit`, written in the UNITS currency.
    #[test]
    fn interpolates_units_number_from_per_unit_cost() {
        let txn = Transaction::new(date(2010, 5, 28), "Buy")
            .with_synthesized_posting(
                units_currency_only("Assets:Account1", "HOOL")
                    .with_cost(per_unit_cost(dec!(300.00), "USD")),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Account2",
                Amount::new(dec!(-600.00), "USD"),
            ));

        let result = interpolate(&txn).expect("solvable: 600.00 / 300.00");

        assert_eq!(result.filled_indices, vec![0]);
        let filled = get_amount(&result.transaction.postings[0]).expect("filled");
        assert_eq!(filled.number, dec!(2), "600.00 / 300.00");
        assert_eq!(
            filled.currency, "HOOL",
            "denominated in the posting's own commodity, NOT the cost currency"
        );
        assert_eq!(
            result.residuals.get("USD").copied(),
            Some(Decimal::ZERO),
            "the solved units must weigh 600.00 USD and cancel the cash leg"
        );
    }

    /// The inverse must actually invert the canonical forward weight function.
    /// This is the drift guard: if `cost_number_weight` changes how a per-unit
    /// cost weighs, solving by division silently stops agreeing with it, and
    /// nothing else in the suite would notice.
    #[test]
    fn solved_units_reproduce_the_canonical_cost_weight() {
        for (per_unit, cash) in [
            (dec!(300.00), dec!(-600.00)),
            (dec!(1.25), dec!(-100.00)),
            // Negative cash: solved to negative units.
            (dec!(300.00), dec!(600.00)),
        ] {
            let txn = Transaction::new(date(2010, 5, 28), "Buy")
                .with_synthesized_posting(
                    units_currency_only("Assets:Stock", "HOOL")
                        .with_cost(per_unit_cost(per_unit, "USD")),
                )
                .with_synthesized_posting(Posting::new("Assets:Cash", Amount::new(cash, "USD")));

            let result = interpolate(&txn).expect("solvable");
            let solved = get_amount(&result.transaction.postings[0]).expect("filled");
            let cost = result.transaction.postings[0]
                .cost
                .as_ref()
                .and_then(|c| c.number.as_ref())
                .expect("cost number");

            let weight = crate::cost_number_weight(solved.number, cost).expect("in range");
            assert_eq!(
                weight, -cash,
                "canonical weight of the solved units must cancel the cash leg \
                 (per_unit={per_unit}, cash={cash})"
            );
        }
    }

    /// A per-unit PRICE scales the weight the same way a per-unit cost does,
    /// so the same inversion applies.
    #[test]
    fn interpolates_units_number_from_per_unit_price() {
        let txn = Transaction::new(date(2010, 5, 28), "Buy")
            .with_synthesized_posting(units_currency_only("Assets:Account1", "HOOL").with_price(
                rustledger_core::PriceAnnotation::unit(Amount::new(dec!(300.00), "USD")),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Account2",
                Amount::new(dec!(-600.00), "USD"),
            ));

        let result = interpolate(&txn).expect("solvable: 600.00 / 300.00");
        let filled = get_amount(&result.transaction.postings[0]).expect("filled");
        assert_eq!(filled.number, dec!(2));
        assert_eq!(filled.currency, "HOOL");
        assert_eq!(result.residuals.get("USD").copied(), Some(Decimal::ZERO));
    }

    /// The quotient is quantized against the UNITS currency's observed scale,
    /// not the cost currency's — the currency it is actually written in.
    ///
    /// Only the VALUE is asserted. Python beancount stores a scale here (`2.00`
    /// where it stores a bare `2` without the extra HOOL posting) because it
    /// quantizes at booking time; rledger stores the value and pads at render
    /// via `DisplayContext`, so `rledger` also SHOWS `2.00` while holding `2`.
    /// That is the presentation-versus-value split of ADR-0008 and #1909, not a
    /// divergence: `2 == 2.00` as a quantity.
    #[test]
    fn solved_units_quantize_to_the_units_currency_scale() {
        let txn = Transaction::new(date(2010, 5, 28), "Buy")
            .with_synthesized_posting(
                units_currency_only("Assets:Account1", "HOOL")
                    .with_cost(per_unit_cost(dec!(300.00), "USD")),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Account2",
                Amount::new(dec!(-600.00), "USD"),
            ))
            .with_synthesized_posting(Posting::new(
                "Assets:Other",
                Amount::new(dec!(5.00), "HOOL"),
            ));

        let result = interpolate(&txn).expect("solvable");
        let filled = get_amount(&result.transaction.postings[0]).expect("filled");
        assert_eq!(filled.number, dec!(2), "600.00 / 300.00, written in HOOL");
        assert_eq!(filled.currency, "HOOL");
        assert_eq!(
            result.residuals.get("USD").copied(),
            Some(Decimal::ZERO),
            "USD still cancels"
        );
        assert_eq!(
            result.residuals.get("HOOL").copied(),
            Some(dec!(5.00)),
            "the cost-carrying posting must NOT absorb the HOOL residual: it \
             weighs in USD only. Before #1911 it solved to -5.00 HOOL here — \
             a lot with the wrong sign AND magnitude."
        );
    }

    /// A cost-carrying posting weighs in the cost currency, so a residual in
    /// its own units currency is none of its business. Previously this filled
    /// `-10.00 HOOL {300.00 USD}`, fabricating a 3000 USD lot from thin air.
    #[test]
    fn cost_posting_does_not_absorb_its_units_currency_residual() {
        let txn = Transaction::new(date(2010, 5, 28), "Buy")
            .with_synthesized_posting(Posting::new(
                "Assets:Account1",
                Amount::new(dec!(10.00), "HOOL"),
            ))
            .with_synthesized_posting(
                units_currency_only("Assets:Account2", "HOOL")
                    .with_cost(per_unit_cost(dec!(300.00), "USD")),
            );

        let result = interpolate(&txn).expect("solves to zero, then fails to balance later");
        assert_eq!(
            result.transaction.postings.len(),
            1,
            "no USD residual to solve from, so the posting solves to zero units \
             and is pruned by the zero-prune step — beancount drops it too"
        );
        assert_eq!(
            result.residuals.get("HOOL").copied(),
            Some(dec!(10.00)),
            "the 10.00 HOOL imbalance survives to be reported"
        );
    }

    /// Every shape whose weight does not vary with the units number must be
    /// REFUSED, never silently left unfilled: `validate_transaction_balance`
    /// skips a transaction containing an unfilled posting, so a silent skip
    /// would accept an unbalanced transaction outright.
    #[test]
    fn refuses_units_whose_weight_does_not_vary_with_them() {
        let cash = Posting::new("Assets:Cash", Amount::new(dec!(-600.00), "USD"));

        let total_cost = CostSpec::empty()
            .with_number(CostNumber::Total {
                value: dec!(600.00),
            })
            .with_currency("USD");
        let zero_cost = per_unit_cost(dec!(0.00), "USD");
        let compound = CostSpec::empty()
            .with_number(CostNumber::Compound {
                per_unit: dec!(300.00),
                total: dec!(5.00),
            })
            .with_currency("USD");
        let empty_spec = CostSpec::empty().with_currency("USD");

        let cases: Vec<(&str, Posting)> = vec![
            (
                "total cost",
                units_currency_only("Assets:S", "HOOL").with_cost(total_cost),
            ),
            (
                "zero per-unit cost",
                units_currency_only("Assets:S", "HOOL").with_cost(zero_cost),
            ),
            (
                "compound cost",
                units_currency_only("Assets:S", "HOOL").with_cost(compound),
            ),
            (
                "empty cost spec",
                units_currency_only("Assets:S", "HOOL").with_cost(empty_spec),
            ),
            (
                "total price",
                units_currency_only("Assets:S", "HOOL").with_price(
                    rustledger_core::PriceAnnotation::total(Amount::new(dec!(600.00), "USD")),
                ),
            ),
            (
                "zero per-unit price",
                units_currency_only("Assets:S", "HOOL").with_price(
                    rustledger_core::PriceAnnotation::unit(Amount::new(dec!(0.00), "USD")),
                ),
            ),
            (
                "cost spec but no units currency at all",
                Posting::auto("Assets:S").with_cost(per_unit_cost(dec!(300.00), "USD")),
            ),
        ];

        for (label, posting) in cases {
            let txn = Transaction::new(date(2010, 5, 28), "Buy")
                .with_synthesized_posting(posting)
                .with_synthesized_posting(cash.clone());

            match interpolate(&txn) {
                Err(InterpolationError::UnsolvableUnits { account, reason }) => {
                    assert_eq!(account.as_str(), "Assets:S", "{label}");
                    assert!(!reason.is_empty(), "{label}: reason must explain why");
                }
                Err(other) => panic!("{label}: expected UnsolvableUnits, got {other}"),
                Ok(result) => panic!(
                    "{label}: expected a refusal, but interpolation returned {:?}. \
                     An unfilled posting that does NOT error is silently accepted \
                     by validate_transaction_balance.",
                    result
                        .transaction
                        .postings
                        .iter()
                        .map(|p| p.units.clone())
                        .collect::<Vec<_>>()
                ),
            }
        }
    }

    /// Two solvable unknowns landing in the SAME weight currency stay ambiguous.
    /// The cost posting is counted against USD (where its weight lands), not
    /// HOOL, so it collides with the plain elided USD posting exactly as
    /// beancount's `InterpolationError` does.
    #[test]
    fn two_unknowns_in_the_same_weight_currency_are_ambiguous() {
        let txn = Transaction::new(date(2010, 5, 28), "Buy")
            .with_synthesized_posting(
                units_currency_only("Assets:Stock", "HOOL")
                    .with_cost(per_unit_cost(dec!(300.00), "USD")),
            )
            .with_synthesized_posting(units_currency_only("Assets:Cash", "USD"))
            .with_synthesized_posting(Posting::new(
                "Assets:Other",
                Amount::new(dec!(-600.00), "USD"),
            ));

        match interpolate(&txn) {
            Err(InterpolationError::MultipleMissing { currency, count }) => {
                assert_eq!(
                    currency,
                    Currency::from("USD"),
                    "counted where the weights land"
                );
                assert_eq!(count, 2);
            }
            other => panic!("expected MultipleMissing in USD, got {other:?}"),
        }
    }

    // ---- #1914: the canonical grouping the E3002 validator enforces ----

    /// The grouping is not eyeballable from the posting: a per-unit cost
    /// redenominates the weight, so `HOOL {300.00 USD}` is an unknown in USD.
    #[test]
    fn elided_groups_use_the_weight_currency_not_the_units_currency() {
        let txn = Transaction::new(date(2010, 5, 28), "Buy")
            .with_synthesized_posting(
                units_currency_only("Assets:Stock", "HOOL")
                    .with_cost(per_unit_cost(dec!(300.00), "USD")),
            )
            .with_synthesized_posting(units_currency_only("Assets:Euro", "EUR"))
            .with_synthesized_posting(Posting::new("Assets:C", Amount::new(dec!(-600.00), "USD")))
            .with_synthesized_posting(Posting::new("Assets:D", Amount::new(dec!(-50.00), "EUR")));

        let groups = elided_unknown_groups(&txn);
        assert_eq!(
            groups,
            vec![
                (0, UnknownGroup::Currency("USD".into())),
                (1, UnknownGroup::Currency("EUR".into())),
            ],
            "the cost posting belongs to USD (where its weight lands), not HOOL"
        );
    }

    /// A fully-elided posting cannot be placed until the residuals are known.
    /// A `NumberOnly` posting with a currency in reach is not an unknown at all.
    #[test]
    fn elided_groups_classify_bare_and_number_only_postings() {
        let mut number_only = Posting::auto("Assets:WithCost");
        number_only.units = Some(IncompleteAmount::NumberOnly(dec!(10)));
        let number_only = number_only.with_cost(per_unit_cost(dec!(300.00), "USD"));

        let mut naked_number = Posting::auto("Assets:Naked");
        naked_number.units = Some(IncompleteAmount::NumberOnly(dec!(10)));

        let txn = Transaction::new(date(2010, 5, 28), "Mixed")
            .with_synthesized_posting(Posting::auto("Assets:Bare"))
            .with_synthesized_posting(number_only)
            .with_synthesized_posting(naked_number)
            .with_synthesized_posting(Posting::new("Assets:C", Amount::new(dec!(-600.00), "USD")));

        let groups = elided_unknown_groups(&txn);
        assert_eq!(
            groups,
            vec![(0, UnknownGroup::Unassigned)],
            "only the fully-bare posting is an unknown. Index 1 and index 2 are \
             NumberOnly: their number is written, so once a currency is read off \
             the balance they contribute a KNOWN weight rather than competing for \
             a residual (#1920). Index 3 is complete."
        );
    }

    /// Drift guard. If this grouping ever disagrees with the one `interpolate`
    /// actually solves by, the E3002 validator starts rejecting transactions
    /// the solver would have handled — which is exactly bug #1914. Two unknowns
    /// the grouping calls same-currency MUST make `interpolate` say so too, and
    /// two it calls disjoint MUST interpolate cleanly.
    #[test]
    fn elided_groups_agree_with_what_interpolate_solves() {
        let same = Transaction::new(date(2010, 5, 28), "Same group")
            .with_synthesized_posting(
                units_currency_only("Assets:Stock", "HOOL")
                    .with_cost(per_unit_cost(dec!(300.00), "USD")),
            )
            .with_synthesized_posting(units_currency_only("Assets:Cash", "USD"))
            .with_synthesized_posting(Posting::new("Assets:C", Amount::new(dec!(-600.00), "USD")));

        let groups = elided_unknown_groups(&same);
        let usd = UnknownGroup::Currency("USD".into());
        assert_eq!(
            groups.iter().filter(|(_, g)| *g == usd).count(),
            2,
            "grouping must see both unknowns in USD"
        );
        match interpolate(&same) {
            Err(InterpolationError::MultipleMissing { currency, count }) => {
                assert_eq!(
                    currency,
                    Currency::from("USD"),
                    "same currency the grouping named"
                );
                assert_eq!(count, 2);
            }
            other => panic!("grouping says ambiguous in USD; interpolate says {other:?}"),
        }

        let disjoint = Transaction::new(date(2010, 5, 28), "Disjoint groups")
            .with_synthesized_posting(
                units_currency_only("Assets:Stock", "HOOL")
                    .with_cost(per_unit_cost(dec!(300.00), "USD")),
            )
            .with_synthesized_posting(units_currency_only("Assets:Euro", "EUR"))
            .with_synthesized_posting(Posting::new("Assets:C", Amount::new(dec!(-600.00), "USD")))
            .with_synthesized_posting(Posting::new("Assets:D", Amount::new(dec!(-50.00), "EUR")));

        let groups = elided_unknown_groups(&disjoint);
        let mut seen: Vec<_> = groups.iter().map(|(_, g)| g.clone()).collect();
        seen.dedup();
        assert_eq!(seen.len(), 2, "grouping must see two distinct groups");
        let result = interpolate(&disjoint).expect("disjoint groups interpolate cleanly");
        assert_eq!(
            get_amount(&result.transaction.postings[0]).map(|a| a.number),
            Some(dec!(2)),
            "600.00 / 300.00"
        );
        assert_eq!(
            get_amount(&result.transaction.postings[1]).map(|a| a.number),
            Some(dec!(50.00))
        );
    }

    // ---- #1915: a bare price sigil (`@` / `@@`) is a request to COMPUTE the
    // price, not an absent price ----

    fn bare_unit_price(account: &str, number: Decimal, currency: &str) -> Posting {
        Posting::new(account, Amount::new(number, currency))
            .with_price(rustledger_core::PriceAnnotation::unit_empty())
    }

    fn solved_price(posting: &Posting) -> Option<(Decimal, Currency, rustledger_core::PriceKind)> {
        let price = posting.price.as_ref()?;
        let amount = price
            .amount
            .as_ref()
            .and_then(IncompleteAmount::as_amount)?;
        Some((amount.number, amount.currency.clone(), price.kind))
    }

    /// `100.00 USD @` against `-50.00 EUR` has exactly one answer: 0.5 EUR.
    #[test]
    fn solves_a_bare_unit_price_from_the_residual() {
        let txn = Transaction::new(date(2010, 5, 28), "Convert")
            .with_synthesized_posting(bare_unit_price("Assets:A", dec!(100.00), "USD"))
            .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(-50.00), "EUR")));

        let result = interpolate(&txn).expect("solvable");
        let (number, currency, kind) =
            solved_price(&result.transaction.postings[0]).expect("price filled");
        assert_eq!(number, dec!(0.5));
        assert_eq!(currency, Currency::from("EUR"));
        assert_eq!(
            kind,
            rustledger_core::PriceKind::Unit,
            "stays a per-unit `@`"
        );
        assert_eq!(
            result.residuals.get("EUR").copied(),
            Some(Decimal::ZERO),
            "the solved price must make the transaction balance"
        );
    }

    /// A `@@` sigil is answered with a TOTAL, and stays a `@@`. Python
    /// beancount normalizes this to a per-unit price; keeping the form the
    /// author chose is the ADR-0008 position, and the weight is identical.
    #[test]
    fn solves_a_bare_total_price_and_keeps_the_total_form() {
        let txn = Transaction::new(date(2010, 5, 28), "Convert")
            .with_synthesized_posting(
                Posting::new("Assets:A", Amount::new(dec!(100.00), "USD"))
                    .with_price(rustledger_core::PriceAnnotation::total_empty()),
            )
            .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(-50.00), "EUR")));

        let result = interpolate(&txn).expect("solvable");
        let (number, currency, kind) =
            solved_price(&result.transaction.postings[0]).expect("price filled");
        assert_eq!(number, dec!(50.00), "the TOTAL, not the 0.5 per-unit rate");
        assert_eq!(currency, Currency::from("EUR"));
        assert_eq!(kind, rustledger_core::PriceKind::Total);
        assert_eq!(result.residuals.get("EUR").copied(), Some(Decimal::ZERO));
    }

    /// The sign convention, which is where Python beancount goes wrong. It
    /// solves the MAGNITUDE (`|residual| / |units|`), so on
    /// `IncompleteInputs.PriceMissing` it fills `@1.2 CAD` against a POSITIVE
    /// `120.00 CAD` and then reports the 240 CAD imbalance it just created.
    /// The value that balances is -1.2, and a negative price is not a price,
    /// so refuse and say so.
    #[test]
    fn refuses_a_bare_price_that_would_have_to_be_negative() {
        let txn = Transaction::new(date(2010, 5, 28), "PriceMissing vector")
            .with_synthesized_posting(bare_unit_price("Assets:Account1", dec!(100.00), "USD"))
            .with_synthesized_posting(Posting::new(
                "Assets:Account2",
                Amount::new(dec!(120.00), "CAD"),
            ));

        match interpolate(&txn) {
            Err(InterpolationError::NegativeInferredPrice {
                account,
                currency,
                price,
            }) => {
                assert_eq!(account.as_str(), "Assets:Account1");
                assert_eq!(currency, Currency::from("CAD"));
                assert_eq!(price, dec!(-1.2));
            }
            other => panic!("expected NegativeInferredPrice, got {other:?}"),
        }
    }

    /// The sigil competes for a residual, so it is an unknown for the
    /// one-per-currency-group rule — the whole point of #1915.
    #[test]
    fn a_bare_price_counts_as_an_unknown_in_its_group() {
        let mut elided = Posting::auto("Assets:Cash");
        elided.units = Some(IncompleteAmount::CurrencyOnly("USD".into()));

        let txn = Transaction::new(date(2010, 5, 28), "Two unknowns in USD")
            .with_synthesized_posting(bare_unit_price("Assets:A", dec!(100.00), "USD"))
            .with_synthesized_posting(elided);

        match interpolate(&txn) {
            Err(InterpolationError::MultipleMissing { currency, count }) => {
                assert_eq!(currency, Currency::from("USD"));
                assert_eq!(count, 2, "the elided posting AND the bare price");
            }
            other => panic!("expected MultipleMissing in USD, got {other:?}"),
        }
    }

    /// The group is the other postings' WEIGHT currency, not their units
    /// currency: `? CAD @ 1.2 USD` weighs in USD, so a bare sigil facing it
    /// resolves in USD and collides there. Reading CAD off the units would put
    /// the two unknowns in different groups and hide the ambiguity — which is
    /// exactly what an earlier draft of this fix did.
    #[test]
    fn a_bare_price_resolves_against_weight_currencies_not_units_currencies() {
        let mut priced_elided = Posting::auto("Assets:Account2");
        priced_elided.units = Some(IncompleteAmount::CurrencyOnly("CAD".into()));
        let priced_elided = priced_elided.with_price(rustledger_core::PriceAnnotation::unit(
            Amount::new(dec!(1.2), "USD"),
        ));

        let txn = Transaction::new(date(2010, 5, 28), "UnitsMissingNumberWithPrice vector")
            .with_synthesized_posting(priced_elided)
            .with_synthesized_posting(bare_unit_price("Assets:Account1", dec!(100.00), "USD"));

        match interpolate(&txn) {
            Err(InterpolationError::MultipleMissing { currency, count }) => {
                assert_eq!(currency, Currency::from("USD"), "not CAD");
                assert_eq!(count, 2);
            }
            other => panic!("expected MultipleMissing in USD, got {other:?}"),
        }
    }

    /// Cost beats price, so alongside a cost the sigil never touches the
    /// balance — it feeds implicit price directives only. Treating it as a
    /// weight unknown there would reject transactions that are perfectly
    /// determined by their cost basis.
    #[test]
    fn a_bare_price_beside_a_cost_is_inert() {
        let txn = Transaction::new(date(2010, 5, 28), "Buy with a bare price")
            .with_synthesized_posting(
                Posting::new("Assets:Stock", Amount::new(dec!(2), "HOOL"))
                    .with_cost(per_unit_cost(dec!(300.00), "USD"))
                    .with_price(rustledger_core::PriceAnnotation::unit_empty()),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(dec!(-600.00), "USD"),
            ));

        let result = interpolate(&txn).expect("the cost determines the weight");
        assert_eq!(result.residuals.get("USD").copied(), Some(Decimal::ZERO));
    }

    /// Both the units number and the price missing is two unknowns on one
    /// posting; one residual cannot determine both.
    #[test]
    fn refuses_a_bare_price_on_a_units_missing_posting() {
        let mut both_missing = Posting::auto("Assets:A");
        both_missing.units = Some(IncompleteAmount::CurrencyOnly("USD".into()));
        let both_missing = both_missing.with_price(rustledger_core::PriceAnnotation::unit_empty());

        let txn = Transaction::new(date(2010, 5, 28), "Two unknowns, one posting")
            .with_synthesized_posting(both_missing)
            .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(-100.00), "USD")));

        match interpolate(&txn) {
            Err(InterpolationError::UnsolvableUnits { account, .. }) => {
                assert_eq!(account.as_str(), "Assets:A");
            }
            other => panic!("expected UnsolvableUnits, got {other:?}"),
        }
    }

    /// `@ USD` — the form beancount's own parser docs call "recommended" —
    /// states the answer's currency and leaves only the number to compute. The
    /// declared currency must WIN over inference: `100.00 USD @ CAD` against
    /// `-50.00 EUR` must not be written back as `@ 0.50 EUR`, substituting a
    /// currency the author never wrote.
    #[test]
    fn a_declared_price_currency_is_not_overridden_by_inference() {
        let declared = |currency: &str| {
            Posting::new("Assets:A", Amount::new(dec!(100.00), "USD")).with_price(
                rustledger_core::PriceAnnotation {
                    kind: rustledger_core::PriceKind::Unit,
                    amount: Some(IncompleteAmount::CurrencyOnly(currency.into())),
                },
            )
        };

        // Declared currency agrees with the residual: solve the number in it.
        let agrees = Transaction::new(date(2010, 5, 28), "Declared EUR")
            .with_synthesized_posting(declared("EUR"))
            .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(-50.00), "EUR")));
        let result = interpolate(&agrees).expect("solvable");
        let (number, currency, _) =
            solved_price(&result.transaction.postings[0]).expect("price filled");
        assert_eq!(number, dec!(0.5));
        assert_eq!(currency, Currency::from("EUR"));

        // Declared currency has nothing to cancel. The arithmetic would give
        // `@ 0 CAD`; writing that would put a rate in the ledger that the author
        // never chose and the balance never implied, so leave it unanswered and
        // let the balance validator report the currency that actually fails.
        let conflicts = Transaction::new(date(2010, 5, 28), "Declared CAD")
            .with_synthesized_posting(declared("CAD"))
            .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(-50.00), "EUR")));
        let result = interpolate(&conflicts).expect("no interpolation error");
        assert!(
            solved_price(&result.transaction.postings[0]).is_none(),
            "must not invent a rate in a currency the balance says nothing about"
        );
        assert_eq!(
            result.residuals.get("EUR").copied(),
            Some(dec!(-50.00)),
            "the real imbalance survives to be reported"
        );
    }

    /// The fallback candidate list must use each posting's WEIGHT currency,
    /// which for a cost-bearing posting is the COST currency. `HOOL {300.00
    /// USD}` offers USD, never HOOL.
    ///
    /// Reading the commodity off its units instead put this sigil in a HOOL
    /// group and the cost posting in a USD one, so two unknowns that genuinely
    /// compete looked disjoint and the transaction was reported as a bare
    /// imbalance rather than as over-constrained. Caught in review of #1919.
    #[test]
    fn bare_price_fallback_uses_cost_currency_not_units_currency() {
        let mut elided_at_cost = Posting::auto("Assets:B");
        elided_at_cost.units = Some(IncompleteAmount::CurrencyOnly("HOOL".into()));
        let elided_at_cost = elided_at_cost.with_cost(per_unit_cost(dec!(300.00), "USD"));

        // Every other posting is itself an unknown, so all residuals are zero
        // and the fallback path is the one that runs.
        let txn = Transaction::new(date(2010, 5, 28), "Both weigh in USD")
            .with_synthesized_posting(bare_unit_price("Assets:A", dec!(100.00), "USD"))
            .with_synthesized_posting(elided_at_cost);

        match interpolate(&txn) {
            Err(InterpolationError::MultipleMissing { currency, count }) => {
                assert_eq!(currency, Currency::from("USD"), "not HOOL");
                assert_eq!(count, 2, "the bare sigil AND the cost posting's units");
            }
            other => panic!("expected MultipleMissing in USD, got {other:?}"),
        }
    }

    /// A zero-units posting carrying a bare sigil has a KNOWN currency; what
    /// fails is that no price gives zero units any weight. The error must say
    /// that, not send the author off to write a price currency they already
    /// have. (Python beancount raises `decimal.DivisionByZero` on this input,
    /// unguarded, where its sibling cost branch checks `units.number != ZERO`.)
    #[test]
    fn refuses_a_bare_price_on_zero_units_without_blaming_the_currency() {
        let txn = Transaction::new(date(2010, 5, 28), "Zero units")
            .with_synthesized_posting(bare_unit_price("Assets:A", dec!(0.00), "USD"))
            .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(-50.00), "EUR")));

        match interpolate(&txn) {
            Err(InterpolationError::UnsolvablePrice { account, reason }) => {
                assert_eq!(account.as_str(), "Assets:A");
                assert!(reason.contains("zero units"), "got: {reason}");
            }
            other => panic!("expected UnsolvablePrice, got {other:?}"),
        }
    }

    /// Zero units AND a balanced book: the sigil is simply unanswerable and
    /// harmless, so leave it rather than erroring.
    #[test]
    fn leaves_a_bare_price_on_zero_units_alone_when_the_books_balance() {
        let txn = Transaction::new(date(2010, 5, 28), "Zero units, balanced")
            .with_synthesized_posting(bare_unit_price("Assets:A", dec!(0.00), "USD"))
            .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(0.00), "EUR")));

        let result = interpolate(&txn).expect("harmless");
        assert!(solved_price(&result.transaction.postings[0]).is_none());
    }

    /// `@ 1.20` writes the price NUMBER and elides only its currency. The
    /// number is data: infer the currency, keep the number.
    ///
    /// Treating it as a sigil overwrote the author's rate with whatever
    /// balanced the books (`1.20` became `1.00`), and diverged from
    /// `calculate_residual`, which has its own test pinning that an incomplete
    /// price with a number does NOT get re-solved. Caught in review of #1919.
    #[test]
    fn price_number_without_a_currency_keeps_its_number() {
        let priced = |number: Decimal| {
            Posting::new("Assets:A", Amount::new(dec!(100.00), "USD")).with_price(
                rustledger_core::PriceAnnotation::unit_incomplete(IncompleteAmount::NumberOnly(
                    number,
                )),
            )
        };

        // Does not balance: 100.00 x 1.20 = 120.00 against -100.00.
        let off = Transaction::new(date(2010, 5, 28), "rate written, currency elided")
            .with_synthesized_posting(priced(dec!(1.20)))
            .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(-100.00), "USD")));
        let result = interpolate(&off).expect("currency is inferable");
        let (number, currency, _) =
            solved_price(&result.transaction.postings[0]).expect("price completed");
        assert_eq!(number, dec!(1.20), "the author's rate, not a re-solved one");
        assert_eq!(currency, Currency::from("USD"));
        assert_eq!(
            result.residuals.get("USD").copied(),
            Some(dec!(20.0000)),
            "the imbalance the author's own rate implies must survive to be reported"
        );

        // And when the rate does balance, it is simply accepted.
        let ok = Transaction::new(date(2010, 5, 28), "rate written, balances")
            .with_synthesized_posting(priced(dec!(1.20)))
            .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(-120.00), "USD")));
        let result = interpolate(&ok).expect("currency is inferable");
        assert_eq!(
            solved_price(&result.transaction.postings[0]).map(|(n, _, _)| n),
            Some(dec!(1.20))
        );
        assert_eq!(result.residuals.get("USD").copied(), Some(Decimal::ZERO));
    }

    /// The fallback candidate scan must see a price currency written WITHOUT a
    /// number (`@ USD`). `crate::price_currency_of` reads only a complete price
    /// amount, so using it made a posting priced `@ USD` offer its units
    /// currency instead, splitting two unknowns that genuinely compete.
    /// Caught in review of #1919.
    #[test]
    fn bare_price_fallback_sees_a_currency_only_price() {
        let bare = bare_unit_price("Assets:A", dec!(100.00), "EUR");
        let at_usd = Posting::new("Assets:B", Amount::new(dec!(200.00), "CAD")).with_price(
            rustledger_core::PriceAnnotation::unit_incomplete(IncompleteAmount::CurrencyOnly(
                "USD".into(),
            )),
        );

        // Both prices are still to be computed, so every residual is zero and
        // the fallback path is the one that runs.
        let txn = Transaction::new(date(2010, 5, 28), "both weigh in USD")
            .with_synthesized_posting(bare)
            .with_synthesized_posting(at_usd);

        match interpolate(&txn) {
            Err(InterpolationError::MultipleMissing { currency, count }) => {
                assert_eq!(currency, Currency::from("USD"), "not CAD, and not EUR");
                assert_eq!(count, 2);
            }
            other => panic!("expected MultipleMissing in USD, got {other:?}"),
        }
    }

    // ---- #1920: a units number written without a currency ----

    fn number_only(account: &str, number: Decimal) -> Posting {
        Posting::with_incomplete(account, IncompleteAmount::NumberOnly(number))
    }

    /// The author's number is DATA, not something to solve for. Only the
    /// currency is read off the balance.
    ///
    /// Previously such a posting joined `unassigned_missing` and was filled
    /// from the residual, so `120.00` against `-999.00 USD` was booked as
    /// `999.00 USD`: the number the author typed was replaced by whatever made
    /// the books balance, and `check` reported success.
    #[test]
    fn number_only_keeps_its_number_and_only_gains_a_currency() {
        let txn = Transaction::new(date(2010, 5, 28), "currency omitted")
            .with_synthesized_posting(number_only("Assets:A", dec!(120.00)))
            .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(-999.00), "USD")));

        let result = interpolate(&txn).expect("currency is inferable");
        let filled = get_amount(&result.transaction.postings[0]).expect("filled");
        assert_eq!(
            filled.number,
            dec!(120.00),
            "the author's number, not 999.00"
        );
        assert_eq!(filled.currency, "USD");
        assert_eq!(
            result.residuals.get("USD").copied(),
            Some(dec!(-879.00)),
            "the imbalance must survive to be reported, not be papered over"
        );
    }

    /// The same shape when it does balance: accepted, number intact. This is
    /// what Python beancount does too.
    #[test]
    fn number_only_balances_when_the_number_is_right() {
        let txn = Transaction::new(date(2010, 5, 28), "currency omitted, balanced")
            .with_synthesized_posting(number_only("Assets:A", dec!(120.00)))
            .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(-120.00), "USD")));

        let result = interpolate(&txn).expect("currency is inferable");
        let filled = get_amount(&result.transaction.postings[0]).expect("filled");
        assert_eq!(filled.number, dec!(120.00));
        assert_eq!(filled.currency, "USD");
        assert_eq!(result.residuals.get("USD").copied(), Some(Decimal::ZERO));
    }

    /// A cost or price names ITS OWN currency, never the commodity being
    /// counted, so with either present the units currency is unknowable.
    /// Beancount agrees ("Could not resolve units currency").
    ///
    /// Before this, both shapes left the posting unfilled AND unreported, so
    /// `validate_transaction_balance` took its documented early return and an
    /// arbitrarily unbalanced transaction passed silently.
    #[test]
    fn number_only_with_a_cost_or_price_is_refused() {
        let cash = Posting::new("Assets:B", Amount::new(dec!(-999.00), "USD"));

        let with_price = number_only("Assets:A", dec!(120.00)).with_price(
            rustledger_core::PriceAnnotation::unit(Amount::new(dec!(1.2), "USD")),
        );
        let with_cost =
            number_only("Assets:A", dec!(10)).with_cost(per_unit_cost(dec!(300.00), "USD"));

        for (label, posting) in [("price", with_price), ("cost", with_cost)] {
            let txn = Transaction::new(date(2010, 5, 28), "unknowable commodity")
                .with_synthesized_posting(posting)
                .with_synthesized_posting(cash.clone());
            match interpolate(&txn) {
                Err(InterpolationError::CannotInferCurrency { account }) => {
                    assert_eq!(account.as_str(), "Assets:A", "{label}");
                }
                other => panic!("{label}: expected CannotInferCurrency, got {other:?}"),
            }
        }
    }

    /// No single currency to read off means no answer. Refuse rather than pick.
    #[test]
    fn number_only_is_refused_when_the_currency_is_ambiguous() {
        let txn = Transaction::new(date(2010, 5, 28), "two candidate currencies")
            .with_synthesized_posting(number_only("Assets:A", dec!(120.00)))
            .with_synthesized_posting(Posting::new("Assets:B", Amount::new(dec!(-50.00), "USD")))
            .with_synthesized_posting(Posting::new("Assets:C", Amount::new(dec!(-70.00), "EUR")));

        match interpolate(&txn) {
            Err(InterpolationError::CannotInferCurrency { account }) => {
                assert_eq!(account.as_str(), "Assets:A");
            }
            other => panic!("expected CannotInferCurrency, got {other:?}"),
        }
    }
}
