//! Shared implicit-price extraction logic.
//!
//! Mirrors Python beancount's `implicit_prices` plugin behavior. Used
//! by BOTH the BQL query path (`rustledger-query::price`) and the
//! native `implicit_prices` plugin (`rustledger-plugin`). Centralizing
//! avoids the parallel-implementations divergence that produced
//! [issue #992]: the plugin emitted `@@` total amounts as per-unit
//! prices, while the query path correctly divided them.
//!
//! The helper is a pure function over primitives (Decimals, bools,
//! Options) rather than over rich types, because the plugin and query
//! paths use different transaction representations
//! (`crate::Transaction` vs `rustledger_plugin_types::TransactionData`).
//! Each caller extracts the primitives from its own type and feeds them
//! in.
//!
//! [issue #992]: https://github.com/rustledger/rustledger/issues/992

use rust_decimal::Decimal;

/// Which input source produced an extracted implicit price.
///
/// Returned alongside the per-unit `Decimal` so callers know which
/// quote-currency source to pair with it. Pre-fix (Copilot review on
/// PR #997), callers picked the quote currency from the annotation
/// even when the per-unit value came from the cost — for inputs like
/// `0 ABC {50 USD} @@ 100 EUR` (zero-units total annotation falls
/// through to cost), they emitted `50 EUR` instead of `50 USD`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImplicitPriceSource {
    /// Value came from the `@` / `@@` price annotation.
    Annotation,
    /// Value came from the `{...}` cost spec.
    Cost,
}

/// Decide the per-unit price implied by a posting.
///
/// Resolution order, mirroring upstream beancount's
/// `beancount.plugins.implicit_prices`:
///
/// 1. **Price annotation** (`@` or `@@`) — if an amount is present.
///    For `@@` (total), divides the total by `units_number.abs()`.
///    For `@` (per-unit), returns the annotation amount directly.
/// 2. **Cost spec** — only as a fallback when no usable price
///    annotation. `number_per` is per-unit and used directly;
///    `number_total` is divided by `units_number.abs()`.
/// 3. **No price** — returns `None`.
///
/// Edge cases:
/// - Zero units with a total-form input (annotation `@@` or
///   `cost.number_total`): can't compute per-unit, falls through to
///   the next priority. If nothing else is available, returns `None`.
/// - Zero units with a per-unit-form input (annotation `@` or
///   `cost.number_per`): the per-unit amount is returned as-is —
///   "1 share = $X regardless of how many shares you transacted."
#[must_use]
pub fn extract_per_unit_price(
    units_number: Decimal,
    annotation_is_total: bool,
    annotation_amount: Option<Decimal>,
    cost_number_per: Option<Decimal>,
    cost_number_total: Option<Decimal>,
) -> Option<(Decimal, ImplicitPriceSource)> {
    // Priority 1: price annotation.
    if let Some(amount) = annotation_amount {
        if annotation_is_total {
            if !units_number.is_zero() {
                return Some((amount / units_number.abs(), ImplicitPriceSource::Annotation));
            }
            // Zero units + total annotation → can't compute per-unit,
            // fall through to cost. This matches the upstream behavior
            // (the @@ amount is unusable without a unit count).
        } else {
            return Some((amount, ImplicitPriceSource::Annotation));
        }
    }

    // Priority 2: cost spec.
    if let Some(per) = cost_number_per {
        return Some((per, ImplicitPriceSource::Cost));
    }
    if let Some(total) = cost_number_total
        && !units_number.is_zero()
    {
        return Some((total / units_number.abs(), ImplicitPriceSource::Cost));
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    // ===== Annotation cases =====

    #[test]
    fn unit_annotation_returns_amount_directly() {
        // @ 1.40 EUR with 5 units → 1.40 (per-unit, used as-is).
        let p = extract_per_unit_price(dec!(5), false, Some(dec!(1.40)), None, None);
        assert_eq!(p, Some((dec!(1.40), ImplicitPriceSource::Annotation)));
    }

    #[test]
    fn total_annotation_divides_by_unit_count() {
        // @@ 1500 USD with 10 units → 1500 / 10 = 150.
        let p = extract_per_unit_price(dec!(10), true, Some(dec!(1500)), None, None);
        assert_eq!(p, Some((dec!(150), ImplicitPriceSource::Annotation)));
    }

    #[test]
    fn total_annotation_uses_abs_unit_count() {
        // The classic #992 reproducer: @@ 15152.07 EUR with -27204.53 BAM
        // must produce 15152.07 / 27204.53 ≈ 0.557 (NOT -0.557, NOT 15152.07).
        let p = extract_per_unit_price(dec!(-27204.53), true, Some(dec!(15152.07)), None, None);
        let expected = dec!(15152.07) / dec!(27204.53);
        assert_eq!(p, Some((expected, ImplicitPriceSource::Annotation)));
        assert!(p.unwrap().0 > dec!(0.55) && p.unwrap().0 < dec!(0.56));
    }

    #[test]
    fn total_annotation_with_zero_units_falls_through_to_cost() {
        // @@ 100 USD on 0 units → can't compute per-unit, but if a cost
        // is also present, fall through to that. The SOURCE returned is
        // Cost, so the caller knows to pick the cost's currency (this
        // is the Copilot-flagged bug from PR #997: pre-fix, callers
        // unconditionally picked the annotation currency, producing
        // mismatched (number, currency) pairs).
        let p = extract_per_unit_price(dec!(0), true, Some(dec!(100)), Some(dec!(50)), None);
        assert_eq!(p, Some((dec!(50), ImplicitPriceSource::Cost)));
    }

    #[test]
    fn total_annotation_with_zero_units_and_no_cost_returns_none() {
        let p = extract_per_unit_price(dec!(0), true, Some(dec!(100)), None, None);
        assert_eq!(p, None);
    }

    // ===== Cost cases =====

    #[test]
    fn cost_per_unit_used_when_no_annotation() {
        // 10 ABC {50.00 USD} → 50.00.
        let p = extract_per_unit_price(dec!(10), false, None, Some(dec!(50.00)), None);
        assert_eq!(p, Some((dec!(50.00), ImplicitPriceSource::Cost)));
    }

    #[test]
    fn cost_total_divides_by_unit_count() {
        // 10 ABC {{500 USD}} → 500 / 10 = 50.
        let p = extract_per_unit_price(dec!(10), false, None, None, Some(dec!(500)));
        assert_eq!(p, Some((dec!(50), ImplicitPriceSource::Cost)));
    }

    #[test]
    fn cost_total_with_zero_units_returns_none() {
        let p = extract_per_unit_price(dec!(0), false, None, None, Some(dec!(500)));
        assert_eq!(p, None);
    }

    // ===== Priority interactions =====

    #[test]
    fn annotation_wins_over_cost_when_both_present() {
        // 5 ABC {1.25 EUR} @ 1.40 EUR → 1.40 (annotation wins).
        // Source = Annotation so the caller pairs with the annotation's
        // currency, not the cost's.
        let p = extract_per_unit_price(dec!(5), false, Some(dec!(1.40)), Some(dec!(1.25)), None);
        assert_eq!(p, Some((dec!(1.40), ImplicitPriceSource::Annotation)));
    }

    #[test]
    fn total_annotation_wins_over_cost_per_unit() {
        // -10 ABC {1.25 EUR} @@ 14 EUR → 14 / 10 = 1.40 (annotation wins).
        let p = extract_per_unit_price(dec!(-10), true, Some(dec!(14)), Some(dec!(1.25)), None);
        assert_eq!(p, Some((dec!(1.4), ImplicitPriceSource::Annotation)));
    }

    #[test]
    fn cost_per_wins_over_cost_total_when_both_present() {
        // {50 USD, 500 USD-total} — number_per takes precedence.
        let p = extract_per_unit_price(dec!(10), false, None, Some(dec!(50)), Some(dec!(999)));
        assert_eq!(p, Some((dec!(50), ImplicitPriceSource::Cost)));
    }

    // ===== Empty cases =====

    #[test]
    fn no_inputs_returns_none() {
        let p = extract_per_unit_price(dec!(10), false, None, None, None);
        assert_eq!(p, None);
    }

    #[test]
    fn annotation_without_amount_falls_through_to_cost() {
        // Incomplete annotation like `@ EUR` (no number) → ann_amount is
        // None → fall through. Cost present → use it. Source is Cost.
        let p = extract_per_unit_price(dec!(10), false, None, Some(dec!(7)), None);
        assert_eq!(p, Some((dec!(7), ImplicitPriceSource::Cost)));
    }
}
