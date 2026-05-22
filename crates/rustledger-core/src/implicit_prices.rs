//! Shared implicit-price extraction logic.
//!
//! Mirrors Python beancount's `implicit_prices` plugin behavior. Used
//! by BOTH the BQL query path (`rustledger-query::price`) and the
//! native `implicit_prices` plugin (`rustledger-plugin`). Centralizing
//! avoids the parallel-implementations divergence that produced
//! [issue #992]: the plugin emitted `@@` total amounts as per-unit
//! prices, while the query path correctly divided them.
//!
//! The helper is generic over the currency type (`T`) because the
//! plugin and query paths use different transaction representations
//! (`crate::Transaction` with `InternedStr` vs
//! `rustledger_plugin_types::TransactionData` with `String`). Each
//! caller assembles its annotation/cost descriptors with its own
//! currency type and the helper returns the per-unit price already
//! paired with the matching currency — making mismatched
//! (number, currency) pairs impossible to construct.
//!
//! [issue #992]: https://github.com/rustledger/rustledger/issues/992

use rust_decimal::Decimal;

/// Decide the per-unit price implied by a posting and the quote
/// currency to pair with it.
///
/// The currency is returned alongside the per-unit `Decimal` so that
/// callers can never accidentally pair a cost-derived value with the
/// annotation currency. The helper matches each value to the currency
/// that came in with it.
///
/// Resolution order, mirroring upstream beancount's
/// `beancount.plugins.implicit_prices`:
///
/// 1. **Price annotation** (`@` or `@@`) — if a parsed number and
///    currency are present (`annotation` is `Some`).
///    For `@@` (`is_total = true`), divides the total by
///    `units_number.abs()`. For `@` (`is_total = false`), returns the
///    number directly.
/// 2. **Cost spec** — only as a fallback when no usable price
///    annotation. `CostNumber::PerUnit` and `PerUnitFromTotal` carry
///    a per-unit value directly. `CostNumber::Total` is divided by
///    `units_number.abs()`. (Pre-#1164 the cost spec could carry a
///    `number_per` *and* a `number_total` simultaneously; the typed
///    enum makes that state unrepresentable.)
/// 3. **No price** — returns `None`.
///
/// Edge cases:
/// - Zero units with a total-form input (annotation `@@` or
///   `CostNumber::Total`): can't compute per-unit, falls through to
///   the next priority. If nothing else is available, returns `None`.
/// - Zero units with a per-unit-form input (annotation `@`,
///   `CostNumber::PerUnit`, or `PerUnitFromTotal`): the per-unit
///   amount is returned as-is — "1 share = $X regardless of how many
///   shares you transacted."
///
/// # Parameters
///
/// - `units_number`: the posting's unit count (sign-insensitive — the
///   helper uses `.abs()` internally for total-form division).
/// - `annotation`: `Some((is_total, amount, currency))` if the posting
///   has a usable `@`/`@@` annotation. Callers should pass `None` for
///   incomplete annotations (e.g. `@ EUR` without a number) so the
///   helper falls through cleanly.
/// - `cost`: `Some((number, currency))` if the posting has a `{...}`
///   cost spec. The number is the typed `Option<CostNumber>` from the
///   spec — `None` means the spec carried no number at all (`{}`),
///   `Some(CostNumber::PerUnit)` and `Some(CostNumber::Total)` carry
///   their respective shapes. The mutual-exclusion invariant is
///   enforced by the type — pre-#1164 this was a `(Option<Decimal>,
///   Option<Decimal>)` pair that the helper had to defensively
///   tie-break.
#[must_use]
pub fn extract_per_unit_price<T>(
    units_number: Decimal,
    annotation: Option<(bool, Decimal, T)>,
    cost: Option<(Option<crate::CostNumber>, T)>,
) -> Option<(Decimal, T)> {
    // Priority 1: price annotation.
    if let Some((is_total, amount, currency)) = annotation {
        if is_total {
            if !units_number.is_zero() {
                return Some((amount / units_number.abs(), currency));
            }
            // Zero units + @@ → can't compute per-unit, fall through
            // to cost. Currency is dropped along with the value, so the
            // cost branch picks the cost's currency, not this one.
        } else {
            return Some((amount, currency));
        }
    }

    // Priority 2: cost spec. The pre-#1164 per-vs-total tie-break
    // becomes a single match: PerUnit and PerUnitFromTotal already
    // carry the per-unit value; Total carries a magnitude that
    // divides by `|units|` here.
    if let Some((number, currency)) = cost {
        match number {
            Some(crate::CostNumber::PerUnit { value: per }) => {
                return Some((per, currency));
            }
            Some(crate::CostNumber::PerUnitFromTotal(b)) => {
                return Some((b.per_unit, currency));
            }
            Some(crate::CostNumber::Total { value: total }) if !units_number.is_zero() => {
                return Some((total / units_number.abs(), currency));
            }
            Some(crate::CostNumber::Total { value: _ }) | None => {}
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    // Tests use `&'static str` for the currency type for readability.
    // Real callers pass `InternedStr` (query path) or `String`
    // (plugin path).

    // ===== Annotation cases =====

    #[test]
    fn unit_annotation_returns_amount_directly() {
        // @ 1.40 EUR with 5 units → 1.40 (per-unit, used as-is).
        let p = extract_per_unit_price(dec!(5), Some((false, dec!(1.40), "EUR")), None);
        assert_eq!(p, Some((dec!(1.40), "EUR")));
    }

    #[test]
    fn total_annotation_divides_by_unit_count() {
        // @@ 1500 USD with 10 units → 1500 / 10 = 150.
        let p = extract_per_unit_price(dec!(10), Some((true, dec!(1500), "USD")), None);
        assert_eq!(p, Some((dec!(150), "USD")));
    }

    #[test]
    fn total_annotation_uses_abs_unit_count() {
        // The classic #992 reproducer: @@ 15152.07 EUR with -27204.53 BAM
        // must produce 15152.07 / 27204.53 ≈ 0.557 (NOT -0.557, NOT 15152.07).
        let p = extract_per_unit_price(dec!(-27204.53), Some((true, dec!(15152.07), "EUR")), None);
        let expected = dec!(15152.07) / dec!(27204.53);
        assert_eq!(p, Some((expected, "EUR")));
        assert!(p.unwrap().0 > dec!(0.55) && p.unwrap().0 < dec!(0.56));
    }

    #[test]
    fn total_annotation_with_zero_units_falls_through_to_cost() {
        // @@ 100 EUR on 0 units → can't compute per-unit, fall through.
        // Cost is `{50 USD}` so we return (50, "USD"), NOT (50, "EUR")
        // — that's the Copilot-flagged bug from PR #997. Returning the
        // currency alongside the value makes the mismatched pair
        // impossible to construct.
        let p = extract_per_unit_price(
            dec!(0),
            Some((true, dec!(100), "EUR")),
            Some((Some(crate::CostNumber::PerUnit { value: dec!(50) }), "USD")),
        );
        assert_eq!(p, Some((dec!(50), "USD")));
    }

    #[test]
    fn total_annotation_with_zero_units_and_no_cost_returns_none() {
        let p = extract_per_unit_price::<&str>(dec!(0), Some((true, dec!(100), "EUR")), None);
        assert_eq!(p, None);
    }

    // ===== Cost cases =====

    #[test]
    fn cost_per_unit_used_when_no_annotation() {
        // 10 ABC {50.00 USD} → 50.00.
        let p = extract_per_unit_price(
            dec!(10),
            None,
            Some((
                Some(crate::CostNumber::PerUnit { value: dec!(50.00) }),
                "USD",
            )),
        );
        assert_eq!(p, Some((dec!(50.00), "USD")));
    }

    #[test]
    fn cost_total_divides_by_unit_count() {
        // 10 ABC {{500 USD}} → 500 / 10 = 50.
        let p = extract_per_unit_price(
            dec!(10),
            None,
            Some((Some(crate::CostNumber::Total { value: dec!(500) }), "USD")),
        );
        assert_eq!(p, Some((dec!(50), "USD")));
    }

    #[test]
    fn cost_total_with_zero_units_returns_none() {
        let p = extract_per_unit_price::<&str>(
            dec!(0),
            None,
            Some((Some(crate::CostNumber::Total { value: dec!(500) }), "USD")),
        );
        assert_eq!(p, None);
    }

    // ===== Priority interactions =====

    #[test]
    fn annotation_wins_over_cost_when_both_present() {
        // 5 ABC {1.25 EUR} @ 1.40 EUR → 1.40 (annotation wins).
        // Currency comes from the annotation — but in this case both
        // happen to be EUR so the test cannot distinguish a buggy
        // unconditional `annotation_currency.or(cost_currency)` from
        // the correct source-aware pick. See the zero-units test for
        // that distinction.
        let p = extract_per_unit_price(
            dec!(5),
            Some((false, dec!(1.40), "EUR")),
            Some((
                Some(crate::CostNumber::PerUnit { value: dec!(1.25) }),
                "EUR",
            )),
        );
        assert_eq!(p, Some((dec!(1.40), "EUR")));
    }

    #[test]
    fn total_annotation_wins_over_cost_per_unit() {
        // -10 ABC {1.25 EUR} @@ 14 EUR → 14 / 10 = 1.40 (annotation wins).
        let p = extract_per_unit_price(
            dec!(-10),
            Some((true, dec!(14), "EUR")),
            Some((
                Some(crate::CostNumber::PerUnit { value: dec!(1.25) }),
                "EUR",
            )),
        );
        assert_eq!(p, Some((dec!(1.4), "EUR")));
    }

    // Note: the pre-#1164 "cost_per wins over cost_total when both are set"
    // tie-break test is gone — the type system now forbids the both-set
    // state at construction time, so there's nothing to tie-break.

    // ===== Empty cases =====

    #[test]
    fn no_inputs_returns_none() {
        let p = extract_per_unit_price::<&str>(dec!(10), None, None);
        assert_eq!(p, None);
    }

    #[test]
    fn annotation_without_amount_falls_through_to_cost() {
        // Incomplete annotation like `@ EUR` (no number) → caller
        // passes `None` for annotation → fall through. Cost present →
        // use it. The returned currency is the cost's, not anything
        // remembered from the dropped annotation.
        let p = extract_per_unit_price(
            dec!(10),
            None,
            Some((Some(crate::CostNumber::PerUnit { value: dec!(7) }), "USD")),
        );
        assert_eq!(p, Some((dec!(7), "USD")));
    }
}
