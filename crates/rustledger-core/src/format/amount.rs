//! Amount and cost formatting.

use super::{escape_string, format_incomplete_amount};
use crate::{Amount, CostSpec, PriceAnnotation};

/// Format an amount.
pub fn format_amount(amount: &Amount) -> String {
    format!("{} {}", amount.number, amount.currency)
}

/// Format a cost specification.
pub fn format_cost_spec(spec: &CostSpec) -> String {
    // Max 4 elements: amount, date, label, merge.
    let mut parts = Vec::with_capacity(4);

    // Amount (per-unit or total). Currency is required for either
    // shape; the per-unit / total distinction comes from the typed
    // `CostNumber` (post-#1164 the invalid both-set state is
    // unrepresentable). `PerUnitFromTotal` renders in per-unit form
    // to match Python beancount's post-booking output.
    if let Some(curr) = &spec.currency {
        match spec.number {
            Some(crate::CostNumber::PerUnit { value: num }) => {
                parts.push(format!("{num} {curr}"));
            }
            Some(crate::CostNumber::PerUnitFromTotal(b)) => {
                parts.push(format!("{} {curr}", b.per_unit));
            }
            Some(crate::CostNumber::Total { value: num }) => {
                // Total cost uses double braces.
                return format!("{{{{{num} {curr}}}}}");
            }
            None => {}
        }
    }

    // Date
    if let Some(date) = spec.date {
        parts.push(date.to_string());
    }

    // Label
    if let Some(label) = &spec.label {
        parts.push(format!("\"{}\"", escape_string(label)));
    }

    // Merge marker
    if spec.merge {
        parts.push("*".to_string());
    }

    format!("{{{}}}", parts.join(", "))
}

/// Format a price annotation.
pub fn format_price_annotation(price: &PriceAnnotation) -> String {
    let sigil = price.kind.to_string();
    match &price.amount {
        Some(crate::IncompleteAmount::Complete(amt)) => {
            format!("{sigil} {}", format_amount(amt))
        }
        Some(inc) => format!("{sigil} {}", format_incomplete_amount(inc)),
        None => sigil,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BookedCost, CostNumber, CostSpec};
    use rust_decimal_macros::dec;

    #[test]
    fn cost_spec_per_unit_renders_single_braces() {
        let spec = CostSpec::empty()
            .with_number(crate::CostNumber::PerUnit { value: dec!(150) })
            .with_currency("USD");
        assert_eq!(format_cost_spec(&spec), "{150 USD}");
    }

    #[test]
    fn cost_spec_total_renders_double_braces() {
        let spec = CostSpec::empty()
            .with_number(crate::CostNumber::Total { value: dec!(1500) })
            .with_currency("USD");
        assert_eq!(format_cost_spec(&spec), "{{1500 USD}}");
    }

    #[test]
    fn cost_spec_per_unit_from_total_renders_as_per_unit() {
        // Python-compat post-booking rendering: the source `{{...}}`
        // becomes per-unit braces after booking derives a per_unit.
        // This is the load-bearing assertion for matching upstream
        // beancount's `Position.__str__` after booking — the original
        // `{{...}}` form is gone post-booking even in upstream.
        let b = BookedCost::new(dec!(150), dec!(300), dec!(2));
        let spec = CostSpec::empty()
            .with_number(CostNumber::PerUnitFromTotal(b))
            .with_currency("USD");
        assert_eq!(format_cost_spec(&spec), "{150 USD}");
    }

    #[test]
    fn cost_spec_empty_renders_braces() {
        let spec = CostSpec::empty();
        assert_eq!(format_cost_spec(&spec), "{}");
    }

    #[test]
    fn cost_spec_currency_only_renders_bare() {
        // Pin the existing behavior: `format_cost_spec` only emits
        // currency when a number is present. A currency-only spec
        // renders as `{}` (currency is dropped). This matches Python
        // beancount's `Position.__str__` for currency-only lot
        // matches.
        let spec = CostSpec::empty().with_currency("USD");
        assert_eq!(format_cost_spec(&spec), "{}");
    }
}
