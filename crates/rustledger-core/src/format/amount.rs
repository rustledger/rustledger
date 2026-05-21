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

    // Amount (per-unit or total)
    if let (Some(num), Some(curr)) = (&spec.number_per, &spec.currency) {
        parts.push(format!("{num} {curr}"));
    } else if let (Some(num), Some(curr)) = (&spec.number_total, &spec.currency) {
        // Total cost uses double braces
        return format!("{{{{{num} {curr}}}}}");
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
