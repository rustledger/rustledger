//! Amount and cost formatting.

use super::{escape_string, format_incomplete_amount};
use crate::{Amount, CostSpec, PriceAnnotation};

/// Format an amount.
pub fn format_amount(amount: &Amount) -> String {
    format!("{} {}", amount.number, amount.currency)
}

/// Format a cost specification.
pub fn format_cost_spec(spec: &CostSpec) -> String {
    // Max 5 elements: amount, date, label, merge
    let mut parts = Vec::with_capacity(5);

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
    match price {
        PriceAnnotation::Unit(amount) => format!("@ {}", format_amount(amount)),
        PriceAnnotation::Total(amount) => format!("@@ {}", format_amount(amount)),
        PriceAnnotation::UnitIncomplete(inc) => format!("@ {}", format_incomplete_amount(inc)),
        PriceAnnotation::TotalIncomplete(inc) => format!("@@ {}", format_incomplete_amount(inc)),
        PriceAnnotation::UnitEmpty => "@".to_string(),
        PriceAnnotation::TotalEmpty => "@@".to_string(),
    }
}
