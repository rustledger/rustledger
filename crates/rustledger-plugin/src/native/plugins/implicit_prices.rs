//! Plugin that generates price entries from transaction costs and prices.

use crate::types::{
    AmountData, DirectiveData, DirectiveWrapper, PluginInput, PluginOutput, PriceData,
};
use rust_decimal::Decimal;
use rustledger_core::{ImplicitPriceSource, extract_per_unit_price};
use std::str::FromStr;

use super::super::NativePlugin;

/// Plugin that generates price entries from transaction postings.
///
/// For each posting with a `@`/`@@` price annotation or a `{...}` cost
/// spec, generates a corresponding `Price` directive. Mirrors Python
/// beancount's `beancount.plugins.implicit_prices`.
///
/// Per-posting price math is delegated to
/// [`rustledger_core::extract_per_unit_price`] — the same helper used
/// by the BQL query path. Pre-fix (issue #992) this plugin had its own
/// implementation that emitted `@@` total amounts as per-unit prices
/// (off by a factor of `units`) AND emitted both an annotation-derived
/// AND a cost-derived price for postings that had both. Both bugs
/// disappear once the helper is the single source of truth.
pub struct ImplicitPricesPlugin;

impl NativePlugin for ImplicitPricesPlugin {
    fn name(&self) -> &'static str {
        "implicit_prices"
    }

    fn description(&self) -> &'static str {
        "Generate price entries from transaction costs/prices"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let mut new_directives = Vec::new();
        let mut generated_prices = Vec::new();

        for wrapper in &input.directives {
            new_directives.push(wrapper.clone());

            if wrapper.directive_type != "transaction" {
                continue;
            }

            let DirectiveData::Transaction(ref txn) = wrapper.data else {
                continue;
            };

            for posting in &txn.postings {
                let Some(ref units) = posting.units else {
                    continue;
                };
                let Ok(units_number) = Decimal::from_str(&units.number) else {
                    continue;
                };

                // Pull annotation primitives. Tie the currency to a
                // successfully-parsed number: if the number fails to
                // parse, drop the currency too. Otherwise the
                // helper would fall through to cost for the value but
                // we'd still pair it with the annotation's currency.
                let (annotation_is_total, annotation_amount, annotation_currency) =
                    match &posting.price {
                        Some(annotation) => {
                            let amount_decimal = annotation
                                .amount
                                .as_ref()
                                .and_then(|a| Decimal::from_str(&a.number).ok());
                            let amount_currency = if amount_decimal.is_some() {
                                annotation.amount.as_ref().map(|a| a.currency.clone())
                            } else {
                                None
                            };
                            (annotation.is_total, amount_decimal, amount_currency)
                        }
                        None => (false, None, None),
                    };

                // Pull cost primitives.
                let (cost_per, cost_total, cost_currency) = match &posting.cost {
                    Some(cost) => {
                        let per = cost
                            .number_per
                            .as_ref()
                            .and_then(|n| Decimal::from_str(n).ok());
                        let total = cost
                            .number_total
                            .as_ref()
                            .and_then(|n| Decimal::from_str(n).ok());
                        (per, total, cost.currency.clone())
                    }
                    None => (None, None, None),
                };

                let Some((per_unit, source)) = extract_per_unit_price(
                    units_number,
                    annotation_is_total,
                    annotation_amount,
                    cost_per,
                    cost_total,
                ) else {
                    continue;
                };

                // Pair the quote currency with the SAME source the helper
                // used. Pre-fix (Copilot review on PR #997) this was
                // unconditionally `annotation_currency.or(cost_currency)`,
                // which produced mismatched (number, currency) pairs when
                // an unusable `@@` annotation fell through to cost.
                let quote_currency = match source {
                    ImplicitPriceSource::Annotation => annotation_currency,
                    ImplicitPriceSource::Cost => cost_currency,
                };
                let Some(quote_currency) = quote_currency else {
                    continue;
                };

                generated_prices.push(DirectiveWrapper {
                    directive_type: "price".to_string(),
                    date: wrapper.date.clone(),
                    filename: None, // plugin-generated
                    lineno: None,
                    data: DirectiveData::Price(PriceData {
                        currency: units.currency.clone(),
                        amount: AmountData {
                            number: per_unit.to_string(),
                            currency: quote_currency,
                        },
                        metadata: vec![],
                    }),
                });
            }
        }

        new_directives.extend(generated_prices);

        PluginOutput {
            directives: new_directives,
            errors: Vec::new(),
        }
    }
}
