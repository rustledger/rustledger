//! Plugin that generates price entries from transaction costs and prices.

use crate::types::{
    AmountData, DirectiveData, DirectiveWrapper, PluginInput, PluginOutput, PriceAnnotationData,
    PriceAnnotationView, PriceData,
};
use rust_decimal::Decimal;
use rustledger_core::extract_per_unit_price;
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

                // Use the typed `view()` enum to derive `is_total` and
                // pull the amount via exhaustive matching — the type
                // system rejects code that confuses Unit and Total
                // (which was exactly the #992 bug shape). We then
                // build the helper's `Option<(is_total, number,
                // currency)>` descriptor; the helper ties currency to
                // value for us, so passing `None` on parse failure or
                // an incomplete annotation cleanly falls through to
                // cost without pairing a fall-through value with a
                // stale annotation currency.
                let annotation = posting
                    .price
                    .as_ref()
                    .map(PriceAnnotationData::view)
                    .and_then(|view| {
                        let (is_total, amount) = match view {
                            PriceAnnotationView::Unit(a) => (false, a),
                            PriceAnnotationView::Total(a) => (true, a),
                            // Incomplete annotations: helper can't use
                            // them; drop the descriptor entirely.
                            PriceAnnotationView::UnitIncomplete { .. }
                            | PriceAnnotationView::TotalIncomplete { .. } => return None,
                        };
                        let number = Decimal::from_str(&amount.number).ok()?;
                        Some((is_total, number, amount.currency.clone()))
                    });

                // Same shape for cost: only build the descriptor when
                // a currency is present AND at least one of per/total
                // parses.
                let cost = posting.cost.as_ref().and_then(|c| {
                    let currency = c.currency.clone()?;
                    let per = c
                        .number_per
                        .as_ref()
                        .and_then(|n| Decimal::from_str(n).ok());
                    let total = c
                        .number_total
                        .as_ref()
                        .and_then(|n| Decimal::from_str(n).ok());
                    if per.is_none() && total.is_none() {
                        return None;
                    }
                    Some((per, total, currency))
                });

                let Some((per_unit, quote_currency)) =
                    extract_per_unit_price(units_number, annotation, cost)
                else {
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
