//! Cross-check a sale's proceeds against its price.

use rust_decimal::Decimal;
use rustledger_core::PriceKind;
use rustledger_core::decimal::add_python_scale;

use crate::types::{
    DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput, PostingData,
    PriceAnnotationView,
};

use super::super::{NativePlugin, RegularPlugin};
use super::utils::at_entry;

/// Plugin that cross-checks a sale's proceeds against the price it was sold
/// at, as beancount's `sellgains` does.
///
/// For a transaction whose postings at cost all carry a price, the priced
/// value of those postings (`-units × price`) must match, currency by
/// currency and within twice the transaction's tolerance, the weight of its
/// postings to Assets, Liabilities, Equity and Expenses accounts (Income is
/// left out: that is the gain the check lets you elide).
///
/// This replaces a check of rledger's own (#2600) that only warned when a
/// priced sale had no Income or Expenses posting at all, and so missed the
/// typo in the proceeds this plugin exists to catch.
///
/// Deliberate divergence: beancount infers the tolerance with the ledger's
/// `inferred_tolerance_default`, `inferred_tolerance_multiplier` and
/// `infer_tolerance_from_cost` options. Plugins are not given those options
/// (they are not in `PluginOptions`, whose wire layout a WASM plugin decodes
/// positionally), so this uses beancount's defaults for them. beancount also
/// leaves out of the tolerance a posting booking interpolated; rledger's
/// plugin data does not mark those, so an interpolated posting's precision
/// counts here and can widen the tolerance (a cash leg booking computed as
/// `40.00` allows 0.01 where beancount allows none).
///
/// Amounts tied in beancount's print order (same-length currencies outside
/// its list, equal numbers) print in the order the postings come in, which
/// can differ from beancount's: its booking regroups a transaction's
/// postings by weight currency before plugins run, rledger's keeps them as
/// written.
///
/// Deliberate divergence: a `@@` total price is used exactly. beancount
/// turns it into a 28-digit per-unit price and multiplies back, so `-3 AAA
/// @@ 40 USD` against 40 USD of proceeds fails there by 1e-26.
pub struct SellGainsPlugin;

/// Amounts per currency, in the order each currency first appears, as a
/// beancount `Inventory` of plain amounts keeps them; a currency summing to
/// zero is dropped, as the inventory drops an empty position.
#[derive(Default, Clone)]
struct Amounts(Vec<(String, Decimal)>);

impl Amounts {
    fn add(&mut self, currency: &str, number: Decimal) {
        if let Some(i) = self.0.iter().position(|(c, _)| c == currency) {
            let sum = add_python_scale(self.0[i].1, number);
            if sum.is_zero() {
                self.0.remove(i);
            } else {
                self.0[i].1 = sum;
            }
        } else if !number.is_zero() {
            self.0.push((currency.to_string(), number));
        }
    }

    fn get(&self, currency: &str) -> Option<Decimal> {
        self.0.iter().find(|(c, _)| c == currency).map(|(_, n)| *n)
    }
}

/// beancount's `CURRENCY_ORDER`, which sorts an inventory's positions for
/// printing; any other currency sorts after these, by name length.
const CURRENCY_ORDER: [&str; 8] = ["USD", "EUR", "JPY", "CAD", "GBP", "AUD", "NZD", "CHF"];

impl std::fmt::Display for Amounts {
    /// As beancount prints an inventory, `(26 USD, 1 EUR)`: sorted by
    /// `Position.sortkey`, its currency's place in `CURRENCY_ORDER` (else
    /// 8 + the name's length), then the number.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut sorted: Vec<&(String, Decimal)> = self.0.iter().collect();
        sorted.sort_by_key(|(currency, number)| {
            let order = CURRENCY_ORDER
                .iter()
                .position(|c| c == currency)
                .unwrap_or(8 + currency.len());
            (order, *number)
        });
        f.write_str("(")?;
        for (i, (currency, number)) in sorted.into_iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{number} {currency}")?;
        }
        f.write_str(")")
    }
}

fn number(text: &str) -> Option<Decimal> {
    text.parse().ok()
}

/// A posting's price as `(number, kind, currency)`, when complete.
fn price_of(posting: &PostingData) -> Option<(Decimal, PriceKind, &str)> {
    match posting.price.as_ref()?.view() {
        PriceAnnotationView::Unit(a) => Some((number(&a.number)?, PriceKind::Unit, &a.currency)),
        PriceAnnotationView::Total(a) => Some((number(&a.number)?, PriceKind::Total, &a.currency)),
        _ => None,
    }
}

impl NativePlugin for SellGainsPlugin {
    fn name(&self) -> &'static str {
        "sellgains"
    }

    fn description(&self) -> &'static str {
        "Cross-check a sale's proceeds against its price"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let roots = &input.options.account_types;
        let mut errors = Vec::new();
        let defaults = rustc_hash::FxHashMap::default();
        let tolerance_options = rustledger_booking::ToleranceOptions {
            multiplier: Decimal::new(5, 1),
            infer_from_cost: false,
            defaults: &defaults,
        };

        for wrapper in &input.directives {
            let DirectiveData::Transaction(txn) = &wrapper.data else {
                continue;
            };
            // Only transactions whose lots at cost all have a price.
            let mut at_cost = txn.postings.iter().filter(|p| p.cost.is_some()).peekable();
            if at_cost.peek().is_none() || !at_cost.all(|p| price_of(p).is_some()) {
                continue;
            }

            let mut total_price = Amounts::default();
            let mut total_proceeds = Amounts::default();
            let mut readable = true;
            for posting in &txn.postings {
                let Some(units) = &posting.units else {
                    readable = false;
                    break;
                };
                let Some(units_number) = number(&units.number) else {
                    readable = false;
                    break;
                };
                if posting.cost.is_some() {
                    // The priced value of the lot sold: `-units × price`.
                    let (price, kind, currency) = price_of(posting).expect("checked above");
                    let Some(weight) = rustledger_booking::price_weight(units_number, price, kind)
                    else {
                        readable = false;
                        break;
                    };
                    total_price.add(currency, -weight);
                } else if !roots.is_income(&posting.account)
                    && (roots.is_balance_sheet(&posting.account)
                        || roots.is_expense(&posting.account))
                {
                    // Otherwise the posting's weight, Income left out.
                    let (weight, currency) = if let Some((price, kind, currency)) =
                        price_of(posting)
                    {
                        let Some(w) = rustledger_booking::price_weight(units_number, price, kind)
                        else {
                            readable = false;
                            break;
                        };
                        (w, currency)
                    } else {
                        (units_number, units.currency.as_str())
                    };
                    total_proceeds.add(currency, weight);
                }
            }
            if !readable {
                continue;
            }

            let tolerances = match crate::convert::wrapper_to_directive(wrapper) {
                Ok(rustledger_core::Directive::Transaction(t)) => {
                    rustledger_booking::transaction_tolerances(&t, &tolerance_options)
                }
                _ => continue,
            };
            let mut remaining = total_proceeds.clone();
            let invalid = total_price.0.iter().any(|(currency, price_number)| {
                // Twice the usual tolerance: rounding happens differently on
                // the two sides, and satisfying both by hand is hard.
                let tolerance = tolerances
                    .get(currency.as_str())
                    .copied()
                    .unwrap_or(Decimal::ZERO)
                    * Decimal::TWO;
                let proceeds = remaining.get(currency).unwrap_or(Decimal::ZERO);
                remaining.0.retain(|(c, _)| c != currency);
                (*price_number - proceeds).abs() > tolerance
            });
            if invalid || !remaining.0.is_empty() {
                let mut difference = total_price.clone();
                for (currency, number) in &total_proceeds.0 {
                    difference.add(currency, -*number);
                }
                errors.push(at_entry(
                    PluginError::error(format!(
                        "Invalid price vs. proceeds/gains: {total_price} vs. {total_proceeds}; difference: {difference}"
                    )),
                    wrapper,
                ));
            }
        }

        PluginOutput {
            ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
            errors,
        }
    }
}

impl RegularPlugin for SellGainsPlugin {}
