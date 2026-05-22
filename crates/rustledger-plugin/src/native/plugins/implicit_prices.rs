//! Plugin that generates price entries from transaction costs and prices.

use crate::types::{
    AmountData, CostData, DirectiveData, DirectiveWrapper, PluginError, PluginInput, PluginOp,
    PluginOutput, PriceAnnotationData, PriceAnnotationView, PriceData,
};
use rust_decimal::Decimal;
use rustledger_core::extract_per_unit_price;
use std::collections::{HashMap, HashSet};
use std::str::FromStr;

use super::super::NativePlugin;

/// Canonical key for tracking lots in the per-account inventory used
/// by the cost-only "skip on REDUCED" check. Mirrors what Python
/// beancount's `Inventory.add_amount` keys lots on:
/// `(currency, Cost(number, currency, date, label))`. We carry the
/// account too so we get per-account tracking.
type LotKey = (String, String, Option<String>);

/// Build the cost-fingerprint half of [`LotKey`]. `None` for postings
/// without a cost spec; otherwise a stable string of the lot's
/// distinguishing fields. Two postings with the same `LotKey` will
/// match against each other in the inventory tracker, exactly as
/// `Inventory.add_amount` would.
///
/// The per-unit number is parsed to [`Decimal`] and then *normalized*
/// (trailing-zero-stripped) before stringifying — without that step,
/// numerically equivalent costs like `"100"` and `"100.00"` would
/// produce different lot keys, so a sell at `{100 USD}` against a
/// prior buy at `{100.00 USD}` wouldn't classify as `REDUCED` and the
/// phantom price emit this gate exists to prevent would slip back in.
/// Caught by Copilot review on PR #1061.
///
/// We canonicalize per-unit from total (dividing by `|units|`) when
/// only the raw `Total` form is set — keeps the key consistent
/// regardless of which form the cost was originally written in. After
/// booking has run, the post-booking `PerUnitFromTotal` variant
/// carries per-unit already, but we don't assume that.
fn cost_fingerprint(cost: &CostData, units_number: Decimal) -> Option<String> {
    let currency = cost.currency.as_deref()?;
    // `per_unit()` covers both PerUnit and PerUnitFromTotal (both
    // carry per-unit by host construction). Raw Total needs division
    // here; bare-`{}` returns None.
    let cn = cost.number.as_ref()?;
    let per_unit_decimal: Decimal = if let Some(per_str) = cn.per_unit() {
        Decimal::from_str(per_str).ok()?
    } else {
        let total_str = cn.total()?;
        let total = Decimal::from_str(total_str).ok()?;
        if units_number.is_zero() {
            return None;
        }
        total / units_number.abs()
    };
    let per_unit = per_unit_decimal.normalize().to_string();
    let date = cost.date.as_deref().unwrap_or("");
    let label = cost.label.as_deref().unwrap_or("");
    Some(format!("{per_unit}|{currency}|{date}|{label}"))
}

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
///
/// Augment-vs-reduce gating: Python's plugin uses
/// `Inventory.add_position` and skips emitting the cost-derived price
/// when the posting matched as `MatchResult.REDUCED` (a sell against
/// an existing lot). Without that check, sells written as `-N CCY {}`
/// — which booking later resolves to a specific lot's cost — produce
/// a phantom price entry per match. We mirror that here by tracking
/// per-account positions keyed on `(account, units.currency,
/// cost-fingerprint)` and treating a posting as REDUCED when the
/// running quantity for its key has the opposite sign. Price
/// annotations (`@`/`@@`) still emit unconditionally even on reducing
/// postings — Python's `from_price` branch fires before the REDUCED
/// check too. Without this gate rledger over-emitted ~4 prices per
/// reducing-sell-with-`{}` posting on fixtures like fava-portfolio-
/// returns (closes the residual ~5 over-emit cases left behind by
/// #1048).
///
/// Pipeline assumption: this plugin operates on **post-booking**
/// directives. Postings that would cross zero (e.g. a `-150` sell
/// against a `+100` lot) have already been split by the booker into
/// two postings — one fully-reducing leg against the existing lot
/// and one augmenting/creating leg for the residual. Our inline
/// inventory update sees them sequentially and correctly classifies
/// the residual leg as not-REDUCED. If the plugin is ever moved
/// earlier in the pipeline, the gate would over-suppress on
/// pre-split crossing postings.
///
/// Lots with a cost spec that carries no `number` at all (e.g. bare
/// `{2024-01-01}` — `CostNumber` is `None`) aren't tracked in the
/// inventory — `cost_fingerprint` returns `None` and the posting
/// passes through the cost-emit branch directly. Python's
/// `Inventory.add_amount` would still track these, but since the
/// cost-derived emit path also requires a number, the tracker
/// participation doesn't change emit decisions.
pub struct ImplicitPricesPlugin;

impl NativePlugin for ImplicitPricesPlugin {
    fn name(&self) -> &'static str {
        "implicit_prices"
    }

    fn description(&self) -> &'static str {
        "Generate price entries from transaction costs/prices"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let mut generated_prices = Vec::new();
        let mut errors: Vec<PluginError> = Vec::new();

        // Per-account lot quantities, keyed identically to Python's
        // `Inventory.add_amount`. Used solely to detect REDUCED for
        // the cost-derived emit gate.
        let mut inventory: HashMap<LotKey, Decimal> = HashMap::new();

        // Dedup of emitted prices by `(date, base_currency, number,
        // quote_currency)` — mirrors Python's `new_price_entry_map`
        // which silently drops a second emit for the same key on the
        // same day. Without this, two postings on the same day that
        // resolve to the same per-unit price (e.g., two buys at the
        // same lot cost) produce two identical entries in `#prices`,
        // inflating the count vs bean-check.
        let mut emitted_keys: HashSet<(String, String, String, String)> = HashSet::new();

        for wrapper in &input.directives {
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
                // a currency is present AND the cost number parses.
                // Translate from wire format (CostNumberData) to core
                // CostNumber for the shared helper. Conversion failures
                // (e.g. a plugin upstream emitted inconsistent
                // `PerUnitFromTotal`) surface as plugin warnings rather
                // than silent drops — a plugin author whose buggy
                // emission produces zero implicit prices now gets a
                // signal (review A-4.5). `units_number` is already
                // parsed above (line 150); reuse it instead of
                // re-parsing.
                let cost_result = posting.cost.as_ref().and_then(|c| {
                    let currency = c.currency.clone()?;
                    let number = match &c.number {
                        Some(rustledger_plugin_types::CostNumberData::PerUnit { value: n }) => {
                            match Decimal::from_str(n) {
                                Ok(d) => Some(rustledger_core::CostNumber::PerUnit { value: d }),
                                Err(_) => {
                                    return Some(Err(format!(
                                        "implicit_prices: posting on account {:?} has cost \
                                         per_unit {n:?} that doesn't parse as a decimal",
                                        posting.account
                                    )));
                                }
                            }
                        }
                        Some(rustledger_plugin_types::CostNumberData::Total { value: n }) => {
                            match Decimal::from_str(n) {
                                Ok(d) => Some(rustledger_core::CostNumber::Total { value: d }),
                                Err(_) => {
                                    return Some(Err(format!(
                                        "implicit_prices: posting on account {:?} has cost \
                                         total {n:?} that doesn't parse as a decimal",
                                        posting.account
                                    )));
                                }
                            }
                        }
                        Some(rustledger_plugin_types::CostNumberData::PerUnitFromTotal {
                            per_unit,
                            total,
                        }) => {
                            let per_unit_d = match Decimal::from_str(per_unit) {
                                Ok(d) => d,
                                Err(_) => {
                                    return Some(Err(format!(
                                        "implicit_prices: posting on account {:?} has \
                                         PerUnitFromTotal per_unit {per_unit:?} that doesn't \
                                         parse as a decimal",
                                        posting.account
                                    )));
                                }
                            };
                            let total_d = match Decimal::from_str(total) {
                                Ok(d) => d,
                                Err(_) => {
                                    return Some(Err(format!(
                                        "implicit_prices: posting on account {:?} has \
                                         PerUnitFromTotal total {total:?} that doesn't parse \
                                         as a decimal",
                                        posting.account
                                    )));
                                }
                            };
                            match rustledger_core::BookedCost::try_new(
                                per_unit_d,
                                total_d,
                                units_number,
                            ) {
                                Ok(b) => Some(rustledger_core::CostNumber::PerUnitFromTotal(b)),
                                Err(e) => {
                                    return Some(Err(format!(
                                        "implicit_prices: posting on account {:?}: {e}",
                                        posting.account
                                    )));
                                }
                            }
                        }
                        None => return None,
                    };
                    Some(Ok((number, currency)))
                });
                let cost = match cost_result {
                    Some(Ok(c)) => Some(c),
                    Some(Err(msg)) => {
                        errors.push(PluginError::warning(msg));
                        None
                    }
                    None => None,
                };

                // Update the per-account lot tracker BEFORE deciding
                // whether to emit. The pre-update quantity is what
                // tells us whether this posting reduces an existing
                // lot (Python's `MatchResult.REDUCED`).
                let reduced = if let Some(c) = posting.cost.as_ref()
                    && let Some(fp) = cost_fingerprint(c, units_number)
                {
                    let key = (posting.account.clone(), units.currency.clone(), Some(fp));
                    let prior = inventory.get(&key).copied().unwrap_or(Decimal::ZERO);
                    let was_reduction = !prior.is_zero()
                        && prior.is_sign_negative() != units_number.is_sign_negative();
                    inventory.insert(key, prior + units_number);
                    was_reduction
                } else {
                    false
                };

                // Two-phase resolution to mirror Python's
                // `if posting.price → emit; elif cost && !REDUCED → emit`:
                // we ask the helper for the annotation-only price first
                // (passing `None` for cost), and only fall back to the
                // cost path when the posting is augmenting (or a
                // first-time CREATED). Calling the helper twice is
                // cheap and avoids duplicating its priority logic.
                let from_annotation = extract_per_unit_price(
                    units_number,
                    annotation,
                    None::<(Option<rustledger_core::CostNumber>, String)>,
                );
                let chosen = match (from_annotation, reduced) {
                    (Some(p), _) => Some(p),
                    (None, false) => extract_per_unit_price(units_number, None, cost),
                    (None, true) => None,
                };

                let Some((per_unit, quote_currency)) = chosen else {
                    continue;
                };

                // Dedup key uses the *normalized* (trailing-zero-stripped)
                // decimal string so two postings with the same numeric
                // per-unit value but different scales (e.g. "100" vs
                // "100.00") collapse to the same key — Python's
                // `new_price_entry_map` compares the numeric value, not
                // its string form. The emitted price keeps the
                // un-normalized representation so user-facing output
                // preserves whatever scale the cost spec produced.
                // Caught by Copilot review on PR #1061.
                let per_unit_str = per_unit.to_string();
                let dedup_key = (
                    wrapper.date.clone(),
                    units.currency.clone(),
                    per_unit.normalize().to_string(),
                    quote_currency.clone(),
                );
                if !emitted_keys.insert(dedup_key) {
                    // Same (date, base, number, quote) already emitted —
                    // skip. Matches Python beancount's silent dedup.
                    continue;
                }

                generated_prices.push(DirectiveWrapper {
                    directive_type: "price".to_string(),
                    date: wrapper.date.clone(),
                    filename: None, // plugin-generated
                    lineno: None,
                    data: DirectiveData::Price(PriceData {
                        currency: units.currency.clone(),
                        amount: AmountData {
                            number: per_unit_str,
                            currency: quote_currency,
                        },
                        metadata: vec![],
                    }),
                });
            }
        }

        // Keep all input directives, then insert generated price entries.
        let mut ops: Vec<PluginOp> = (0..input.directives.len()).map(PluginOp::Keep).collect();
        for w in generated_prices {
            ops.push(PluginOp::Insert(w));
        }

        PluginOutput { ops, errors }
    }
}
