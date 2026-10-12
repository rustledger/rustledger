//! Plugin that checks all used commodities are declared.
//!
//! Behaves as beancount's `beancount.plugins.check_commodity`, message for
//! message (#2539): one error per undeclared currency, named with the first
//! account (in sorted order) that uses it, or `Price Directive Context` when
//! only a price does, and the config's `{account-regex: currency-regex}`
//! pairs exempting a currency in matching accounts.

use std::collections::{BTreeSet, HashSet};

use crate::types::{DirectiveData, PluginError, PluginInput, PluginOp, PluginOutput};

use super::super::{NativePlugin, RegularPlugin};
use super::py_literal::{self, PyValue};
use super::py_regex::PyRegexError;
use super::utils::{python_match, python_match_regex};

/// Context naming a currency that only a `price` directive uses.
const PRICE_CONTEXT: &str = "Price Directive Context";

/// Plugin that checks all used commodities are declared.
pub struct CheckCommodityPlugin;

/// The config's ignore pairs, `(account regex, currency regex)`, and the
/// errors reading it. `Err` when the config is not a dict: the plugin
/// skips, as beancount's does.
fn ignore_patterns(
    config: Option<&str>,
) -> Result<(Vec<(regex::Regex, regex::Regex)>, Vec<PluginError>), PluginError> {
    let Some(config) = config.filter(|c| !c.trim().is_empty()) else {
        return Ok((Vec::new(), Vec::new()));
    };
    let invalid =
        || PluginError::error("Invalid configuration for check_commodity plugin; skipping.");
    let Ok(PyValue::Dict(entries)) = py_literal::parse(config) else {
        return Err(invalid());
    };
    let mut patterns = Vec::new();
    let mut errors = Vec::new();
    for (key, value) in entries {
        let (PyValue::Str(key), PyValue::Str(value)) = (key, value) else {
            return Err(invalid());
        };
        let compiled = (python_match_regex(&key), python_match_regex(&value));
        // beancount reports each pattern that does not compile, naming the
        // value either way. A pattern Python compiles and rledger cannot
        // express gets its own message, naming the construct (#2601).
        for (pattern, result) in [(&key, &compiled.0), (&value, &compiled.1)] {
            match result {
                Err(PyRegexError::Invalid(_)) => errors.push(PluginError::error(format!(
                    "Invalid regexp: '{value}' for {key}"
                ))),
                Err(e @ PyRegexError::Unsupported(_)) => errors.push(PluginError::error(format!(
                    "check_commodity: the pattern '{pattern}' cannot be used: {e}"
                ))),
                Ok(_) => {}
            }
        }
        if let (Ok(account), Ok(currency)) = compiled {
            patterns.push((account, currency));
        }
    }
    Ok((patterns, errors))
}

impl NativePlugin for CheckCommodityPlugin {
    fn name(&self) -> &'static str {
        "check_commodity"
    }

    fn description(&self) -> &'static str {
        "Verify all commodities are declared"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let ops = (0..input.directives.len()).map(PluginOp::Keep).collect();
        let (ignore, mut errors) = match ignore_patterns(input.config.as_deref()) {
            Ok(parsed) => parsed,
            Err(error) => {
                return PluginOutput {
                    ops,
                    errors: vec![error],
                };
            }
        };

        let mut declared: HashSet<&str> = HashSet::new();
        // (context, currency), sorted, as beancount sorts its occurrences.
        let mut occurrences: BTreeSet<(&str, &str)> = BTreeSet::new();
        let mut anonymous: BTreeSet<(&str, &str)> = BTreeSet::new();
        for wrapper in &input.directives {
            match &wrapper.data {
                DirectiveData::Commodity(comm) => {
                    declared.insert(&comm.currency);
                }
                DirectiveData::Open(open) => {
                    for currency in &open.currencies {
                        occurrences.insert((&open.account, currency));
                    }
                }
                DirectiveData::Transaction(txn) => {
                    for posting in &txn.postings {
                        let account = posting.account.as_str();
                        if let Some(units) = &posting.units {
                            occurrences.insert((account, &units.currency));
                        }
                        if let Some(currency) =
                            posting.cost.as_ref().and_then(|c| c.currency.as_ref())
                        {
                            occurrences.insert((account, currency));
                        }
                        if let Some(price) = &posting.price {
                            let currency = price
                                .amount
                                .as_ref()
                                .map(|a| &a.currency)
                                .or(price.currency.as_ref());
                            if let Some(currency) = currency {
                                occurrences.insert((account, currency));
                            }
                        }
                    }
                }
                DirectiveData::Balance(bal) => {
                    occurrences.insert((&bal.account, &bal.amount.currency));
                }
                DirectiveData::Price(price) => {
                    anonymous.insert((PRICE_CONTEXT, &price.currency));
                    anonymous.insert((PRICE_CONTEXT, &price.amount.currency));
                }
                _ => {}
            }
        }

        let missing = |currency: &str, context: &str| {
            PluginError::error(format!(
                "Missing Commodity directive for '{currency}' in '{context}'"
            ))
        };
        let mut issued: HashSet<&str> = HashSet::new();
        let mut ignored: HashSet<&str> = HashSet::new();
        for (context, currency) in occurrences {
            if declared.contains(currency) || issued.contains(currency) {
                continue;
            }
            if ignore
                .iter()
                .any(|(a, c)| python_match(a, context) && python_match(c, currency))
            {
                ignored.insert(currency);
                continue;
            }
            errors.push(missing(currency, context));
            issued.insert(currency);
        }
        // A currency only prices use, unless an account already reported or
        // exempted it.
        for (context, currency) in anonymous {
            if declared.contains(currency)
                || issued.contains(currency)
                || ignored.contains(currency)
            {
                continue;
            }
            errors.push(missing(currency, context));
        }

        PluginOutput { ops, errors }
    }
}

impl RegularPlugin for CheckCommodityPlugin {}
