//! Capital gains classifier plugin.
//!
//! This plugin rebooks capital gains into separate accounts based on:
//! - **`long_short`**: Whether gains are long-term (held > 1 year) or short-term
//! - **`gain_loss`**: Whether the posting is a gain (negative income) or loss (positive income)
//!
//! Usage for `long_short`:
//! ```text
//! plugin "beancount_reds_plugins.capital_gains_classifier.long_short" "{
//!   'Income.*:Capital-Gains': [':Capital-Gains', ':Capital-Gains:Short', ':Capital-Gains:Long']
//! }"
//! ```
//!
//! Usage for `gain_loss`:
//! ```text
//! plugin "beancount_reds_plugins.capital_gains_classifier.gain_loss" "{
//!   'Income.*:Capital-Gains:Long': [':Long', ':Long:Gains', ':Long:Losses']
//! }"
//! ```

use regex::Regex;
use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::collections::{BTreeSet, HashSet};
use std::str::FromStr;

use crate::types::{
    AmountData, DirectiveData, DirectiveWrapper, OpenData, PluginError, PluginInput, PluginOp,
    PluginOutput, PostingData, TransactionData,
};

use super::super::{NativePlugin, RegularPlugin};
use super::py_literal::{self, PyValue};
use super::py_regex;
use super::utils::python_match;

/// Plugin for classifying capital gains into long/short term categories.
pub struct CapitalGainsLongShortPlugin;

/// Plugin for classifying capital gains into gains/losses categories.
pub struct CapitalGainsGainLossPlugin;

impl NativePlugin for CapitalGainsLongShortPlugin {
    fn name(&self) -> &'static str {
        "long_short"
    }

    fn description(&self) -> &'static str {
        "Classify capital gains into long-term vs short-term based on holding period"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        process_long_short(input)
    }
}

impl NativePlugin for CapitalGainsGainLossPlugin {
    fn name(&self) -> &'static str {
        "gain_loss"
    }

    fn description(&self) -> &'static str {
        "Classify capital gains into gains vs losses based on posting amount"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        process_gain_loss(input)
    }
}

impl RegularPlugin for CapitalGainsLongShortPlugin {}
impl RegularPlugin for CapitalGainsGainLossPlugin {}

/// Configuration for `long_short` classification.
struct LongShortConfig {
    /// Matched as Python's `re.match` matches: at the start of the account.
    pattern: Regex,
    account_to_replace: String,
    short_replacement: String,
    long_replacement: String,
}

/// One `gain_loss` rewrite.
struct GainLossConfig {
    /// Matched as Python's `re.match` matches: at the start of the account.
    pattern: Regex,
    account_to_replace: String,
    gains_replacement: String,
    losses_replacement: String,
}

/// One config entry, `'pattern': ['to_replace', 'first', 'second']`.
struct Rule {
    pattern: Regex,
    to_replace: String,
    first: String,
    second: String,
}

/// The config's rules in dict order (a repeated key keeps its first position
/// and takes its last value, as in a Python dict), read as the upstream
/// plugins read it: `literal_eval`, then `re.compile` on each key.
///
/// `first_only` reads only the first entry, as `long_short` reads
/// `next(iter(config_obj))`: the others are not checked either.
fn parse_rules(config: &str, plugin: &str, first_only: bool) -> Result<Vec<Rule>, PluginError> {
    let invalid =
        |why: &str| PluginError::error(format!("Invalid configuration for {plugin}: {why}"));
    let Ok(PyValue::Dict(entries)) = py_literal::parse(config) else {
        return Err(invalid("expected a dict"));
    };
    let mut merged: Vec<(String, PyValue)> = Vec::with_capacity(entries.len());
    for (key, value) in entries {
        let PyValue::Str(key) = key else {
            return Err(invalid("a pattern must be a string"));
        };
        if let Some(entry) = merged.iter_mut().find(|(k, _)| *k == key) {
            entry.1 = value;
        } else {
            merged.push((key, value));
        }
    }
    if first_only {
        merged.truncate(1);
    }
    let mut rules = Vec::with_capacity(merged.len());
    for (key, value) in merged {
        let PyValue::Seq(items) = value else {
            return Err(invalid(&format!(
                "the value for '{key}' must be a list of three strings"
            )));
        };
        // Upstream reads `[0]`, `[1]` and `[2]`; any more are ignored.
        let [
            PyValue::Str(to_replace),
            PyValue::Str(first),
            PyValue::Str(second),
            ..,
        ] = items.as_slice()
        else {
            return Err(invalid(&format!(
                "the value for '{key}' must be a list of three strings"
            )));
        };
        let pattern = py_regex::compile_match(&key).map_err(|e| {
            PluginError::error(format!("{plugin}: the pattern '{key}' cannot be used: {e}"))
        })?;
        rules.push(Rule {
            pattern,
            to_replace: to_replace.clone(),
            first: first.clone(),
            second: second.clone(),
        });
    }
    if rules.is_empty() {
        return Err(invalid("the dict is empty"));
    }
    Ok(rules)
}

/// Every input directive kept, and `error`.
fn unchanged(input: &PluginInput, error: Option<PluginError>) -> PluginOutput {
    PluginOutput {
        ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
        errors: error.into_iter().collect(),
    }
}

/// Process entries with `long_short` classification.
fn process_long_short(input: PluginInput) -> PluginOutput {
    let config = match input.config.as_deref() {
        Some(c) => match parse_long_short_config(c) {
            Ok(cfg) => cfg,
            Err(error) => return unchanged(&input, Some(error)),
        },
        None => return unchanged(&input, None),
    };

    // Sorted, as beancount_reds_plugins opens them (`create_open_directives`
    // walks `sorted(new_accounts)`); a `HashSet` emitted them in a different
    // order on every run (#2625).
    let mut new_accounts: BTreeSet<String> = BTreeSet::new();
    let mut ops: Vec<PluginOp> = Vec::with_capacity(input.directives.len());
    // Track earliest date from input directives for synthesized Open directives.
    let earliest_date = input
        .directives
        .iter()
        .map(|d| d.date.as_str())
        .min()
        .unwrap_or("1970-01-01")
        .to_string();
    // Accounts already opened by the user; we must not synthesize a
    // duplicate Open or Late validation will emit E1002.
    let existing_opens: HashSet<String> = input
        .directives
        .iter()
        .filter_map(|d| match &d.data {
            DirectiveData::Open(open) => Some(open.account.clone()),
            _ => None,
        })
        .collect();

    for (i, directive) in input.directives.into_iter().enumerate() {
        if directive.directive_type != "transaction" {
            ops.push(PluginOp::Keep(i));
            continue;
        }

        if let DirectiveData::Transaction(txn) = &directive.data {
            // Check if transaction has matching capital gains postings
            let has_generic = txn
                .postings
                .iter()
                .any(|p| python_match(&config.pattern, &p.account));
            let has_specific = txn.postings.iter().any(|p| {
                p.account.contains(&config.short_replacement)
                    || p.account.contains(&config.long_replacement)
            });

            if !has_generic || has_specific {
                ops.push(PluginOp::Keep(i));
                continue;
            }

            // Find reduction postings (sales with cost and price)
            let reductions: Vec<&PostingData> = txn
                .postings
                .iter()
                .filter(|p| p.cost.is_some() && p.units.is_some() && p.price.is_some())
                .collect();

            if reductions.is_empty() {
                ops.push(PluginOp::Keep(i));
                continue;
            }

            // Calculate short vs long gains
            let entry_date = if let Ok(d) = directive.date.parse::<NaiveDate>() {
                d
            } else {
                ops.push(PluginOp::Keep(i));
                continue;
            };

            // Fall through if ANY reduction lacks a parseable cost
            // date. Without it the plugin can't classify holding
            // period, and pre-fix (issue #1010) it would silently
            // drop the generic Income:Capital-Gains posting in the
            // post-loop filter, leaving the transaction unbalanced.
            // Falling through preserves the user's ledger.
            let any_missing_cost_date = reductions.iter().any(|p| {
                p.cost
                    .as_ref()
                    .and_then(|c| c.date.as_ref())
                    .and_then(|d| d.parse::<NaiveDate>().ok())
                    .is_none()
            });
            if any_missing_cost_date {
                ops.push(PluginOp::Keep(i));
                continue;
            }

            let mut short_gains = Decimal::ZERO;
            let mut long_gains = Decimal::ZERO;

            for posting in &reductions {
                if let (Some(cost), Some(units), Some(price)) =
                    (&posting.cost, &posting.units, &posting.price)
                {
                    // Get cost date
                    let cost_date = cost.date.as_ref().and_then(|d| d.parse::<NaiveDate>().ok());

                    if let Some(cost_date) = cost_date {
                        // Calculate gain
                        // Capital-gains classification operates on
                        // post-booking transactions where the cost
                        // carries a per-unit value (both PerUnit and
                        // PerUnitFromTotal expose per_unit()).
                        let cost_number = cost
                            .number
                            .as_ref()
                            .and_then(|cn| cn.per_unit())
                            .map_or(Decimal::ZERO, |s| {
                                Decimal::from_str(s).unwrap_or(Decimal::ZERO)
                            });
                        let price_number = price
                            .amount
                            .as_ref()
                            .and_then(|a| Decimal::from_str(&a.number).ok())
                            .unwrap_or(Decimal::ZERO);
                        let units_number =
                            Decimal::from_str(&units.number).unwrap_or(Decimal::ZERO);

                        let gain = (cost_number - price_number) * units_number.abs();

                        // Check if long-term (> 1 year)
                        let days_held = entry_date.since(cost_date).map_or(0, |s| s.get_days());
                        let years_held = (days_held / 365) as u32;
                        let is_long_term = years_held > 1
                            || (years_held == 1
                                && (entry_date.month() > cost_date.month()
                                    || (entry_date.month() == cost_date.month()
                                        && entry_date.day() >= cost_date.day())));

                        if is_long_term {
                            long_gains += gain;
                        } else {
                            short_gains += gain;
                        }
                    }
                }
            }

            // Find and remove original capital gains postings
            let orig_postings: Vec<&PostingData> = txn
                .postings
                .iter()
                .filter(|p| python_match(&config.pattern, &p.account))
                .collect();

            if orig_postings.is_empty() {
                ops.push(PluginOp::Keep(i));
                continue;
            }

            let orig_sum: Decimal = orig_postings
                .iter()
                .filter_map(|p| p.units.as_ref())
                .filter_map(|u| Decimal::from_str(&u.number).ok())
                .sum();

            // Adjust for rounding differences
            let diff = orig_sum - (short_gains + long_gains);
            if diff.abs() > Decimal::new(1, 6) {
                let total = short_gains + long_gains;
                if total != Decimal::ZERO {
                    short_gains += (short_gains / total) * diff;
                    long_gains += (long_gains / total) * diff;
                }
            }

            // Create new postings
            let mut new_postings: Vec<PostingData> = txn
                .postings
                .iter()
                .filter(|p| !python_match(&config.pattern, &p.account))
                .cloned()
                .collect();

            let template = orig_postings[0];

            if short_gains != Decimal::ZERO {
                let new_account = template
                    .account
                    .replace(&config.account_to_replace, &config.short_replacement);
                new_accounts.insert(new_account.clone());
                new_postings.push(PostingData {
                    account: new_account,
                    units: template.units.as_ref().map(|u| AmountData {
                        number: format_decimal(short_gains),
                        currency: u.currency.clone(),
                    }),
                    cost: None,
                    price: None,
                    flag: template.flag.clone(),
                    metadata: vec![],
                    span: None,
                });
            }

            if long_gains != Decimal::ZERO {
                let new_account = template
                    .account
                    .replace(&config.account_to_replace, &config.long_replacement);
                new_accounts.insert(new_account.clone());
                new_postings.push(PostingData {
                    account: new_account,
                    units: template.units.as_ref().map(|u| AmountData {
                        number: format_decimal(long_gains),
                        currency: u.currency.clone(),
                    }),
                    cost: None,
                    price: None,
                    flag: template.flag.clone(),
                    metadata: vec![],
                    span: None,
                });
            }

            ops.push(PluginOp::Modify(
                i,
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: directive.date.clone(),
                    filename: directive.filename.clone(),
                    lineno: directive.lineno,
                    data: DirectiveData::Transaction(TransactionData {
                        flag: txn.flag.clone(),
                        payee: txn.payee.clone(),
                        narration: txn.narration.clone(),
                        tags: txn.tags.clone(),
                        links: txn.links.clone(),
                        metadata: txn.metadata.clone(),
                        postings: new_postings,
                    }),
                },
            ));
        } else {
            ops.push(PluginOp::Keep(i));
        }
    }

    // Insert Open directives for newly synthesized accounts the user
    // hasn't already opened.
    for account in &new_accounts {
        if existing_opens.contains(account) {
            continue;
        }
        ops.push(PluginOp::Insert(DirectiveWrapper {
            directive_type: "open".to_string(),
            date: earliest_date.clone(),
            filename: Some("<long_short>".to_string()),
            lineno: Some(0),
            data: DirectiveData::Open(OpenData {
                account: account.clone(),
                currencies: vec![],
                booking: None,
                metadata: vec![],
            }),
        }));
    }

    PluginOutput {
        ops,
        errors: Vec::new(),
    }
}

/// Process entries with `gain_loss` classification.
fn process_gain_loss(input: PluginInput) -> PluginOutput {
    let rules = match input.config.as_deref() {
        Some(c) => match parse_gain_loss_config(c) {
            Ok(rules) => rules,
            Err(error) => return unchanged(&input, Some(error)),
        },
        None => return unchanged(&input, None),
    };
    // beancount's plugin fails outright when a rule matches a posting an
    // earlier rule already changed (it removes the posting twice); a rule
    // that matched without changing the account leaves the posting equal to
    // itself, and the next rule applies normally. So that one case is
    // reported and nothing is rewritten, rather than chaining the rules.
    for wrapper in &input.directives {
        let DirectiveData::Transaction(txn) = &wrapper.data else {
            continue;
        };
        for posting in &txn.postings {
            let Some(number) = posting
                .units
                .as_ref()
                .and_then(|units| Decimal::from_str(&units.number).ok())
            else {
                continue;
            };
            let mut account = posting.account.clone();
            let mut changed = false;
            for rule in &rules {
                if python_match(&rule.pattern, &account) {
                    if changed {
                        return unchanged(
                            &input,
                            Some(PluginError::error(format!(
                                "gain_loss: a second rule matches the posting to {} after an earlier one rewrote it (beancount's plugin fails on this)",
                                posting.account
                            ))),
                        );
                    }
                    let replacement = if number < Decimal::ZERO {
                        &rule.gains_replacement
                    } else {
                        &rule.losses_replacement
                    };
                    let rewritten = account.replace(&rule.account_to_replace, replacement);
                    changed = rewritten != account;
                    account = rewritten;
                }
            }
        }
    }

    // Sorted, as beancount_reds_plugins opens them (`create_open_directives`
    // walks `sorted(new_accounts)`); a `HashSet` emitted them in a different
    // order on every run (#2625).
    let mut new_accounts: BTreeSet<String> = BTreeSet::new();
    let mut ops: Vec<PluginOp> = Vec::with_capacity(input.directives.len());
    // Earliest date from input for synthesized Open directives.
    let earliest_date = input
        .directives
        .iter()
        .map(|d| d.date.as_str())
        .min()
        .unwrap_or("1970-01-01")
        .to_string();
    // Accounts already opened by the user; suppress duplicate Opens.
    let existing_opens: HashSet<String> = input
        .directives
        .iter()
        .filter_map(|d| match &d.data {
            DirectiveData::Open(open) => Some(open.account.clone()),
            _ => None,
        })
        .collect();

    for (i, directive) in input.directives.into_iter().enumerate() {
        if directive.directive_type != "transaction" {
            ops.push(PluginOp::Keep(i));
            continue;
        }

        if let DirectiveData::Transaction(txn) = &directive.data {
            let mut modified = false;
            let mut new_postings: Vec<PostingData> = Vec::new();

            for posting in &txn.postings {
                // Every rule in config order, each matched against the account
                // as the rules before it left it, as upstream's loop does (a
                // match after a rewrite is refused above).
                let number = posting
                    .units
                    .as_ref()
                    .and_then(|units| Decimal::from_str(&units.number).ok());
                let mut new_account = posting.account.clone();
                let mut rewritten = false;
                if let Some(number) = number {
                    for config in &rules {
                        if python_match(&config.pattern, &new_account) {
                            new_account = if number < Decimal::ZERO {
                                // Negative = gains (income is negative)
                                new_account
                                    .replace(&config.account_to_replace, &config.gains_replacement)
                            } else {
                                // Positive = losses
                                new_account
                                    .replace(&config.account_to_replace, &config.losses_replacement)
                            };
                            new_accounts.insert(new_account.clone());
                            rewritten = true;
                        }
                    }
                }
                if rewritten {
                    new_postings.push(PostingData {
                        account: new_account,
                        units: posting.units.clone(),
                        cost: posting.cost.clone(),
                        price: posting.price.clone(),
                        flag: posting.flag.clone(),
                        metadata: posting.metadata.clone(),
                        span: None,
                    });
                    modified = true;
                    continue;
                }
                new_postings.push(posting.clone());
            }

            if modified {
                ops.push(PluginOp::Modify(
                    i,
                    DirectiveWrapper {
                        directive_type: "transaction".to_string(),
                        date: directive.date.clone(),
                        filename: directive.filename.clone(),
                        lineno: directive.lineno,
                        data: DirectiveData::Transaction(TransactionData {
                            flag: txn.flag.clone(),
                            payee: txn.payee.clone(),
                            narration: txn.narration.clone(),
                            tags: txn.tags.clone(),
                            links: txn.links.clone(),
                            metadata: txn.metadata.clone(),
                            postings: new_postings,
                        }),
                    },
                ));
            } else {
                ops.push(PluginOp::Keep(i));
            }
        } else {
            ops.push(PluginOp::Keep(i));
        }
    }

    // Insert Open directives for newly synthesized accounts the user
    // hasn't already opened.
    for account in &new_accounts {
        if existing_opens.contains(account) {
            continue;
        }
        ops.push(PluginOp::Insert(DirectiveWrapper {
            directive_type: "open".to_string(),
            date: earliest_date.clone(),
            filename: Some("<gain_loss>".to_string()),
            lineno: Some(0),
            data: DirectiveData::Open(OpenData {
                account: account.clone(),
                currencies: vec![],
                booking: None,
                metadata: vec![],
            }),
        }));
    }

    PluginOutput {
        ops,
        errors: Vec::new(),
    }
}

/// Parse `long_short` configuration: its first entry, as upstream reads
/// `next(iter(config_obj))`.
/// Format: `{'pattern': ['to_replace', 'short_repl', 'long_repl']}`
fn parse_long_short_config(config: &str) -> Result<LongShortConfig, PluginError> {
    let rule = parse_rules(config, "long_short", true)?
        .into_iter()
        .next()
        .expect("parse_rules returns at least one rule");
    Ok(LongShortConfig {
        pattern: rule.pattern,
        account_to_replace: rule.to_replace,
        short_replacement: rule.first,
        long_replacement: rule.second,
    })
}

/// Parse `gain_loss` configuration: every entry, in order.
/// Format: `{'pattern': ['to_replace', 'gains_repl', 'losses_repl'], ...}`
fn parse_gain_loss_config(config: &str) -> Result<Vec<GainLossConfig>, PluginError> {
    Ok(parse_rules(config, "gain_loss", false)?
        .into_iter()
        .map(|rule| GainLossConfig {
            pattern: rule.pattern,
            account_to_replace: rule.to_replace,
            gains_replacement: rule.first,
            losses_replacement: rule.second,
        })
        .collect())
}

/// Format a decimal number.
fn format_decimal(d: Decimal) -> String {
    let s = d.to_string();
    if s.contains('.') {
        s.trim_end_matches('0').trim_end_matches('.').to_string()
    } else {
        s
    }
}

#[cfg(test)]
mod tests {
    use super::super::utils::materialize_ops;
    use super::*;
    use crate::types::*;

    #[test]
    fn test_parse_long_short_config() {
        let config = "{'Income.*:Capital-Gains': [':Capital-Gains', ':Capital-Gains:Short', ':Capital-Gains:Long']}";
        let cfg = parse_long_short_config(config).unwrap_or_else(|e| panic!("{e:?}"));
        assert_eq!(cfg.account_to_replace, ":Capital-Gains");
        assert_eq!(cfg.short_replacement, ":Capital-Gains:Short");
        assert_eq!(cfg.long_replacement, ":Capital-Gains:Long");
    }

    #[test]
    fn test_parse_gain_loss_config() {
        let config = "{'Income.*:Long': [':Long', ':Long:Gains', ':Long:Losses']}";
        let rules = parse_gain_loss_config(config).unwrap_or_else(|e| panic!("{e:?}"));
        assert_eq!(rules.len(), 1);
        let cfg = &rules[0];
        assert_eq!(cfg.account_to_replace, ":Long");
        assert_eq!(cfg.gains_replacement, ":Long:Gains");
        assert_eq!(cfg.losses_replacement, ":Long:Losses");
    }

    #[test]
    fn test_gain_loss_classification() {
        let plugin = CapitalGainsGainLossPlugin;

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-01-15".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "Sell stock".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![],
                    postings: vec![
                        PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "1000".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        },
                        PostingData {
                            account: "Income:Capital-Gains:Long".to_string(),
                            units: Some(AmountData {
                                number: "-100".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        },
                    ],
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: Some(
                "{'Income.*:Capital-Gains:Long': [':Long', ':Long:Gains', ':Long:Losses']}"
                    .to_string(),
            ),
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);

        // Find the transaction
        let txn = directives
            .iter()
            .find(|d| matches!(d.data, DirectiveData::Transaction(_)));
        assert!(txn.is_some());

        if let DirectiveData::Transaction(t) = &txn.unwrap().data {
            // The negative posting should be renamed to :Long:Gains
            let gains_posting = t
                .postings
                .iter()
                .find(|p| p.account.contains(":Long:Gains"));
            assert!(gains_posting.is_some());
        }
    }
}
