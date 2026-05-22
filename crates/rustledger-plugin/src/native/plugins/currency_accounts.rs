//! Auto-generate currency trading account postings.

use crate::types::{DirectiveData, DirectiveWrapper, PluginInput, PluginOp, PluginOutput};

use super::super::NativePlugin;

/// Plugin that auto-generates currency trading account postings.
///
/// Implements the currency trading accounts method as in Python beancount's
/// `beancount.plugins.currency_accounts`. For transactions that mix multiple
/// currencies and use price annotations, this plugin:
///
/// 1. Groups postings by `cost.currency` (if the posting has a cost) or
///    `units.currency` (otherwise). **Price currency is never used as the
///    group key** — this matches Python's `group_postings_by_weight_currency`.
/// 2. If there is at least one price annotation in the transaction and
///    there are two or more distinct group keys, inserts a neutralizing
///    posting for each group. The neutralizing posting goes to
///    `<base>:<group_key>` and carries the negated weight inventory of
///    that group (denominated in the weight/cost currency, which may
///    differ from the group key).
/// 3. Unlike Python's plugin, does NOT strip `price` annotations from
///    the original postings. Python strips them because its pipeline
///    runs plugins before booking; rustledger runs booking first, so
///    stripping prices would cause balance-check failures (E3001) in
///    the post-plugin validator.
/// 4. Emits `open` directives at the earliest transaction date for all
///    newly created currency trading accounts.
pub struct CurrencyAccountsPlugin {
    /// Base account for currency tracking (default: "Equity:CurrencyAccounts").
    base_account: String,
}

impl CurrencyAccountsPlugin {
    /// Create with default base account.
    pub fn new() -> Self {
        Self {
            base_account: "Equity:CurrencyAccounts".to_string(),
        }
    }

    /// Create with custom base account.
    pub const fn with_base_account(base_account: String) -> Self {
        Self { base_account }
    }
}

impl Default for CurrencyAccountsPlugin {
    fn default() -> Self {
        Self::new()
    }
}

impl NativePlugin for CurrencyAccountsPlugin {
    fn name(&self) -> &'static str {
        "currency_accounts"
    }

    fn description(&self) -> &'static str {
        "Auto-generate currency trading postings"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use crate::types::{AmountData, OpenData, PostingData};
        use rust_decimal::Decimal;
        use std::collections::{BTreeMap, HashSet};
        use std::str::FromStr;

        // Get base account from config if provided. We only check for
        // non-empty (Python's plugin additionally validates that it is a
        // well-formed account name and falls back to the default when
        // it isn't, but we skip that check for simplicity).
        let base_account = input
            .config
            .as_ref()
            .map(|c| c.trim().to_string())
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| self.base_account.clone());

        // Find earliest date and collect existing Open accounts in one pass.
        let mut existing_opens: HashSet<String> = HashSet::new();
        let mut earliest_date: Option<&str> = None;
        for wrapper in &input.directives {
            match earliest_date {
                None => earliest_date = Some(&wrapper.date),
                Some(current) if wrapper.date.as_str() < current => {
                    earliest_date = Some(&wrapper.date);
                }
                _ => {}
            }
            if let DirectiveData::Open(open) = &wrapper.data {
                existing_opens.insert(open.account.clone());
            }
        }
        let earliest_date = earliest_date.unwrap_or("1970-01-01").to_string();

        let mut ops: Vec<PluginOp> = Vec::with_capacity(input.directives.len());
        let mut created_accounts: HashSet<String> = HashSet::new();

        for (i, wrapper) in input.directives.iter().enumerate() {
            let DirectiveData::Transaction(txn) = &wrapper.data else {
                ops.push(PluginOp::Keep(i));
                continue;
            };

            // Group postings by key and track whether any posting has a price.
            //
            // Use BTreeMap for deterministic iteration so the order in which
            // neutralizing postings are appended is stable across runs.
            let mut curmap: BTreeMap<String, Vec<usize>> = BTreeMap::new();
            let mut has_price = false;

            for (i, posting) in txn.postings.iter().enumerate() {
                let Some(units) = &posting.units else {
                    continue;
                };

                // Group key: cost.currency if the posting has a cost,
                // otherwise units.currency. Matches Python's
                // `group_postings_by_weight_currency` at
                // currency_accounts.py:93-104.
                let key = if let Some(cost) = &posting.cost {
                    cost.currency
                        .clone()
                        .unwrap_or_else(|| units.currency.clone())
                } else {
                    units.currency.clone()
                };

                if posting.price.is_some() {
                    has_price = true;
                }

                curmap.entry(key).or_default().push(i);
            }

            // Only neutralize when there's at least one price AND more than
            // one currency group. This is Python's gating condition.
            if !has_price || curmap.len() < 2 {
                ops.push(PluginOp::Keep(i));
                continue;
            }

            // `weight(posting)` returns (amount, currency):
            //   - Cost (PerUnit): (units * per_unit, cost.currency).
            //   - Cost (Total / PerUnitFromTotal): preserved total
            //     magnitude with sign following units.
            //   - Price: (units * price, price.currency). For @@ (is_total),
            //     weight magnitude is the total price, sign follows units.
            //   - Else: (units.amount, units.currency)
            let weight_of = |posting: &PostingData| -> Option<(Decimal, String)> {
                let units = posting.units.as_ref()?;
                let units_num = Decimal::from_str(&units.number).unwrap_or_default();
                if let Some(cost) = &posting.cost {
                    let currency = cost
                        .currency
                        .clone()
                        .unwrap_or_else(|| units.currency.clone());
                    // Exhaustive variant match. The Total and
                    // PerUnitFromTotal arms use the preserved total
                    // (matching Python's `beancount.core.convert.get_cost`,
                    // which uses the source total exactly and avoids
                    // the division-then-multiplication precision
                    // loss). PerUnit multiplies. Future variant
                    // additions to `CostNumberData` will compile-fail
                    // here, which is what we want.
                    let amount = match &cost.number {
                        Some(rustledger_plugin_types::CostNumberData::PerUnit { value }) => {
                            let per = Decimal::from_str(value).unwrap_or_default();
                            units_num * per
                        }
                        Some(rustledger_plugin_types::CostNumberData::Total { value }) => {
                            let total = Decimal::from_str(value).unwrap_or_default();
                            if units_num.is_sign_negative() {
                                -total.abs()
                            } else {
                                total.abs()
                            }
                        }
                        Some(rustledger_plugin_types::CostNumberData::PerUnitFromTotal {
                            total,
                            ..
                        }) => {
                            let total = Decimal::from_str(total).unwrap_or_default();
                            if units_num.is_sign_negative() {
                                -total.abs()
                            } else {
                                total.abs()
                            }
                        }
                        None => units_num,
                    };
                    Some((amount, currency))
                } else if let Some(price) = &posting.price {
                    let price_amount = price.amount.as_ref()?;
                    let price_num = Decimal::from_str(&price_amount.number).unwrap_or_default();
                    let currency = price_amount.currency.clone();
                    let amount = if price.is_total {
                        if units_num.is_sign_negative() {
                            -price_num.abs()
                        } else {
                            price_num.abs()
                        }
                    } else {
                        units_num * price_num
                    };
                    Some((amount, currency))
                } else {
                    Some((units_num, units.currency.clone()))
                }
            };

            // Compute each group's weight inventory for neutralization.
            let mut group_inv: BTreeMap<&String, BTreeMap<String, Decimal>> = BTreeMap::new();
            for (group_key, posting_indices) in &curmap {
                let inv = group_inv.entry(group_key).or_default();
                for &idx in posting_indices {
                    if let Some((amount, currency)) = weight_of(&txn.postings[idx]) {
                        *inv.entry(currency).or_default() += amount;
                    }
                }
                inv.retain(|_, amount| !amount.is_zero());
            }

            // Re-insert ALL original postings in their original order
            // (including any with units == None, which are auto-balanced
            // postings that must not be dropped).
            //
            // Python's plugin strips price annotations here
            // (currency_accounts.py:145) because its pipeline runs
            // plugins BEFORE booking. rustledger also runs plugins
            // before booking (since PR #1116), but we still keep prices
            // because the appended neutralizing postings already make
            // each currency group balanced on its own — booking then
            // fills any elided posting from the per-currency residual
            // and the extra prices are redundant rather than harmful.
            // See `rustledger_validate::Phase` docs and CLAUDE.md's
            // "Python Compatibility Policy" section for the broader
            // ordering rationale.
            let mut new_postings: Vec<PostingData> =
                Vec::with_capacity(txn.postings.len() + curmap.len());
            for posting in &txn.postings {
                new_postings.push(posting.clone());
            }

            // Append neutralizing postings (sorted by group key for
            // deterministic output).
            for (group_key, inv) in &group_inv {
                // Python calls `inv.get_only_position()` and errors on
                // multi-currency groups. We skip neutralization in that
                // case rather than failing — it indicates a transaction
                // shape the prototype plugin never handled.
                if inv.len() != 1 {
                    continue;
                }

                let (weight_currency, weight_amount) = inv.iter().next().unwrap();
                let account_name = format!("{base_account}:{group_key}");
                created_accounts.insert(account_name.clone());

                new_postings.push(PostingData {
                    account: account_name,
                    units: Some(AmountData {
                        number: (-*weight_amount).to_string(),
                        currency: weight_currency.clone(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                    span: None,
                });
            }

            let mut modified_txn = txn.clone();
            modified_txn.postings = new_postings;

            ops.push(PluginOp::Modify(
                i,
                DirectiveWrapper {
                    directive_type: wrapper.directive_type.clone(),
                    date: wrapper.date.clone(),
                    filename: wrapper.filename.clone(),
                    lineno: wrapper.lineno,
                    data: DirectiveData::Transaction(modified_txn),
                },
            ));
        }

        // Insert Open directives for newly-created currency accounts (skip existing).
        let mut new_open_accounts: Vec<String> = created_accounts
            .into_iter()
            .filter(|account| !existing_opens.contains(account))
            .collect();
        new_open_accounts.sort();
        for account in new_open_accounts {
            ops.push(PluginOp::Insert(DirectiveWrapper {
                directive_type: "open".to_string(),
                date: earliest_date.clone(),
                filename: Some("<currency_accounts>".to_string()),
                lineno: None,
                data: DirectiveData::Open(OpenData {
                    account,
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
}

#[cfg(test)]
mod currency_accounts_tests {
    use super::super::utils::materialize_ops;
    use super::*;
    use crate::types::*;

    fn txn_wrapper(date: &str, narration: &str, postings: Vec<PostingData>) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: narration.to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings,
            }),
        }
    }

    fn posting(account: &str, number: &str, currency: &str) -> PostingData {
        PostingData {
            account: account.to_string(),
            units: Some(AmountData {
                number: number.to_string(),
                currency: currency.to_string(),
            }),
            cost: None,
            price: None,
            flag: None,
            metadata: vec![],
            span: None,
        }
    }

    fn price_usd(number: &str) -> PriceAnnotationData {
        PriceAnnotationData {
            is_total: false,
            amount: Some(AmountData {
                number: number.to_string(),
                currency: "USD".to_string(),
            }),
            number: None,
            currency: None,
        }
    }

    fn default_options() -> PluginOptions {
        PluginOptions {
            operating_currencies: vec!["USD".to_string()],
            title: None,
        }
    }

    /// Regression test for #776. The canonical reproducer: a currency
    /// exchange with a price annotation on one side. Python groups by
    /// units currency, yielding EUR and USD groups, and emits two
    /// neutralizing postings and two Open directives.
    #[test]
    fn test_issue_776_currency_exchange_with_price() {
        let plugin = CurrencyAccountsPlugin::with_base_account("Equity:Currency".to_string());

        let mut p1 = posting("Assets:Bank:EUR", "-100", "EUR");
        p1.price = Some(price_usd("1.10"));

        let input = PluginInput {
            directives: vec![txn_wrapper(
                "2026-03-17",
                "Currency exchange",
                vec![p1, posting("Assets:Bank:USD", "110", "USD")],
            )],
            options: default_options(),
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);

        // 2 opens + 1 modified txn
        assert_eq!(directives.len(), 3);

        let mut opens: Vec<&str> = directives
            .iter()
            .filter_map(|d| {
                if let DirectiveData::Open(o) = &d.data {
                    Some(o.account.as_str())
                } else {
                    None
                }
            })
            .collect();
        opens.sort_unstable();
        assert_eq!(opens, vec!["Equity:Currency:EUR", "Equity:Currency:USD"]);

        let txn_dir = directives
            .iter()
            .find(|d| matches!(d.data, DirectiveData::Transaction(_)))
            .expect("expected transaction");
        let DirectiveData::Transaction(txn) = &txn_dir.data else {
            unreachable!()
        };
        // 2 originals + 2 neutralizers
        assert_eq!(txn.postings.len(), 4);
        // Original postings keep their price annotations (rustledger
        // runs booking before plugins, so stripping prices would cause
        // E3001 in the validator).
        assert!(txn.postings[0].price.is_some()); // EUR posting has price
        assert!(txn.postings[1].price.is_none()); // USD posting never had price

        // EUR group weight is -110 USD → neutralizer +110 USD on Equity:Currency:EUR.
        // Note the counter-intuitive currency mismatch — this is what Python emits.
        let eur_neut = txn
            .postings
            .iter()
            .find(|p| p.account == "Equity:Currency:EUR")
            .expect("missing EUR neutralizer");
        // rust_decimal preserves precision of operands: -100 * 1.10 = -110.00,
        // so the negated weight string is "110.00" (two trailing zeros from
        // the 1.10 factor). Python prints the same Decimal as "110.00".
        assert_eq!(eur_neut.units.as_ref().unwrap().number, "110.00");
        assert_eq!(eur_neut.units.as_ref().unwrap().currency, "USD");

        // USD group weight is +110 USD → neutralizer -110 USD on Equity:Currency:USD.
        let usd_neut = txn
            .postings
            .iter()
            .find(|p| p.account == "Equity:Currency:USD")
            .expect("missing USD neutralizer");
        assert_eq!(usd_neut.units.as_ref().unwrap().number, "-110");
        assert_eq!(usd_neut.units.as_ref().unwrap().currency, "USD");
    }

    /// Cost-only transaction: grouping key is cost.currency, and the plugin
    /// only neutralizes when `has_price` is true. Without a price annotation,
    /// the transaction passes through unchanged (no currency accounts created).
    #[test]
    fn test_cost_only_no_price_skipped() {
        let plugin = CurrencyAccountsPlugin::new();

        let mut p1 = posting("Assets:Shares:RING", "9", "RING");
        p1.cost = Some(CostData {
            number: Some(rustledger_plugin_types::CostNumberData::PerUnit {
                value: "68.55".to_string(),
            }),
            currency: Some("USD".to_string()),
            date: None,
            label: None,
            merge: false,
        });

        let input = PluginInput {
            directives: vec![txn_wrapper(
                "2026-03-21",
                "Buy RING",
                vec![
                    p1,
                    posting("Expenses:Financial", "0.35", "USD"),
                    posting("Assets:Cash:USD", "-617.30", "USD"),
                ],
            )],
            options: default_options(),
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);
        assert_eq!(directives.len(), 1);
        let DirectiveData::Transaction(txn) = &directives[0].data else {
            panic!("expected transaction");
        };
        assert_eq!(txn.postings.len(), 3);
    }

    /// Single-currency transaction (no price, no cost): passed through.
    #[test]
    fn test_single_currency_unchanged() {
        let plugin = CurrencyAccountsPlugin::new();
        let input = PluginInput {
            directives: vec![txn_wrapper(
                "2024-01-15",
                "Simple transfer",
                vec![
                    posting("Assets:Bank", "-100", "USD"),
                    posting("Expenses:Food", "100", "USD"),
                ],
            )],
            options: default_options(),
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        let directives = materialize_ops(&input_dirs, &output);
        assert_eq!(directives.len(), 1);
        let DirectiveData::Transaction(txn) = &directives[0].data else {
            panic!("expected transaction");
        };
        assert_eq!(txn.postings.len(), 2);
    }

    /// Custom base account via config string.
    #[test]
    fn test_custom_base_account() {
        let plugin = CurrencyAccountsPlugin::new();

        let mut p1 = posting("Assets:Bank:EUR", "-100", "EUR");
        p1.price = Some(price_usd("1.10"));

        let input = PluginInput {
            directives: vec![txn_wrapper(
                "2024-01-15",
                "Exchange",
                vec![p1, posting("Assets:Bank:USD", "110", "USD")],
            )],
            options: default_options(),
            config: Some("Income:Trading".to_string()),
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        let directives = materialize_ops(&input_dirs, &output);
        assert_eq!(directives.len(), 3);
        assert!(directives.iter().any(|d| {
            if let DirectiveData::Open(o) = &d.data {
                o.account == "Income:Trading:EUR"
            } else {
                false
            }
        }));
        assert!(directives.iter().any(|d| {
            if let DirectiveData::Open(o) = &d.data {
                o.account == "Income:Trading:USD"
            } else {
                false
            }
        }));
    }

    /// Pre-existing Open for a currency account should not be duplicated
    /// by the plugin (would cause E1002 in the validator).
    #[test]
    fn test_skips_existing_open() {
        let plugin = CurrencyAccountsPlugin::new();

        let existing_open = DirectiveWrapper {
            directive_type: "open".to_string(),
            date: "2024-01-01".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Open(OpenData {
                account: "Equity:CurrencyAccounts:USD".to_string(),
                currencies: vec![],
                booking: None,
                metadata: vec![],
            }),
        };

        let mut p1 = posting("Assets:Bank:EUR", "-100", "EUR");
        p1.price = Some(price_usd("1.10"));

        let input = PluginInput {
            directives: vec![
                existing_open,
                txn_wrapper(
                    "2024-01-15",
                    "Exchange",
                    vec![p1, posting("Assets:Bank:USD", "110", "USD")],
                ),
            ],
            options: default_options(),
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        let directives = materialize_ops(&input_dirs, &output);

        // Only Equity:CurrencyAccounts:EUR should be a newly-created open
        // (filename marker <currency_accounts>). The USD open passed
        // through from the input.
        let new_currency_opens: Vec<&str> = directives
            .iter()
            .filter_map(|d| {
                if let DirectiveData::Open(o) = &d.data
                    && d.filename.as_deref() == Some("<currency_accounts>")
                {
                    Some(o.account.as_str())
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(new_currency_opens, vec!["Equity:CurrencyAccounts:EUR"]);
    }

    /// Open directives for plugin-created accounts use the earliest date
    /// observed in the input (matches Python `earliest_date = entries[0].date`
    /// when entries are date-sorted upstream).
    #[test]
    fn test_open_uses_earliest_date() {
        let plugin = CurrencyAccountsPlugin::new();

        let mut p_later = posting("Assets:Bank:EUR", "-100", "EUR");
        p_later.price = Some(price_usd("1.10"));

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:Bank:EUR".to_string(),
                        currencies: vec![],
                        booking: None,
                        metadata: vec![],
                    }),
                },
                txn_wrapper(
                    "2026-03-17",
                    "Exchange",
                    vec![p_later, posting("Assets:Bank:USD", "110", "USD")],
                ),
            ],
            options: default_options(),
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        let directives = materialize_ops(&input_dirs, &output);
        for wrapper in &directives {
            if let DirectiveData::Open(o) = &wrapper.data
                && o.account.starts_with("Equity:CurrencyAccounts:")
                && wrapper.filename.as_deref() == Some("<currency_accounts>")
            {
                assert_eq!(
                    wrapper.date, "2024-01-01",
                    "plugin-created open should use earliest date"
                );
            }
        }
    }
}
