//! Auto-generate currency trading account postings.

use crate::types::{DirectiveData, DirectiveWrapper, PluginInput, PluginOp, PluginOutput};

use super::super::{NativePlugin, RegularPlugin};

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
///    posting for each group WHOSE COST BASIS IS NON-ZERO (a group that
///    already nets to zero needs none — see step 3). It goes to
///    `<base>:<group_key>` and carries the negated COST BASIS of that
///    group — units, or `units x cost` for a posting held at cost. A
///    price annotation is deliberately NOT applied, matching Python's
///    `convert.get_cost`, so the posting is denominated in the group's
///    own currency.
/// 3. Postings in a neutralized group have their `price` stripped, as
///    Python does. Once the group's imbalance is stated explicitly by a
///    currency-account posting, leaving the price on would double-count
///    the conversion and the transaction would not balance. Groups whose
///    cost basis nets to zero get no neutralizing posting and keep their
///    prices.
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

            // `weight(posting)` returns (amount, currency), delegating the
            // arithmetic to the booking crate's single-source weight ladder
            // (`cost_number_weight` / `price_weight`), after parsing this DTO's
            // string numbers.
            //
            // The ARITHMETIC is shared; the LADDER is not the balance
            // validator's. `residual_weight` differs deliberately — it does not
            // infer a cost number that carries no currency, and it does not let
            // a bare `{}` fall through to a price — because #1026 turns on
            // that. This comment previously claimed it was "the exact rule the
            // balance validator's residual uses", which would send someone
            // chasing a `weight`-vs-`rledger check` disagreement into aligning
            // the residual and flipping E3001 for every ledger holding a
            // bare-cost-plus-price posting. This copy also differs from
            // `rustledger_booking::posting_weight` for the same two shapes;
            // see that function's docs for the other half of the pair. The `CostNumberData` → `CostNumber` mapping is
            // an exhaustive match, so future variant additions still
            // compile-fail here, which is what we want.
            //   - Cost: canonical cost weight in cost.currency (preserved
            //     totals — no division-then-multiplication precision loss).
            //   - Else: (units.amount, units.currency)
            //
            // There is deliberately NO price arm — this is a COST BASIS, not
            // a weight. Consequently the currency returned here is always the
            // one the group is keyed on, since both derive it from the same
            // `cost.currency` / `units.currency` expression.
            let cost_basis_of = |posting: &PostingData| -> Option<(Decimal, String)> {
                use rustledger_core::{BookedCost, CostNumber};
                use rustledger_plugin_types::CostNumberData;
                let units = posting.units.as_ref()?;
                let units_num = Decimal::from_str(&units.number).unwrap_or_default();
                let parse = |s: &str| Decimal::from_str(s).unwrap_or_default();
                if let Some(cost) = &posting.cost {
                    let currency = cost
                        .currency
                        .clone()
                        .unwrap_or_else(|| units.currency.clone());
                    let number = match &cost.number {
                        Some(CostNumberData::PerUnit { value }) => Some(CostNumber::PerUnit {
                            value: parse(value),
                        }),
                        Some(CostNumberData::Total { value }) => Some(CostNumber::Total {
                            value: parse(value),
                        }),
                        Some(CostNumberData::Compound { per_unit, total }) => {
                            Some(CostNumber::Compound {
                                per_unit: parse(per_unit),
                                total: parse(total),
                            })
                        }
                        Some(CostNumberData::PerUnitFromTotal { per_unit, total }) => {
                            // Struct literal, deliberately NOT
                            // `BookedCost::try_new`: the weight arithmetic
                            // reads only `.total` for this variant (see
                            // `cost_number_weight`), so the
                            // `per_unit x |units| == total` invariant is
                            // irrelevant here — and enforcing it would need
                            // an error channel this infallible closure
                            // doesn't have. Consistency of wire-supplied
                            // pairs is the ingress boundary's job
                            // (ffi-wasi `input_entry_to_directive` rejects
                            // inconsistent pairs via `try_new`); this DTO
                            // arrives from the host's own booked data.
                            Some(CostNumber::PerUnitFromTotal(BookedCost {
                                per_unit: parse(per_unit),
                                total: parse(total),
                            }))
                        }
                        None => None,
                    };
                    let amount = match &number {
                        // `None` from the weight ladder means the product left
                        // `rust_decimal`'s range (#1863); the posting is then
                        // skipped rather than grouped under a clamped weight.
                        Some(n) => rustledger_booking::cost_number_weight(units_num, n)?,
                        // Empty `{}` — no determinable cost number; fall back
                        // to the units magnitude (pre-existing behavior; the
                        // spec is resolved by booking before plugins run).
                        None => units_num,
                    };
                    Some((amount, currency))
                } else {
                    // NO price branch. This mirrors Python's
                    // `convert.get_cost`, which returns the cost basis when
                    // there is a cost and the bare UNITS otherwise — it never
                    // applies a price annotation. Using the price-converted
                    // weight here is what made every neutralizing posting land
                    // in the price currency.
                    Some((units_num, units.currency.clone()))
                }
            };

            // Compute each group's weight inventory for neutralization.
            let mut group_inv: BTreeMap<&String, BTreeMap<String, Decimal>> = BTreeMap::new();
            for (group_key, posting_indices) in &curmap {
                let inv = group_inv.entry(group_key).or_default();
                for &idx in posting_indices {
                    if let Some((amount, currency)) = cost_basis_of(&txn.postings[idx]) {
                        *inv.entry(currency).or_default() += amount;
                    }
                }
                inv.retain(|_, amount| !amount.is_zero());
            }

            // Re-insert ALL original postings in their original order
            // (including any with units == None, which are auto-balanced
            // postings that must not be dropped).
            //
            //
            // Postings in a neutralized group have their PRICE STRIPPED, as
            // Python does. This is not cosmetic: once the group's imbalance is
            // represented explicitly by a currency-account posting, leaving the
            // price on would double-count the conversion and the transaction
            // would not balance. Groups that net to zero get no neutralizing
            // posting and keep their prices, again matching Python.
            let neutralized: std::collections::HashSet<usize> = curmap
                .iter()
                .filter(|(k, _)| group_inv.get(k).is_some_and(|inv| inv.len() == 1))
                .flat_map(|(_, idxs)| idxs.iter().copied())
                .collect();
            let mut new_postings: Vec<PostingData> =
                Vec::with_capacity(txn.postings.len() + curmap.len());
            for (idx, posting) in txn.postings.iter().enumerate() {
                let mut posting = posting.clone();
                if neutralized.contains(&idx) {
                    posting.price = None;
                }
                new_postings.push(posting);
            }

            // Append neutralizing postings (sorted by group key for
            // deterministic output).
            for (group_key, inv) in &group_inv {
                // A group's cost basis is denominated in exactly the
                // currency the group is keyed on, so this map holds at most
                // one entry (len 0 means the basis netted to zero, which
                // needs no neutralizing posting — Python's `inv.is_empty()`
                // branch).
                //
                // The `!= 1` guard is therefore unreachable on the >1 side
                // today; it is kept as a fail-closed backstop. It was
                // reachable before the cost-basis fix, when a price posting
                // contributed `price.currency` to a group keyed on
                // `units.currency` — which is precisely how the wrong-currency
                // neutralizers arose. Python asserts here via
                // `get_only_position()`; we skip the group instead.
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

impl RegularPlugin for CurrencyAccountsPlugin {}

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
            ..Default::default()
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
        // The price is STRIPPED from the EUR posting. Once the group's
        // imbalance is stated explicitly by a currency-account posting, the
        // price would double-count the conversion and the transaction would
        // not balance.
        assert!(txn.postings[0].price.is_none()); // EUR posting: price stripped
        assert!(txn.postings[1].price.is_none()); // USD posting never had one

        // The EUR group's COST BASIS is -100 EUR (a price annotation is not a
        // cost), so the neutralizer is +100 EUR.
        //
        // This test previously asserted +110.00 USD here, with a comment
        // calling the currency mismatch "counter-intuitive... what Python
        // emits". Python emits no such thing — beancount 3.2.3 on this exact
        // ledger produces `Equity:Currency:EUR 100 EUR`. The old expectation
        // also made the method useless: two neutralizers in the SAME currency
        // are equal and opposite, so `Equity:Currency:*` always summed to
        // zero and could never show the FX gain the accounts exist to track.
        let eur_neut = txn
            .postings
            .iter()
            .find(|p| p.account == "Equity:Currency:EUR")
            .expect("missing EUR neutralizer");
        assert_eq!(eur_neut.units.as_ref().unwrap().number, "100");
        assert_eq!(eur_neut.units.as_ref().unwrap().currency, "EUR");

        // USD group weight is +110 USD → neutralizer -110 USD on Equity:Currency:USD.
        let usd_neut = txn
            .postings
            .iter()
            .find(|p| p.account == "Equity:Currency:USD")
            .expect("missing USD neutralizer");
        assert_eq!(usd_neut.units.as_ref().unwrap().number, "-110");
        assert_eq!(usd_neut.units.as_ref().unwrap().currency, "USD");
    }

    /// A group whose COST BASIS nets to zero gets no neutralizing posting,
    /// and — importantly — keeps its price annotations.
    ///
    /// Mirrors Python's `if inv.is_empty(): new_postings.extend(postings)`
    /// branch, which re-inserts that group's postings untouched. Verified
    /// against beancount 3.2.3: its `Inventory` drops zero positions, so a
    /// group summing to zero reports `is_empty()` and is skipped.
    ///
    /// This matters because price stripping and neutralizing are a package:
    /// stripping a price WITHOUT adding the compensating posting would leave
    /// the transaction unbalanced.
    #[test]
    fn test_zero_basis_group_keeps_prices_and_gets_no_posting() {
        let plugin = CurrencyAccountsPlugin::with_base_account("Equity:Currency".to_string());

        // Two EUR postings that cancel, one carrying a price, plus a USD leg
        // so there are two groups and the plugin engages.
        let mut e1 = posting("Assets:Bank:EUR", "-100", "EUR");
        e1.price = Some(price_usd("1.10"));
        let e2 = posting("Assets:Other:EUR", "100", "EUR");
        let u1 = posting("Assets:Bank:USD", "50", "USD");

        let input = PluginInput {
            directives: vec![txn_wrapper(
                "2026-03-17",
                "Zero EUR group",
                vec![e1, e2, u1],
            )],
            options: default_options(),
            config: None,
        };
        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);

        let txn_dir = directives
            .iter()
            .find(|d| matches!(d.data, DirectiveData::Transaction(_)))
            .expect("expected transaction");
        let DirectiveData::Transaction(txn) = &txn_dir.data else {
            unreachable!()
        };

        // No EUR currency account: that group's basis is -100 + 100 = 0.
        assert!(
            !txn.postings
                .iter()
                .any(|p| p.account == "Equity:Currency:EUR"),
            "zero-basis group must not be neutralized: {:?}",
            txn.postings.iter().map(|p| &p.account).collect::<Vec<_>>()
        );
        // And its price survives, because nothing compensates for removing it.
        assert!(
            txn.postings[0].price.is_some(),
            "a skipped group keeps its price"
        );
        // The USD group is non-zero, so it IS neutralized.
        let usd = txn
            .postings
            .iter()
            .find(|p| p.account == "Equity:Currency:USD")
            .expect("USD group should be neutralized");
        assert_eq!(usd.units.as_ref().unwrap().number, "-50");
        assert_eq!(usd.units.as_ref().unwrap().currency, "USD");
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
