//! Effective date plugin - move postings to their effective dates.
//!
//! When a posting has an `effective_date` metadata, this plugin:
//! 1. Moves the original posting to a holding account on the transaction date
//! 2. Creates a new transaction on the effective date
//!
//! Configuration (optional):
//! ```text
//! plugin "beancount_reds_plugins.effective_date.effective_date" "{
//!   'Expenses': {'earlier': 'Liabilities:Hold:Expenses', 'later': 'Assets:Hold:Expenses'},
//!   'Income': {'earlier': 'Assets:Hold:Income', 'later': 'Liabilities:Hold:Income'},
//! }"
//! ```

use std::collections::{BTreeSet, HashSet};

use crate::types::{
    AmountData, DirectiveData, DirectiveWrapper, MetaValueData, OpenData, PluginError,
    PluginErrorSeverity, PluginInput, PluginOp, PluginOutput, PostingData, TransactionData,
};

use super::super::{NativePlugin, RegularPlugin};

/// Plugin for handling effective dates on postings.
pub struct EffectiveDatePlugin;

/// The holding accounts config: `(prefix, (earlier, later))` in the order
/// the config names them.
///
/// A list, not a hash map, because the order decides the answer when two
/// prefixes match one account (`Expenses` and `Expenses:Car`): the plugin
/// takes the LAST match in config order, as the upstream Python plugin does
/// (`for acct in holding_accts: if ...startswith(acct): found_acct = acct`).
/// Over a `HashMap` the winner, and so the holding account, changed from run
/// to run.
type HoldingAccounts = Vec<(String, (String, String))>;

/// Default holding accounts configuration.
fn default_holding_accounts() -> HoldingAccounts {
    vec![
        (
            "Expenses".to_string(),
            (
                "Liabilities:Hold:Expenses".to_string(),
                "Assets:Hold:Expenses".to_string(),
            ),
        ),
        (
            "Income".to_string(),
            (
                "Assets:Hold:Income".to_string(),
                "Liabilities:Hold:Income".to_string(),
            ),
        ),
    ]
}

impl NativePlugin for EffectiveDatePlugin {
    fn name(&self) -> &'static str {
        "effective_date"
    }

    fn description(&self) -> &'static str {
        "Move postings to their effective dates using holding accounts"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        // Parse configuration or use defaults. A config that does not parse
        // is an error and the plugin changes nothing, as upstream, where
        // `literal_eval` raises and beancount reports the plugin's failure.
        // This used to fall back to the default config silently, so a typo
        // in a custom config moved postings to holding accounts the user had
        // not asked for.
        let holding_accounts = match input.config.as_deref().map(parse_config) {
            None => default_holding_accounts(),
            Some(Ok(config)) => config,
            Some(Err(e)) => {
                return PluginOutput {
                    ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                    errors: vec![PluginError {
                        message: format!("effective_date: cannot read the config: {e}"),
                        source_file: None,
                        line_number: None,
                        severity: PluginErrorSeverity::Error,
                    }],
                };
            }
        };
        let mut errors: Vec<PluginError> = Vec::new();

        // Sorted: the synthesized `open`s are emitted in this order, all on
        // one date, and the upstream plugin emits them `sorted(new_accounts)`.
        // A `HashSet` here made `PRINT` and `#entries` output differ between
        // two runs over the same ledger.
        let mut new_accounts: BTreeSet<String> = BTreeSet::new();
        let mut earliest_date: Option<String> = None;
        // Accounts already opened by the user; suppress duplicate Opens
        // for holding accounts the user has pre-declared (else Late
        // validation emits E1002 AccountAlreadyOpen). Mirrors the
        // pattern in `zerosum`, `currency_accounts`, `split_expenses`,
        // and `capital_gains_classifier`.
        let mut existing_opens: HashSet<String> = HashSet::new();

        // Compute earliest date AND record existing opens in one pass.
        for directive in &input.directives {
            if earliest_date.is_none() || directive.date < *earliest_date.as_ref().unwrap() {
                earliest_date = Some(directive.date.clone());
            }
            if let DirectiveData::Open(open) = &directive.data {
                existing_opens.insert(open.account.clone());
            }
        }

        let mut ops: Vec<PluginOp> = Vec::with_capacity(input.directives.len());
        // Inserted new transactions (one per posting with effective_date),
        // accumulated into ops after the main loop so the Modify(i, ...)
        // entries stay paired with their input indices in input-order.
        let mut inserted_txns: Vec<DirectiveWrapper> = Vec::new();

        // Links number the entries this run moves on each date, in input
        // order: the same ledger gets the same links every time, in any
        // process, and an edit shifts only the links of later moved entries
        // on the same date. They came from a process-wide counter taken
        // modulo 4096, so an LSP or FFI host reloading a ledger saw its
        // links change, and the 4097th entry reused the first one's link.
        let mut moved_on: std::collections::BTreeMap<String, usize> =
            std::collections::BTreeMap::new();

        for (i, mut directive) in input.directives.into_iter().enumerate() {
            let DirectiveData::Transaction(txn) = &directive.data else {
                ops.push(PluginOp::Keep(i));
                continue;
            };
            if !txn
                .postings
                .iter()
                .any(|p| effective_date_meta(p).is_some())
            {
                ops.push(PluginOp::Keep(i));
                continue;
            }

            // Every marked posting must be one the plugin can move, or the
            // whole entry stays as written and each one that cannot is
            // reported: a posting marked `effective_date` is moved or
            // reported, never kept in place beside siblings that moved.
            let entry_date = directive.date.clone();
            let mut plans: Vec<Option<(String, String)>> = Vec::with_capacity(txn.postings.len());
            let mut problems: Vec<String> = Vec::new();
            for posting in &txn.postings {
                let Some(value) = effective_date_meta(posting) else {
                    plans.push(None);
                    continue;
                };
                let plan = match value {
                    // As upstream, which reports it and keeps the entry.
                    MetaValueData::Date(date) if *date == entry_date => {
                        Err("Effective and actual dates are identical".to_string())
                    }
                    MetaValueData::Date(date) => {
                        match find_holding_account(
                            &posting.account,
                            date,
                            &entry_date,
                            &holding_accounts,
                        ) {
                            // Upstream crashes on an elided amount (`-None`).
                            Some(_) if posting.units.is_none() => {
                                Err("the posting has no amount to move".to_string())
                            }
                            Some(new_account) => Ok((date.clone(), new_account)),
                            // Upstream fails the whole plugin (`KeyError: ''`).
                            None => Err("no holding account is configured for it".to_string()),
                        }
                    }
                    // Upstream skips a non-date value silently, leaving
                    // the posting where it is.
                    other => Err(format!(
                        "its `effective_date` is not a date: {}",
                        describe_meta(other)
                    )),
                };
                match plan {
                    Ok(plan) => plans.push(Some(plan)),
                    Err(reason) => {
                        problems.push(format!("{} ({reason})", posting.account));
                        plans.push(None);
                    }
                }
            }
            if !problems.is_empty() {
                for problem in problems {
                    errors.push(PluginError {
                        message: format!(
                            "effective_date: cannot move {problem}; the transaction is left as written"
                        ),
                        source_file: directive.filename.clone(),
                        line_number: directive.lineno,
                        severity: PluginErrorSeverity::Error,
                    });
                }
                ops.push(PluginOp::Keep(i));
                continue;
            }

            let n = moved_on.entry(entry_date.clone()).or_insert(0);
            let link = edate_link(&entry_date, *n);
            *n += 1;

            if let DirectiveData::Transaction(ref mut txn) = directive.data {
                if !txn.links.contains(&link) {
                    txn.links.push(link.clone());
                }
                let mut modified_postings = Vec::with_capacity(txn.postings.len());
                for (posting, plan) in txn.postings.iter().zip(plans) {
                    let Some((effective_date, new_account)) = plan else {
                        modified_postings.push(posting.clone());
                        continue;
                    };
                    new_accounts.insert(new_account.clone());

                    // The posting moves to the holding account, its metadata
                    // as written, `effective_date` included, as upstream.
                    let mut modified_posting = posting.clone();
                    modified_posting.account.clone_from(&new_account);

                    // The new entry: the holding account reversed and the
                    // original posting, both without `effective_date`.
                    let mut cleaned_original = posting.clone();
                    cleaned_original
                        .metadata
                        .retain(|(k, _)| k != "effective_date");
                    let mut hold_posting = create_opposite_posting(&modified_posting);
                    hold_posting.metadata.retain(|(k, _)| k != "effective_date");
                    modified_postings.push(modified_posting);

                    // It keeps the transaction's metadata, tags and links (the
                    // edate link among them), plus `original_date`, as
                    // upstream's `entry._replace(meta={**entry.meta, ...})`.
                    let mut metadata: Vec<(String, MetaValueData)> = txn
                        .metadata
                        .iter()
                        .filter(|(k, _)| k != "original_date")
                        .cloned()
                        .collect();
                    metadata.push((
                        "original_date".to_string(),
                        MetaValueData::Date(entry_date.clone()),
                    ));
                    let new_txn = TransactionData {
                        flag: txn.flag.clone(),
                        payee: txn.payee.clone(),
                        narration: txn.narration.clone(),
                        tags: txn.tags.clone(),
                        links: txn.links.clone(),
                        metadata,
                        postings: vec![hold_posting, cleaned_original],
                    };
                    inserted_txns.push(DirectiveWrapper {
                        directive_type: "transaction".to_string(),
                        date: effective_date,
                        filename: directive.filename.clone(),
                        lineno: directive.lineno,
                        data: DirectiveData::Transaction(new_txn),
                    });
                }
                txn.postings = modified_postings;
            }

            ops.push(PluginOp::Modify(i, directive));
        }

        // Append all inserted new-date transactions.
        for w in inserted_txns {
            ops.push(PluginOp::Insert(w));
        }

        // Insert Open directives for newly synthesized holding accounts
        // the user hasn't already opened.
        if let Some(date) = &earliest_date {
            for account in &new_accounts {
                if existing_opens.contains(account) {
                    continue;
                }
                ops.push(PluginOp::Insert(DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: date.clone(),
                    filename: Some("<effective_date>".to_string()),
                    lineno: Some(0),
                    data: DirectiveData::Open(OpenData {
                        account: account.clone(),
                        currencies: vec![],
                        booking: None,
                        metadata: vec![],
                    }),
                }));
            }
        }

        PluginOutput { ops, errors }
    }
}

impl RegularPlugin for EffectiveDatePlugin {}

/// A posting's `effective_date` metadata value, whatever its type.
fn effective_date_meta(posting: &PostingData) -> Option<&MetaValueData> {
    posting
        .metadata
        .iter()
        .find(|(key, _)| key == "effective_date")
        .map(|(_, value)| value)
}

/// A metadata value as the ledger wrote it, for an error message.
fn describe_meta(value: &MetaValueData) -> String {
    match value {
        MetaValueData::String(s) => format!("the string \"{s}\""),
        MetaValueData::Number(n) => format!("the number {n}"),
        MetaValueData::Account(a) => format!("the account {a}"),
        MetaValueData::Currency(c) => format!("the currency {c}"),
        other => format!("{other:?}"),
    }
}

/// The holding account `account` moves to: the most specific configured
/// prefix that `account` equals or sits under (on a `:` boundary), with that
/// prefix replaced by its earlier holding account when the effective date is
/// not after the entry's, else its later one.
///
/// Deliberately not upstream's rule. Upstream tests `startswith` on the raw
/// string, takes the last match in config order, and renames with
/// `str.replace`, which replaces every occurrence. So `Expenses:Car` matched
/// `Expenses:Cards:Fee`; a general prefix listed after a specific one
/// shadowed it; and prefix `Income` turned `Income:Interest:Income` into
/// `Assets:Hold:Income:Interest:Assets:Hold:Income`. Here only whole account
/// components match, the most specific prefix wins whatever the order, and
/// only the leading prefix is replaced.
fn find_holding_account(
    account: &str,
    effective_date: &str,
    entry_date: &str,
    holding_accounts: &HoldingAccounts,
) -> Option<String> {
    let (prefix, (earlier, later)) = holding_accounts
        .iter()
        .filter(|(prefix, _)| {
            // A prefix written with its trailing `:` (`'Expenses:'`) is
            // already on a boundary.
            account == prefix
                || account
                    .strip_prefix(prefix.as_str())
                    .is_some_and(|rest| prefix.ends_with(':') || rest.starts_with(':'))
        })
        .max_by_key(|(prefix, _)| prefix.len())?;
    let hold = if effective_date > entry_date {
        later
    } else {
        earlier
    };
    Some(format!("{hold}{}", &account[prefix.len()..]))
}

/// Create a posting with the opposite amount.
fn create_opposite_posting(posting: &PostingData) -> PostingData {
    let mut opposite = posting.clone();
    if let Some(ref units) = opposite.units {
        let number = if units.number.starts_with('-') {
            units.number[1..].to_string()
        } else {
            format!("-{}", units.number)
        };
        opposite.units = Some(AmountData {
            number,
            currency: units.currency.clone(),
        });
    }
    opposite
}

/// The link joining an entry the plugin moves to its new entries:
/// `edate-<yymmdd>-<n>`, `n` counting, in hex and with no wraparound, the
/// entries of that date moved before it in this run. Upstream draws three
/// random letters (`edate-200301-flb`).
fn edate_link(date: &str, n: usize) -> String {
    let date_short = date.replace('-', "");
    let date_short = date_short.get(2..).unwrap_or(&date_short);
    format!("edate-{date_short}-{n:03x}")
}

/// Parse the configuration string the way upstream does: `if config:
/// literal_eval(config)`, with a falsy result meaning the default config.
///
/// The value must then be a dict mapping each account prefix to a dict with
/// string `earlier` and `later` entries (other entries are ignored, as
/// upstream ignores them). Upstream only fails on a malformed entry when a
/// posting reaches it (`KeyError`, `TypeError`); this reports it up front.
/// A text `literal_eval` rejects is an error here too.
fn parse_config(config: &str) -> Result<HoldingAccounts, String> {
    use super::py_literal::{self, PyValue};

    if config.is_empty() {
        return Ok(default_holding_accounts());
    }
    let value = py_literal::parse(config)?;
    if !value.is_truthy() {
        return Ok(default_holding_accounts());
    }
    let PyValue::Dict(entries) = value else {
        return Err("expected a dict of holding accounts".to_string());
    };
    // Python builds the dict first: a repeated key keeps its first position
    // and takes its last value, so an earlier, malformed value under that key
    // is gone before anything reads it.
    let mut merged: Vec<(PyValue, PyValue)> = Vec::with_capacity(entries.len());
    for (key, holding) in entries {
        if let Some(entry) = merged.iter_mut().find(|(k, _)| *k == key) {
            entry.1 = holding;
        } else {
            merged.push((key, holding));
        }
    }
    let mut result: HoldingAccounts = Vec::with_capacity(merged.len());
    for (key, holding) in merged {
        let PyValue::Str(prefix) = key else {
            return Err(format!("a prefix must be a string, found {key:?}"));
        };
        let field = |name: &str| -> Result<String, String> {
            let PyValue::Dict(fields) = &holding else {
                return Err(format!("the entry for '{prefix}' must be a dict"));
            };
            // The last value of a repeated key wins, as in a Python dict.
            match fields
                .iter()
                .rev()
                .find(|(k, _)| matches!(k, PyValue::Str(k) if k == name))
            {
                Some((_, PyValue::Str(account))) => Ok(account.clone()),
                Some(_) => Err(format!("'{name}' for '{prefix}' must be a string")),
                None => Err(format!("the entry for '{prefix}' needs '{name}'")),
            }
        };
        let accounts = (field("earlier")?, field("later")?);
        result.push((prefix, accounts));
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::super::utils::materialize_ops;
    use super::*;
    use crate::types::*;

    fn create_test_transaction_with_effective_date(
        date: &str,
        effective_date: &str,
    ) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "Test with effective date".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        account: "Assets:Cash".to_string(),
                        units: Some(AmountData {
                            number: "-100.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                    PostingData {
                        account: "Expenses:Food".to_string(),
                        units: Some(AmountData {
                            number: "100.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![(
                            "effective_date".to_string(),
                            MetaValueData::Date(effective_date.to_string()),
                        )],
                        span: None,
                    },
                ],
            }),
        }
    }

    #[test]
    fn test_effective_date_later() {
        let plugin = EffectiveDatePlugin;

        let input = PluginInput {
            directives: vec![create_test_transaction_with_effective_date(
                "2024-01-15",
                "2024-02-01",
            )],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);

        // Should have: open directives + original modified + new at effective date
        assert!(directives.len() >= 2);

        // Check that we have a transaction at the effective date
        let effective_txn_count = directives
            .iter()
            .filter(|d| d.date == "2024-02-01" && matches!(d.data, DirectiveData::Transaction(_)))
            .count();
        assert_eq!(effective_txn_count, 1);
    }

    #[test]
    fn test_effective_date_earlier() {
        let plugin = EffectiveDatePlugin;

        let input = PluginInput {
            directives: vec![create_test_transaction_with_effective_date(
                "2024-02-01",
                "2024-01-15",
            )],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);

        // Check that we have a transaction at the earlier effective date
        let effective_txn_count = directives
            .iter()
            .filter(|d| d.date == "2024-01-15" && matches!(d.data, DirectiveData::Transaction(_)))
            .count();
        assert_eq!(effective_txn_count, 1);
    }

    #[test]
    fn test_no_effective_date_unchanged() {
        let plugin = EffectiveDatePlugin;

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-01-15".to_string(),
                filename: None,
                lineno: None,
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "Regular transaction".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![],
                    postings: vec![
                        PostingData {
                            account: "Assets:Cash".to_string(),
                            units: Some(AmountData {
                                number: "-100.00".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                            span: None,
                        },
                        PostingData {
                            account: "Expenses:Food".to_string(),
                            units: Some(AmountData {
                                number: "100.00".to_string(),
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
            config: None,
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);
        // Should have exactly 1 transaction (unchanged)
        let txn_count = directives
            .iter()
            .filter(|d| matches!(d.data, DirectiveData::Transaction(_)))
            .count();
        assert_eq!(txn_count, 1);
    }

    /// A transaction whose postings are `(account, number, effective_date)`.
    fn txn_with(date: &str, postings: &[(&str, &str, Option<&str>)]) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "t".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: postings
                    .iter()
                    .map(|(account, number, effective)| PostingData {
                        account: (*account).to_string(),
                        units: Some(AmountData {
                            number: (*number).to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: effective
                            .map(|d| {
                                vec![(
                                    "effective_date".to_string(),
                                    MetaValueData::Date(d.to_string()),
                                )]
                            })
                            .unwrap_or_default(),
                        span: None,
                    })
                    .collect(),
            }),
        }
    }

    fn input(directives: Vec<DirectiveWrapper>, config: Option<&str>) -> PluginInput {
        PluginInput {
            directives,
            options: PluginOptions::default(),
            config: config.map(ToString::to_string),
        }
    }

    /// The synthesized `open`s come out sorted, as the upstream plugin emits
    /// them (`sorted(new_accounts)`). They were in `HashSet` order, so two runs
    /// over one ledger printed them in different orders.
    #[test]
    fn synthesized_opens_are_sorted() {
        let directives = vec![txn_with(
            "2024-01-15",
            &[
                ("Expenses:Rent", "10", Some("2024-02-01")),
                ("Expenses:Car", "10", Some("2024-02-01")),
                ("Expenses:Food", "10", Some("2024-02-01")),
                ("Income:Salary", "-10", Some("2024-01-01")),
                ("Expenses:Books", "10", Some("2024-01-01")),
                ("Assets:Cash", "-30", None),
            ],
        )];
        let output = EffectiveDatePlugin.process(input(directives.clone(), None));
        let opened: Vec<String> = materialize_ops(&directives, &output)
            .into_iter()
            .filter_map(|d| match d.data {
                DirectiveData::Open(open) => Some(open.account),
                _ => None,
            })
            .collect();
        let mut sorted = opened.clone();
        sorted.sort();
        assert_eq!(opened.len(), 5, "{opened:?}");
        assert_eq!(opened, sorted);
    }

    const CAR_CONFIG: &str = "{'Expenses:Car': {'earlier': 'Liabilities:Hold:Car', 'later': 'Assets:Hold:Car'}, \
                              'Expenses': {'earlier': 'Liabilities:Hold:Expenses', 'later': 'Assets:Hold:Expenses'}}";

    /// The most specific matching prefix wins whatever the config order:
    /// `Expenses:Car` listed BEFORE `Expenses` still takes `Expenses:Car:Gas`.
    /// Upstream takes the last match in config order, so there the general
    /// prefix listed after shadows the specific one. Over the old `HashMap`
    /// the winner was random, so the run is repeated.
    #[test]
    fn the_most_specific_prefix_wins_in_any_order() {
        let directives = vec![txn_with(
            "2024-01-15",
            &[
                ("Expenses:Car:Gas", "10", Some("2024-02-01")),
                ("Assets:Cash", "-10", None),
            ],
        )];
        for _ in 0..32 {
            let output = EffectiveDatePlugin.process(input(directives.clone(), Some(CAR_CONFIG)));
            assert!(output.errors.is_empty(), "{:?}", output.errors);
            assert_eq!(opened(&directives, &output), ["Assets:Hold:Car:Gas"]);
        }
    }

    /// Prefixes match whole account components: `Expenses:Car` does not take
    /// `Expenses:Cards:Fee`, which falls to `Expenses`. Upstream's raw
    /// `startswith` matched it, and moved it to `Assets:Hold:Cards:Fee`.
    #[test]
    fn a_prefix_matches_whole_components_only() {
        let directives = vec![txn_with(
            "2024-01-15",
            &[
                ("Expenses:Cards:Fee", "10", Some("2024-02-01")),
                ("Expenses:Car", "10", Some("2024-02-01")),
                ("Assets:Cash", "-20", None),
            ],
        )];
        let output = EffectiveDatePlugin.process(input(directives.clone(), Some(CAR_CONFIG)));
        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert_eq!(
            opened(&directives, &output),
            ["Assets:Hold:Car", "Assets:Hold:Expenses:Cards:Fee"]
        );
    }

    /// A prefix written with a trailing `:` still matches the accounts under
    /// it, and the holding account written the same way joins cleanly, as
    /// upstream's `startswith` / `replace` handle it.
    #[test]
    fn a_prefix_with_a_trailing_colon_matches() {
        let config = "{'Expenses:': {'earlier': 'Liabilities:Hold:E:', 'later': 'Assets:Hold:E:'}}";
        let directives = vec![txn_with(
            "2024-01-15",
            &[
                ("Expenses:Food", "10", Some("2024-02-01")),
                ("Assets:Cash", "-10", None),
            ],
        )];
        let output = EffectiveDatePlugin.process(input(directives.clone(), Some(config)));
        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert_eq!(opened(&directives, &output), ["Assets:Hold:E:Food"]);
    }

    /// A link depends only on the moved entries of its own date before it:
    /// adding an unrelated transaction, or a moved one on another date,
    /// leaves every link as it was. A moved entry added earlier on the same
    /// date renumbers the later ones of that date; that is the cost of links
    /// that need no randomness.
    #[test]
    fn links_shift_only_with_moved_entries_of_the_same_date() {
        let moved = |date: &str| {
            txn_with(
                date,
                &[
                    ("Expenses:Rent", "10", Some("2024-03-01")),
                    ("Assets:Cash", "-10", None),
                ],
            )
        };
        let unrelated = txn_with(
            "2024-01-10",
            &[("Expenses:Food", "1", None), ("Assets:Cash", "-1", None)],
        );
        let links = |directives: Vec<DirectiveWrapper>| -> Vec<String> {
            let out = materialize_ops(
                &directives,
                &EffectiveDatePlugin.process(input(directives.clone(), None)),
            );
            out.iter()
                .filter_map(|d| match &d.data {
                    DirectiveData::Transaction(t)
                        if !t.metadata.iter().any(|(k, _)| k == "original_date") =>
                    {
                        t.links.iter().find(|l| l.starts_with("edate-")).cloned()
                    }
                    _ => None,
                })
                .collect()
        };
        let base = links(vec![moved("2024-01-15"), moved("2024-02-15")]);
        assert_eq!(base, ["edate-240115-000", "edate-240215-000"]);
        assert_eq!(
            links(vec![unrelated, moved("2024-01-15"), moved("2024-02-15")]),
            base
        );
        assert_eq!(
            links(vec![
                moved("2024-01-12"),
                moved("2024-01-15"),
                moved("2024-02-15")
            ])[1..],
            base[..]
        );
        assert_eq!(
            links(vec![
                moved("2024-01-15"),
                moved("2024-01-15"),
                moved("2024-02-15")
            ]),
            ["edate-240115-000", "edate-240115-001", "edate-240215-000"]
        );
    }

    /// An entry left as written leaves nothing behind: no holding-account
    /// `open` for the postings it would have moved, while another entry in
    /// the same run is moved as usual. The prefix `Expenses:` does not match
    /// the root `Expenses` itself, as upstream's `startswith` does not.
    #[test]
    fn a_kept_entry_leaves_no_opens_behind() {
        let config = "{'Expenses:': {'earlier': 'Liabilities:Hold:E:', 'later': 'Assets:Hold:E:'}}";
        let directives = vec![
            txn_with(
                "2024-01-15",
                &[
                    ("Expenses:Rent", "10", Some("2024-02-01")),
                    ("Expenses", "10", Some("2024-02-01")),
                    ("Assets:Cash", "-20", None),
                ],
            ),
            txn_with(
                "2024-01-16",
                &[
                    ("Expenses:Food", "10", Some("2024-02-01")),
                    ("Assets:Cash", "-10", None),
                ],
            ),
        ];
        let output = EffectiveDatePlugin.process(input(directives.clone(), Some(config)));
        assert_eq!(output.errors.len(), 1, "{:?}", output.errors);
        assert!(
            output.errors[0].message.contains("cannot move Expenses ("),
            "{}",
            output.errors[0].message
        );
        assert_eq!(opened(&directives, &output), ["Assets:Hold:E:Food"]);
    }

    /// Only the leading prefix is replaced. Upstream's `str.replace` replaced
    /// every occurrence: `Income:Interest:Income` became
    /// `Assets:Hold:Income:Interest:Assets:Hold:Income`.
    #[test]
    fn only_the_leading_prefix_is_renamed() {
        let directives = vec![txn_with(
            "2024-01-15",
            &[
                ("Income:Interest:Income", "-10", Some("2024-01-01")),
                ("Assets:Cash", "10", None),
            ],
        )];
        let output = EffectiveDatePlugin.process(input(directives.clone(), None));
        assert!(output.errors.is_empty(), "{:?}", output.errors);
        assert_eq!(
            opened(&directives, &output),
            ["Assets:Hold:Income:Interest:Income"]
        );
    }

    /// An `effective_date` that is not a date (here a quoted string) cannot be
    /// applied: reported, and the whole entry stays as written. Upstream
    /// skips it silently.
    #[test]
    fn a_non_date_effective_date_is_reported_and_the_entry_kept() {
        let mut directives = vec![txn_with(
            "2024-01-15",
            &[
                ("Expenses:Rent", "10", Some("2024-02-01")),
                ("Expenses:Food", "10", None),
                ("Assets:Cash", "-20", None),
            ],
        )];
        if let DirectiveData::Transaction(txn) = &mut directives[0].data {
            txn.postings[1].metadata.push((
                "effective_date".to_string(),
                MetaValueData::String("2024-03-01".to_string()),
            ));
        }
        let output = EffectiveDatePlugin.process(input(directives.clone(), None));
        assert_eq!(output.errors.len(), 1, "{:?}", output.errors);
        assert!(output.errors[0].message.contains("Expenses:Food"));
        assert!(output.errors[0].message.contains("not a date"));
        assert_eq!(materialize_ops(&directives, &output), directives);
    }

    /// A marked posting with no amount cannot be reversed: reported, entry
    /// kept. Upstream crashes on `-None`.
    #[test]
    fn a_posting_without_an_amount_is_reported_and_the_entry_kept() {
        let mut directives = vec![txn_with(
            "2024-01-15",
            &[
                ("Expenses:Rent", "10", Some("2024-02-01")),
                ("Assets:Cash", "-10", None),
            ],
        )];
        if let DirectiveData::Transaction(txn) = &mut directives[0].data {
            txn.postings[0].units = None;
        }
        let output = EffectiveDatePlugin.process(input(directives.clone(), None));
        assert_eq!(output.errors.len(), 1, "{:?}", output.errors);
        assert!(output.errors[0].message.contains("no amount"));
        assert_eq!(materialize_ops(&directives, &output), directives);
    }

    /// The links number the moved entries within the run: running the plugin
    /// twice in one process gives identical output (the process-wide counter
    /// made the second run's links differ), and 5,000 moved entries get 5,000
    /// distinct links (the counter wrapped at 4,096).
    #[test]
    fn links_are_deterministic_and_unique() {
        let directives: Vec<DirectiveWrapper> = (0..5000)
            .map(|_| {
                txn_with(
                    "2024-01-15",
                    &[
                        ("Expenses:Rent", "10", Some("2024-02-01")),
                        ("Assets:Cash", "-10", None),
                    ],
                )
            })
            .collect();
        let first = materialize_ops(
            &directives,
            &EffectiveDatePlugin.process(input(directives.clone(), None)),
        );
        let second = materialize_ops(
            &directives,
            &EffectiveDatePlugin.process(input(directives.clone(), None)),
        );
        assert_eq!(first, second, "the same ledger, the same output");
        let links: BTreeSet<String> = first
            .iter()
            .filter(|d| d.date == "2024-01-15")
            .filter_map(|d| match &d.data {
                DirectiveData::Transaction(t) => t.links.first().cloned(),
                _ => None,
            })
            .collect();
        assert_eq!(links.len(), 5000);
    }

    /// The new entry keeps the transaction's payee, tags, links and metadata,
    /// adding `original_date` and the edate link, as upstream does (checked
    /// against beancount 3.2.3). The moved posting keeps its metadata,
    /// `effective_date` included, as upstream; the new entry's postings drop
    /// `effective_date`.
    #[test]
    fn the_new_entry_keeps_the_transactions_metadata_and_links() {
        let mut directives = vec![txn_with(
            "2024-01-15",
            &[
                ("Expenses:Rent", "10", Some("2024-02-01")),
                ("Assets:Cash", "-10", None),
            ],
        )];
        if let DirectiveData::Transaction(txn) = &mut directives[0].data {
            txn.payee = Some("Landlord".to_string());
            txn.tags = vec!["housing".to_string()];
            txn.links = vec!["lease".to_string()];
            txn.metadata = vec![(
                "txnkey".to_string(),
                MetaValueData::String("tv".to_string()),
            )];
            txn.postings[0]
                .metadata
                .push(("pkey".to_string(), MetaValueData::String("pv".to_string())));
        }
        let out = materialize_ops(
            &directives,
            &EffectiveDatePlugin.process(input(directives.clone(), None)),
        );
        let txns: Vec<&TransactionData> = out
            .iter()
            .filter_map(|d| match &d.data {
                DirectiveData::Transaction(t) => Some(t),
                _ => None,
            })
            .collect();
        let original = txns
            .iter()
            .find(|t| !t.metadata.iter().any(|(k, _)| k == "original_date"))
            .expect("original");
        let new = txns
            .iter()
            .find(|t| t.metadata.iter().any(|(k, _)| k == "original_date"))
            .expect("new entry");
        assert_eq!(new.payee.as_deref(), Some("Landlord"));
        assert_eq!(new.tags, ["housing"]);
        assert_eq!(new.links, original.links);
        assert!(
            new.links.contains(&"lease".to_string())
                && new.links.iter().any(|l| l.starts_with("edate-"))
        );
        assert!(new.metadata.iter().any(|(k, _)| k == "txnkey"));
        let moved = &original.postings[0];
        assert_eq!(moved.account, "Assets:Hold:Expenses:Rent");
        assert!(moved.metadata.iter().any(|(k, _)| k == "effective_date"));
        assert!(
            new.postings
                .iter()
                .all(|p| p.metadata.iter().all(|(k, _)| k != "effective_date"))
        );
        assert!(
            new.postings
                .iter()
                .all(|p| p.metadata.iter().any(|(k, _)| k == "pkey"))
        );
    }

    fn opened(directives: &[DirectiveWrapper], output: &PluginOutput) -> Vec<String> {
        materialize_ops(directives, output)
            .into_iter()
            .filter_map(|d| match d.data {
                DirectiveData::Open(open) => Some(open.account),
                _ => None,
            })
            .collect()
    }

    /// A config that does not parse is an error, and nothing changes, as
    /// upstream (`literal_eval` raises). It used to fall back to the default
    /// config without a word.
    #[test]
    fn an_unreadable_config_is_an_error_and_changes_nothing() {
        let directives = vec![create_test_transaction_with_effective_date(
            "2024-01-15",
            "2024-02-01",
        )];
        for config in [
            "{'Expenses': {'earlier': 'Liabilities:Hold:X'",
            "{'Expenses': {'earlier': 'Liabilities:Hold:X'}}",
            "not a dict",
        ] {
            let output = EffectiveDatePlugin.process(input(directives.clone(), Some(config)));
            assert_eq!(output.errors.len(), 1, "{config}: {:?}", output.errors);
            assert!(output.errors[0].message.contains("cannot read the config"));
            assert_eq!(
                materialize_ops(&directives, &output),
                directives,
                "{config}"
            );
        }
    }

    /// The same dict in the other spellings Python accepts: double quotes, and
    /// `later` before `earlier`. An empty dict is the default config.
    #[test]
    fn the_config_reads_either_quote_style_and_field_order() {
        let directives = vec![create_test_transaction_with_effective_date(
            "2024-01-15",
            "2024-02-01",
        )];
        for config in [
            "{'Expenses': {'earlier': 'Liabilities:Hold:E', 'later': 'Assets:Hold:E'}}",
            r#"{"Expenses": {"later": "Assets:Hold:E", "earlier": "Liabilities:Hold:E"}}"#,
        ] {
            let output = EffectiveDatePlugin.process(input(directives.clone(), Some(config)));
            assert!(output.errors.is_empty(), "{config}: {:?}", output.errors);
            assert_eq!(
                opened(&directives, &output),
                ["Assets:Hold:E:Food"],
                "{config}"
            );
        }
        let output = EffectiveDatePlugin.process(input(directives.clone(), Some("{}")));
        assert!(output.errors.is_empty());
        assert_eq!(opened(&directives, &output), ["Assets:Hold:Expenses:Food"]);
    }

    /// An effective date equal to the entry's date: upstream's error, and the
    /// entry stays as written. It used to go through a holding account and
    /// back on the same day.
    #[test]
    fn an_effective_date_equal_to_the_entry_date_is_an_error() {
        let directives = vec![create_test_transaction_with_effective_date(
            "2024-01-15",
            "2024-01-15",
        )];
        let output = EffectiveDatePlugin.process(input(directives.clone(), None));
        assert_eq!(output.errors.len(), 1, "{:?}", output.errors);
        assert!(
            output.errors[0]
                .message
                .contains("Effective and actual dates are identical")
                && output.errors[0].message.contains("Expenses:Food"),
            "{:?}",
            output.errors[0].message
        );
        assert_eq!(materialize_ops(&directives, &output), directives);
    }

    enum Expect {
        Ok(Vec<(&'static str, &'static str, &'static str)>),
        Default,
        Err,
    }

    /// `parse_config` accepts and rejects what upstream's `if config:
    /// literal_eval(config)` does. Every expectation below is Python's own
    /// (3.13 `ast.literal_eval`), classified as: a usable dict, a falsy value
    /// meaning the default config, or an error. "Unusable" values (a dict
    /// missing `later`, a non-string account, a list) parse in Python and
    /// fail when a posting reaches them; they are errors here up front.
    #[test]
    fn the_config_reads_as_literal_eval_reads_it() {
        let cases: Vec<(&str, Expect)> = vec![
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r#"{"Expenses": {"earlier": "L:H", "later": "A:H"}}"#,
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"{'Expenses': {'later': 'A:H', 'earlier': 'L:H'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H',},}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"  {  'Expenses'  :  {'earlier':'L:H','later':'A:H'}  }  ",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"{'Expenses':
 {'earlier': 'L:H',
  'later': 'A:H'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"{'Ex\x70enses': {'earlier': 'L:H', 'later': 'A:H'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"{'Expenses': {'earlier': 'L:\u0048', 'later': 'A:H'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"{'Exp' 'enses': {'earlier': 'L:H', 'later': 'A:H'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"{r'Expenses': {'earlier': 'L:H', 'later': 'A:H'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"{u'Expenses': {'earlier': 'L:H', 'later': 'A:H'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H', 'note': 'x'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H', 'nested': {'a': 1}}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (r"{'Expenses': {'earlier': 'L:H'}}", Expect::Err), // unusable
            (r"{'Expenses': {'earlier': 1, 'later': 'A:H'}}", Expect::Err), // unusable
            (r"{'Expenses': 'L:H'}", Expect::Err),              // unusable
            (r"{}", Expect::Default),
            (r"", Expect::Default),
            (r"  ", Expect::Err), // error
            (r"None", Expect::Default),
            (r"[]", Expect::Default),
            (r"''", Expect::Default),
            (r"0", Expect::Default),
            (r"False", Expect::Default),
            (r"()", Expect::Default),
            (r"['Expenses']", Expect::Err), // unusable
            (r"'Expenses'", Expect::Err),   // unusable
            (r"1", Expect::Err),            // unusable
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H'}",
                Expect::Err,
            ), // error
            (
                r"{'Expenses' {'earlier': 'L:H', 'later': 'A:H'}}",
                Expect::Err,
            ), // error
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H'},, }",
                Expect::Err,
            ), // error
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H'}} junk",
                Expect::Err,
            ), // error
            (
                r"{Expenses: {'earlier': 'L:H', 'later': 'A:H'}}",
                Expect::Err,
            ), // error
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H'}, 'Expenses': {'earlier': 'L:X', 'later': 'A:X'}}",
                Expect::Ok(vec![("Expenses", "L:X", "A:X")]),
            ),
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H'}, # c
}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (r"dict(Expenses=1)", Expect::Err), // error
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H'}}
",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r#"{"Exp'enses": {'earlier': 'L:H', 'later': 'A:H'}}"#,
                Expect::Ok(vec![("Exp'enses", "L:H", "A:H")]),
            ),
            (
                r"{'Expenses': {'earlier': f'L:H', 'later': 'A:H'}}",
                Expect::Err,
            ), // error
            (
                r"{'Expenses': {'earlier': b'L:H', 'later': 'A:H'}}",
                Expect::Err,
            ), // unusable
            (r"{'Expenses', 'Income'}", Expect::Err), // unusable
            (
                r"( {'Expenses': {'earlier': 'L:H', 'later': 'A:H'}} )",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H'}}  # trailing comment",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"
{'Expenses': {'earlier': 'L:H', 'later': 'A:H'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (r"-0", Expect::Default),
            (r"0.0", Expect::Default),
            (r"0x0", Expect::Default),
            (r"1_000", Expect::Err), // unusable
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H'}}

",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (r"'''x'''", Expect::Err), // unusable
            (
                r"{'''Expenses''': {'earlier': 'L:H', 'later': 'A:H'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H'}} \
",
                Expect::Err,
            ), // error
            (
                r"{'Expenses': {'earlier': 'L:H' 'X', 'later': 'A:H'}}",
                Expect::Ok(vec![("Expenses", "L:HX", "A:H")]),
            ),
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H'}}
# c",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (r"{1: {'earlier': 'L:H', 'later': 'A:H'}}", Expect::Err), // unusable
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H', 'later': 'A:Z'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:Z")]),
            ),
            (
                r"{'Expenses':	{'earlier': 'L:H', 'later': 'A:H'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
            (
                r#"{"""Exp
enses""": {'earlier': 'L:H', 'later': 'A:H'}}"#,
                Expect::Ok(vec![("Exp\nenses", "L:H", "A:H")]),
            ),
            (
                r"{'Expenses': {'earlier': 'L:H', 'later': 'A:H'}}
{'x': 1}",
                Expect::Err,
            ), // error
            (r"07", Expect::Err),        // error
            (r"{'a': 1,}", Expect::Err), // unusable
            (
                "{'Expenses': {'earlier': 1}, 'Expenses': {'earlier': 'L:H', 'later': 'A:H'}}",
                Expect::Ok(vec![("Expenses", "L:H", "A:H")]),
            ),
        ];
        for (config, expect) in cases {
            let got = parse_config(config);
            match expect {
                Expect::Ok(want) => {
                    let want: HoldingAccounts = want
                        .into_iter()
                        .map(|(p, e, l)| (p.to_string(), (e.to_string(), l.to_string())))
                        .collect();
                    assert_eq!(got, Ok(want), "{config:?}");
                }
                Expect::Default => assert_eq!(got, Ok(default_holding_accounts()), "{config:?}"),
                Expect::Err => assert!(got.is_err(), "{config:?} should be rejected: {got:?}"),
            }
        }
    }

    /// `parse_config` against Python on 500 generated configs (every quote
    /// style and prefix, escapes, implicit concatenation, comments, line
    /// continuations, trailing commas, repeated and extra keys, non-string
    /// values, and random mutations), each classified by running
    /// `ast.literal_eval`. See `tests/fixtures/effective_date/generate_configs.py`
    /// to regenerate or draw more; 20,000 drawn cases agree.
    #[test]
    fn the_config_reads_as_literal_eval_reads_it_on_generated_configs() {
        let cases: Vec<(String, String)> = serde_json::from_str(include_str!(
            "../../../tests/fixtures/effective_date/configs.json"
        ))
        .expect("the fixture parses");
        assert!(cases.len() >= 500, "{} cases", cases.len());
        let mut wrong = Vec::new();
        for (config, want) in &cases {
            let got = match parse_config(config) {
                Err(_) => "error".to_string(),
                Ok(h) if want == "default" && h == default_holding_accounts() => {
                    "default".to_string()
                }
                Ok(h) => {
                    let rows: Vec<[&str; 3]> = h
                        .iter()
                        .map(|(p, (e, l))| [p.as_str(), e.as_str(), l.as_str()])
                        .collect();
                    format!("ok:{}", serde_json::to_string(&rows).expect("json"))
                }
            };
            if got.replace(", ", ",") != want.replace(", ", ",") {
                wrong.push(format!("{config:?}\n  want {want}\n  got  {got}"));
            }
        }
        assert!(
            wrong.is_empty(),
            "{} of {}:\n{}",
            wrong.len(),
            cases.len(),
            wrong.join("\n")
        );
    }
}
