//! Zero-sum account matching plugin.
//!
//! Matches postings in "zerosum" accounts that net to zero within a date range,
//! and moves them to a "matched" account. Useful for tracking transfers between
//! accounts.
//!
//! Configuration (as a Python-style dict string):
//! ```text
//! plugin "beancount_reds_plugins.zerosum.zerosum" "{
//!   'zerosum_accounts': {
//!     'Assets:ZeroSum:Transfers': ('Assets:ZeroSum-Matched:Transfers', 30),
//!   },
//!   'account_name_replace': ('ZeroSum', 'ZeroSum-Matched')
//! }"
//! ```

use rust_decimal::Decimal;
use std::collections::{HashMap, HashSet};
use std::str::FromStr;

use crate::types::{
    DirectiveData, DirectiveWrapper, OpenData, PluginError, PluginErrorSeverity, PluginInput,
    PluginOp, PluginOutput,
};

use super::super::{NativePlugin, RegularPlugin};

/// Default tolerance for matching amounts.
const DEFAULT_TOLERANCE: &str = "0.0099";

/// Plugin for matching zero-sum postings.
pub struct ZerosumPlugin;

impl NativePlugin for ZerosumPlugin {
    fn name(&self) -> &'static str {
        "zerosum"
    }

    fn description(&self) -> &'static str {
        "Match postings in zero-sum accounts and move to matched account"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        // Parse configuration
        let config = match &input.config {
            Some(c) => c,
            None => {
                return PluginOutput {
                    ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                    errors: vec![PluginError {
                        message: "zerosum plugin requires configuration".to_string(),
                        source_file: None,
                        line_number: None,
                        severity: PluginErrorSeverity::Error,
                        // A config it cannot use: nothing is matched.
                        failed: true,
                    }],
                };
            }
        };

        // Parse the Python-style dict config
        let (zerosum_accounts, account_replace, tolerance) = match parse_config(config) {
            Ok(c) => c,
            Err(e) => {
                return PluginOutput {
                    ops: (0..input.directives.len()).map(PluginOp::Keep).collect(),
                    errors: vec![PluginError {
                        message: format!("Failed to parse zerosum config: {e}"),
                        source_file: None,
                        line_number: None,
                        severity: PluginErrorSeverity::Error,
                        // A config it cannot use: nothing is matched.
                        failed: true,
                    }],
                };
            }
        };

        let mut new_accounts: HashSet<String> = HashSet::new();
        let mut earliest_date: Option<String> = None;

        // Collect existing Open accounts to avoid creating duplicates
        let existing_opens: HashSet<String> = input
            .directives
            .iter()
            .filter_map(|d| {
                if let DirectiveData::Open(ref open) = d.data {
                    Some(open.account.clone())
                } else {
                    None
                }
            })
            .collect();

        // Index transactions by zerosum account
        let mut txn_indices: HashMap<String, Vec<usize>> = HashMap::new();

        for (i, directive) in input.directives.iter().enumerate() {
            if directive.directive_type == "transaction" {
                if earliest_date.is_none() || directive.date < *earliest_date.as_ref().unwrap() {
                    earliest_date = Some(directive.date.clone());
                }

                if let DirectiveData::Transaction(ref txn) = directive.data {
                    for (zs_account, _) in &zerosum_accounts {
                        if txn.postings.iter().any(|p| &p.account == zs_account) {
                            txn_indices.entry(zs_account.clone()).or_default().push(i);
                        }
                    }
                }
            }
        }

        // Convert to mutable.
        let mut directives = input.directives;
        // Track which input indices were mutated, so we can emit Modify
        // ops for them and Keep ops for everything else.
        let mut modified_indices: HashSet<usize> = HashSet::new();

        // For each zerosum account, find matching pairs, in the order the
        // config lists them, as beancount_reds_plugins walks its
        // `zerosum_accounts` dict. The order matters when one account's
        // target is another zerosum account: the earlier one's matches are
        // renamed before the later one is matched. Over a `HashMap` that
        // order, and so the result, changed from run to run (#2625).
        for (zs_account, (target_account_opt, date_range)) in &zerosum_accounts {
            // Determine target account
            let target_account = target_account_opt.clone().unwrap_or_else(|| {
                if let Some((from, to)) = &account_replace {
                    zs_account.replace(from, to)
                } else {
                    format!("{zs_account}-Matched")
                }
            });

            let indices = match txn_indices.get(zs_account) {
                Some(i) => i.clone(),
                None => continue,
            };

            // Track which postings have been matched (by txn_idx, posting_idx)
            let mut matched: HashSet<(usize, usize)> = HashSet::new();

            // For each transaction in this zerosum account
            for &txn_i in &indices {
                let directive = &directives[txn_i];
                let txn_date = &directive.date;

                if let DirectiveData::Transaction(ref txn) = directive.data {
                    // Find postings in this transaction that are in the zerosum account
                    for (post_i, posting) in txn.postings.iter().enumerate() {
                        if &posting.account != zs_account {
                            continue;
                        }
                        if matched.contains(&(txn_i, post_i)) {
                            continue;
                        }

                        // Get the amount
                        let amount = match &posting.units {
                            Some(u) => match Decimal::from_str(&u.number) {
                                Ok(n) => n,
                                Err(_) => continue,
                            },
                            None => continue,
                        };
                        let currency = posting.units.as_ref().map(|u| &u.currency);

                        // Look for a matching posting in other transactions
                        for &other_txn_i in &indices {
                            if other_txn_i == txn_i {
                                // Check within same transaction but different posting
                                if let DirectiveData::Transaction(ref other_txn) =
                                    directives[other_txn_i].data
                                {
                                    for (other_post_i, other_posting) in
                                        other_txn.postings.iter().enumerate()
                                    {
                                        if other_post_i == post_i {
                                            continue;
                                        }
                                        if &other_posting.account != zs_account {
                                            continue;
                                        }
                                        if matched.contains(&(other_txn_i, other_post_i)) {
                                            continue;
                                        }

                                        let other_currency =
                                            other_posting.units.as_ref().map(|u| &u.currency);
                                        if currency != other_currency {
                                            continue;
                                        }

                                        let other_amount = match &other_posting.units {
                                            Some(u) => match Decimal::from_str(&u.number) {
                                                Ok(n) => n,
                                                Err(_) => continue,
                                            },
                                            None => continue,
                                        };

                                        // Check if they sum to zero (within tolerance)
                                        let sum = (amount + other_amount).abs();
                                        if sum < tolerance {
                                            // Found a match!
                                            matched.insert((txn_i, post_i));
                                            matched.insert((other_txn_i, other_post_i));
                                            new_accounts.insert(target_account.clone());
                                            break;
                                        }
                                    }
                                }
                                continue;
                            }

                            // Check date range
                            let other_date = &directives[other_txn_i].date;
                            if !within_date_range(txn_date, other_date, *date_range) {
                                continue;
                            }

                            if let DirectiveData::Transaction(ref other_txn) =
                                directives[other_txn_i].data
                            {
                                for (other_post_i, other_posting) in
                                    other_txn.postings.iter().enumerate()
                                {
                                    if &other_posting.account != zs_account {
                                        continue;
                                    }
                                    if matched.contains(&(other_txn_i, other_post_i)) {
                                        continue;
                                    }

                                    let other_currency =
                                        other_posting.units.as_ref().map(|u| &u.currency);
                                    if currency != other_currency {
                                        continue;
                                    }

                                    let other_amount = match &other_posting.units {
                                        Some(u) => match Decimal::from_str(&u.number) {
                                            Ok(n) => n,
                                            Err(_) => continue,
                                        },
                                        None => continue,
                                    };

                                    // Check if they sum to zero (within tolerance)
                                    let sum = (amount + other_amount).abs();
                                    if sum < tolerance {
                                        // Found a match!
                                        matched.insert((txn_i, post_i));
                                        matched.insert((other_txn_i, other_post_i));
                                        new_accounts.insert(target_account.clone());
                                        break;
                                    }
                                }
                            }

                            // If we found a match, break out
                            if matched.contains(&(txn_i, post_i)) {
                                break;
                            }
                        }
                    }
                }
            }

            // Update the matched postings to use the target account, IN PLACE.
            //
            // Deliberate divergence from `beancount_reds_plugins`, whose
            // `account_replace` does:
            //
            //     new_posting = posting._replace(account=new_account)
            //     txn.postings.remove(posting)
            //     txn.postings.append(new_posting)
            //
            // — moving every rewritten posting to the END of the transaction.
            // That reordering is incidental to mutating a Python list while
            // iterating it (the caller has to `break` and reprocess because,
            // in its own words, "this entry's postings changes under us"), not
            // a property anyone chose. It silently destroys the order the user
            // wrote, which is the only thing posting order carries.
            //
            // Rewriting the account in place keeps that order. The values,
            // accounts and signs are identical either way, so nothing
            // downstream depends on the difference — only rendered posting
            // order differs, which is why the four affected pairs on
            // `tests/regressions/issue-278.beancount` are registered in
            // `KNOWN_RUST_DIVERGENCES` (see `scripts/compat-bql-test.py`)
            // rather than chased.
            //
            // Revisit if upstream ever makes the ordering intentional, or if a
            // consumer starts deriving meaning from posting position.
            for (txn_i, post_i) in &matched {
                if let DirectiveData::Transaction(ref mut txn) = directives[*txn_i].data
                    && *post_i < txn.postings.len()
                {
                    txn.postings[*post_i].account.clone_from(&target_account);
                    modified_indices.insert(*txn_i);
                }
            }
        }

        // Emit ops: Modify for mutated indices, Keep otherwise.
        let mut ops: Vec<PluginOp> = Vec::with_capacity(directives.len() + new_accounts.len());
        for (i, d) in directives.into_iter().enumerate() {
            if modified_indices.contains(&i) {
                ops.push(PluginOp::Modify(i, d));
            } else {
                ops.push(PluginOp::Keep(i));
            }
        }

        // Insert Open directives for newly synthesized matched accounts
        // (only if not already opened).
        if let Some(date) = earliest_date {
            let mut accounts: Vec<&String> = new_accounts.iter().collect();
            accounts.sort();
            for account in accounts {
                if existing_opens.contains(account) {
                    continue;
                }
                ops.push(PluginOp::Insert(DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: date.clone(),
                    filename: Some("<zerosum>".to_string()),
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

        PluginOutput {
            ops,
            errors: Vec::new(),
        }
    }
}

impl RegularPlugin for ZerosumPlugin {}

/// The configured zerosum accounts and their `(target, days)`, in config
/// order.
type ZerosumAccounts = Vec<(String, (Option<String>, i64))>;

/// Parse the Python-style config dict, as beancount's `literal_eval` reads
/// it: anything that is not that dict, or whose entries are not the shapes
/// below, is an error (the plugin then does nothing, and says so), where a
/// pattern match on the text used to skip it silently.
///
/// ```text
/// {'zerosum_accounts': {'Account': ('Target', 30), ...},
///  'account_name_replace': ('From', 'To'),
///  'tolerance': 0.01}
/// ```
///
/// Every key is optional, as beancount `pop`s each with a default; other
/// keys are ignored, as there.
fn parse_config(
    config: &str,
) -> Result<(ZerosumAccounts, Option<(String, String)>, Decimal), String> {
    use super::py_literal::{self, PyValue};

    let PyValue::Dict(entries) = py_literal::parse(config)? else {
        return Err("expected a dict".to_string());
    };
    // The last value of a repeated key wins, as in a Python dict.
    let get = |name: &str| {
        entries
            .iter()
            .rev()
            .find(|(k, _)| matches!(k, PyValue::Str(k) if k == name))
            .map(|(_, v)| v)
    };

    let mut zerosum_accounts: ZerosumAccounts = Vec::new();
    if let Some(value) = get("zerosum_accounts") {
        let PyValue::Dict(accounts) = value else {
            return Err("'zerosum_accounts' must be a dict".to_string());
        };
        for (key, entry) in accounts {
            let PyValue::Str(account) = key else {
                return Err(format!("a zerosum account must be a string, found {key:?}"));
            };
            let (target, days) = match entry {
                PyValue::Seq(items) => match items.as_slice() {
                    [PyValue::Str(target), PyValue::Number { text, .. }] => {
                        let days: i64 = text.parse().map_err(|_| {
                            format!("the days for '{account}' must be a whole number, found {text}")
                        })?;
                        (target, days)
                    }
                    _ => {
                        return Err(format!(
                            "the entry for '{account}' must be ('target account', days)"
                        ));
                    }
                },
                _ => {
                    return Err(format!(
                        "the entry for '{account}' must be ('target account', days)"
                    ));
                }
            };
            // An empty target means: use account_name_replace.
            let target = (!target.is_empty()).then(|| target.clone());
            // As in a Python dict: a repeated account keeps its first
            // position and takes its last value.
            if let Some(slot) = zerosum_accounts.iter_mut().find(|(a, _)| a == account) {
                slot.1 = (target, days);
            } else {
                zerosum_accounts.push((account.clone(), (target, days)));
            }
        }
    }

    let account_replace = match get("account_name_replace") {
        None => None,
        Some(PyValue::Seq(items)) => match items.as_slice() {
            [PyValue::Str(from), PyValue::Str(to)] => Some((from.clone(), to.clone())),
            _ => return Err("'account_name_replace' must be ('from', 'to')".to_string()),
        },
        Some(_) => return Err("'account_name_replace' must be ('from', 'to')".to_string()),
    };

    let tolerance = match get("tolerance") {
        None => Decimal::from_str(DEFAULT_TOLERANCE).expect("DEFAULT_TOLERANCE is a decimal"),
        Some(PyValue::Number { text, .. }) => Decimal::from_str(text)
            .or_else(|_| Decimal::from_scientific(text))
            .map_err(|_| format!("'tolerance' must be a number, found {text}"))?,
        Some(other) => return Err(format!("'tolerance' must be a number, found {other:?}")),
    };

    Ok((zerosum_accounts, account_replace, tolerance))
}

/// Check if two dates are within a given range (in days).
fn within_date_range(date1: &str, date2: &str, days: i64) -> bool {
    use rustledger_core::NaiveDate;

    let d1 = match date1.parse::<NaiveDate>() {
        Ok(d) => d,
        Err(_) => return false,
    };
    let d2 = match date2.parse::<NaiveDate>() {
        Ok(d) => d,
        Err(_) => return false,
    };

    let diff = i64::from(d2.since(d1).unwrap_or_default().get_days()).abs();
    diff <= days
}

#[cfg(test)]
mod tests {
    use super::super::utils::materialize_ops;
    use super::*;
    use crate::types::*;

    fn create_transfer_txn(
        date: &str,
        from_account: &str,
        to_account: &str,
        amount: &str,
        currency: &str,
    ) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "Transfer".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        account: from_account.to_string(),
                        units: Some(AmountData {
                            number: format!("-{amount}"),
                            currency: currency.to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                    PostingData {
                        account: to_account.to_string(),
                        units: Some(AmountData {
                            number: amount.to_string(),
                            currency: currency.to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                ],
            }),
        }
    }

    #[test]
    fn test_zerosum_matches_transfers() {
        let plugin = ZerosumPlugin;

        let config = r"{
            'zerosum_accounts': {
                'Assets:ZeroSum:Transfers': ('Assets:ZeroSum-Matched:Transfers', 30)
            }
        }";

        let input = PluginInput {
            directives: vec![
                create_transfer_txn(
                    "2024-01-01",
                    "Assets:Bank",
                    "Assets:ZeroSum:Transfers",
                    "100.00",
                    "USD",
                ),
                create_transfer_txn(
                    "2024-01-03",
                    "Assets:ZeroSum:Transfers",
                    "Assets:Investment",
                    "100.00",
                    "USD",
                ),
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: Some(config.to_string()),
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);

        // Check that matched postings were moved to target account
        let mut found_matched = false;
        for directive in &directives {
            if let DirectiveData::Transaction(ref txn) = directive.data {
                for posting in &txn.postings {
                    if posting.account == "Assets:ZeroSum-Matched:Transfers" {
                        found_matched = true;
                    }
                }
            }
        }
        assert!(found_matched, "Should have matched postings");
    }

    /// A matched posting is rewritten IN PLACE — its position in the
    /// transaction does not change.
    ///
    /// `beancount_reds_plugins` removes and re-appends the posting, so every
    /// rewritten posting ends up last. That is incidental to mutating a list
    /// while iterating it, not a chosen property, and it discards the order
    /// the user wrote. We keep the order; accounts and amounts are identical
    /// either way.
    ///
    /// The two transactions put the zerosum leg at DIFFERENT positions —
    /// first in one, last in the other — so the test distinguishes "kept in
    /// place" from "moved to the end", which a single transaction with the
    /// leg already last could not.
    ///
    /// Pinned because it is the observable behind four registered entries in
    /// `KNOWN_RUST_DIVERGENCES` for `tests/regressions/issue-278.beancount`.
    /// If this flips, those entries go stale and the compat run fails — the
    /// intended coupling.
    #[test]
    fn test_matched_posting_keeps_its_position() {
        let plugin = ZerosumPlugin;
        let config = r"{
            'zerosum_accounts': {
                'Assets:ZeroSum:Transfers': ('Assets:ZeroSum-Matched:Transfers', 30)
            }
        }";

        // `create_transfer_txn` writes `from` first with the NEGATED amount
        // and `to` second, so this puts the zerosum leg first in one txn
        // (at -100) and second in the other (at +100) — they cancel.
        let input = PluginInput {
            directives: vec![
                create_transfer_txn(
                    "2024-01-01",
                    "Assets:ZeroSum:Transfers",
                    "Assets:Bank",
                    "100.00",
                    "USD",
                ),
                create_transfer_txn(
                    "2024-01-03",
                    "Assets:Investment",
                    "Assets:ZeroSum:Transfers",
                    "100.00",
                    "USD",
                ),
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: Some(config.to_string()),
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);

        let accounts: Vec<Vec<String>> = directives
            .iter()
            .filter_map(|d| match &d.data {
                DirectiveData::Transaction(t) => {
                    Some(t.postings.iter().map(|p| p.account.clone()).collect())
                }
                _ => None,
            })
            .collect();
        assert_eq!(accounts.len(), 2, "both transactions survive");

        // Rewritten, but each still where it was written. Upstream's
        // remove/append would make BOTH of these last.
        assert_eq!(
            accounts[0],
            vec!["Assets:ZeroSum-Matched:Transfers", "Assets:Bank"],
            "leg written FIRST must stay first"
        );
        assert_eq!(
            accounts[1],
            vec!["Assets:Investment", "Assets:ZeroSum-Matched:Transfers"],
            "leg written SECOND must stay second"
        );
    }

    #[test]
    fn test_zerosum_no_match_outside_range() {
        let plugin = ZerosumPlugin;

        let config = r"{
            'zerosum_accounts': {
                'Assets:ZeroSum:Transfers': ('Assets:ZeroSum-Matched:Transfers', 5)
            }
        }";

        let input = PluginInput {
            directives: vec![
                create_transfer_txn(
                    "2024-01-01",
                    "Assets:Bank",
                    "Assets:ZeroSum:Transfers",
                    "100.00",
                    "USD",
                ),
                // 10 days later - outside the 5-day range
                create_transfer_txn(
                    "2024-01-11",
                    "Assets:ZeroSum:Transfers",
                    "Assets:Investment",
                    "100.00",
                    "USD",
                ),
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: Some(config.to_string()),
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);

        // Check that postings were NOT matched (still in original account)
        let mut found_unmatched = false;
        for directive in &directives {
            if let DirectiveData::Transaction(ref txn) = directive.data {
                for posting in &txn.postings {
                    if posting.account == "Assets:ZeroSum:Transfers" {
                        found_unmatched = true;
                    }
                }
            }
        }
        assert!(found_unmatched, "Should have unmatched postings");
    }

    #[test]
    fn test_zerosum_does_not_duplicate_open() {
        // Regression test: zerosum should not create duplicate Open directives
        // when the target account already has an Open directive.
        let plugin = ZerosumPlugin;

        let config = r"{
            'zerosum_accounts': {
                'Assets:Transfer': ('Assets:ZSA-Matched:Transfer', 7)
            }
        }";

        // Create an existing Open for the target account
        let existing_open = DirectiveWrapper {
            directive_type: "open".to_string(),
            date: "2020-01-01".to_string(),
            filename: Some("accounts.beancount".to_string()),
            lineno: Some(422),
            data: DirectiveData::Open(OpenData {
                account: "Assets:ZSA-Matched:Transfer".to_string(),
                currencies: vec![],
                booking: None,
                metadata: vec![],
            }),
        };

        let input = PluginInput {
            directives: vec![
                existing_open,
                create_transfer_txn(
                    "2024-01-01",
                    "Assets:Bank",
                    "Assets:Transfer",
                    "100.00",
                    "USD",
                ),
                create_transfer_txn(
                    "2024-01-02",
                    "Assets:Transfer",
                    "Assets:Investment",
                    "100.00",
                    "USD",
                ),
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
                ..Default::default()
            },
            config: Some(config.to_string()),
        };

        let input_dirs = input.directives.clone();
        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        let directives = materialize_ops(&input_dirs, &output);

        // Count Open directives for the target account
        let open_count = directives
            .iter()
            .filter(|d| {
                if let DirectiveData::Open(ref open) = d.data {
                    open.account == "Assets:ZSA-Matched:Transfer"
                } else {
                    false
                }
            })
            .count();

        // Should only have 1 Open (the existing one, not a duplicate from the plugin)
        assert_eq!(
            open_count, 1,
            "Should not create duplicate Open directives for existing accounts"
        );
    }

    /// A config `literal_eval` would refuse is an error, which the plugin
    /// reports as a failure, where the pattern match it replaced found no
    /// accounts and did nothing without a word.
    #[test]
    fn test_parse_config_refuses_what_beancount_cannot_read() {
        for (config, why) in [
            // Malformed: a missing colon.
            (
                "{'zerosum_accounts': {'Assets:Transit' ('Assets:Transit-Matched', 30)}}",
                "",
            ),
            // Not a dict.
            ("['Assets:Transit']", "expected a dict"),
            // Wrong value shapes.
            (
                "{'zerosum_accounts': {'Assets:Transit': 'Assets:Transit-Matched'}}",
                "must be ('target account', days)",
            ),
            (
                "{'zerosum_accounts': {'Assets:Transit': ('Assets:Matched', 'thirty')}}",
                "must be ('target account', days)",
            ),
            (
                "{'zerosum_accounts': ['Assets:Transit']}",
                "'zerosum_accounts' must be a dict",
            ),
            (
                "{'account_name_replace': 'ZeroSum'}",
                "'account_name_replace' must be ('from', 'to')",
            ),
            ("{'tolerance': 'small'}", "'tolerance' must be a number"),
        ] {
            let err = parse_config(config).expect_err(config);
            assert!(err.contains(why), "{config}: {err}");
        }
    }

    #[test]
    fn test_process_marks_an_unusable_config_failed() {
        let input = PluginInput {
            directives: vec![],
            options: crate::types::PluginOptions::default(),
            config: Some(
                "{'zerosum_accounts': {'Assets:Transit' ('Assets:Transit-Matched', 30)}}"
                    .to_string(),
            ),
        };
        let output = ZerosumPlugin.process(input);
        assert_eq!(output.errors.len(), 1, "{:?}", output.errors);
        assert!(output.errors[0].failed, "{:?}", output.errors);
    }

    /// Keys are optional and the last of a repeated key wins, as in Python.
    #[test]
    fn test_parse_config_defaults_and_repeated_keys() {
        let (accounts, replace, tolerance) = parse_config("{}").unwrap();
        assert!(accounts.is_empty() && replace.is_none());
        assert_eq!(tolerance, Decimal::from_str(DEFAULT_TOLERANCE).unwrap());
        let (_, _, tolerance) = parse_config("{'tolerance': 0.5, 'tolerance': 0.25}").unwrap();
        assert_eq!(tolerance, Decimal::from_str("0.25").unwrap());
    }

    #[test]
    fn test_parse_config() {
        let config = r"{
            'zerosum_accounts': {
                'Assets:ZeroSum:Transfers': ('Assets:ZeroSum-Matched:Transfers', 30),
                'Assets:ZeroSum:CreditCard': ('', 6)
            },
            'account_name_replace': ('ZeroSum', 'ZeroSum-Matched'),
            'tolerance': 0.01
        }";

        let (accounts, replace, tolerance) = parse_config(config).unwrap();

        // In config order.
        let names: Vec<&str> = accounts.iter().map(|(a, _)| a.as_str()).collect();
        assert_eq!(
            names,
            ["Assets:ZeroSum:Transfers", "Assets:ZeroSum:CreditCard"]
        );

        let (target, days) = &accounts[0].1;
        assert_eq!(target.as_ref().unwrap(), "Assets:ZeroSum-Matched:Transfers");
        assert_eq!(*days, 30);

        let (target2, days2) = &accounts[1].1;
        assert!(target2.is_none()); // Empty target means use account_name_replace
        assert_eq!(*days2, 6);

        assert!(replace.is_some());
        let (from, to) = replace.unwrap();
        assert_eq!(from, "ZeroSum");
        assert_eq!(to, "ZeroSum-Matched");

        assert_eq!(tolerance, Decimal::from_str("0.01").unwrap());
    }
}
