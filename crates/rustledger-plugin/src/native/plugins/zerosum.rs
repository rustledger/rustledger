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

use regex::Regex;
use rust_decimal::Decimal;
use std::collections::{HashMap, HashSet};
use std::str::FromStr;
use std::sync::LazyLock;

/// Regex for parsing zerosum account entries.
/// Format: `'AccountName': ('TargetAccount', days)` where `TargetAccount` may be empty (`''`).
static ACCOUNT_ENTRY_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"'([^']+)'\s*:\s*\(\s*'([^']*)'\s*,\s*(\d+)\s*\)")
        .expect("ACCOUNT_ENTRY_RE: invalid regex pattern")
});

/// Regex for parsing `account_name_replace`.
/// Format: `'account_name_replace': ('from', 'to')`
static ACCOUNT_REPLACE_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"'account_name_replace'\s*:\s*\(\s*'([^']*)'\s*,\s*'([^']*)'\s*\)")
        .expect("ACCOUNT_REPLACE_RE: invalid regex pattern")
});

/// Regex for parsing tolerance.
/// Format: `'tolerance': 0.01`
static TOLERANCE_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"'tolerance'\s*:\s*([0-9.]+)").expect("TOLERANCE_RE: invalid regex pattern")
});

use crate::types::{
    DirectiveData, DirectiveWrapper, OpenData, PluginError, PluginErrorSeverity, PluginInput,
    PluginOp, PluginOutput,
};

use super::super::NativePlugin;

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
                    for zs_account in zerosum_accounts.keys() {
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

        // For each zerosum account, find matching pairs
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

            // Now update the matched postings to use the target account
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

/// Parse the Python-style config dict.
fn parse_config(
    config: &str,
) -> Result<
    (
        HashMap<String, (Option<String>, i64)>,
        Option<(String, String)>,
        Decimal,
    ),
    String,
> {
    let mut zerosum_accounts = HashMap::new();
    let mut account_replace: Option<(String, String)> = None;
    let mut tolerance = Decimal::from_str(DEFAULT_TOLERANCE).unwrap();

    // Simple parsing of Python dict format
    // 'zerosum_accounts': {'Account': ('Target', 30), ...}
    // 'account_name_replace': ('From', 'To')

    // Extract zerosum_accounts
    if let Some(start) = config.find("'zerosum_accounts'")
        && let Some(dict_offset) = config[start..].find('{')
    {
        let dict_start = start + dict_offset;
        let mut depth = 0;
        let mut dict_end = dict_start;
        for (i, c) in config[dict_start..].char_indices() {
            match c {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        dict_end = dict_start + i + 1;
                        break;
                    }
                }
                _ => {}
            }
        }

        let dict_str = &config[dict_start..dict_end];
        // Parse individual account entries
        // Format: 'AccountName': ('TargetAccount', days)
        // or: 'AccountName': ('', days)
        for cap in ACCOUNT_ENTRY_RE.captures_iter(dict_str) {
            let account = cap[1].to_string();
            let target = if cap[2].is_empty() {
                None
            } else {
                Some(cap[2].to_string())
            };
            let days: i64 = cap[3].parse().unwrap_or(30);
            zerosum_accounts.insert(account, (target, days));
        }
    }

    // Extract account_name_replace
    if let Some(start) = config.find("'account_name_replace'")
        && let Some(cap) = ACCOUNT_REPLACE_RE.captures(&config[start..])
    {
        account_replace = Some((cap[1].to_string(), cap[2].to_string()));
    }

    // Extract tolerance
    if let Some(start) = config.find("'tolerance'")
        && let Some(cap) = TOLERANCE_RE.captures(&config[start..])
        && let Ok(t) = Decimal::from_str(&cap[1])
    {
        tolerance = t;
    }

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

        assert_eq!(accounts.len(), 2);
        assert!(accounts.contains_key("Assets:ZeroSum:Transfers"));
        assert!(accounts.contains_key("Assets:ZeroSum:CreditCard"));

        let (target, days) = accounts.get("Assets:ZeroSum:Transfers").unwrap();
        assert_eq!(target.as_ref().unwrap(), "Assets:ZeroSum-Matched:Transfers");
        assert_eq!(*days, 30);

        let (target2, days2) = accounts.get("Assets:ZeroSum:CreditCard").unwrap();
        assert!(target2.is_none()); // Empty target means use account_name_replace
        assert_eq!(*days2, 6);

        assert!(replace.is_some());
        let (from, to) = replace.unwrap();
        assert_eq!(from, "ZeroSum");
        assert_eq!(to, "ZeroSum-Matched");

        assert_eq!(tolerance, Decimal::from_str("0.01").unwrap());
    }
}
