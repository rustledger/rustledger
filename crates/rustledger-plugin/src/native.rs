//! Native (non-WASM) plugin support.
//!
//! These plugins run as native Rust code for maximum performance.
//! They implement the same interface as WASM plugins.

use crate::types::{
    DirectiveData, DirectiveWrapper, DocumentData, OpenData, PluginError, PluginInput,
    PluginOutput, TransactionData,
};

/// Trait for native plugins.
pub trait NativePlugin: Send + Sync {
    /// Plugin name.
    fn name(&self) -> &'static str;

    /// Plugin description.
    fn description(&self) -> &'static str;

    /// Process directives and return modified directives + errors.
    fn process(&self, input: PluginInput) -> PluginOutput;
}

/// Registry of built-in native plugins.
pub struct NativePluginRegistry {
    plugins: Vec<Box<dyn NativePlugin>>,
}

impl NativePluginRegistry {
    /// Create a new registry with all built-in plugins.
    pub fn new() -> Self {
        Self {
            plugins: vec![
                Box::new(ImplicitPricesPlugin),
                Box::new(CheckCommodityPlugin),
                Box::new(AutoTagPlugin::new()),
                Box::new(AutoAccountsPlugin),
                Box::new(LeafOnlyPlugin),
                Box::new(NoDuplicatesPlugin),
                Box::new(OneCommodityPlugin),
                Box::new(UniquePricesPlugin),
                Box::new(CheckClosingPlugin),
                Box::new(CloseTreePlugin),
                Box::new(CoherentCostPlugin),
                Box::new(SellGainsPlugin),
                Box::new(PedanticPlugin),
                Box::new(UnrealizedPlugin::new()),
                Box::new(NoUnusedPlugin),
                Box::new(CheckDrainedPlugin),
                Box::new(CommodityAttrPlugin::new()),
                Box::new(CheckAverageCostPlugin::new()),
                Box::new(CurrencyAccountsPlugin::new()),
            ],
        }
    }

    /// Find a plugin by name.
    pub fn find(&self, name: &str) -> Option<&dyn NativePlugin> {
        // Check for beancount.plugins.* prefix
        let name = name.strip_prefix("beancount.plugins.").unwrap_or(name);

        self.plugins
            .iter()
            .find(|p| p.name() == name)
            .map(std::convert::AsRef::as_ref)
    }

    /// List all available plugins.
    pub fn list(&self) -> Vec<&dyn NativePlugin> {
        self.plugins.iter().map(AsRef::as_ref).collect()
    }

    /// Check if a name refers to a built-in plugin.
    pub fn is_builtin(name: &str) -> bool {
        let name = name.strip_prefix("beancount.plugins.").unwrap_or(name);

        matches!(
            name,
            "implicit_prices"
                | "check_commodity"
                | "auto_tag"
                | "auto_accounts"
                | "leafonly"
                | "noduplicates"
                | "onecommodity"
                | "unique_prices"
                | "check_closing"
                | "close_tree"
                | "coherent_cost"
                | "sellgains"
                | "pedantic"
                | "unrealized"
                | "nounused"
                | "check_drained"
                | "commodity_attr"
                | "check_average_cost"
                | "currency_accounts"
        )
    }
}

impl Default for NativePluginRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Plugin that generates price entries from transaction costs and prices.
///
/// When a transaction has a posting with a cost or price annotation,
/// this plugin generates a corresponding Price directive.
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

            // Only process transactions
            if wrapper.directive_type != "transaction" {
                continue;
            }

            // Extract prices from transaction data
            if let crate::types::DirectiveData::Transaction(ref txn) = wrapper.data {
                for posting in &txn.postings {
                    // Check for price annotation
                    if let Some(ref units) = posting.units {
                        if let Some(ref price) = posting.price {
                            // Generate a price directive only if we have a complete amount
                            if let Some(ref price_amount) = price.amount {
                                let price_wrapper = DirectiveWrapper {
                                    directive_type: "price".to_string(),
                                    date: wrapper.date.clone(),
                                    data: crate::types::DirectiveData::Price(
                                        crate::types::PriceData {
                                            currency: units.currency.clone(),
                                            amount: price_amount.clone(),
                                        },
                                    ),
                                };
                                generated_prices.push(price_wrapper);
                            }
                        }

                        // Check for cost with price info
                        if let Some(ref cost) = posting.cost {
                            if let (Some(ref number), Some(ref currency)) =
                                (&cost.number_per, &cost.currency)
                            {
                                let price_wrapper = DirectiveWrapper {
                                    directive_type: "price".to_string(),
                                    date: wrapper.date.clone(),
                                    data: crate::types::DirectiveData::Price(
                                        crate::types::PriceData {
                                            currency: units.currency.clone(),
                                            amount: crate::types::AmountData {
                                                number: number.clone(),
                                                currency: currency.clone(),
                                            },
                                        },
                                    ),
                                };
                                generated_prices.push(price_wrapper);
                            }
                        }
                    }
                }
            }
        }

        // Add generated prices
        new_directives.extend(generated_prices);

        PluginOutput {
            directives: new_directives,
            errors: Vec::new(),
        }
    }
}

/// Plugin that checks all used commodities are declared.
pub struct CheckCommodityPlugin;

impl NativePlugin for CheckCommodityPlugin {
    fn name(&self) -> &'static str {
        "check_commodity"
    }

    fn description(&self) -> &'static str {
        "Verify all commodities are declared"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::HashSet;

        let mut declared_commodities: HashSet<String> = HashSet::new();
        let mut used_commodities: HashSet<String> = HashSet::new();
        let mut errors = Vec::new();

        // First pass: collect declared commodities
        for wrapper in &input.directives {
            if wrapper.directive_type == "commodity" {
                if let crate::types::DirectiveData::Commodity(ref comm) = wrapper.data {
                    declared_commodities.insert(comm.currency.clone());
                }
            }
        }

        // Second pass: collect used commodities and check
        for wrapper in &input.directives {
            match &wrapper.data {
                crate::types::DirectiveData::Transaction(txn) => {
                    for posting in &txn.postings {
                        if let Some(ref units) = posting.units {
                            used_commodities.insert(units.currency.clone());
                        }
                        if let Some(ref cost) = posting.cost {
                            if let Some(ref currency) = cost.currency {
                                used_commodities.insert(currency.clone());
                            }
                        }
                    }
                }
                crate::types::DirectiveData::Balance(bal) => {
                    used_commodities.insert(bal.amount.currency.clone());
                }
                crate::types::DirectiveData::Price(price) => {
                    used_commodities.insert(price.currency.clone());
                    used_commodities.insert(price.amount.currency.clone());
                }
                _ => {}
            }
        }

        // Report undeclared commodities
        for currency in &used_commodities {
            if !declared_commodities.contains(currency) {
                errors.push(PluginError::warning(format!(
                    "commodity '{currency}' used but not declared"
                )));
            }
        }

        PluginOutput {
            directives: input.directives,
            errors,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_native_plugin_registry() {
        let registry = NativePluginRegistry::new();

        assert!(registry.find("implicit_prices").is_some());
        assert!(registry.find("beancount.plugins.implicit_prices").is_some());
        assert!(registry.find("check_commodity").is_some());
        assert!(registry.find("nonexistent").is_none());
    }

    #[test]
    fn test_is_builtin() {
        assert!(NativePluginRegistry::is_builtin("implicit_prices"));
        assert!(NativePluginRegistry::is_builtin(
            "beancount.plugins.implicit_prices"
        ));
        assert!(!NativePluginRegistry::is_builtin("my_custom_plugin"));
    }
}

/// Plugin that automatically adds tags based on account patterns.
///
/// This is an example plugin showing how to implement custom tagging logic.
/// It can be configured with rules like:
/// - "Expenses:Food" -> #food
/// - "Expenses:Travel" -> #travel
/// - "Assets:Bank" -> #banking
pub struct AutoTagPlugin {
    /// Rules mapping account prefixes to tags.
    rules: Vec<(String, String)>,
}

impl AutoTagPlugin {
    /// Create with default rules.
    pub fn new() -> Self {
        Self {
            rules: vec![
                ("Expenses:Food".to_string(), "food".to_string()),
                ("Expenses:Travel".to_string(), "travel".to_string()),
                ("Expenses:Transport".to_string(), "transport".to_string()),
                ("Income:Salary".to_string(), "income".to_string()),
            ],
        }
    }

    /// Create with custom rules.
    pub const fn with_rules(rules: Vec<(String, String)>) -> Self {
        Self { rules }
    }
}

impl Default for AutoTagPlugin {
    fn default() -> Self {
        Self::new()
    }
}

impl NativePlugin for AutoTagPlugin {
    fn name(&self) -> &'static str {
        "auto_tag"
    }

    fn description(&self) -> &'static str {
        "Auto-tag transactions by account patterns"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let directives: Vec<_> = input
            .directives
            .into_iter()
            .map(|mut wrapper| {
                if wrapper.directive_type == "transaction" {
                    if let crate::types::DirectiveData::Transaction(ref mut txn) = wrapper.data {
                        // Check each posting against rules
                        for posting in &txn.postings {
                            for (prefix, tag) in &self.rules {
                                if posting.account.starts_with(prefix) {
                                    // Add tag if not already present
                                    if !txn.tags.contains(tag) {
                                        txn.tags.push(tag.clone());
                                    }
                                }
                            }
                        }
                    }
                }
                wrapper
            })
            .collect();

        PluginOutput {
            directives,
            errors: Vec::new(),
        }
    }
}

#[cfg(test)]
mod auto_tag_tests {
    use super::*;
    use crate::types::*;

    #[test]
    fn test_auto_tag_adds_tag() {
        let plugin = AutoTagPlugin::new();

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-01-15".to_string(),
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "Lunch".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![],
                    postings: vec![
                        PostingData {
                            account: "Expenses:Food:Restaurants".to_string(),
                            units: Some(AmountData {
                                number: "25.00".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        },
                        PostingData {
                            account: "Assets:Cash".to_string(),
                            units: Some(AmountData {
                                number: "-25.00".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        },
                    ],
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        assert_eq!(output.directives.len(), 1);

        if let DirectiveData::Transaction(txn) = &output.directives[0].data {
            assert!(txn.tags.contains(&"food".to_string()));
        } else {
            panic!("Expected transaction");
        }
    }
}

// ============================================================================
// Additional Built-in Plugins
// ============================================================================

/// Plugin that auto-generates Open directives for accounts used without explicit open.
pub struct AutoAccountsPlugin;

impl NativePlugin for AutoAccountsPlugin {
    fn name(&self) -> &'static str {
        "auto_accounts"
    }

    fn description(&self) -> &'static str {
        "Auto-generate Open directives for used accounts"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::{HashMap, HashSet};

        let mut opened_accounts: HashSet<String> = HashSet::new();
        let mut account_first_use: HashMap<String, String> = HashMap::new(); // account -> date

        // First pass: find all open directives and first use of each account
        for wrapper in &input.directives {
            match &wrapper.data {
                DirectiveData::Open(data) => {
                    opened_accounts.insert(data.account.clone());
                }
                DirectiveData::Transaction(txn) => {
                    for posting in &txn.postings {
                        account_first_use
                            .entry(posting.account.clone())
                            .or_insert_with(|| wrapper.date.clone());
                    }
                }
                DirectiveData::Balance(data) => {
                    account_first_use
                        .entry(data.account.clone())
                        .or_insert_with(|| wrapper.date.clone());
                }
                DirectiveData::Pad(data) => {
                    account_first_use
                        .entry(data.account.clone())
                        .or_insert_with(|| wrapper.date.clone());
                    account_first_use
                        .entry(data.source_account.clone())
                        .or_insert_with(|| wrapper.date.clone());
                }
                _ => {}
            }
        }

        // Generate open directives for accounts without explicit open
        let mut new_directives: Vec<DirectiveWrapper> = Vec::new();
        for (account, date) in &account_first_use {
            if !opened_accounts.contains(account) {
                new_directives.push(DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: date.clone(),
                    data: DirectiveData::Open(OpenData {
                        account: account.clone(),
                        currencies: vec![],
                        booking: None,
                    }),
                });
            }
        }

        // Add existing directives
        new_directives.extend(input.directives);

        // Sort by date
        new_directives.sort_by(|a, b| a.date.cmp(&b.date));

        PluginOutput {
            directives: new_directives,
            errors: Vec::new(),
        }
    }
}

/// Plugin that errors when posting to non-leaf (parent) accounts.
pub struct LeafOnlyPlugin;

impl NativePlugin for LeafOnlyPlugin {
    fn name(&self) -> &'static str {
        "leafonly"
    }

    fn description(&self) -> &'static str {
        "Error on postings to non-leaf accounts"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::HashSet;

        // Collect all accounts used
        let mut all_accounts: HashSet<String> = HashSet::new();
        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    all_accounts.insert(posting.account.clone());
                }
            }
        }

        // Find parent accounts (accounts that are prefixes of others)
        let parent_accounts: HashSet<&String> = all_accounts
            .iter()
            .filter(|acc| {
                all_accounts
                    .iter()
                    .any(|other| other != *acc && other.starts_with(&format!("{acc}:")))
            })
            .collect();

        // Check for postings to parent accounts
        let mut errors = Vec::new();
        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    if parent_accounts.contains(&posting.account) {
                        errors.push(PluginError::error(format!(
                            "Posting to non-leaf account '{}' - has child accounts",
                            posting.account
                        )));
                    }
                }
            }
        }

        PluginOutput {
            directives: input.directives,
            errors,
        }
    }
}

/// Plugin that detects duplicate transactions based on hash.
pub struct NoDuplicatesPlugin;

impl NativePlugin for NoDuplicatesPlugin {
    fn name(&self) -> &'static str {
        "noduplicates"
    }

    fn description(&self) -> &'static str {
        "Hash-based duplicate transaction detection"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::hash_map::DefaultHasher;
        use std::collections::HashSet;
        use std::hash::{Hash, Hasher};

        fn hash_transaction(date: &str, txn: &TransactionData) -> u64 {
            let mut hasher = DefaultHasher::new();
            date.hash(&mut hasher);
            txn.narration.hash(&mut hasher);
            txn.payee.hash(&mut hasher);
            for posting in &txn.postings {
                posting.account.hash(&mut hasher);
                if let Some(units) = &posting.units {
                    units.number.hash(&mut hasher);
                    units.currency.hash(&mut hasher);
                }
            }
            hasher.finish()
        }

        let mut seen: HashSet<u64> = HashSet::new();
        let mut errors = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                let hash = hash_transaction(&wrapper.date, txn);
                if !seen.insert(hash) {
                    errors.push(PluginError::error(format!(
                        "Duplicate transaction: {} \"{}\"",
                        wrapper.date, txn.narration
                    )));
                }
            }
        }

        PluginOutput {
            directives: input.directives,
            errors,
        }
    }
}

/// Plugin that enforces single commodity per account.
pub struct OneCommodityPlugin;

impl NativePlugin for OneCommodityPlugin {
    fn name(&self) -> &'static str {
        "onecommodity"
    }

    fn description(&self) -> &'static str {
        "Enforce single commodity per account"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::HashMap;

        // Track currencies used per account
        let mut account_currencies: HashMap<String, String> = HashMap::new();
        let mut errors = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    if let Some(units) = &posting.units {
                        if let Some(existing) = account_currencies.get(&posting.account) {
                            if existing != &units.currency {
                                errors.push(PluginError::error(format!(
                                    "Account '{}' uses multiple currencies: {} and {}",
                                    posting.account, existing, units.currency
                                )));
                            }
                        } else {
                            account_currencies
                                .insert(posting.account.clone(), units.currency.clone());
                        }
                    }
                }
            }
        }

        PluginOutput {
            directives: input.directives,
            errors,
        }
    }
}

/// Plugin that enforces unique prices (one per commodity pair per day).
pub struct UniquePricesPlugin;

impl NativePlugin for UniquePricesPlugin {
    fn name(&self) -> &'static str {
        "unique_prices"
    }

    fn description(&self) -> &'static str {
        "One price per day per currency pair"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::HashSet;

        // Track (date, base_currency, quote_currency) tuples
        let mut seen: HashSet<(String, String, String)> = HashSet::new();
        let mut errors = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Price(price) = &wrapper.data {
                let key = (
                    wrapper.date.clone(),
                    price.currency.clone(),
                    price.amount.currency.clone(),
                );
                if !seen.insert(key.clone()) {
                    errors.push(PluginError::error(format!(
                        "Duplicate price for {}/{} on {}",
                        price.currency, price.amount.currency, wrapper.date
                    )));
                }
            }
        }

        PluginOutput {
            directives: input.directives,
            errors,
        }
    }
}

/// Plugin that auto-discovers document files from configured directories.
///
/// Scans directories specified in `option "documents"` for files matching
/// the pattern: `{Account}/YYYY-MM-DD.description.*`
///
/// For example: `documents/Assets/Bank/Checking/2024-01-15.statement.pdf`
/// generates: `2024-01-15 document Assets:Bank:Checking "documents/Assets/Bank/Checking/2024-01-15.statement.pdf"`
pub struct DocumentDiscoveryPlugin {
    /// Directories to scan for documents.
    pub directories: Vec<String>,
}

impl DocumentDiscoveryPlugin {
    /// Create a new plugin with the given directories.
    pub const fn new(directories: Vec<String>) -> Self {
        Self { directories }
    }
}

impl NativePlugin for DocumentDiscoveryPlugin {
    fn name(&self) -> &'static str {
        "document_discovery"
    }

    fn description(&self) -> &'static str {
        "Auto-discover documents from directories"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::path::Path;

        let mut new_directives = Vec::new();
        let mut errors = Vec::new();

        // Collect existing document paths to avoid duplicates
        let mut existing_docs: std::collections::HashSet<String> = std::collections::HashSet::new();
        for wrapper in &input.directives {
            if let DirectiveData::Document(doc) = &wrapper.data {
                existing_docs.insert(doc.path.clone());
            }
        }

        // Scan each directory
        for dir in &self.directories {
            let dir_path = Path::new(dir);
            if !dir_path.exists() {
                continue;
            }

            if let Err(e) = scan_documents(
                dir_path,
                dir,
                &existing_docs,
                &mut new_directives,
                &mut errors,
            ) {
                errors.push(PluginError::error(format!(
                    "Error scanning documents in {dir}: {e}"
                )));
            }
        }

        // Add discovered documents to directives
        let mut all_directives = input.directives;
        all_directives.extend(new_directives);

        // Sort by date
        all_directives.sort_by(|a, b| a.date.cmp(&b.date));

        PluginOutput {
            directives: all_directives,
            errors,
        }
    }
}

/// Recursively scan a directory for document files.
#[allow(clippy::only_used_in_recursion)]
fn scan_documents(
    path: &std::path::Path,
    base_dir: &str,
    existing: &std::collections::HashSet<String>,
    directives: &mut Vec<DirectiveWrapper>,
    errors: &mut Vec<PluginError>,
) -> std::io::Result<()> {
    use std::fs;

    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let entry_path = entry.path();

        if entry_path.is_dir() {
            scan_documents(&entry_path, base_dir, existing, directives, errors)?;
        } else if entry_path.is_file() {
            // Try to parse filename as YYYY-MM-DD.description.ext
            if let Some(file_name) = entry_path.file_name().and_then(|n| n.to_str()) {
                if file_name.len() >= 10
                    && file_name.chars().nth(4) == Some('-')
                    && file_name.chars().nth(7) == Some('-')
                {
                    let date_str = &file_name[0..10];
                    // Validate date format
                    if date_str.chars().take(4).all(|c| c.is_ascii_digit())
                        && date_str.chars().skip(5).take(2).all(|c| c.is_ascii_digit())
                        && date_str.chars().skip(8).take(2).all(|c| c.is_ascii_digit())
                    {
                        // Extract account from path relative to base_dir
                        if let Ok(rel_path) = entry_path.strip_prefix(base_dir) {
                            if let Some(parent) = rel_path.parent() {
                                let account = parent
                                    .components()
                                    .map(|c| c.as_os_str().to_string_lossy().to_string())
                                    .collect::<Vec<_>>()
                                    .join(":");

                                if !account.is_empty() {
                                    let full_path = entry_path.to_string_lossy().to_string();

                                    // Skip if already exists
                                    if existing.contains(&full_path) {
                                        continue;
                                    }

                                    directives.push(DirectiveWrapper {
                                        directive_type: "document".to_string(),
                                        date: date_str.to_string(),
                                        data: DirectiveData::Document(DocumentData {
                                            account,
                                            path: full_path,
                                        }),
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    Ok(())
}

/// Plugin that inserts zero balance assertion when posting has `closing: TRUE` metadata.
///
/// When a posting has metadata `closing: TRUE`, this plugin adds a balance assertion
/// for that account with zero balance on the next day.
pub struct CheckClosingPlugin;

impl NativePlugin for CheckClosingPlugin {
    fn name(&self) -> &'static str {
        "check_closing"
    }

    fn description(&self) -> &'static str {
        "Zero balance assertion on account closing"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use crate::types::{AmountData, BalanceData, MetaValueData};

        let mut new_directives: Vec<DirectiveWrapper> = Vec::new();

        for wrapper in &input.directives {
            new_directives.push(wrapper.clone());

            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    // Check for closing: TRUE metadata
                    let has_closing = posting.metadata.iter().any(|(key, val)| {
                        key == "closing" && matches!(val, MetaValueData::Bool(true))
                    });

                    if has_closing {
                        // Parse the date and add one day
                        if let Some(next_date) = increment_date(&wrapper.date) {
                            // Get the currency from the posting
                            let currency = posting
                                .units
                                .as_ref()
                                .map_or_else(|| "USD".to_string(), |u| u.currency.clone());

                            // Add zero balance assertion
                            new_directives.push(DirectiveWrapper {
                                directive_type: "balance".to_string(),
                                date: next_date,
                                data: DirectiveData::Balance(BalanceData {
                                    account: posting.account.clone(),
                                    amount: AmountData {
                                        number: "0".to_string(),
                                        currency,
                                    },
                                    tolerance: None,
                                }),
                            });
                        }
                    }
                }
            }
        }

        // Sort by date
        new_directives.sort_by(|a, b| a.date.cmp(&b.date));

        PluginOutput {
            directives: new_directives,
            errors: Vec::new(),
        }
    }
}

/// Increment a date string by one day (YYYY-MM-DD format).
fn increment_date(date: &str) -> Option<String> {
    let parts: Vec<&str> = date.split('-').collect();
    if parts.len() != 3 {
        return None;
    }

    let year: i32 = parts[0].parse().ok()?;
    let month: u32 = parts[1].parse().ok()?;
    let day: u32 = parts[2].parse().ok()?;

    // Simple date increment (handles month/year rollovers)
    let days_in_month = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => {
            if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) {
                29
            } else {
                28
            }
        }
        _ => return None,
    };

    let (new_year, new_month, new_day) = if day < days_in_month {
        (year, month, day + 1)
    } else if month < 12 {
        (year, month + 1, 1)
    } else {
        (year + 1, 1, 1)
    };

    Some(format!("{new_year:04}-{new_month:02}-{new_day:02}"))
}

/// Plugin that closes all descendant accounts when a parent account closes.
///
/// When an account like `Assets:Bank` is closed, this plugin also generates
/// close directives for all sub-accounts like `Assets:Bank:Checking`.
pub struct CloseTreePlugin;

impl NativePlugin for CloseTreePlugin {
    fn name(&self) -> &'static str {
        "close_tree"
    }

    fn description(&self) -> &'static str {
        "Close descendant accounts automatically"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use crate::types::CloseData;
        use std::collections::HashSet;

        // Collect all accounts that are used
        let mut all_accounts: HashSet<String> = HashSet::new();
        for wrapper in &input.directives {
            if let DirectiveData::Open(data) = &wrapper.data {
                all_accounts.insert(data.account.clone());
            }
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    all_accounts.insert(posting.account.clone());
                }
            }
        }

        // Collect accounts that are explicitly closed
        let mut closed_parents: Vec<(String, String)> = Vec::new(); // (account, date)
        for wrapper in &input.directives {
            if let DirectiveData::Close(data) = &wrapper.data {
                closed_parents.push((data.account.clone(), wrapper.date.clone()));
            }
        }

        // Find child accounts for each closed parent
        let mut new_directives = input.directives;

        for (parent, close_date) in &closed_parents {
            let prefix = format!("{parent}:");
            for account in &all_accounts {
                if account.starts_with(&prefix) {
                    // Check if already closed
                    let already_closed = new_directives.iter().any(|w| {
                        if let DirectiveData::Close(data) = &w.data {
                            &data.account == account
                        } else {
                            false
                        }
                    });

                    if !already_closed {
                        new_directives.push(DirectiveWrapper {
                            directive_type: "close".to_string(),
                            date: close_date.clone(),
                            data: DirectiveData::Close(CloseData {
                                account: account.clone(),
                            }),
                        });
                    }
                }
            }
        }

        // Sort by date
        new_directives.sort_by(|a, b| a.date.cmp(&b.date));

        PluginOutput {
            directives: new_directives,
            errors: Vec::new(),
        }
    }
}

/// Plugin that ensures currencies use cost OR price consistently, never both.
///
/// If a currency is used with cost notation `{...}`, it should not also be used
/// with price notation `@` in the same ledger, as this can lead to inconsistencies.
pub struct CoherentCostPlugin;

impl NativePlugin for CoherentCostPlugin {
    fn name(&self) -> &'static str {
        "coherent_cost"
    }

    fn description(&self) -> &'static str {
        "Enforce cost OR price (not both) consistency"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::{HashMap, HashSet};

        // Track which currencies are used with cost vs price
        let mut currencies_with_cost: HashSet<String> = HashSet::new();
        let mut currencies_with_price: HashSet<String> = HashSet::new();
        let mut first_use: HashMap<String, (String, String)> = HashMap::new(); // currency -> (type, date)

        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    if let Some(units) = &posting.units {
                        let currency = &units.currency;

                        if posting.cost.is_some() && !currencies_with_cost.contains(currency) {
                            currencies_with_cost.insert(currency.clone());
                            first_use
                                .entry(currency.clone())
                                .or_insert(("cost".to_string(), wrapper.date.clone()));
                        }

                        if posting.price.is_some() && !currencies_with_price.contains(currency) {
                            currencies_with_price.insert(currency.clone());
                            first_use
                                .entry(currency.clone())
                                .or_insert(("price".to_string(), wrapper.date.clone()));
                        }
                    }
                }
            }
        }

        // Find currencies used with both
        let mut errors = Vec::new();
        for currency in currencies_with_cost.intersection(&currencies_with_price) {
            errors.push(PluginError::error(format!(
                "Currency '{currency}' is used with both cost and price notation - this may cause inconsistencies"
            )));
        }

        PluginOutput {
            directives: input.directives,
            errors,
        }
    }
}

/// Plugin that cross-checks declared gains against sale prices.
///
/// When selling a position at a price, this plugin verifies that any
/// income/expense postings match the expected gain/loss from the sale.
pub struct SellGainsPlugin;

impl NativePlugin for SellGainsPlugin {
    fn name(&self) -> &'static str {
        "sellgains"
    }

    fn description(&self) -> &'static str {
        "Cross-check capital gains against sales"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use rust_decimal::Decimal;
        use std::str::FromStr;

        let mut errors = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                // Find postings that are sales (negative units with cost and price)
                for posting in &txn.postings {
                    if let (Some(units), Some(cost), Some(price)) =
                        (&posting.units, &posting.cost, &posting.price)
                    {
                        // Check if this is a sale (negative units)
                        let units_num = Decimal::from_str(&units.number).unwrap_or_default();
                        if units_num >= Decimal::ZERO {
                            continue;
                        }

                        // Get cost basis
                        let cost_per = cost
                            .number_per
                            .as_ref()
                            .and_then(|s| Decimal::from_str(s).ok())
                            .unwrap_or_default();

                        // Get sale price
                        let sale_price = price
                            .amount
                            .as_ref()
                            .and_then(|a| Decimal::from_str(&a.number).ok())
                            .unwrap_or_default();

                        // Calculate expected gain/loss
                        let expected_gain = (sale_price - cost_per) * units_num.abs();

                        // Look for income/expense posting that should match
                        let has_gain_posting = txn.postings.iter().any(|p| {
                            p.account.starts_with("Income:") || p.account.starts_with("Expenses:")
                        });

                        if expected_gain != Decimal::ZERO && !has_gain_posting {
                            errors.push(PluginError::warning(format!(
                                "Sale of {} {} at {} (cost {}) has expected gain/loss of {} but no Income/Expenses posting",
                                units_num.abs(),
                                units.currency,
                                sale_price,
                                cost_per,
                                expected_gain
                            )));
                        }
                    }
                }
            }
        }

        PluginOutput {
            directives: input.directives,
            errors,
        }
    }
}

/// Meta-plugin that enables all strict validation plugins.
///
/// This plugin runs multiple validation checks:
/// - leafonly: No postings to parent accounts
/// - onecommodity: Single currency per account
/// - `check_commodity`: All currencies must be declared
/// - noduplicates: No duplicate transactions
pub struct PedanticPlugin;

impl NativePlugin for PedanticPlugin {
    fn name(&self) -> &'static str {
        "pedantic"
    }

    fn description(&self) -> &'static str {
        "Enable all strict validation rules"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let mut all_errors = Vec::new();

        // Run leafonly checks
        let leafonly = LeafOnlyPlugin;
        let result = leafonly.process(PluginInput {
            directives: input.directives.clone(),
            options: input.options.clone(),
            config: None,
        });
        all_errors.extend(result.errors);

        // Run onecommodity checks
        let onecommodity = OneCommodityPlugin;
        let result = onecommodity.process(PluginInput {
            directives: input.directives.clone(),
            options: input.options.clone(),
            config: None,
        });
        all_errors.extend(result.errors);

        // Run noduplicates checks
        let noduplicates = NoDuplicatesPlugin;
        let result = noduplicates.process(PluginInput {
            directives: input.directives.clone(),
            options: input.options.clone(),
            config: None,
        });
        all_errors.extend(result.errors);

        // Run check_commodity checks
        let check_commodity = CheckCommodityPlugin;
        let result = check_commodity.process(PluginInput {
            directives: input.directives.clone(),
            options: input.options.clone(),
            config: None,
        });
        all_errors.extend(result.errors);

        PluginOutput {
            directives: input.directives,
            errors: all_errors,
        }
    }
}

/// Plugin that calculates unrealized gains on positions.
///
/// For each position held at cost, this plugin can generate unrealized
/// gain/loss entries based on current market prices from the price database.
pub struct UnrealizedPlugin {
    /// Account to book unrealized gains to.
    pub gains_account: String,
}

impl UnrealizedPlugin {
    /// Create a new plugin with the default gains account.
    pub fn new() -> Self {
        Self {
            gains_account: "Income:Unrealized".to_string(),
        }
    }

    /// Create with a custom gains account.
    pub const fn with_account(account: String) -> Self {
        Self {
            gains_account: account,
        }
    }
}

impl Default for UnrealizedPlugin {
    fn default() -> Self {
        Self::new()
    }
}

impl NativePlugin for UnrealizedPlugin {
    fn name(&self) -> &'static str {
        "unrealized"
    }

    fn description(&self) -> &'static str {
        "Calculate unrealized gains/losses"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use rust_decimal::Decimal;
        use std::collections::HashMap;
        use std::str::FromStr;

        // Build price database from Price directives
        let mut prices: HashMap<(String, String), (String, Decimal)> = HashMap::new(); // (base, quote) -> (date, price)

        for wrapper in &input.directives {
            if let DirectiveData::Price(price) = &wrapper.data {
                let key = (price.currency.clone(), price.amount.currency.clone());
                let price_val = Decimal::from_str(&price.amount.number).unwrap_or_default();

                // Keep the most recent price
                if let Some((existing_date, _)) = prices.get(&key) {
                    if &wrapper.date > existing_date {
                        prices.insert(key, (wrapper.date.clone(), price_val));
                    }
                } else {
                    prices.insert(key, (wrapper.date.clone(), price_val));
                }
            }
        }

        // Track positions by account
        let mut positions: HashMap<String, HashMap<String, (Decimal, Decimal)>> = HashMap::new(); // account -> currency -> (units, cost_basis)

        let mut errors = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    if let Some(units) = &posting.units {
                        let units_num = Decimal::from_str(&units.number).unwrap_or_default();

                        let cost_basis = if let Some(cost) = &posting.cost {
                            cost.number_per
                                .as_ref()
                                .and_then(|s| Decimal::from_str(s).ok())
                                .unwrap_or_default()
                                * units_num.abs()
                        } else {
                            Decimal::ZERO
                        };

                        let account_positions =
                            positions.entry(posting.account.clone()).or_default();

                        let (existing_units, existing_cost) = account_positions
                            .entry(units.currency.clone())
                            .or_insert((Decimal::ZERO, Decimal::ZERO));

                        *existing_units += units_num;
                        *existing_cost += cost_basis;
                    }
                }
            }
        }

        // Calculate unrealized gains for positions with known prices
        for (account, currencies) in &positions {
            for (currency, (units, cost_basis)) in currencies {
                if *units == Decimal::ZERO {
                    continue;
                }

                // Look for a price to the operating currency (assume USD for now)
                if let Some((_, market_price)) = prices.get(&(currency.clone(), "USD".to_string()))
                {
                    let market_value = *units * market_price;
                    let unrealized_gain = market_value - cost_basis;

                    if unrealized_gain.abs() > Decimal::new(1, 2) {
                        // More than $0.01
                        errors.push(PluginError::warning(format!(
                            "Unrealized gain on {units} {currency} in {account}: {unrealized_gain} USD"
                        )));
                    }
                }
            }
        }

        PluginOutput {
            directives: input.directives,
            errors,
        }
    }
}

/// Plugin that identifies accounts that are opened but never used.
///
/// Reports a warning for each account that has an Open directive but is never
/// referenced in any transaction, balance, pad, or other directive.
pub struct NoUnusedPlugin;

impl NativePlugin for NoUnusedPlugin {
    fn name(&self) -> &'static str {
        "nounused"
    }

    fn description(&self) -> &'static str {
        "Warn about unused accounts"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use std::collections::HashSet;

        let mut opened_accounts: HashSet<String> = HashSet::new();
        let mut used_accounts: HashSet<String> = HashSet::new();

        // Collect all opened accounts and used accounts in one pass
        for wrapper in &input.directives {
            match &wrapper.data {
                DirectiveData::Open(data) => {
                    opened_accounts.insert(data.account.clone());
                }
                DirectiveData::Close(data) => {
                    // Closing an account counts as using it
                    used_accounts.insert(data.account.clone());
                }
                DirectiveData::Transaction(txn) => {
                    for posting in &txn.postings {
                        used_accounts.insert(posting.account.clone());
                    }
                }
                DirectiveData::Balance(data) => {
                    used_accounts.insert(data.account.clone());
                }
                DirectiveData::Pad(data) => {
                    used_accounts.insert(data.account.clone());
                    used_accounts.insert(data.source_account.clone());
                }
                DirectiveData::Note(data) => {
                    used_accounts.insert(data.account.clone());
                }
                DirectiveData::Document(data) => {
                    used_accounts.insert(data.account.clone());
                }
                DirectiveData::Custom(data) => {
                    // Check custom directive values for account references
                    // Account names start with standard prefixes
                    for value in &data.values {
                        if value.starts_with("Assets:")
                            || value.starts_with("Liabilities:")
                            || value.starts_with("Equity:")
                            || value.starts_with("Income:")
                            || value.starts_with("Expenses:")
                        {
                            used_accounts.insert(value.clone());
                        }
                    }
                }
                _ => {}
            }
        }

        // Find unused accounts (opened but never used)
        let mut errors = Vec::new();
        let mut unused: Vec<_> = opened_accounts
            .difference(&used_accounts)
            .cloned()
            .collect();
        unused.sort(); // Consistent ordering for output

        for account in unused {
            errors.push(PluginError::warning(format!(
                "Account '{account}' is opened but never used"
            )));
        }

        PluginOutput {
            directives: input.directives,
            errors,
        }
    }
}

#[cfg(test)]
mod nounused_tests {
    use super::*;
    use crate::types::*;

    #[test]
    fn test_nounused_reports_unused_account() {
        let plugin = NoUnusedPlugin;

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:Bank".to_string(),
                        currencies: vec![],
                        booking: None,
                    }),
                },
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:Unused".to_string(),
                        currencies: vec![],
                        booking: None,
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-15".to_string(),
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Test".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Bank".to_string(),
                            units: Some(AmountData {
                                number: "100".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 1);
        assert!(output.errors[0].message.contains("Assets:Unused"));
        assert!(output.errors[0].message.contains("never used"));
    }

    #[test]
    fn test_nounused_no_warning_for_used_accounts() {
        let plugin = NoUnusedPlugin;

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:Bank".to_string(),
                        currencies: vec![],
                        booking: None,
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-15".to_string(),
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Test".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Bank".to_string(),
                            units: Some(AmountData {
                                number: "100".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
    }

    #[test]
    fn test_nounused_close_counts_as_used() {
        let plugin = NoUnusedPlugin;

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:OldAccount".to_string(),
                        currencies: vec![],
                        booking: None,
                    }),
                },
                DirectiveWrapper {
                    directive_type: "close".to_string(),
                    date: "2024-12-31".to_string(),
                    data: DirectiveData::Close(CloseData {
                        account: "Assets:OldAccount".to_string(),
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        // Close counts as usage, so no warning
        assert_eq!(output.errors.len(), 0);
    }
}

/// Plugin that inserts zero balance assertions when balance sheet accounts are closed.
///
/// When a Close directive is encountered for an account (Assets, Liabilities, or Equity),
/// this plugin generates Balance directives with zero amounts for all currencies that
/// were used in that account. The assertions are dated one day after the close date.
pub struct CheckDrainedPlugin;

impl NativePlugin for CheckDrainedPlugin {
    fn name(&self) -> &'static str {
        "check_drained"
    }

    fn description(&self) -> &'static str {
        "Zero balance assertion on balance sheet account close"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use crate::types::{AmountData, BalanceData};
        use std::collections::{HashMap, HashSet};

        // Track currencies used per account
        let mut account_currencies: HashMap<String, HashSet<String>> = HashMap::new();

        // First pass: collect all currencies used per account
        for wrapper in &input.directives {
            match &wrapper.data {
                DirectiveData::Transaction(txn) => {
                    for posting in &txn.postings {
                        if let Some(units) = &posting.units {
                            account_currencies
                                .entry(posting.account.clone())
                                .or_default()
                                .insert(units.currency.clone());
                        }
                    }
                }
                DirectiveData::Balance(data) => {
                    account_currencies
                        .entry(data.account.clone())
                        .or_default()
                        .insert(data.amount.currency.clone());
                }
                DirectiveData::Open(data) => {
                    // If Open has currencies, track them
                    for currency in &data.currencies {
                        account_currencies
                            .entry(data.account.clone())
                            .or_default()
                            .insert(currency.clone());
                    }
                }
                _ => {}
            }
        }

        // Second pass: generate balance assertions for closed balance sheet accounts
        let mut new_directives: Vec<DirectiveWrapper> = Vec::new();

        for wrapper in &input.directives {
            new_directives.push(wrapper.clone());

            if let DirectiveData::Close(data) = &wrapper.data {
                // Only generate for balance sheet accounts (Assets, Liabilities, Equity)
                let is_balance_sheet = data.account.starts_with("Assets:")
                    || data.account.starts_with("Liabilities:")
                    || data.account.starts_with("Equity:")
                    || data.account == "Assets"
                    || data.account == "Liabilities"
                    || data.account == "Equity";

                if !is_balance_sheet {
                    continue;
                }

                // Get currencies for this account
                if let Some(currencies) = account_currencies.get(&data.account) {
                    // Calculate the day after close
                    if let Some(next_date) = increment_date(&wrapper.date) {
                        // Generate zero balance assertion for each currency
                        let mut sorted_currencies: Vec<_> = currencies.iter().collect();
                        sorted_currencies.sort(); // Consistent ordering

                        for currency in sorted_currencies {
                            new_directives.push(DirectiveWrapper {
                                directive_type: "balance".to_string(),
                                date: next_date.clone(),
                                data: DirectiveData::Balance(BalanceData {
                                    account: data.account.clone(),
                                    amount: AmountData {
                                        number: "0".to_string(),
                                        currency: currency.clone(),
                                    },
                                    tolerance: None,
                                }),
                            });
                        }
                    }
                }
            }
        }

        // Sort by date
        new_directives.sort_by(|a, b| a.date.cmp(&b.date));

        PluginOutput {
            directives: new_directives,
            errors: Vec::new(),
        }
    }
}

#[cfg(test)]
mod check_drained_tests {
    use super::*;
    use crate::types::*;

    #[test]
    fn test_check_drained_adds_balance_assertion() {
        let plugin = CheckDrainedPlugin;

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:Bank".to_string(),
                        currencies: vec!["USD".to_string()],
                        booking: None,
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-06-15".to_string(),
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Deposit".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Bank".to_string(),
                            units: Some(AmountData {
                                number: "100".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "close".to_string(),
                    date: "2024-12-31".to_string(),
                    data: DirectiveData::Close(CloseData {
                        account: "Assets:Bank".to_string(),
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);

        // Should have 4 directives: open, transaction, close, balance
        assert_eq!(output.directives.len(), 4);

        // Find the balance directive
        let balance = output
            .directives
            .iter()
            .find(|d| d.directive_type == "balance")
            .expect("Should have balance directive");

        assert_eq!(balance.date, "2025-01-01"); // Day after close
        if let DirectiveData::Balance(b) = &balance.data {
            assert_eq!(b.account, "Assets:Bank");
            assert_eq!(b.amount.number, "0");
            assert_eq!(b.amount.currency, "USD");
        } else {
            panic!("Expected Balance directive");
        }
    }

    #[test]
    fn test_check_drained_ignores_income_expense() {
        let plugin = CheckDrainedPlugin;

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    data: DirectiveData::Open(OpenData {
                        account: "Income:Salary".to_string(),
                        currencies: vec!["USD".to_string()],
                        booking: None,
                    }),
                },
                DirectiveWrapper {
                    directive_type: "close".to_string(),
                    date: "2024-12-31".to_string(),
                    data: DirectiveData::Close(CloseData {
                        account: "Income:Salary".to_string(),
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        // Should not add balance assertions for income/expense accounts
        assert_eq!(output.directives.len(), 2);
        assert!(!output
            .directives
            .iter()
            .any(|d| d.directive_type == "balance"));
    }

    #[test]
    fn test_check_drained_multiple_currencies() {
        let plugin = CheckDrainedPlugin;

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "open".to_string(),
                    date: "2024-01-01".to_string(),
                    data: DirectiveData::Open(OpenData {
                        account: "Assets:Bank".to_string(),
                        currencies: vec![],
                        booking: None,
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-06-15".to_string(),
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "USD Deposit".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Bank".to_string(),
                            units: Some(AmountData {
                                number: "100".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-07-15".to_string(),
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "EUR Deposit".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Bank".to_string(),
                            units: Some(AmountData {
                                number: "50".to_string(),
                                currency: "EUR".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "close".to_string(),
                    date: "2024-12-31".to_string(),
                    data: DirectiveData::Close(CloseData {
                        account: "Assets:Bank".to_string(),
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        // Should have 6 directives: open, 2 transactions, close, 2 balance assertions
        assert_eq!(output.directives.len(), 6);

        let balances: Vec<_> = output
            .directives
            .iter()
            .filter(|d| d.directive_type == "balance")
            .collect();
        assert_eq!(balances.len(), 2);

        // Both should be dated 2025-01-01
        for b in &balances {
            assert_eq!(b.date, "2025-01-01");
        }
    }
}

/// Plugin that validates Commodity directives have required metadata attributes.
///
/// Can be configured with a string specifying required attributes and their allowed values:
/// - `"{'name': null, 'sector': ['Tech', 'Finance']}"` means:
///   - `name` is required but any value is allowed
///   - `sector` is required and must be one of the allowed values
pub struct CommodityAttrPlugin {
    /// Required attributes and their allowed values (None means any value is allowed).
    required_attrs: Vec<(String, Option<Vec<String>>)>,
}

impl CommodityAttrPlugin {
    /// Create with default configuration (no required attributes).
    pub fn new() -> Self {
        Self {
            required_attrs: Vec::new(),
        }
    }

    /// Create with required attributes.
    pub const fn with_attrs(attrs: Vec<(String, Option<Vec<String>>)>) -> Self {
        Self {
            required_attrs: attrs,
        }
    }

    /// Parse configuration string in Python dict-like format.
    ///
    /// Example: `"{'name': null, 'sector': ['Tech', 'Finance']}"`
    fn parse_config(config: &str) -> Vec<(String, Option<Vec<String>>)> {
        let mut result = Vec::new();

        // Simple parser for the config format
        // Strip outer braces and split by commas
        let trimmed = config.trim();
        let content = if trimmed.starts_with('{') && trimmed.ends_with('}') {
            &trimmed[1..trimmed.len() - 1]
        } else {
            trimmed
        };

        // Split by comma (careful with nested arrays)
        let mut depth = 0;
        let mut current = String::new();
        let mut entries = Vec::new();

        for c in content.chars() {
            match c {
                '[' => {
                    depth += 1;
                    current.push(c);
                }
                ']' => {
                    depth -= 1;
                    current.push(c);
                }
                ',' if depth == 0 => {
                    entries.push(current.trim().to_string());
                    current.clear();
                }
                _ => current.push(c),
            }
        }
        if !current.trim().is_empty() {
            entries.push(current.trim().to_string());
        }

        // Parse each entry: "'key': value"
        for entry in entries {
            if let Some((key_part, value_part)) = entry.split_once(':') {
                let key = key_part
                    .trim()
                    .trim_matches('\'')
                    .trim_matches('"')
                    .to_string();
                let value = value_part.trim();

                if value == "null" || value == "None" {
                    result.push((key, None));
                } else if value.starts_with('[') && value.ends_with(']') {
                    // Parse array of allowed values
                    let inner = &value[1..value.len() - 1];
                    let allowed: Vec<String> = inner
                        .split(',')
                        .map(|s| s.trim().trim_matches('\'').trim_matches('"').to_string())
                        .filter(|s| !s.is_empty())
                        .collect();
                    result.push((key, Some(allowed)));
                }
            }
        }

        result
    }
}

impl Default for CommodityAttrPlugin {
    fn default() -> Self {
        Self::new()
    }
}

impl NativePlugin for CommodityAttrPlugin {
    fn name(&self) -> &'static str {
        "commodity_attr"
    }

    fn description(&self) -> &'static str {
        "Validate commodity metadata attributes"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        // Parse config if provided
        let required = if let Some(config) = &input.config {
            Self::parse_config(config)
        } else {
            self.required_attrs.clone()
        };

        // If no required attributes configured, pass through
        if required.is_empty() {
            return PluginOutput {
                directives: input.directives,
                errors: Vec::new(),
            };
        }

        let mut errors = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Commodity(comm) = &wrapper.data {
                // Check each required attribute
                for (attr_name, allowed_values) in &required {
                    // Find the attribute in metadata
                    let found = comm.metadata.iter().find(|(k, _)| k == attr_name);

                    match found {
                        None => {
                            errors.push(PluginError::error(format!(
                                "Commodity '{}' missing required attribute '{}'",
                                comm.currency, attr_name
                            )));
                        }
                        Some((_, value)) => {
                            // Check if value is in allowed list (if specified)
                            if let Some(allowed) = allowed_values {
                                let value_str = match value {
                                    crate::types::MetaValueData::String(s) => s.clone(),
                                    other => format!("{other:?}"),
                                };
                                if !allowed.contains(&value_str) {
                                    errors.push(PluginError::error(format!(
                                        "Commodity '{}' attribute '{}' has invalid value '{}' (allowed: {:?})",
                                        comm.currency, attr_name, value_str, allowed
                                    )));
                                }
                            }
                        }
                    }
                }
            }
        }

        PluginOutput {
            directives: input.directives,
            errors,
        }
    }
}

#[cfg(test)]
mod commodity_attr_tests {
    use super::*;
    use crate::types::*;

    #[test]
    fn test_commodity_attr_missing_required() {
        let plugin = CommodityAttrPlugin::new();

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "commodity".to_string(),
                date: "2024-01-01".to_string(),
                data: DirectiveData::Commodity(CommodityData {
                    currency: "AAPL".to_string(),
                    metadata: vec![], // Missing 'name'
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("{'name': null}".to_string()),
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 1);
        assert!(output.errors[0].message.contains("missing required"));
        assert!(output.errors[0].message.contains("name"));
    }

    #[test]
    fn test_commodity_attr_has_required() {
        let plugin = CommodityAttrPlugin::new();

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "commodity".to_string(),
                date: "2024-01-01".to_string(),
                data: DirectiveData::Commodity(CommodityData {
                    currency: "AAPL".to_string(),
                    metadata: vec![("name".to_string(), MetaValueData::String("Apple Inc".to_string()))],
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("{'name': null}".to_string()),
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
    }

    #[test]
    fn test_commodity_attr_invalid_value() {
        let plugin = CommodityAttrPlugin::new();

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "commodity".to_string(),
                date: "2024-01-01".to_string(),
                data: DirectiveData::Commodity(CommodityData {
                    currency: "AAPL".to_string(),
                    metadata: vec![(
                        "sector".to_string(),
                        MetaValueData::String("Healthcare".to_string()),
                    )],
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("{'sector': ['Tech', 'Finance']}".to_string()),
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 1);
        assert!(output.errors[0].message.contains("invalid value"));
        assert!(output.errors[0].message.contains("Healthcare"));
    }

    #[test]
    fn test_commodity_attr_valid_value() {
        let plugin = CommodityAttrPlugin::new();

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "commodity".to_string(),
                date: "2024-01-01".to_string(),
                data: DirectiveData::Commodity(CommodityData {
                    currency: "AAPL".to_string(),
                    metadata: vec![("sector".to_string(), MetaValueData::String("Tech".to_string()))],
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("{'sector': ['Tech', 'Finance']}".to_string()),
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
    }

    #[test]
    fn test_config_parsing() {
        let config = "{'name': null, 'sector': ['Tech', 'Finance']}";
        let parsed = CommodityAttrPlugin::parse_config(config);

        assert_eq!(parsed.len(), 2);
        assert_eq!(parsed[0].0, "name");
        assert!(parsed[0].1.is_none());
        assert_eq!(parsed[1].0, "sector");
        assert_eq!(parsed[1].1.as_ref().unwrap(), &vec!["Tech", "Finance"]);
    }
}

/// Plugin that validates reducing postings use average cost for accounts with NONE booking.
///
/// For accounts with booking method NONE (average cost), when selling/reducing positions,
/// this plugin verifies that the cost basis used matches the calculated average cost
/// within a specified tolerance.
pub struct CheckAverageCostPlugin {
    /// Tolerance for cost comparison (default: 0.01 = 1%).
    tolerance: rust_decimal::Decimal,
}

impl CheckAverageCostPlugin {
    /// Create with default tolerance (1%).
    pub fn new() -> Self {
        Self {
            tolerance: rust_decimal::Decimal::new(1, 2), // 0.01 = 1%
        }
    }

    /// Create with custom tolerance.
    pub const fn with_tolerance(tolerance: rust_decimal::Decimal) -> Self {
        Self { tolerance }
    }
}

impl Default for CheckAverageCostPlugin {
    fn default() -> Self {
        Self::new()
    }
}

impl NativePlugin for CheckAverageCostPlugin {
    fn name(&self) -> &'static str {
        "check_average_cost"
    }

    fn description(&self) -> &'static str {
        "Validate reducing postings match average cost"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        use rust_decimal::Decimal;
        use std::collections::HashMap;
        use std::str::FromStr;

        // Parse optional tolerance from config
        let tolerance = if let Some(config) = &input.config {
            Decimal::from_str(config.trim()).unwrap_or(self.tolerance)
        } else {
            self.tolerance
        };

        // Track average cost per account per commodity
        // Key: (account, commodity) -> (total_units, total_cost)
        let mut inventory: HashMap<(String, String), (Decimal, Decimal)> = HashMap::new();

        let mut errors = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                for posting in &txn.postings {
                    // Only process postings with units and cost
                    let Some(units) = &posting.units else {
                        continue;
                    };
                    let Some(cost) = &posting.cost else {
                        continue;
                    };

                    let units_num = Decimal::from_str(&units.number).unwrap_or_default();
                    let Some(cost_currency) = &cost.currency else {
                        continue;
                    };

                    let key = (posting.account.clone(), units.currency.clone());

                    if units_num > Decimal::ZERO {
                        // Acquisition: add to inventory
                        let cost_per = cost
                            .number_per
                            .as_ref()
                            .and_then(|s| Decimal::from_str(s).ok())
                            .unwrap_or_default();

                        let entry = inventory.entry(key).or_insert((Decimal::ZERO, Decimal::ZERO));
                        entry.0 += units_num; // total units
                        entry.1 += units_num * cost_per; // total cost
                    } else if units_num < Decimal::ZERO {
                        // Reduction: check against average cost
                        let entry = inventory.get(&key);

                        if let Some((total_units, total_cost)) = entry {
                            if *total_units > Decimal::ZERO {
                                let avg_cost = *total_cost / *total_units;

                                // Get the cost used in this posting
                                let used_cost = cost
                                    .number_per
                                    .as_ref()
                                    .and_then(|s| Decimal::from_str(s).ok())
                                    .unwrap_or_default();

                                // Calculate relative difference
                                let diff = (used_cost - avg_cost).abs();
                                let relative_diff = if avg_cost != Decimal::ZERO {
                                    diff / avg_cost
                                } else {
                                    diff
                                };

                                if relative_diff > tolerance {
                                    errors.push(PluginError::warning(format!(
                                        "Sale of {} {} in {} uses cost {} {} but average cost is {} {} (difference: {:.2}%)",
                                        units_num.abs(),
                                        units.currency,
                                        posting.account,
                                        used_cost,
                                        cost_currency,
                                        avg_cost.round_dp(4),
                                        cost_currency,
                                        relative_diff * Decimal::from(100)
                                    )));
                                }

                                // Update inventory
                                let entry = inventory.get_mut(&key).unwrap();
                                let units_sold = units_num.abs();
                                let cost_removed = units_sold * avg_cost;
                                entry.0 -= units_sold;
                                entry.1 -= cost_removed;
                            }
                        }
                    }
                }
            }
        }

        PluginOutput {
            directives: input.directives,
            errors,
        }
    }
}

#[cfg(test)]
mod check_average_cost_tests {
    use super::*;
    use crate::types::*;

    #[test]
    fn test_check_average_cost_matching() {
        let plugin = CheckAverageCostPlugin::new();

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-01".to_string(),
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("100.00".to_string()),
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-02-01".to_string(),
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Sell at avg cost".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "-5".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("100.00".to_string()), // Matches average
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
    }

    #[test]
    fn test_check_average_cost_mismatch() {
        let plugin = CheckAverageCostPlugin::new();

        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-01".to_string(),
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy at 100".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("100.00".to_string()),
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-02-01".to_string(),
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Sell at wrong cost".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "-5".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("90.00".to_string()), // 10% different from avg
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 1);
        assert!(output.errors[0].message.contains("average cost"));
    }

    #[test]
    fn test_check_average_cost_multiple_buys() {
        let plugin = CheckAverageCostPlugin::new();

        // Buy 10 at $100, then 10 at $120 -> avg = $110
        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-01".to_string(),
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy at 100".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("100.00".to_string()),
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-01-15".to_string(),
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Buy at 120".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "10".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("120.00".to_string()),
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
                DirectiveWrapper {
                    directive_type: "transaction".to_string(),
                    date: "2024-02-01".to_string(),
                    data: DirectiveData::Transaction(TransactionData {
                        flag: "*".to_string(),
                        payee: None,
                        narration: "Sell at avg cost".to_string(),
                        tags: vec![],
                        links: vec![],
                        metadata: vec![],
                        postings: vec![PostingData {
                            account: "Assets:Broker".to_string(),
                            units: Some(AmountData {
                                number: "-5".to_string(),
                                currency: "AAPL".to_string(),
                            }),
                            cost: Some(CostData {
                                number_per: Some("110.00".to_string()), // Matches average
                                number_total: None,
                                currency: Some("USD".to_string()),
                                date: None,
                                label: None,
                                merge: false,
                            }),
                            price: None,
                            flag: None,
                            metadata: vec![],
                        }],
                    }),
                },
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
    }
}

/// Plugin that auto-generates currency trading account postings.
///
/// For multi-currency transactions, this plugin adds neutralizing postings
/// to equity accounts like `Equity:CurrencyAccounts:USD` to track currency
/// conversion gains/losses. This enables proper reporting of currency
/// trading activity.
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
        use crate::types::{AmountData, PostingData};
        use rust_decimal::Decimal;
        use std::collections::HashMap;
        use std::str::FromStr;

        // Get base account from config if provided
        let base_account = input
            .config
            .as_ref()
            .map_or_else(|| self.base_account.clone(), |c| c.trim().to_string());

        let mut new_directives: Vec<DirectiveWrapper> = Vec::new();

        for wrapper in &input.directives {
            if let DirectiveData::Transaction(txn) = &wrapper.data {
                // Calculate currency totals for this transaction
                // Map from currency -> total amount in that currency
                let mut currency_totals: HashMap<String, Decimal> = HashMap::new();

                for posting in &txn.postings {
                    if let Some(units) = &posting.units {
                        let amount = Decimal::from_str(&units.number).unwrap_or_default();
                        *currency_totals.entry(units.currency.clone()).or_default() += amount;
                    }
                }

                // If we have multiple currencies with non-zero totals, add balancing postings
                let non_zero_currencies: Vec<_> = currency_totals
                    .iter()
                    .filter(|(_, &total)| total != Decimal::ZERO)
                    .collect();

                if non_zero_currencies.len() > 1 {
                    // Clone the transaction and add currency account postings
                    let mut modified_txn = txn.clone();

                    for (currency, &total) in &non_zero_currencies {
                        // Add posting to currency account to neutralize
                        modified_txn.postings.push(PostingData {
                            account: format!("{}:{}", base_account, currency),
                            units: Some(AmountData {
                                number: (-total).to_string(),
                                currency: (*currency).clone(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        });
                    }

                    new_directives.push(DirectiveWrapper {
                        directive_type: wrapper.directive_type.clone(),
                        date: wrapper.date.clone(),
                        data: DirectiveData::Transaction(modified_txn),
                    });
                } else {
                    // Single currency or balanced - pass through
                    new_directives.push(wrapper.clone());
                }
            } else {
                new_directives.push(wrapper.clone());
            }
        }

        PluginOutput {
            directives: new_directives,
            errors: Vec::new(),
        }
    }
}

#[cfg(test)]
mod currency_accounts_tests {
    use super::*;
    use crate::types::*;

    #[test]
    fn test_currency_accounts_adds_balancing_postings() {
        let plugin = CurrencyAccountsPlugin::new();

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-01-15".to_string(),
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "Currency exchange".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![],
                    postings: vec![
                        PostingData {
                            account: "Assets:Bank:USD".to_string(),
                            units: Some(AmountData {
                                number: "-100".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        },
                        PostingData {
                            account: "Assets:Bank:EUR".to_string(),
                            units: Some(AmountData {
                                number: "85".to_string(),
                                currency: "EUR".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        },
                    ],
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);
        assert_eq!(output.directives.len(), 1);

        if let DirectiveData::Transaction(txn) = &output.directives[0].data {
            // Should have original 2 postings + 2 currency account postings
            assert_eq!(txn.postings.len(), 4);

            // Check for currency account postings
            let usd_posting = txn
                .postings
                .iter()
                .find(|p| p.account == "Equity:CurrencyAccounts:USD");
            assert!(usd_posting.is_some());
            let usd_posting = usd_posting.unwrap();
            // Should neutralize the -100 USD
            assert_eq!(
                usd_posting.units.as_ref().unwrap().number,
                "100"
            );

            let eur_posting = txn
                .postings
                .iter()
                .find(|p| p.account == "Equity:CurrencyAccounts:EUR");
            assert!(eur_posting.is_some());
            let eur_posting = eur_posting.unwrap();
            // Should neutralize the 85 EUR
            assert_eq!(
                eur_posting.units.as_ref().unwrap().number,
                "-85"
            );
        } else {
            panic!("Expected Transaction directive");
        }
    }

    #[test]
    fn test_currency_accounts_single_currency_unchanged() {
        let plugin = CurrencyAccountsPlugin::new();

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-01-15".to_string(),
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "Simple transfer".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![],
                    postings: vec![
                        PostingData {
                            account: "Assets:Bank".to_string(),
                            units: Some(AmountData {
                                number: "-100".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        },
                        PostingData {
                            account: "Expenses:Food".to_string(),
                            units: Some(AmountData {
                                number: "100".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        },
                    ],
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = plugin.process(input);
        assert_eq!(output.errors.len(), 0);

        // Single currency balanced - should not add any postings
        if let DirectiveData::Transaction(txn) = &output.directives[0].data {
            assert_eq!(txn.postings.len(), 2);
        }
    }

    #[test]
    fn test_currency_accounts_custom_base_account() {
        let plugin = CurrencyAccountsPlugin::new();

        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-01-15".to_string(),
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "Exchange".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![],
                    postings: vec![
                        PostingData {
                            account: "Assets:USD".to_string(),
                            units: Some(AmountData {
                                number: "-50".to_string(),
                                currency: "USD".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        },
                        PostingData {
                            account: "Assets:EUR".to_string(),
                            units: Some(AmountData {
                                number: "42".to_string(),
                                currency: "EUR".to_string(),
                            }),
                            cost: None,
                            price: None,
                            flag: None,
                            metadata: vec![],
                        },
                    ],
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("Income:Trading".to_string()),
        };

        let output = plugin.process(input);
        if let DirectiveData::Transaction(txn) = &output.directives[0].data {
            // Check for custom base account
            assert!(txn
                .postings
                .iter()
                .any(|p| p.account.starts_with("Income:Trading:")));
        }
    }
}
