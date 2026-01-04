//! Currency Check Plugin
//!
//! This plugin validates currency usage across the ledger:
//! - Warns about currencies used but not declared
//! - Warns about mixed currencies in expense accounts
//! - Enforces operating currency for certain account types

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

// Plugin types (matching beancount-plugin/src/types.rs)
#[derive(Debug, Serialize, Deserialize)]
pub struct PluginInput {
    pub directives: Vec<DirectiveWrapper>,
    pub options: PluginOptions,
    pub config: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PluginOutput {
    pub directives: Vec<DirectiveWrapper>,
    pub errors: Vec<PluginError>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PluginOptions {
    pub operating_currencies: Vec<String>,
    pub title: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PluginError {
    pub message: String,
    pub severity: String,
    pub date: Option<String>,
    pub account: Option<String>,
}

impl PluginError {
    pub fn warning(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            severity: "warning".to_string(),
            date: None,
            account: None,
        }
    }

    pub fn with_date(mut self, date: &str) -> Self {
        self.date = Some(date.to_string());
        self
    }

    pub fn with_account(mut self, account: &str) -> Self {
        self.account = Some(account.to_string());
        self
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DirectiveWrapper {
    pub directive_type: String,
    pub date: String,
    pub data: DirectiveData,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum DirectiveData {
    Transaction(TransactionData),
    Commodity(CommodityData),
    Open(OpenData),
    #[serde(other)]
    Other,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransactionData {
    pub flag: String,
    pub payee: Option<String>,
    pub narration: String,
    pub tags: Vec<String>,
    pub links: Vec<String>,
    pub metadata: Vec<(String, serde_json::Value)>,
    pub postings: Vec<PostingData>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PostingData {
    pub account: String,
    pub units: Option<AmountData>,
    pub cost: Option<CostData>,
    pub price: Option<serde_json::Value>,
    pub flag: Option<String>,
    pub metadata: Vec<(String, serde_json::Value)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AmountData {
    pub number: String,
    pub currency: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CostData {
    pub number_per: Option<String>,
    pub number_total: Option<String>,
    pub currency: Option<String>,
    pub date: Option<String>,
    pub label: Option<String>,
    pub merge: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CommodityData {
    pub currency: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OpenData {
    pub account: String,
    pub currencies: Vec<String>,
    pub booking: Option<String>,
}

// Memory management
#[no_mangle]
pub extern "C" fn alloc(size: u32) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(size as usize, 1).unwrap();
    unsafe { std::alloc::alloc(layout) }
}

#[no_mangle]
pub extern "C" fn process(input_ptr: u32, input_len: u32) -> u64 {
    let input_bytes =
        unsafe { std::slice::from_raw_parts(input_ptr as *const u8, input_len as usize) };

    let input: PluginInput = match rmp_serde::from_slice(input_bytes) {
        Ok(i) => i,
        Err(e) => return pack_error(&format!("Deserialization error: {}", e)),
    };

    let output = check_currencies(input);

    let output_bytes = match rmp_serde::to_vec(&output) {
        Ok(b) => b,
        Err(e) => return pack_error(&format!("Serialization error: {}", e)),
    };

    let output_ptr = alloc(output_bytes.len() as u32);
    unsafe {
        std::ptr::copy_nonoverlapping(output_bytes.as_ptr(), output_ptr, output_bytes.len());
    }

    ((output_ptr as u64) << 32) | (output_bytes.len() as u64)
}

fn pack_error(message: &str) -> u64 {
    let output = PluginOutput {
        directives: Vec::new(),
        errors: vec![PluginError {
            message: message.to_string(),
            severity: "error".to_string(),
            date: None,
            account: None,
        }],
    };
    let bytes = rmp_serde::to_vec(&output).unwrap_or_default();
    let ptr = alloc(bytes.len() as u32);
    unsafe {
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), ptr, bytes.len());
    }
    ((ptr as u64) << 32) | (bytes.len() as u64)
}

/// Main plugin logic: check currency usage
fn check_currencies(input: PluginInput) -> PluginOutput {
    let mut errors = Vec::new();

    // Collect declared commodities
    let mut declared_currencies: HashSet<String> = HashSet::new();
    for wrapper in &input.directives {
        if let DirectiveData::Commodity(comm) = &wrapper.data {
            declared_currencies.insert(comm.currency.clone());
        }
    }

    // Operating currencies are always considered declared
    for currency in &input.options.operating_currencies {
        declared_currencies.insert(currency.clone());
    }

    // Track currencies used per account
    let mut account_currencies: HashMap<String, HashSet<String>> = HashMap::new();

    // Check transactions
    for wrapper in &input.directives {
        if let DirectiveData::Transaction(txn) = &wrapper.data {
            for posting in &txn.postings {
                if let Some(units) = &posting.units {
                    // Track currency usage
                    account_currencies
                        .entry(posting.account.clone())
                        .or_default()
                        .insert(units.currency.clone());

                    // Warn about undeclared currencies (if we have any declared)
                    if !declared_currencies.is_empty()
                        && !declared_currencies.contains(&units.currency)
                    {
                        errors.push(
                            PluginError::warning(format!(
                                "Currency '{}' used but not declared as commodity",
                                units.currency
                            ))
                            .with_date(&wrapper.date)
                            .with_account(&posting.account),
                        );
                    }
                }

                // Check cost currency too
                if let Some(cost) = &posting.cost {
                    if let Some(currency) = &cost.currency {
                        if !declared_currencies.is_empty()
                            && !declared_currencies.contains(currency)
                        {
                            errors.push(
                                PluginError::warning(format!(
                                    "Cost currency '{}' not declared as commodity",
                                    currency
                                ))
                                .with_date(&wrapper.date)
                                .with_account(&posting.account),
                            );
                        }
                    }
                }
            }
        }
    }

    // Warn about accounts with multiple currencies (for expense/income accounts)
    for (account, currencies) in &account_currencies {
        if currencies.len() > 1 {
            // Only warn for expense/income accounts
            if account.starts_with("Expenses:") || account.starts_with("Income:") {
                let currency_list: Vec<_> = currencies.iter().collect();
                errors.push(
                    PluginError::warning(format!(
                        "Account '{}' uses multiple currencies: {}",
                        account,
                        currency_list.join(", ")
                    ))
                    .with_account(account),
                );
            }
        }
    }

    PluginOutput {
        directives: input.directives,
        errors,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detects_undeclared_currency() {
        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: "commodity".to_string(),
                    date: "2024-01-01".to_string(),
                    data: DirectiveData::Commodity(CommodityData {
                        currency: "USD".to_string(),
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
                            account: "Expenses:Food".to_string(),
                            units: Some(AmountData {
                                number: "100".to_string(),
                                currency: "EUR".to_string(), // Not declared!
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

        let output = check_currencies(input);

        assert!(
            output.errors.iter().any(|e| e.message.contains("EUR")),
            "Should warn about undeclared EUR"
        );
    }
}
