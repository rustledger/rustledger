//! Duplicate Transaction Detector Plugin
//!
//! This plugin detects potentially duplicate transactions by comparing:
//! - Same date
//! - Same payee (if present)
//! - Same amount
//!
//! Configure with: "days=N" to look for duplicates within N days (default 3)

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

// Plugin types
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
    pub cost: Option<serde_json::Value>,
    pub price: Option<serde_json::Value>,
    pub flag: Option<String>,
    pub metadata: Vec<(String, serde_json::Value)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AmountData {
    pub number: String,
    pub currency: String,
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

    let output = detect_duplicates(input);

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

/// Transaction fingerprint for duplicate detection
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct TxnFingerprint {
    payee: Option<String>,
    amount: String, // First posting amount as string
    currency: String,
}

/// Parse date string to (year, month, day)
fn parse_date(date: &str) -> Option<(i32, u32, u32)> {
    let parts: Vec<&str> = date.split('-').collect();
    if parts.len() != 3 {
        return None;
    }
    let year: i32 = parts[0].parse().ok()?;
    let month: u32 = parts[1].parse().ok()?;
    let day: u32 = parts[2].parse().ok()?;
    Some((year, month, day))
}

/// Calculate days between two dates (approximate)
fn days_between(date1: &str, date2: &str) -> i32 {
    let d1 = parse_date(date1);
    let d2 = parse_date(date2);

    match (d1, d2) {
        (Some((y1, m1, d1)), Some((y2, m2, d2))) => {
            // Simple approximation: assume 30 days per month
            let days1 = y1 * 365 + m1 as i32 * 30 + d1 as i32;
            let days2 = y2 * 365 + m2 as i32 * 30 + d2 as i32;
            (days1 - days2).abs()
        }
        _ => i32::MAX,
    }
}

/// Main plugin logic: detect duplicate transactions
fn detect_duplicates(input: PluginInput) -> PluginOutput {
    let mut errors = Vec::new();

    // Parse config for duplicate window (default 3 days)
    let day_window: i32 = input
        .config
        .as_ref()
        .and_then(|c| c.strip_prefix("days="))
        .and_then(|s| s.parse().ok())
        .unwrap_or(3);

    // Collect all transactions with their fingerprints
    let mut transactions: Vec<(String, TxnFingerprint, &str)> = Vec::new();

    for wrapper in &input.directives {
        if let DirectiveData::Transaction(txn) = &wrapper.data {
            // Skip flagged transactions (already reconciled)
            if txn.flag == "!" {
                continue;
            }

            // Create fingerprint from first posting with amount
            if let Some(posting) = txn.postings.iter().find(|p| p.units.is_some()) {
                if let Some(units) = &posting.units {
                    let fingerprint = TxnFingerprint {
                        payee: txn.payee.clone(),
                        amount: units.number.clone(),
                        currency: units.currency.clone(),
                    };
                    transactions.push((wrapper.date.clone(), fingerprint, &txn.narration));
                }
            }
        }
    }

    // Compare all pairs looking for potential duplicates
    let mut reported: std::collections::HashSet<(usize, usize)> = std::collections::HashSet::new();

    for i in 0..transactions.len() {
        for j in (i + 1)..transactions.len() {
            let (date1, fp1, narr1) = &transactions[i];
            let (date2, fp2, narr2) = &transactions[j];

            // Check if within day window
            if days_between(date1, date2) > day_window {
                continue;
            }

            // Check if fingerprints match
            if fp1 == fp2 {
                let key = (i.min(j), i.max(j));
                if !reported.contains(&key) {
                    reported.insert(key);
                    errors.push(
                        PluginError::warning(format!(
                            "Potential duplicate: '{}' on {} and '{}' on {} \
                             (same payee {:?}, amount {} {})",
                            narr1, date1, narr2, date2, fp1.payee, fp1.amount, fp1.currency
                        ))
                        .with_date(date1),
                    );
                }
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

    fn make_transaction(date: &str, payee: Option<&str>, narration: &str, amount: &str) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: date.to_string(),
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: payee.map(String::from),
                narration: narration.to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![PostingData {
                    account: "Expenses:Test".to_string(),
                    units: Some(AmountData {
                        number: amount.to_string(),
                        currency: "USD".to_string(),
                    }),
                    cost: None,
                    price: None,
                    flag: None,
                    metadata: vec![],
                }],
            }),
        }
    }

    #[test]
    fn test_detects_duplicate() {
        let input = PluginInput {
            directives: vec![
                make_transaction("2024-01-15", Some("Store"), "Purchase 1", "50.00"),
                make_transaction("2024-01-15", Some("Store"), "Purchase 2", "50.00"),
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = detect_duplicates(input);

        assert!(!output.errors.is_empty(), "Should detect duplicate");
        assert!(output.errors[0].message.contains("Potential duplicate"));
    }

    #[test]
    fn test_no_false_positive_different_amount() {
        let input = PluginInput {
            directives: vec![
                make_transaction("2024-01-15", Some("Store"), "Purchase 1", "50.00"),
                make_transaction("2024-01-15", Some("Store"), "Purchase 2", "75.00"),
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: None,
        };

        let output = detect_duplicates(input);

        assert!(output.errors.is_empty(), "Different amounts should not be duplicates");
    }

    #[test]
    fn test_respects_day_window() {
        let input = PluginInput {
            directives: vec![
                make_transaction("2024-01-01", Some("Store"), "Purchase 1", "50.00"),
                make_transaction("2024-01-10", Some("Store"), "Purchase 2", "50.00"),
            ],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("days=3".to_string()), // Only 3 day window
        };

        let output = detect_duplicates(input);

        assert!(output.errors.is_empty(), "10 days apart should not be flagged with 3-day window");
    }
}
