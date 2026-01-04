//! Example WASM Plugin for Ironcount
//!
//! This plugin demonstrates how to create a WASM plugin that:
//! 1. Receives directives from the host
//! 2. Processes them (adds tags, validates, generates new directives)
//! 3. Returns modified directives and any errors
//!
//! # Building
//!
//! ```bash
//! # Install WASM target
//! rustup target add wasm32-unknown-unknown
//!
//! # Build the plugin
//! cargo build --target wasm32-unknown-unknown --release
//!
//! # The plugin will be at:
//! # target/wasm32-unknown-unknown/release/example_plugin.wasm
//! ```
//!
//! # Using with ironcount
//!
//! ```beancount
//! plugin "path/to/example_plugin.wasm"
//!
//! 2024-01-01 open Assets:Bank USD
//! ```

use serde::{Deserialize, Serialize};

// ============================================================================
// Plugin Interface Types
// These must match the types in beancount-plugin/src/types.rs
// ============================================================================

/// Input to the plugin from the host.
#[derive(Debug, Serialize, Deserialize)]
pub struct PluginInput {
    /// All directives to process.
    pub directives: Vec<DirectiveWrapper>,
    /// Global options.
    pub options: PluginOptions,
    /// Plugin configuration string (from plugin directive).
    pub config: Option<String>,
}

/// Output from the plugin.
#[derive(Debug, Serialize, Deserialize)]
pub struct PluginOutput {
    /// Modified/generated directives.
    pub directives: Vec<DirectiveWrapper>,
    /// Any errors or warnings.
    pub errors: Vec<PluginError>,
}

/// Global options passed to plugins.
#[derive(Debug, Serialize, Deserialize)]
pub struct PluginOptions {
    /// Operating currencies.
    pub operating_currencies: Vec<String>,
    /// Ledger title.
    pub title: Option<String>,
}

/// A plugin error or warning.
#[derive(Debug, Serialize, Deserialize)]
pub struct PluginError {
    /// Error message.
    pub message: String,
    /// Severity level.
    pub severity: String,
    /// Associated date (if any).
    pub date: Option<String>,
    /// Associated account (if any).
    pub account: Option<String>,
}

impl PluginError {
    pub fn error(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            severity: "error".to_string(),
            date: None,
            account: None,
        }
    }

    pub fn warning(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            severity: "warning".to_string(),
            date: None,
            account: None,
        }
    }
}

/// Wrapper around a directive for serialization.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DirectiveWrapper {
    /// Directive type name.
    pub directive_type: String,
    /// Directive date.
    pub date: String,
    /// Directive data.
    pub data: DirectiveData,
}

/// Directive-specific data.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum DirectiveData {
    Transaction(TransactionData),
    Balance(BalanceData),
    Open(OpenData),
    Close(CloseData),
    Commodity(CommodityData),
    Pad(PadData),
    Event(EventData),
    Note(NoteData),
    Document(DocumentData),
    Price(PriceData),
    Query(QueryData),
    Custom(CustomData),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransactionData {
    pub flag: String,
    pub payee: Option<String>,
    pub narration: String,
    pub tags: Vec<String>,
    pub links: Vec<String>,
    pub metadata: Vec<(String, MetaValueData)>,
    pub postings: Vec<PostingData>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PostingData {
    pub account: String,
    pub units: Option<AmountData>,
    pub cost: Option<CostData>,
    pub price: Option<PriceAnnotationData>,
    pub flag: Option<String>,
    pub metadata: Vec<(String, MetaValueData)>,
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
pub struct PriceAnnotationData {
    pub is_total: bool,
    pub amount: Option<AmountData>,
    pub number: Option<String>,
    pub currency: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum MetaValueData {
    String(String),
    Number(String),
    Date(String),
    Account(String),
    Currency(String),
    Tag(String),
    Link(String),
    Amount(AmountData),
    Bool(bool),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BalanceData {
    pub account: String,
    pub amount: AmountData,
    pub tolerance: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OpenData {
    pub account: String,
    pub currencies: Vec<String>,
    pub booking: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CloseData {
    pub account: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CommodityData {
    pub currency: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PadData {
    pub account: String,
    pub source_account: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EventData {
    pub event_type: String,
    pub value: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NoteData {
    pub account: String,
    pub comment: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocumentData {
    pub account: String,
    pub path: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PriceData {
    pub currency: String,
    pub amount: AmountData,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueryData {
    pub name: String,
    pub query: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CustomData {
    pub custom_type: String,
    pub values: Vec<String>,
}

// ============================================================================
// Memory Management for WASM
// ============================================================================

/// Allocate memory in WASM linear memory.
/// Called by the host to reserve space for input data.
#[no_mangle]
pub extern "C" fn alloc(size: u32) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(size as usize, 1).unwrap();
    unsafe { std::alloc::alloc(layout) }
}

/// Free memory in WASM linear memory.
#[no_mangle]
pub extern "C" fn dealloc(ptr: *mut u8, size: u32) {
    let layout = std::alloc::Layout::from_size_align(size as usize, 1).unwrap();
    unsafe { std::alloc::dealloc(ptr, layout) }
}

// ============================================================================
// Plugin Entry Point
// ============================================================================

/// Process directives.
///
/// This is the main entry point called by the host.
///
/// # Arguments
/// * `input_ptr` - Pointer to MessagePack-encoded PluginInput
/// * `input_len` - Length of input data
///
/// # Returns
/// Packed u64: (output_ptr << 32) | output_len
#[no_mangle]
pub extern "C" fn process(input_ptr: u32, input_len: u32) -> u64 {
    // Read input from WASM memory
    let input_bytes =
        unsafe { std::slice::from_raw_parts(input_ptr as *const u8, input_len as usize) };

    // Deserialize input
    let input: PluginInput = match rmp_serde::from_slice(input_bytes) {
        Ok(i) => i,
        Err(e) => {
            return pack_error(&format!("Failed to deserialize input: {}", e));
        }
    };

    // Process the directives
    let output = process_directives(input);

    // Serialize output
    let output_bytes = match rmp_serde::to_vec(&output) {
        Ok(b) => b,
        Err(e) => {
            return pack_error(&format!("Failed to serialize output: {}", e));
        }
    };

    // Allocate output buffer
    let output_ptr = alloc(output_bytes.len() as u32);
    unsafe {
        std::ptr::copy_nonoverlapping(output_bytes.as_ptr(), output_ptr, output_bytes.len());
    }

    // Pack pointer and length into u64
    ((output_ptr as u64) << 32) | (output_bytes.len() as u64)
}

/// Helper to return an error result.
fn pack_error(message: &str) -> u64 {
    let output = PluginOutput {
        directives: Vec::new(),
        errors: vec![PluginError::error(message)],
    };
    let bytes = rmp_serde::to_vec(&output).unwrap_or_default();
    let ptr = alloc(bytes.len() as u32);
    unsafe {
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), ptr, bytes.len());
    }
    ((ptr as u64) << 32) | (bytes.len() as u64)
}

// ============================================================================
// Plugin Logic
// ============================================================================

/// Main plugin processing logic.
///
/// This example plugin:
/// 1. Adds a "processed" tag to all transactions
/// 2. Validates that expense accounts have expense tags
/// 3. Generates warnings for large transactions
fn process_directives(input: PluginInput) -> PluginOutput {
    let mut directives = Vec::new();
    let mut errors = Vec::new();

    // Parse config (example: "threshold=1000")
    let threshold: f64 = input
        .config
        .as_ref()
        .and_then(|c| {
            c.strip_prefix("threshold=")
                .and_then(|s| s.parse().ok())
        })
        .unwrap_or(1000.0);

    for mut wrapper in input.directives {
        if wrapper.directive_type == "transaction" {
            if let DirectiveData::Transaction(ref mut txn) = wrapper.data {
                // Add "processed" tag
                if !txn.tags.contains(&"processed".to_string()) {
                    txn.tags.push("processed".to_string());
                }

                // Check for large transactions
                for posting in &txn.postings {
                    if let Some(ref units) = posting.units {
                        if let Ok(amount) = units.number.parse::<f64>() {
                            if amount.abs() > threshold {
                                errors.push(PluginError::warning(format!(
                                    "Large transaction: {} {} in {} (threshold: {})",
                                    units.number, units.currency, posting.account, threshold
                                )));
                            }
                        }
                    }

                    // Check expense accounts have expense-related tags
                    if posting.account.starts_with("Expenses:") {
                        let has_expense_tag = txn.tags.iter().any(|t| {
                            t == "expense" || t == "deductible" || t == "business"
                        });
                        if !has_expense_tag && txn.tags.len() <= 1 {
                            // Only "processed" tag
                            errors.push(PluginError::warning(format!(
                                "Expense transaction without category tag: {}",
                                txn.narration
                            )));
                        }
                    }
                }
            }
        }

        directives.push(wrapper);
    }

    PluginOutput { directives, errors }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_process_adds_tag() {
        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-01-15".to_string(),
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: Some("Coffee Shop".to_string()),
                    narration: "Morning coffee".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![],
                    postings: vec![
                        PostingData {
                            account: "Expenses:Food:Coffee".to_string(),
                            units: Some(AmountData {
                                number: "5.00".to_string(),
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
                                number: "-5.00".to_string(),
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

        let output = process_directives(input);

        assert_eq!(output.directives.len(), 1);
        if let DirectiveData::Transaction(txn) = &output.directives[0].data {
            assert!(txn.tags.contains(&"processed".to_string()));
        } else {
            panic!("Expected transaction");
        }
    }

    #[test]
    fn test_large_transaction_warning() {
        let input = PluginInput {
            directives: vec![DirectiveWrapper {
                directive_type: "transaction".to_string(),
                date: "2024-01-15".to_string(),
                data: DirectiveData::Transaction(TransactionData {
                    flag: "*".to_string(),
                    payee: None,
                    narration: "Big purchase".to_string(),
                    tags: vec![],
                    links: vec![],
                    metadata: vec![],
                    postings: vec![PostingData {
                        account: "Expenses:Shopping".to_string(),
                        units: Some(AmountData {
                            number: "5000.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                    }],
                }),
            }],
            options: PluginOptions {
                operating_currencies: vec!["USD".to_string()],
                title: None,
            },
            config: Some("threshold=1000".to_string()),
        };

        let output = process_directives(input);

        // Should have a warning about large transaction
        assert!(output.errors.iter().any(|e| e.message.contains("Large transaction")));
    }
}
