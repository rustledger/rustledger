//! Example WASM plugin for ironcount.
//!
//! This plugin adds a "processed" tag to all transactions.
//!
//! Build with:
//! ```sh
//! cargo build --target wasm32-unknown-unknown --release
//! ```
//!
//! The output will be in `target/wasm32-unknown-unknown/release/example_plugin.wasm`

use serde::{Deserialize, Serialize};
use std::alloc::Layout;

// Plugin data types (must match beancount-plugin types)

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
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PostingData {
    pub account: String,
    pub units: Option<AmountData>,
    pub cost: Option<CostData>,
    pub price: Option<AmountData>,
    pub flag: Option<String>,
    pub metadata: Vec<(String, MetaValue)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MetaValue {
    String(String),
    Number(String),
    Date(String),
    Account(String),
    Currency(String),
    Tag(String),
    Amount(AmountData),
    Boolean(bool),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransactionData {
    pub flag: String,
    pub payee: Option<String>,
    pub narration: String,
    pub tags: Vec<String>,
    pub links: Vec<String>,
    pub metadata: Vec<(String, MetaValue)>,
    pub postings: Vec<PostingData>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DirectiveData {
    Transaction(TransactionData),
    // Other directive types...
    Other,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DirectiveWrapper {
    pub directive_type: String,
    pub date: String,
    pub data: DirectiveData,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginOptions {
    pub operating_currencies: Vec<String>,
    pub title: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginInput {
    pub directives: Vec<DirectiveWrapper>,
    pub options: PluginOptions,
    pub config: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginError {
    pub message: String,
    pub source_file: Option<String>,
    pub line_number: Option<u32>,
    pub severity: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginOutput {
    pub directives: Vec<DirectiveWrapper>,
    pub errors: Vec<PluginError>,
}

// Memory allocation for the host to write input data

#[no_mangle]
pub extern "C" fn alloc(size: u32) -> *mut u8 {
    let layout = Layout::from_size_align(size as usize, 1).unwrap();
    unsafe { std::alloc::alloc(layout) }
}

// Main plugin entry point

#[no_mangle]
pub extern "C" fn process(input_ptr: u32, input_len: u32) -> u64 {
    // Read input from memory
    let input_bytes = unsafe {
        std::slice::from_raw_parts(input_ptr as *const u8, input_len as usize)
    };

    // Deserialize input
    let input: PluginInput = match rmp_serde::from_slice(input_bytes) {
        Ok(i) => i,
        Err(e) => {
            return error_result(&format!("Failed to deserialize input: {}", e));
        }
    };

    // Process directives
    let output = process_directives(input);

    // Serialize output
    let output_bytes = match rmp_serde::to_vec(&output) {
        Ok(b) => b,
        Err(e) => {
            return error_result(&format!("Failed to serialize output: {}", e));
        }
    };

    // Allocate space for output and copy
    let output_ptr = alloc(output_bytes.len() as u32);
    unsafe {
        std::ptr::copy_nonoverlapping(
            output_bytes.as_ptr(),
            output_ptr,
            output_bytes.len(),
        );
    }

    // Return packed pointer and length
    ((output_ptr as u64) << 32) | (output_bytes.len() as u64)
}

fn error_result(message: &str) -> u64 {
    let output = PluginOutput {
        directives: vec![],
        errors: vec![PluginError {
            message: message.to_string(),
            source_file: None,
            line_number: None,
            severity: "error".to_string(),
        }],
    };

    let output_bytes = rmp_serde::to_vec(&output).unwrap_or_default();
    let output_ptr = alloc(output_bytes.len() as u32);
    unsafe {
        std::ptr::copy_nonoverlapping(
            output_bytes.as_ptr(),
            output_ptr,
            output_bytes.len(),
        );
    }

    ((output_ptr as u64) << 32) | (output_bytes.len() as u64)
}

/// Main processing logic - customize this!
fn process_directives(input: PluginInput) -> PluginOutput {
    let mut directives = Vec::new();

    for mut wrapper in input.directives {
        // Add "processed" tag to all transactions
        if wrapper.directive_type == "transaction" {
            if let DirectiveData::Transaction(ref mut txn) = wrapper.data {
                if !txn.tags.contains(&"processed".to_string()) {
                    txn.tags.push("processed".to_string());
                }
            }
        }
        directives.push(wrapper);
    }

    PluginOutput {
        directives,
        errors: vec![],
    }
}
