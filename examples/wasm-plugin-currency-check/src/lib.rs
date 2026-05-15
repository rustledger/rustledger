//! Currency Check Plugin
//!
//! This plugin validates currency usage across the ledger:
//! - Warns about currencies used but not declared
//! - Warns about mixed currencies in expense accounts
//! - Enforces operating currency for certain account types
//!
//! This is a **pure validator** — it never modifies, inserts, or
//! deletes directives. All inputs pass through unchanged via
//! [`PluginOutput::passthrough`]; only warnings are emitted.

use rustledger_plugin_types::*;
use std::collections::{HashMap, HashSet};

// ============================================================================
// Required Exports
// ============================================================================

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
        ops: Vec::new(),
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

/// Check currency usage across the ledger.
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

                    // Warn about undeclared currencies
                    if !declared_currencies.is_empty()
                        && !declared_currencies.contains(&units.currency)
                    {
                        errors.push(PluginError::warning(format!(
                            "Currency '{}' used but not declared (date: {}, account: {})",
                            units.currency, wrapper.date, posting.account
                        )));
                    }
                }

                // Check cost currency too
                if let Some(cost) = &posting.cost {
                    if let Some(currency) = &cost.currency {
                        if !declared_currencies.is_empty()
                            && !declared_currencies.contains(currency)
                        {
                            errors.push(PluginError::warning(format!(
                                "Cost currency '{}' not declared (date: {}, account: {})",
                                currency, wrapper.date, posting.account
                            )));
                        }
                    }
                }
            }
        }
    }

    // Warn about accounts with multiple currencies (for expense/income accounts)
    for (account, currencies) in &account_currencies {
        if currencies.len() > 1
            && (account.starts_with("Expenses:") || account.starts_with("Income:"))
        {
            let currency_list: Vec<&str> = currencies.iter().map(|s| s.as_str()).collect();
            errors.push(PluginError::warning(format!(
                "Account '{}' uses multiple currencies: {}",
                account,
                currency_list.join(", ")
            )));
        }
    }

    // Pure validator: pass every input through unchanged.
    let mut output = PluginOutput::passthrough(input.directives.len());
    output.errors = errors;
    output
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detects_undeclared_currency() {
        let input = PluginInput {
            directives: vec![
                DirectiveWrapper {
                    directive_type: String::new(),
                    date: "2024-01-01".to_string(),
                    filename: None,
                    lineno: None,
                    data: DirectiveData::Commodity(CommodityData {
                        currency: "USD".to_string(),
                        metadata: vec![],
                    }),
                },
                DirectiveWrapper {
                    directive_type: String::new(),
                    date: "2024-01-15".to_string(),
                    filename: None,
                    lineno: None,
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

        // Pure validator — every input directive is emitted as Keep.
        assert_eq!(output.ops.len(), 2);
        assert!(matches!(output.ops[0], PluginOp::Keep(0)));
        assert!(matches!(output.ops[1], PluginOp::Keep(1)));

        assert!(
            output.errors.iter().any(|e| e.message.contains("EUR")),
            "Should warn about undeclared EUR"
        );
    }
}
