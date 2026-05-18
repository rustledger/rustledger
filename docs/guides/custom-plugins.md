______________________________________________________________________

## title: Custom Plugins Guide description: How to write custom WASM plugins for rustledger

# Custom Plugins Guide

This guide walks you through creating custom plugins for rustledger using WebAssembly (WASM).

## Overview

WASM plugins let you extend rustledger without modifying its source code. You write your plugin in Rust, compile it to WebAssembly, and reference it in your beancount file.

**Why WASM?**

- **Sandboxed**: Plugins run in isolation, can't access your filesystem or network
- **Portable**: Same binary works on any platform
- **Fast**: Near-native performance after compilation
- **Safe**: Memory-safe by design

## Prerequisites

- Rust toolchain (`rustup`)
- WASM target: `rustup target add wasm32-unknown-unknown`

## Recommended: use `wasm_plugin_main!`

The shortest path to a working plugin is the `wasm_plugin_main!` macro
in `rustledger-plugin-types` (behind the `guest` feature). It generates
the `alloc` + `process` exports from a single user function, eliminating
the ~50 lines of boilerplate the long-form walkthrough below covers.

```toml
# Cargo.toml
[package]
name = "my_plugin"
version = "0.1.0"
edition = "2024"

[lib]
crate-type = ["cdylib"]

[dependencies]
rustledger-plugin-types = { version = "0.15", features = ["guest"] }

[profile.release]
opt-level = "s"
lto = true
strip = true
```

```rust,ignore
// src/lib.rs
use rustledger_plugin_types::{
    DirectiveData, PluginInput, PluginOp, PluginOutput,
    wasm_plugin_main,
};

fn process(input: PluginInput) -> PluginOutput {
    let mut ops = Vec::with_capacity(input.directives.len());
    for (i, mut wrapper) in input.directives.into_iter().enumerate() {
        if let DirectiveData::Transaction(ref mut txn) = wrapper.data {
            txn.tags.push("processed".to_string());
            ops.push(PluginOp::Modify(i, wrapper));
        } else {
            ops.push(PluginOp::Keep(i));
        }
    }
    PluginOutput { ops, errors: vec![] }
}

wasm_plugin_main! {
    process: process,
}
```

Then build and load as in steps 4–5 of the long-form walkthrough below.

> **Invoke the macro once per cdylib crate.** It emits the host-expected
> `alloc` and `process` exports — two invocations cause a duplicate-symbol
> linker error on `wasm32`. Build separate cdylib crates if you need
> multiple plugins.

The walkthrough below shows what the macro expands to and is useful if
you want finer control (custom allocator, hand-rolled msgpack codec,
non-`std` builds). For 95% of plugins, the macro is the right starting
point.

## Quick Start (long form — what the macro expands to)

### 1. Create a New Plugin Project

```bash
cargo new --lib my_plugin
cd my_plugin
```

### 2. Configure Cargo.toml

```toml
[package]
name = "my_plugin"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["cdylib"]

[dependencies]
rmp-serde = "1.3"
serde = { version = "1.0", features = ["derive"] }

[profile.release]
opt-level = "s"      # Optimize for size
lto = true           # Link-time optimization
strip = true         # Strip symbols
```

### 3. Write Your Plugin

```rust
// src/lib.rs
use serde::{Deserialize, Serialize};

// Plugin input structure
#[derive(Deserialize)]
struct PluginInput {
    directives: Vec<Directive>,
    options: Options,
    config: Option<String>,
}

// Plugin output structure
#[derive(Serialize)]
struct PluginOutput {
    /// Ordered ops describing the resulting directive list.
    /// Every input index must appear in exactly one Keep/Modify/Delete.
    ops: Vec<PluginOp>,
    errors: Vec<PluginError>,
}

#[derive(Serialize)]
#[serde(tag = "type")]
enum PluginOp {
    /// Reuse input[i] unchanged (preserves span + file_id).
    Keep(usize),
    /// Replace input[i]'s content with `wrapper`, inheriting its source identity.
    Modify(usize, Directive),
    /// Emit a fresh directive with synthesized location.
    Insert(Directive),
    /// Drop input[i]. Must be explicit.
    Delete(usize),
}

#[derive(Serialize)]
struct PluginError {
    message: String,
    source_file: Option<String>,
    line_number: Option<u32>,
    severity: String,  // "error" or "warning"
}

// Directive types - copy these from the wasm-plugin-template or define your own
// matching the serialization format rustledger uses
#[derive(Deserialize, Serialize, Clone)]
#[serde(tag = "type")]
enum Directive {
    Transaction(Transaction),
    Open(Open),
    Close(Close),
    Balance(Balance),
    Price(Price),
    // ... other directive types
}

#[derive(Deserialize, Serialize, Clone)]
struct Transaction {
    date: String,
    flag: String,
    payee: Option<String>,
    narration: String,
    tags: Vec<String>,
    links: Vec<String>,
    metadata: Vec<(String, MetaValue)>,
    postings: Vec<Posting>,
}

#[derive(Deserialize, Serialize, Clone)]
enum MetaValue {
    String(String),
    Number(String),
    Date(String),
    Account(String),
    Currency(String),
    Tag(String),
    Amount(Amount),
    Boolean(bool),
}

#[derive(Deserialize, Serialize, Clone)]
struct Posting {
    account: String,
    units: Option<Amount>,
    cost: Option<CostSpec>,
    price: Option<Amount>,
    flag: Option<String>,
    metadata: Vec<(String, MetaValue)>,
}

#[derive(Deserialize, Serialize, Clone)]
struct Amount {
    number: String,
    currency: String,
}

#[derive(Deserialize, Serialize, Clone)]
struct CostSpec {
    number_per: Option<String>,
    number_total: Option<String>,
    currency: Option<String>,
    date: Option<String>,
    label: Option<String>,
    merge: bool,
}

#[derive(Deserialize, Serialize, Clone)]
struct Open {
    account: String,
    currencies: Vec<String>,
    booking: Option<String>,
    metadata: Vec<(String, MetaValue)>,
}

#[derive(Deserialize, Serialize, Clone)]
struct Close {
    account: String,
    metadata: Vec<(String, MetaValue)>,
}

#[derive(Deserialize, Serialize, Clone)]
struct Balance {
    account: String,
    amount: Amount,
    tolerance: Option<String>,
    metadata: Vec<(String, MetaValue)>,
}

#[derive(Deserialize, Serialize, Clone)]
struct Price {
    currency: String,
    amount: Amount,
    metadata: Vec<(String, MetaValue)>,
}

#[derive(Deserialize, Serialize, Clone)]
struct Options {
    title: Option<String>,
    operating_currencies: Vec<String>,
}

// Memory allocation for WASM
#[no_mangle]
pub extern "C" fn alloc(size: u32) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(size as usize, 1).unwrap();
    unsafe { std::alloc::alloc(layout) }
}

// Main plugin entry point
#[no_mangle]
pub extern "C" fn process(input_ptr: u32, input_len: u32) -> u64 {
    // Read input
    let input_bytes = unsafe {
        std::slice::from_raw_parts(input_ptr as *const u8, input_len as usize)
    };

    // Deserialize input
    let input: PluginInput = match rmp_serde::from_slice(input_bytes) {
        Ok(i) => i,
        Err(e) => {
            return write_error(&format!("Failed to parse input: {}", e));
        }
    };

    // Process directives
    let output = process_directives(input);

    // Serialize output
    let output_bytes = match rmp_serde::to_vec(&output) {
        Ok(b) => b,
        Err(e) => {
            return write_error(&format!("Failed to serialize output: {}", e));
        }
    };

    // Return pointer and length packed into u64
    let ptr = output_bytes.as_ptr() as u64;
    let len = output_bytes.len() as u64;
    std::mem::forget(output_bytes);
    (ptr << 32) | len
}

fn write_error(message: &str) -> u64 {
    let output = PluginOutput {
        ops: vec![],
        errors: vec![PluginError {
            message: message.to_string(),
            severity: "error".to_string(),
            source_file: None,
            line_number: None,
        }],
    };
    let bytes = rmp_serde::to_vec(&output).unwrap_or_default();
    let ptr = bytes.as_ptr() as u64;
    let len = bytes.len() as u64;
    std::mem::forget(bytes);
    (ptr << 32) | len
}

// Your plugin logic goes here
fn process_directives(input: PluginInput) -> PluginOutput {
    let mut errors = Vec::new();
    let mut ops: Vec<PluginOp> = Vec::with_capacity(input.directives.len());

    let threshold: f64 = input.config
        .as_ref()
        .and_then(|c| c.strip_prefix("threshold="))
        .and_then(|s| s.parse().ok())
        .unwrap_or(10000.0);

    for (i, mut directive) in input.directives.into_iter().enumerate() {
        if let Directive::Transaction(ref mut txn) = directive {
            // Warn about large postings
            for posting in &txn.postings {
                if let Some(units) = &posting.units {
                    if let Ok(amount) = units.number.parse::<f64>() {
                        if amount.abs() > threshold {
                            errors.push(PluginError {
                                message: format!(
                                    "Large transaction: {} {} in {}",
                                    units.number, units.currency, posting.account
                                ),
                                severity: "warning".to_string(),
                                source_file: None,
                                line_number: None,
                            });
                        }
                    }
                }
            }

            // Add a tag to every transaction
            if !txn.tags.contains(&"processed".to_string()) {
                txn.tags.push("processed".to_string());
                ops.push(PluginOp::Modify(i, directive));
            } else {
                ops.push(PluginOp::Keep(i));
            }
        } else {
            ops.push(PluginOp::Keep(i));
        }
    }

    PluginOutput { ops, errors }
}
```

### 4. Build the Plugin

```bash
cargo build --target wasm32-unknown-unknown --release
```

The plugin will be at `target/wasm32-unknown-unknown/release/my_plugin.wasm`.

### 5. Use the Plugin

In your beancount file:

```beancount
plugin "/path/to/my_plugin.wasm" "threshold=5000"

2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD

2024-01-20 * "Car Dealer" "New car"
  Expenses:Transport  25000.00 USD
  Assets:Bank        -25000.00 USD
```

Run rustledger:

```bash
rledger check ledger.beancount
```

Output:

```
warning: Large transaction: 25000.00 USD in Expenses:Transport
  --> ledger.beancount:10
```

## Examples

### Example: Require Tags on Expenses

```rust
fn process_directives(input: PluginInput) -> PluginOutput {
    let mut errors = Vec::new();

    for directive in &input.directives {
        if let Directive::Transaction(txn) = directive {
            // Check if any posting is to an Expenses account
            let has_expense = txn.postings.iter()
                .any(|p| p.account.starts_with("Expenses:"));

            // Require at least one tag on expense transactions
            if has_expense && txn.tags.is_empty() {
                errors.push(PluginError {
                    message: format!(
                        "Expense transaction missing tags: {}",
                        txn.narration
                    ),
                    severity: "error".to_string(),
                    source_file: None,
                    line_number: None,
                });
            }
        }
    }

    // Pure validator: pass every input through unchanged.
    let ops = (0..input.directives.len()).map(PluginOp::Keep).collect();
    PluginOutput { ops, errors }
}
```

### Example: Auto-Generate Metadata

```rust
fn process_directives(input: PluginInput) -> PluginOutput {
    let mut ops = Vec::with_capacity(input.directives.len());

    for (i, mut directive) in input.directives.into_iter().enumerate() {
        if let Directive::Transaction(ref mut txn) = directive {
            // Add review-status metadata if not present
            if !txn.meta.contains_key("review-status") {
                txn.meta.insert(
                    "review-status".to_string(),
                    "pending".to_string(),
                );
                ops.push(PluginOp::Modify(i, directive));
                continue;
            }
        }
        ops.push(PluginOp::Keep(i));
    }

    PluginOutput { ops, errors: vec![] }
}
```

### Example: Currency Validation

```rust
fn process_directives(input: PluginInput) -> PluginOutput {
    let mut errors = Vec::new();

    // Get allowed currencies from options or config
    let allowed: Vec<&str> = input.config
        .as_ref()
        .map(|c| c.split(',').collect())
        .unwrap_or_else(|| vec!["USD", "EUR", "GBP"]);

    for directive in &input.directives {
        if let Directive::Transaction(txn) = directive {
            for posting in &txn.postings {
                if let Some(units) = &posting.units {
                    if !allowed.contains(&units.currency.as_str()) {
                        errors.push(PluginError {
                            message: format!(
                                "Currency {} not in allowed list: {:?}",
                                units.currency, allowed
                            ),
                            severity: "error".to_string(),
                            source_file: None,
                            line_number: None,
                        });
                    }
                }
            }
        }
    }

    // Pure validator: pass every input through unchanged.
    let ops = (0..input.directives.len()).map(PluginOp::Keep).collect();
    PluginOutput { ops, errors }
}
```

## Plugin Interface Reference

### PluginInput

| Field | Type | Description |
|-------|------|-------------|
| `directives` | `Vec<Directive>` | All directives from the ledger |
| `options` | `Options` | Ledger options (title, operating_currency, etc.) |
| `config` | `Option<String>` | Configuration string from plugin directive |

### PluginOutput

| Field | Type | Description |
|-------|------|-------------|
| `ops` | `Vec<PluginOp>` | Ordered Keep/Modify/Insert/Delete ops describing the resulting directive list |
| `errors` | `Vec<PluginError>` | Errors and warnings to report |

### PluginOp

| Variant | Description |
|---------|-------------|
| `Keep(i)` | Reuse `input[i]` unchanged (preserves span + `file_id`) |
| `Modify(i, w)` | Replace `input[i]`'s content with `w`, inheriting its source identity |
| `Insert(w)` | Emit a fresh directive with synthesized location |
| `Delete(i)` | Drop `input[i]` (must be explicit) |

### PluginError

| Field | Type | Description |
|-------|------|-------------|
| `message` | `String` | Human-readable error message |
| `severity` | `String` | `"error"` or `"warning"` |
| `source_file` | `Option<String>` | Source file path (if known) |
| `line_number` | `Option<u32>` | 1-based line number (if known) |

## Testing Your Plugin

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_adds_tag() {
        let input = PluginInput {
            directives: vec![Directive::Transaction(Transaction {
                date: "2024-01-15".to_string(),
                flag: "*".to_string(),
                payee: None,
                narration: "Test".to_string(),
                tags: vec![],
                links: vec![],
                meta: Default::default(),
                postings: vec![],
                source: None,
            })],
            options: Options {
                title: None,
                operating_currency: vec![],
            },
            config: None,
        };

        let output = process_directives(input);

        // The transformer rewrites input[0], so we expect Modify(0, _).
        match &output.ops[0] {
            PluginOp::Modify(0, wrapper) => {
                if let Directive::Transaction(txn) = wrapper {
                    assert!(txn.tags.contains(&"processed".to_string()));
                } else {
                    panic!("expected Transaction");
                }
            }
            other => panic!("expected Modify(0, _), got {:?}", other),
        }
    }
}
```

### Integration Testing

```bash
# Create a test ledger
cat > test.beancount << 'EOF'
plugin "./target/wasm32-unknown-unknown/release/my_plugin.wasm"

2024-01-01 open Assets:Bank USD

2024-01-15 * "Test Transaction"
  Assets:Bank  100.00 USD
  Income:Test -100.00 USD
EOF

# Run rustledger
rledger check test.beancount
```

## Debugging Tips

1. **Return detailed errors**: WASM plugins run in a sandbox without access to stderr, so include context in error messages for debugging:

   ```rust
   errors.push(PluginError {
       message: format!("Account '{}' has {} postings", account, count),
       severity: "warning".to_string(),
       source_file: None,
                                line_number: None,
   });
   ```

1. **Test incrementally**: Start with a minimal plugin and add features one at a time.

## Performance Tips

1. **Minimize allocations**: Reuse vectors when possible
1. **Use `&str` over `String`**: For comparisons and lookups
1. **Optimize for size**: Use `opt-level = "s"` in release profile
1. **Enable LTO**: Link-time optimization reduces binary size

## More Examples

See the rustledger repository for more examples:

- [`examples/wasm-plugin`](https://github.com/rustledger/rustledger/tree/main/examples/wasm-plugin) - Basic example
- [`examples/wasm-plugin-currency-check`](https://github.com/rustledger/rustledger/tree/main/examples/wasm-plugin-currency-check) - Currency validation
- [`examples/wasm-plugin-duplicate-detect`](https://github.com/rustledger/rustledger/tree/main/examples/wasm-plugin-duplicate-detect) - Duplicate detection
- [`examples/wasm-plugin-template`](https://github.com/rustledger/rustledger/tree/main/examples/wasm-plugin-template) - Starter template

## See Also

- [Plugins Reference](../reference/plugins.md) - Built-in plugins and architecture
- [Contributing Plugins](../development/contributing-plugins.md) - Adding native plugins to rustledger
