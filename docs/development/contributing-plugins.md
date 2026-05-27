______________________________________________________________________

## title: Contributing Plugins description: How to add native Rust plugins to rustledger

# Contributing Native Plugins

This guide explains how to add new native Rust plugins to rustledger itself.

::: tip For Custom Plugins
If you want to write a plugin for your own use without modifying rustledger, see the [Custom Plugins Guide](../guides/custom-plugins.md) for WASM plugins.
:::

## When to Add a Native Plugin

Add a native plugin when:

- The functionality is generally useful to many users
- You want to contribute to rustledger
- Maximum performance is critical
- The plugin implements a Python beancount plugin for compatibility

## Plugin Architecture

Native plugins live in `crates/rustledger-plugin/src/native/plugins/`:

```
crates/rustledger-plugin/
├── src/
│   ├── lib.rs
│   ├── types.rs           # PluginInput, PluginOutput, DirectiveWrapper, etc.
│   └── native/
│       ├── mod.rs         # NativePlugin trait + NativePluginRegistry
│       └── plugins/
│           ├── mod.rs     # Plugin exports
│           ├── auto_accounts.rs
│           ├── implicit_prices.rs
│           ├── no_duplicates.rs
│           └── your_plugin.rs  # Your new plugin
```

## Step-by-Step Guide

### 1. Create the Plugin File

Create a new file in `crates/rustledger-plugin/src/native/plugins/`:

````rust
// crates/rustledger-plugin/src/native/plugins/my_plugin.rs

use crate::native::{NativePlugin, RegularPlugin};
use crate::types::{PluginError, PluginErrorSeverity, PluginInput, PluginOp, PluginOutput};

/// My Plugin - brief description.
///
/// Longer description explaining what the plugin does,
/// when to use it, and any configuration options.
///
/// # Example
///
/// ```beancount
/// plugin "beancount.plugins.my_plugin" "optional_config"
/// ```
pub struct MyPlugin;

impl NativePlugin for MyPlugin {
    fn name(&self) -> &'static str {
        "my_plugin"
    }

    fn description(&self) -> &'static str {
        "Brief description of what the plugin does"
    }

    fn process(&self, input: PluginInput) -> PluginOutput {
        let errors = Vec::new();

        // Your plugin logic here
        // Access config via: input.config
        // Access options via: input.options
        //
        // Emit ops describing the resulting directive list:
        //   PluginOp::Keep(i)         — reuse input[i] unchanged
        //   PluginOp::Modify(i, w)    — replace input[i]'s content
        //   PluginOp::Insert(w)       — append a synthesized directive
        //   PluginOp::Delete(i)       — drop input[i] (must be explicit)

        // Pure-validator default: pass everything through unchanged.
        let ops = (0..input.directives.len()).map(PluginOp::Keep).collect();
        PluginOutput { ops, errors }
    }
}

// Mark the plugin's pass — runs post-booking, like most plugins.
// If your plugin synthesizes directives (e.g. injected `Open`s) that the
// loader's pre-booking Early validation depends on, implement `SynthPlugin`
// instead.
impl RegularPlugin for MyPlugin {}
````

### 2. Register the Plugin

Add your plugin to `crates/rustledger-plugin/src/native/plugins/mod.rs`:

```rust
// Add the module
mod my_plugin;

// Re-export
pub use my_plugin::MyPlugin;
```

Then register it in `crates/rustledger-plugin/src/native/mod.rs`. The registry
is a `LazyLock<NativePluginRegistry>` singleton initialized from two
separately-typed `Vec`s, one per pass — add your plugin to the
`regular` Vec (or `synth`, if it implements `SynthPlugin`):

```rust
static GLOBAL_REGISTRY: LazyLock<NativePluginRegistry> = LazyLock::new(|| {
    let synth: Vec<Box<dyn SynthPlugin>> = vec![
        Box::new(AutoAccountsPlugin),
        // ... other synth plugins ...
    ];
    let regular: Vec<Box<dyn RegularPlugin>> = vec![
        // ... existing regular plugins ...
        Box::new(ImplicitPricesPlugin),
        Box::new(CheckCommodityPlugin),
        // Add your plugin to the appropriate list
        Box::new(MyPlugin),
    ];
    NativePluginRegistry { synth, regular }
});
```

### 3. Prefix Aliases (Automatic)

Plugin name lookups automatically strip well-known prefixes — short
names (`"my_plugin"`) and fully-qualified module paths
(`"beancount.plugins.my_plugin"`, `"beancount_reds_plugins.my_plugin.my_plugin"`)
both resolve through the same `find_synth` / `find_regular` calls.
No explicit alias registration is needed.

### 4. Write Tests

Add tests in your plugin file:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::*;

    fn make_transaction(narration: &str) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-01-15".to_string(),
            filename: Some("test.beancount".to_string()),
            lineno: Some(1),
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: narration.to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![],
            }),
        }
    }

    #[test]
    fn test_basic_functionality() {
        let plugin = MyPlugin;
        let input = PluginInput {
            directives: vec![make_transaction("Test")],
            options: PluginOptions::default(),
            config: None,
        };

        let output = plugin.process(input);

        assert!(output.errors.is_empty());
        // Pure validator passes through every input as Keep.
        assert_eq!(output.ops.len(), 1);
        assert!(matches!(output.ops[0], PluginOp::Keep(0)));
    }

    #[test]
    fn test_with_config() {
        let plugin = MyPlugin;
        let input = PluginInput {
            directives: vec![],
            options: PluginOptions::default(),
            config: Some("threshold=100".to_string()),
        };

        let output = plugin.process(input);
        // Assert based on config
    }

    #[test]
    fn test_error_case() {
        let plugin = MyPlugin;
        // Create input that should trigger an error
        let input = PluginInput {
            directives: vec![make_transaction("problematic")],
            options: PluginOptions::default(),
            config: None,
        };

        let output = plugin.process(input);

        assert!(!output.errors.is_empty());
        assert_eq!(output.errors[0].severity, PluginErrorSeverity::Error);
    }
}
```

### 5. Add Integration Tests

Add integration tests in `crates/rustledger-plugin/tests/`:

```rust
// crates/rustledger-plugin/tests/my_plugin_test.rs

use rustledger_plugin::types::*;
use rustledger_plugin::{NativePlugin, NativePluginRegistry};

// Helper to create test input
fn make_input(directives: Vec<DirectiveWrapper>) -> PluginInput {
    PluginInput {
        directives,
        options: PluginOptions {
            operating_currencies: vec!["USD".to_string()],
            title: None,
        },
        config: None,
    }
}

fn make_transaction(date: &str, narration: &str) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "transaction".to_string(),
        date: date.to_string(),
        filename: Some("test.beancount".to_string()),
        lineno: Some(1),
        data: DirectiveData::Transaction(TransactionData {
            flag: "*".to_string(),
            payee: None,
            narration: narration.to_string(),
            tags: vec![],
            links: vec![],
            metadata: vec![],
            postings: vec![],
        }),
    }
}

#[test]
fn test_my_plugin_integration() {
    // Process-wide singleton — no allocation per call.
    let registry = NativePluginRegistry::global();
    // `find_regular` returns `Option<&dyn RegularPlugin>` — the type
    // system guarantees we won't accidentally invoke a synth-pass
    // plugin in a regular-pass test (and vice versa for `find_synth`).
    let plugin = registry
        .find_regular("my_plugin")
        .expect("plugin should exist");

    let input = make_input(vec![
        make_transaction("2024-01-15", "Test transaction"),
    ]);

    let output = plugin.process(input);

    // Verify no errors
    assert!(output.errors.is_empty(), "expected no errors");

    // Verify every input directive was accounted for in the op list.
    assert_eq!(output.ops.len(), 1);
}
```

## The NativePlugin Trait

```rust
pub trait NativePlugin: Send + Sync {
    /// Plugin identifier (used in `plugin "name"`)
    fn name(&self) -> &'static str;

    /// Human-readable description
    fn description(&self) -> &'static str;

    /// Process directives and return results
    fn process(&self, input: PluginInput) -> PluginOutput;
}
```

## Working with Directives

::: info Plugin Types vs Core Types
Plugins receive `DirectiveWrapper` with `DirectiveData` (from `crate::types`), not `rustledger_core::Directive`. These wrapper types use strings for dates and decimals to simplify serialization. See `crates/rustledger-plugin/src/types.rs` for the complete type definitions.
:::

### Iterating Over Directives

```rust
use crate::types::{DirectiveWrapper, DirectiveData, TransactionData};

for wrapper in &input.directives {
    match &wrapper.data {
        DirectiveData::Transaction(txn) => {
            // txn.flag, txn.payee, txn.narration, txn.postings, etc.
        }
        DirectiveData::Open(open) => {
            // open.account, open.currencies, open.booking
        }
        DirectiveData::Close(close) => {
            // close.account
        }
        DirectiveData::Balance(bal) => {
            // bal.account, bal.amount
        }
        DirectiveData::Price(price) => {
            // price.currency, price.amount
        }
        _ => {}
    }
}
```

### Modifying Directives

Emit `PluginOp::Modify(i, wrapper)` for every input index you change,
and `PluginOp::Keep(i)` for the rest. `Modify` inherits the original
directive's span and `file_id` so errors keep pointing at the source.

```rust
fn process(&self, input: PluginInput) -> PluginOutput {
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
```

### Adding New Directives

Keep every input index and append `PluginOp::Insert(wrapper)` for each
synthesized directive. Inserted directives get `SYNTHESIZED_FILE_ID`
and a zero span. If your plugin synthesizes `Open` or `Document`
directives that the loader's pre-booking Early validation depends on,
implement `SynthPlugin` (instead of `RegularPlugin`) so the loader runs it
in the synth pass:

```rust
impl SynthPlugin for MyPlugin {}
```

Implement exactly one of `SynthPlugin` or `RegularPlugin` — the registry's
typed `Vec`s reject anything else at compile time.

```rust
fn process(&self, input: PluginInput) -> PluginOutput {
    let mut ops: Vec<PluginOp> =
        (0..input.directives.len()).map(PluginOp::Keep).collect();

    // Generate new directives using wrapper types
    let new_price = DirectiveWrapper {
        directive_type: String::new(),
        date: "2024-01-15".to_string(),
        filename: None,
        lineno: None,
        data: DirectiveData::Price(PriceData {
            currency: "AAPL".to_string(),
            amount: AmountData {
                number: "150.00".to_string(),
                currency: "USD".to_string(),
            },
            metadata: vec![],
        }),
    };
    ops.push(PluginOp::Insert(new_price));

    PluginOutput { ops, errors: vec![] }
}
```

### Reporting Errors

```rust
use crate::types::{PluginError, PluginErrorSeverity};

fn process(&self, input: PluginInput) -> PluginOutput {
    let mut errors = Vec::new();

    for directive in &input.directives {
        if let DirectiveData::Transaction(txn) = &directive.data {
            if txn.postings.is_empty() {
                errors.push(PluginError::error("Transaction has no postings"));
            }
        }
    }

    // Pure validator: pass every input through unchanged.
    let ops = (0..input.directives.len()).map(PluginOp::Keep).collect();
    PluginOutput { ops, errors }
}
```

## Best Practices

### Performance

1. **Avoid cloning when possible**: Use references and iterators
1. **Early returns**: Skip directives that don't need processing
1. **Batch operations**: Collect changes before applying

```rust
// Good: Filter first, then process
let transactions: Vec<_> = input.directives
    .iter()
    .filter_map(|d| match d {
        Directive::Transaction(t) => Some(t),
        _ => None,
    })
    .collect();

// Process only relevant directives
for txn in &transactions {
    // ...
}
```

### Error Messages

Write clear, actionable error messages:

```rust
// Good - use builder methods and include context
PluginError::error(format!(
    "Account '{}' uses currency {} but was opened with {:?}",
    posting.account, currency, allowed_currencies
))

// Bad - vague message with no context
PluginError::error("Invalid currency")
```

### Configuration Parsing

Handle configuration gracefully:

```rust
fn process(&self, input: PluginInput) -> PluginOutput {
    // Parse config with defaults
    let threshold: f64 = input.config
        .as_ref()
        .and_then(|c| c.strip_prefix("threshold="))
        .and_then(|s| s.parse().ok())
        .unwrap_or(1000.0);

    // Or for more complex config:
    let config = parse_config(&input.config);

    // ...
}

fn parse_config(config: &Option<String>) -> PluginConfig {
    let Some(config_str) = config else {
        return PluginConfig::default();
    };

    // Parse key=value pairs
    let mut result = PluginConfig::default();
    for part in config_str.split(',') {
        if let Some((key, value)) = part.split_once('=') {
            match key.trim() {
                "threshold" => result.threshold = value.parse().unwrap_or(1000.0),
                "strict" => result.strict = value == "true",
                _ => {} // Ignore unknown keys
            }
        }
    }
    result
}
```

## Documentation Requirements

1. **Module docs**: Explain what the plugin does
1. **Example usage**: Show beancount syntax
1. **Configuration**: Document all options
1. **Error codes**: List possible errors

````rust
//! Check that all accounts have a specific prefix.
//!
//! This plugin validates that all account names start with one of the
//! standard prefixes (Assets, Liabilities, Equity, Income, Expenses).
//!
//! # Usage
//!
//! ```beancount
//! plugin "beancount.plugins.check_prefix"
//! ```
//!
//! # Configuration
//!
//! Optional: specify custom allowed prefixes:
//!
//! ```beancount
//! plugin "beancount.plugins.check_prefix" "Assets,Liabilities,Equity"
//! ```
//!
//! # Errors
//!
//! - `E1001`: Account name does not start with an allowed prefix
````

## Submitting Your Plugin

1. **Fork rustledger** and create a feature branch
1. **Add your plugin** following this guide
1. **Write tests** for all functionality
1. **Update documentation** in `docs/reference/plugins.md`
1. **Run the test suite**: `cargo test -p rustledger-plugin`
1. **Submit a PR** with a clear description

## See Also

- [Custom Plugins Guide](../guides/custom-plugins.md) - WASM plugins for personal use
- [Plugins Reference](../reference/plugins.md) - All available plugins
- [Contributing Guide](https://github.com/rustledger/rustledger/blob/main/CONTRIBUTING.md) - General contribution guidelines
