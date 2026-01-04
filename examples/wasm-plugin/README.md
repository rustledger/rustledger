# Example WASM Plugin for Rustledger

This is an example WASM plugin that demonstrates the plugin interface.

## What This Plugin Does

1. Adds a "processed" tag to all transactions
2. Warns about large transactions (configurable threshold)
3. Warns about expense transactions without category tags

## Building

```bash
# Install WASM target
rustup target add wasm32-unknown-unknown

# Build the plugin
cd examples/wasm-plugin
cargo build --target wasm32-unknown-unknown --release

# The plugin will be at:
# target/wasm32-unknown-unknown/release/example_plugin.wasm
```

## Using the Plugin

In your Beancount file:

```beancount
plugin "path/to/example_plugin.wasm" "threshold=5000"

2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
```

## Plugin Interface

WASM plugins must export:

- `alloc(size: u32) -> *mut u8` - Allocate memory
- `process(input_ptr: u32, input_len: u32) -> u64` - Process directives

The `process` function:
1. Receives MessagePack-encoded `PluginInput`
2. Returns packed pointer/length to MessagePack-encoded `PluginOutput`

## Data Types

See `src/lib.rs` for the complete type definitions that match `beancount-plugin/src/types.rs`.

## Testing

```bash
cargo test
```
