# Beancount WASM Plugin Template

This is a template for creating WASM plugins for rustledger.

## Building

```bash
# Install the WASM target if you haven't
rustup target add wasm32-unknown-unknown

# Build the plugin
cargo build --target wasm32-unknown-unknown --release
```

The output will be at `target/wasm32-unknown-unknown/release/example_plugin.wasm`.

## Plugin Interface

Plugins must export two functions:

### `alloc(size: u32) -> *mut u8`
Allocates memory for the host to write input data.

### `process(input_ptr: u32, input_len: u32) -> u64`
Main entry point. Receives MessagePack-encoded `PluginInput`, returns a packed
pointer and length to MessagePack-encoded `PluginOutput`.

Return value format: `(output_ptr << 32) | output_len`

## Data Types

See `src/lib.rs` for the complete type definitions. The types must match the
host's `beancount-plugin` crate types for serialization to work.

## Example Plugins

- **Add tag**: Add a tag to all transactions (this template)
- **Validate payee**: Ensure all transactions have a payee
- **Currency check**: Warn about undeclared currencies
- **Auto-categorize**: Add metadata based on payee patterns

## Testing

You can test your plugin using the rustledger CLI (once plugin support is integrated):

```bash
bean-check --plugin ./target/wasm32-unknown-unknown/release/example_plugin.wasm ledger.beancount
```
