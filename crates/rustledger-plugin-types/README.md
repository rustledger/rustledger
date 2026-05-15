# rustledger-plugin-types

WASM plugin interface types for [rustledger](https://github.com/rustledger/rustledger).

This crate provides the canonical type definitions that plugins must use to communicate with the rustledger host. Using this crate ensures your plugin's types are always compatible with the host.

## Installation

Add to your plugin's `Cargo.toml`:

```toml
[package]
name = "my-plugin"
edition = "2021"

[lib]
crate-type = ["cdylib"]

[dependencies]
rustledger-plugin-types = "0.10"
rmp-serde = "1"
```

**Version compatibility**: Use the same minor version as your target rustledger host (e.g., `0.10.x` types for rustledger `0.10.x`).

## Quick Start

```rust
use rustledger_plugin_types::*;

#[no_mangle]
pub extern "C" fn alloc(size: u32) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(size as usize, 1).unwrap();
    unsafe { std::alloc::alloc(layout) }
}

#[no_mangle]
pub extern "C" fn process(input_ptr: u32, input_len: u32) -> u64 {
    // Read input
    let input_bytes = unsafe {
        std::slice::from_raw_parts(input_ptr as *const u8, input_len as usize)
    };

    // Deserialize with error handling
    let input: PluginInput = match rmp_serde::from_slice(input_bytes) {
        Ok(i) => i,
        Err(e) => return error_response(&format!("Deserialize failed: {}", e)),
    };

    // Process directives. Emit one op per input directive:
    //   Keep(i)        — unchanged (preserves span)
    //   Modify(i, w)   — transformed content, inherits input[i]'s span
    //   Delete(i)      — drop input[i]
    //   Insert(w)      — fresh directive (synthesized location)
    let mut ops = Vec::with_capacity(input.directives.len());
    for (i, mut wrapper) in input.directives.into_iter().enumerate() {
        if let DirectiveData::Transaction(ref mut txn) = wrapper.data {
            txn.tags.push("processed".to_string());
            ops.push(PluginOp::Modify(i, wrapper));
        } else {
            ops.push(PluginOp::Keep(i));
        }
    }

    // Serialize output
    let output = PluginOutput { ops, errors: vec![] };
    let output_bytes = match rmp_serde::to_vec(&output) {
        Ok(b) => b,
        Err(e) => return error_response(&format!("Serialize failed: {}", e)),
    };

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

/// Helper to return an error response
fn error_response(message: &str) -> u64 {
    let output = PluginOutput {
        ops: vec![],
        errors: vec![PluginError::error(message)],
    };
    let bytes = rmp_serde::to_vec(&output).unwrap_or_default();
    let ptr = alloc(bytes.len() as u32);
    unsafe {
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), ptr, bytes.len());
    }
    ((ptr as u64) << 32) | (bytes.len() as u64)
}
```

Pure pass-through validators that emit no transformations can build the
op list with the convenience constructor:

```rust
let output = PluginOutput::passthrough(input.directives.len());
```

## Building

```sh
# Install WASM target
rustup target add wasm32-unknown-unknown

# Build your plugin
cargo build --target wasm32-unknown-unknown --release
```

The plugin will be at `target/wasm32-unknown-unknown/release/my_plugin.wasm`.

## Using Your Plugin

In your beancount file:

```beancount
plugin "path/to/my_plugin.wasm" "optional-config-string"

2024-01-01 open Assets:Bank USD
```

## Types Overview

| Type | Description |
|------|-------------|
| `PluginInput` | Input from host: directives, options, config |
| `PluginOutput` | Output to host: `ops: Vec<PluginOp>` describing the resulting directive list, plus errors |
| `PluginOp` | One Keep/Modify/Insert/Delete operation against the input |
| `DirectiveWrapper` | Wrapper with date, source location, and data |
| `DirectiveData` | Enum of all directive types |
| `PluginError` | Error/warning with optional source location |

## PluginOp Variants

`PluginOutput.ops` is an ordered list of operations, not a replacement
directive list. Every input index must appear in exactly one of
`Keep`, `Modify`, or `Delete`; the host validates this and emits a
plugin error if violated.

| Variant | Semantics |
|---------|-----------|
| `Keep(i)` | Reuse `input[i]` unchanged. Span and `file_id` preserved. |
| `Modify(i, wrapper)` | Replace `input[i]`'s content with `wrapper`, inheriting `input[i]`'s source identity so errors still point at the original line. |
| `Insert(wrapper)` | Emit a fresh directive with synthesized location (`SYNTHESIZED_FILE_ID`, zero span). Use for directives the plugin invents. |
| `Delete(i)` | Drop `input[i]`. Must be explicit — omitting an index is a protocol violation. |

## Creating Errors

```rust
use rustledger_plugin_types::{PluginError, PluginErrorSeverity};

// Simple error
let error = PluginError::error("Something went wrong");

// Warning with source location
let warning = PluginError::warning("Duplicate entry")
    .at("ledger.beancount", 42);
```

## Memory Management

Plugins must export:

- `alloc(size: u32) -> *mut u8` - **Required**. The host calls this to allocate memory for input data.

Plugins may optionally export:

- `dealloc(ptr: *mut u8, size: u32)` - Optional. For freeing memory within the plugin.

## License

GPL-3.0-only
