# rustledger-plugin-types

WASM plugin interface types for [rustledger](https://github.com/rustledger/rustledger).

This crate provides the canonical type definitions that plugins must use to
communicate with the rustledger host. Using this crate ensures your plugin's
types are always compatible with the host.

There are **two distinct WASM plugin subsystems**, and this crate hosts the
shared types for both:

- **Directive plugins** transform the directive stream *after* parsing
  (tagging, dedup, categorization). Required export: `process`. Host loader:
  `rustledger-plugin`. See the "Directive Plugin Quick Start" section below.
- **WASM importers** turn bank-statement files *into* directives (CSV, OFX,
  custom formats). Required exports: `metadata`, `identify`, `extract`,
  `extract_enriched`. Host loader: `rustledger-importer::WasmImporter`. See
  the "WASM Importer Quick Start" section below, and use the
  `wasm_importer_main!` macro (behind the `guest` feature) to skip writing
  the export boilerplate yourself.

## Installation

Add to your plugin's `Cargo.toml`:

```toml
[package]
name = "my-plugin"
edition = "2021"

[lib]
crate-type = ["cdylib"]

[dependencies]
rustledger-plugin-types = "0.15"
rmp-serde = "1"
```

**Version compatibility**: Use the same minor version as your target rustledger host (e.g., `0.15.x` types for rustledger `0.15.x`).

## Directive Plugin Quick Start

The `wasm_plugin_main!` macro (behind the `guest` feature) generates
the required `alloc` + `process` exports from a single user
`fn(PluginInput) -> PluginOutput`. This is the recommended path —
collapses what used to be ~50 lines of `#[unsafe(no_mangle)] extern
"C"` boilerplate down to a 5-line invocation. Add the feature to
your `Cargo.toml`:

```toml
[dependencies]
rustledger-plugin-types = { version = "0.15", features = ["guest"] }
```

Then:

```rust,ignore
use rustledger_plugin_types::{
    DirectiveData, PluginInput, PluginOp, PluginOutput,
    wasm_plugin_main,
};

fn process(input: PluginInput) -> PluginOutput {
    // Emit one op per input directive:
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
    PluginOutput { ops, errors: vec![] }
}

wasm_plugin_main! {
    process: process,
}
```

Pure-passthrough validators that emit no transformations can short-circuit
with the convenience constructor:

```rust,ignore
fn process(input: PluginInput) -> PluginOutput {
    PluginOutput::passthrough(input.directives.len())
}
```

> **Invoke `wasm_plugin_main!` once per cdylib crate.** It emits
> exports named `alloc` and `process` — symbols the host loader looks
> up by name. Two invocations cause a duplicate-symbol linker error on
> `wasm32`. If you need multiple plugins, build them as separate
> cdylib crates.

<details>
<summary>Without the macro (manual exports)</summary>

The macro saves you from writing this, but if you need finer control —
or you want to understand what the wire format looks like — here's the
expansion in raw `extern "C"` form:

```rust
use rustledger_plugin_types::*;

#[unsafe(no_mangle)]
pub extern "C" fn alloc(size: u32) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(size as usize, 1).unwrap();
    unsafe { std::alloc::alloc(layout) }
}

#[unsafe(no_mangle)]
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

    // (process logic — see the macro example above)
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

</details>

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

## WASM Importer Quick Start

Importers read source files (CSV, OFX, …) and emit directives. The host
loader is in `rustledger-importer` (`WasmImporter::load`); the wire format
lives in this crate.

Use the `wasm_importer_main!` macro to generate the required exports.
Enable it with the `guest` feature:

```toml
[dependencies]
rustledger-plugin-types = { version = "0.15", features = ["guest"] }
```

```rust,ignore
use rustledger_plugin_types::{
    DirectiveData, DirectiveWrapper, ImporterInput, ImporterOutput,
    OpenData, wasm_importer_main,
};

fn identify(path: &str) -> bool {
    path.ends_with(".mybank")
}

fn extract(input: ImporterInput) -> ImporterOutput {
    // Parse input.content (Vec<u8>) and emit DirectiveWrapper values.
    // input.account / input.currency / input.options carry per-call config.
    ImporterOutput::new(vec![DirectiveWrapper {
        directive_type: String::new(),
        date: "2024-01-01".into(),
        filename: None,
        lineno: None,
        data: DirectiveData::Open(OpenData {
            account: input.account,
            currencies: input.currency.into_iter().collect(),
            booking: None,
            metadata: vec![],
        }),
    }])
}

wasm_importer_main! {
    name: "my-bank",
    description: "Importer for MyBank CSV statements",
    identify: identify,
    extract: extract,
    // `extract_enriched` is auto-generated as a passthrough that wraps
    // each directive with `CategorizationMethod::Default`. Add an
    // `extract_enriched:` entry to override (and provide real
    // categorization confidence + fingerprints).
}
```

The macro emits the required exports (`memory`, `alloc`, `metadata`,
`identify`, `extract`, `extract_enriched`) gated on
`#[cfg_attr(target_arch = "wasm32", ...)]` so the host-target build of
your crate (used by tests) doesn't collide with the WASM linker's symbol
namespace.

See [`examples/wasm-importer-csv-example`][csv-example] in the rustledger
repo for a complete reference implementation.

[csv-example]: https://github.com/rustledger/rustledger/tree/main/examples/wasm-importer-csv-example

### Importer ABI types

| Type | Description |
|------|-------------|
| `ImporterInput` | Input to `extract`/`extract_enriched`: path, content bytes, account, currency, options map |
| `IdentifyInput` | Input to `identify`: path only (content isn't read until extract) |
| `ImporterOutput` | Result of `extract`: directives + warnings + structured errors |
| `EnrichedImporterOutput` | Result of `extract_enriched`: `(DirectiveWrapper, EnrichmentWrapper)` pairs |
| `IdentifyOutput` | Result of `identify`: `bool` |
| `MetadataOutput` | Result of `metadata`: name + description, called once at load |
| `EnrichmentWrapper` | Per-directive categorization metadata (method, confidence, fingerprint, alternatives) |
| `AlternativeWrapper` | Alternative account categorization with confidence |

### Categorization method strings

`EnrichmentWrapper::method` is a wire-format string that must match one of:
`"rule"`, `"merchant-dict"` (hyphen, not underscore!), `"ml"`, `"llm"`,
`"manual"`, `"default"`. Unknown strings cause the host to emit a warning
and fall back to `Default`. The host pinning lives in
`rustledger_ops::enrichment::CategorizationMethod::as_meta_value`.

## License

GPL-3.0-only
