# WASM Plugin System Specification

## Overview

This document specifies the WASM-based plugin system for rustledger. Unlike Python Beancount which uses Python plugins, we use WebAssembly modules for:

- **Language agnosticism**: Write plugins in Rust, Go, C, AssemblyScript, or any WASM-targeting language
- **Sandboxing**: Plugins run in isolated environments with controlled capabilities
- **Portability**: Same plugin binary works everywhere (native, browser, embedded)
- **Performance**: Near-native execution speed

## Runtime

We use **wasmtime** as the WASM runtime:

- Bytecode Alliance project with strong security focus
- Excellent WASI support for filesystem/environment access
- Component Model support for rich type interfaces
- Conservative, well-audited codebase

## Plugin Interface

### Core Contract

Plugins implement a single function that transforms directives:

```rust
/// Plugin entry point
///
/// Receives: serialized list of directives + options
/// Returns: serialized list of (possibly modified) directives + errors
fn process(input: PluginInput) -> PluginOutput;
```

### Data Serialization

We use **MessagePack** (via `rmp-serde`) for the WASM boundary:

- Compact binary format
- Fast serialization/deserialization
- Schema-less (flexible evolution)
- Wide language support

Alternative: Consider **bincode** for Rust-to-Rust plugins (faster but Rust-specific).

### Type Definitions (WIT)

Using the WebAssembly Interface Types (WIT) format:

```wit
package beancount:plugin@0.1.0;

interface types {
    record amount {
        number: string,  // Decimal as string for precision
        currency: string,
    }

    record cost {
        number: string,
        currency: string,
        date: option<string>,  // YYYY-MM-DD
        label: option<string>,
    }

    record posting {
        account: string,
        units: option<amount>,
        cost: option<cost>,
        price: option<amount>,
        flag: option<string>,
        metadata: list<tuple<string, meta-value>>,
    }

    variant meta-value {
        text(string),
        number(string),
        date(string),
        account(string),
        currency(string),
        tag(string),
        amount(amount),
        bool(bool),
    }

    record transaction {
        date: string,
        flag: string,
        payee: option<string>,
        narration: string,
        tags: list<string>,
        links: list<string>,
        metadata: list<tuple<string, meta-value>>,
        postings: list<posting>,
    }

    // ... other directive types ...

    variant directive {
        transaction(transaction),
        balance(balance-assertion),
        open(open-account),
        close(close-account),
        commodity(commodity-decl),
        pad(pad-directive),
        event(event),
        query(query),
        note(note),
        document(document),
        price(price-directive),
        custom(custom),
    }

    record error {
        message: string,
        source-file: option<string>,
        line-number: option<u32>,
        severity: severity,
    }

    enum severity {
        error,
        warning,
    }

    record options {
        operating-currencies: list<string>,
        title: option<string>,
        // ... other options ...
    }
}

interface plugin {
    use types.{directive, error, options};

    record plugin-input {
        directives: list<directive>,
        options: options,
        config: option<string>,  // Plugin-specific config string
    }

    record plugin-output {
        directives: list<directive>,
        errors: list<error>,
    }

    process: func(input: plugin-input) -> plugin-output;
}

world beancount-plugin {
    export plugin;
}
```

## Plugin Loading

### Declaration in Beancount Files

```beancount
plugin "path/to/plugin.wasm"
plugin "path/to/plugin.wasm" "config=value"
```

### Loading Process

1. Parse `plugin` directive, extract path and optional config string
1. Resolve path relative to beancount file directory
1. Load and compile WASM module (cache compiled modules)
1. Instantiate module with WASI imports (limited capabilities)
1. Call `process` function with serialized directives
1. Deserialize results, merge into directive stream

### Plugin Discovery

Standard locations (checked in order):

1. Path relative to beancount file
1. `~/.config/beancount/plugins/`
1. `/usr/share/beancount/plugins/`

## Sandboxing

### Default Capabilities (Deny by Default)

Plugins have NO filesystem, network, or environment access by default.

### Optional Capabilities

Via WASI, plugins can request:

- **Read-only filesystem**: For document verification plugins
- **Environment variables**: For configuration
- **Random number generation**: For ID generation

Capabilities declared in plugin manifest (embedded in WASM custom section).

```toml
# Plugin manifest (embedded)
[capabilities]
fs_read = ["documents/"]  # Read access to documents dir only
env = ["BEANCOUNT_*"]     # Access env vars with prefix
```

### Resource Limits

- **Memory**: 256MB default, configurable
- **Execution time**: 30 seconds per plugin invocation
- **Stack depth**: wasmtime defaults

## Plugin Execution Order

1. Built-in implicit plugins (if enabled via options)
1. User-declared plugins in file order
1. Each plugin receives output of previous

```
directives → plugin1 → plugin2 → plugin3 → validated_directives
```

## Error Handling

Plugins return errors alongside directives. Errors are:

- Collected and reported to user
- Do not halt processing (unless severity is critical)
- Include source location when available

```rust
struct PluginError {
    message: String,
    source_file: Option<String>,
    line_number: Option<u32>,
    severity: Severity,
}

enum Severity {
    Warning,  // Continue processing
    Error,    // Continue but mark ledger as invalid
}
```

## Built-in Plugins (Reimplemented in Rust)

These run as native Rust code, not WASM, for performance:

| Plugin | Description |
|--------|-------------|
| `implicit_prices` | Generate price entries from transaction costs/prices |
| `check_commodity` | Verify commodities are declared |
| `check_average_cost` | Validate AVERAGE booking usage |
| `coherent_cost` | Ensure consistent cost currencies |

Enable via:

```beancount
plugin "beancount.plugins.implicit_prices"  ; recognized as built-in
```

## Writing Plugins

### Rust Plugin Template

```rust
use rustledger_plugin_types::*;

#[no_mangle]
pub extern "C" fn process(input_ptr: *const u8, input_len: usize) -> *mut u8 {
    let input: PluginInput = deserialize(input_ptr, input_len);

    let mut ops = Vec::with_capacity(input.directives.len());
    let mut errors = Vec::new();

    // Emit one PluginOp per input directive (Keep / Modify / Delete),
    // plus any Insert ops for fresh directives. Every input index must
    // appear in EXACTLY ONE of {Keep, Modify, Delete}.
    for (i, wrapper) in input.directives.into_iter().enumerate() {
        match wrapper.data {
            DirectiveData::Transaction(mut txn) => {
                // Plugin logic here — mutate `txn` then emit Modify
                // (substitutes content while keeping input[i]'s source span)
                // or Keep(i) if you didn't change anything.
                let new_wrapper = DirectiveWrapper {
                    directive_type: wrapper.directive_type,
                    date: wrapper.date,
                    filename: wrapper.filename,
                    lineno: wrapper.lineno,
                    data: DirectiveData::Transaction(txn),
                };
                ops.push(PluginOp::Modify(i, new_wrapper));
            }
            _ => ops.push(PluginOp::Keep(i)),
        }
    }

    let output = PluginOutput { ops, errors };
    serialize_to_ptr(output)
}
```

For pure passthrough plugins (e.g. validators that only emit errors),
use the one-liner `PluginOutput::passthrough(input.directives.len())`
instead of building the op list by hand.

### AssemblyScript Plugin Template

```typescript
import { PluginInput, PluginOutput, PluginOp, Error } from "rustledger-plugin-sdk";

export function process(input: PluginInput): PluginOutput {
    const ops: PluginOp[] = [];
    const errors: Error[] = [];

    for (let i = 0; i < input.directives.length; i++) {
        // Plugin logic — push Keep(i) for unchanged, Modify(i, wrapper)
        // for transformed, Delete(i) to drop, or push Insert(wrapper)
        // anywhere in the sequence to add fresh directives.
        ops.push({ kind: "Keep", index: i });
    }

    return { ops, errors };
}
```

## Performance Considerations

### Compilation Caching

- Cache compiled WASM modules to disk
- Use content-hash as cache key
- Invalidate on wasmtime version change

### Lazy Loading

- Only load plugins when their directive is encountered
- Compile in background while parsing continues

### Batching

- Pass all directives at once, not one-by-one
- Amortizes serialization/deserialization cost

## Migration from Python Plugins

Common Python plugins and their WASM equivalents:

| Python Plugin | Status |
|---------------|--------|
| `implicit_prices` | Built-in Rust |
| `check_commodity` | Built-in Rust |
| `auto_accounts` | Example WASM plugin |
| `forecast` | Example WASM plugin |

We provide example implementations to help users port custom plugins.

## Future Extensions

### Hot Reloading

Watch plugin files for changes during interactive use (bean-query REPL).

### Plugin Marketplace

Registry of community plugins with verified signatures.

### Component Model

Adopt full WASM Component Model when stable for richer interfaces.
