______________________________________________________________________

## title: Integration Guide description: Embedding rustledger in applications and other languages

# Integration Guide

This guide covers all the ways to integrate rustledger into your applications, from direct Rust usage to embedding in Python, Node.js, or any other language.

## Overview

rustledger provides multiple integration paths:

| Approach | Best For | Languages |
|----------|----------|-----------|
| [CLI](#command-line-interface) | Shell scripts, CI/CD pipelines | Any (subprocess) |
| [Rust Crates](#rust-crates) | Rust applications | Rust |
| [WASM Library](#webassembly-library) | Browsers, Node.js | JavaScript, TypeScript |
| [Component Model (WIT)](#component-model-wit) | **Recommended** typed embedding on wasip2 hosts (primary embedding path) | Any wasip2 host |
| [WASI FFI](#wasi-ffi-json-rpc) | Embedding via JSON-RPC (legacy — deprecated, slated for Phase 5 removal) | Python, Ruby, Go, etc. |
| [LSP](#language-server-protocol) | Editor integrations | Any LSP client |

## Command-Line Interface

The simplest integration is calling `rledger` as a subprocess.

### JSON Output

Most commands support `--format json` for machine-readable output:

```bash
# Get balances as JSON
# Note: --format must precede the FILE/QUERY arguments, otherwise the
# variadic QUERY argument swallows the flag.
rledger query --format json ledger.beancount "BALANCES"

# Check for errors
rledger check ledger.beancount --format json

# Format and compare
rledger format ledger.beancount --check
```

### Example: Python Subprocess

```python
import subprocess
import json

def get_balances(ledger_path):
    result = subprocess.run(
        ["rledger", "query", "--format", "json", ledger_path, "BALANCES"],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr)
    return json.loads(result.stdout)

balances = get_balances("ledger.beancount")
for row in balances["rows"]:
    print(f"{row['account']}: {row['balance']}")
```

## Rust Crates

For Rust applications, use the crates directly:

```toml
[dependencies]
rustledger-core = "0.x"
rustledger-parser = "0.x"
rustledger-loader = "0.x"
rustledger-query = "0.x"
```

### Parsing

```rust
use rustledger_parser::parse;

let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Expenses:Food  5 USD
  Assets:Bank   -5 USD
"#;

let result = parse(source);
for directive in result.directives {
    println!("{:?}", directive);
}
```

### Loading with Includes

```rust
use std::path::Path;
use rustledger_loader::Loader;

let mut loader = Loader::new();
let result = loader.load(Path::new("ledger.beancount"))?;

// Access loaded directives
for directive in &result.directives {
    println!("{:?}", directive);
}
```

### Running Queries

```rust
use std::path::Path;
use rustledger_loader::Loader;
use rustledger_query::{parse as parse_query, Executor};

let mut loader = Loader::new();
let result = loader.load(Path::new("ledger.beancount"))?;

let query = parse_query("SELECT account, sum(position) GROUP BY account")?;

// Strip spans: the executor takes `&[Directive]`, while the loader
// returns `Vec<Spanned<Directive>>`.
let directives: Vec<_> = result.directives.into_iter().map(|s| s.value).collect();
let mut executor = Executor::new(&directives);
let query_result = executor.execute(&query)?;

for row in &query_result.rows {
    println!("{:?}", row);
}
```

## WebAssembly Library

For browser or Node.js applications, use the WASM package:

```bash
npm install @rustledger/wasm
```

### Browser Usage

```javascript
import init, { parse, validateSource, query } from '@rustledger/wasm';

await init();

const source = `
2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
`;

const result = parse(source);
if (result.errors.length === 0) {
    const validation = validateSource(source);
    console.log('Valid:', validation.valid);

    const balances = query(source, 'BALANCES');
    console.log('Balances:', balances.rows);
}
```

### Single-file Stateful API

For multiple operations on the same source, use `ParsedLedger` to avoid re-parsing:

```javascript
import { ParsedLedger } from '@rustledger/wasm';

const ledger = new ParsedLedger(source);

if (ledger.isValid()) {
    const balances = ledger.balances();
    const formatted = ledger.format();

    // Editor features
    const completions = ledger.getCompletions(5, 10);
    const hover = ledger.getHoverInfo(3, 5);
    const definition = ledger.getDefinition(4, 3);
}

ledger.free(); // Release WASM memory
```

### Multi-file Stateful API

For ledgers spanning multiple files with `include` directives, use `Ledger`:

```javascript
import { Ledger } from '@rustledger/wasm';

const ledger = Ledger.fromFiles({
    "main.beancount": 'include "accounts.beancount"\n...',
    "accounts.beancount": "2024-01-01 open Assets:Bank USD\n..."
}, "main.beancount");

if (ledger.isValid()) {
    const balances = ledger.query("BALANCES");

    // Cross-file completions (pass the file being edited)
    const completions = ledger.getCompletions(currentFileSource, line, char);
}

ledger.free();
```

### Available Functions

| Function / Class | Description |
|------------------|-------------|
| `parse()` | Parse Beancount source to JSON |
| `validateSource()` | Validate ledger with error reporting |
| `query()` | Run BQL queries |
| `format()` | Format source with consistent alignment |
| `expandPads()` | Expand pad directives |
| `runPlugin()` | Run native plugins (requires `plugins` feature) |
| `bqlCompletions()` | BQL query completions (requires `completions` feature) |
| `ParsedLedger` | Single-file stateful class with editor features |
| `Ledger` | Multi-file stateful class for queries and cross-file completions |
| `parseMultiFile()` | Parse multiple files with include resolution |
| `validateMultiFile()` | Validate across multiple files |
| `queryMultiFile()` | Query across multiple files |

## WASI FFI (JSON-RPC)

> **Legacy / deprecated.** This wasip1 JSON-RPC surface
> (`rustledger-ffi-wasi`) is the older embedding path. New integrations should
> prefer the typed [Component Model (WIT)](#component-model-wit) surface, which
> is now the primary, default embedding path (the default backend in rustfava).
> The JSON-RPC surface is slated for removal in Phase 5
> ([#1419](https://github.com/rustledger/rustledger/issues/1419)). The reference
> below remains accurate for as long as it ships.

The WASI FFI module exposes a JSON-RPC 2.0 API that can be embedded in any language with a WASI runtime. This is ideal for building an API server or embedding in Python, Ruby, Go, etc.

### Quick Start

Build or download the WASM module, then run with wasmtime:

```bash
# Build from source
cargo build -p rustledger-ffi-wasi --target wasm32-wasip1 --release

# Run with wasmtime
echo '{"jsonrpc":"2.0","method":"ledger.validate","params":{"source":"2024-01-01 open Assets:Bank USD"},"id":1}' | \
    wasmtime target/wasm32-wasip1/release/rustledger-ffi-wasi.wasm
```

### Available Methods

#### Ledger Operations

| Method | Description |
|--------|-------------|
| `ledger.load` | Parse beancount source and return structured data |
| `ledger.loadFile` | Load and process a beancount file (with includes, booking, plugins) |
| `ledger.validate` | Validate beancount source and return errors |
| `ledger.validateFile` | Validate a beancount file |

#### Query Operations

| Method | Description |
|--------|-------------|
| `query.execute` | Execute a BQL query on source |
| `query.executeFile` | Execute a BQL query on a file |
| `query.batch` | Execute multiple queries on source |
| `query.batchFile` | Execute multiple queries on a file |

#### Format Operations

| Method | Description |
|--------|-------------|
| `format.source` | Format beancount source code |
| `format.file` | Format a beancount file |
| `format.entry` | Format a single entry from JSON |
| `format.entries` | Format multiple entries from JSON |

#### Entry Operations

| Method | Description |
|--------|-------------|
| `entry.create` | Create an entry from JSON |
| `entry.createBatch` | Create multiple entries from JSON |
| `entry.filter` | Filter entries by date range |
| `entry.clamp` | Clamp entries to date range |

#### Utility Operations

| Method | Description |
|--------|-------------|
| `util.version` | Get API and package version |
| `util.types` | Get supported directive types, booking methods |

### Example: Python with wasmtime-py

```python
import subprocess
import json

def call_rpc(method, params, wasm_path="rustledger-ffi-wasi.wasm"):
    """Call a JSON-RPC method on the rustledger WASI module."""
    request = json.dumps({
        "jsonrpc": "2.0",
        "method": method,
        "params": params,
        "id": 1
    })

    proc = subprocess.run(
        ["wasmtime", wasm_path],
        input=request,
        capture_output=True,
        text=True
    )

    if proc.returncode != 0:
        raise RuntimeError(f"WASI module failed: {proc.stderr}")

    response = json.loads(proc.stdout)
    if "error" in response:
        raise RuntimeError(f"JSON-RPC error: {response['error']}")

    return response.get("result")

# Validate a ledger
result = call_rpc("ledger.validate", {
    "source": "2024-01-01 open Assets:Bank USD"
})
print(f"Valid: {result['valid']}")

# Run a query
balances = call_rpc("query.execute", {
    "source": "2024-01-01 open Assets:Bank USD\n2024-01-15 * \"Test\"\n  Assets:Bank 100 USD\n  Income:Test",
    "query": "BALANCES"
})
print(balances)
```

### Error Codes

Standard JSON-RPC errors:

| Code | Message |
|------|---------|
| -32700 | Parse error (invalid JSON) |
| -32600 | Invalid Request |
| -32601 | Method not found |
| -32602 | Invalid params |
| -32603 | Internal error |

Beancount-specific errors:

| Code | Message |
|------|---------|
| -32000 | Beancount parse error |
| -32001 | Beancount validation error |
| -32002 | BQL query error |
| -32003 | File I/O error |

### Batch Requests

Send multiple requests in a single call:

```bash
echo '[
  {"jsonrpc":"2.0","method":"util.version","id":1},
  {"jsonrpc":"2.0","method":"ledger.validate","params":{"source":"..."},"id":2}
]' | wasmtime rustledger-ffi-wasi.wasm
```

## Component Model (WIT)

> **Recommended embedding surface.** The typed WASI Preview 2 component
> (`rustledger-ffi-component`, [#1384](https://github.com/rustledger/rustledger/issues/1384))
> is the primary, default embedding path. It is the default backend in rustfava
> as of #1384 Phase 4 (rustfava [#183](https://github.com/rustledger/rustfava/pull/183))
> and ships as a prebuilt wasip2 component artifact. The legacy JSON-RPC WASI FFI
> above remains available but is slated for removal in Phase 5
> ([#1419](https://github.com/rustledger/rustledger/issues/1419)).

Instead of a hand-rolled JSON-RPC wire shape, this surface exposes a generated
**WIT contract** (`crates/rustledger-ffi-component/wit/world.wit`, versioned
package `rustledger:ledger@2.1.0`). The same operations — `load` / `validate` /
`query` / `batch` (+ `-file` variants), entry `create` / `filter` / `clamp`,
`util`, and `format` — are strongly-typed component functions with no JSON
envelope. The contract itself is the versioned wire shape; a `version()` func
remains for runtime negotiation in place of the old per-response `api_version`.

### Surface

The world exports four interfaces — `ledger`, `builder`, `util`, and `format`:

- **`ledger`** — `version`, `load(source, filename)` (the `filename` is recorded
  as the directives' source location; pass `<stdin>` if unknown), `validate`,
  `query`, `batch`, plus their `-file` variants.
- **`ledger.session`** — a stateful `resource` holding a loaded, booked ledger
  inside the component (rustfava [#173](https://github.com/rustledger/rustfava/issues/173)).
  The host constructs one handle (`constructor(source)` or
  `from-file(path, …)`), then runs `info`, `query`, `filter`, and `clamp`
  against the *held* ledger with no re-parse and no re-render — the typed,
  stateful successor to the free `load`/`query`/`clamp` functions.
- **`builder`** — `create` / `create-batch` (validate and round-trip typed input
  through core; both fallible, batch all-or-nothing), `filter` / `clamp` over a
  date window, and `query-entries`, which runs a BQL query directly against an
  already-loaded directive set (the embedder passes the directives it holds, so
  there is no re-parse and no re-render to beancount text).
- **`util`** — `types` / `is-encrypted` / `get-account-type`.
- **`format`** — `format-source` / `-file` / `-entry` / `-entries`.

`clamp` is provenance-preserving: in-window directives keep their original
`filename`/`lineno`, and only the *synthesized* opening-balance / summary
boundary directives get synthetic source locations.

A host consumes it via `wasmtime`'s component bindings; a guest/other language
binds with `wit-bindgen`:

```rust
// Host side (Rust), via wasmtime's component model:
wasmtime::component::bindgen!({ world: "rustledger", path: "world.wit" });
// ... instantiate the component, then call typed methods:
let version = inst.rustledger_ledger_ledger().call_version(&mut store)?;
let result  = inst.rustledger_ledger_ledger().call_query(&mut store, source, "SELECT account, position")?;
```

Build the component with `cargo build -p rustledger-ffi-component --target wasm32-wasip2`. See `crates/rustledger-ffi-component/README.md` for the full
surface and modeling decisions.

## Language Server Protocol

For editor integrations, rustledger provides an LSP server:

```bash
rledger-lsp
```

The LSP supports:

- Diagnostics (validation errors)
- Go to definition (accounts, commodities)
- Hover information (account details, balances)
- Completions (accounts, currencies, payees)
- Document formatting
- Code actions

See [Editor Integration](editor-integration.md) for setup instructions.

## Comparison

The embedding columns below cover both surfaces: **Component** is the
recommended Component Model (WIT) path, and **WASI FFI** is the legacy JSON-RPC
surface (slated for Phase 5 removal). They expose the same operations.

| Feature | CLI | Rust | WASM | Component | WASI FFI | LSP |
|---------|-----|------|------|-----------|----------|-----|
| Parse ledger | Y | Y | Y | Y | Y | - |
| Validate | Y | Y | Y | Y | Y | Y |
| BQL queries | Y | Y | Y | Y | Y | - |
| Format | Y | Y | Y | Y | Y | Y |
| File access | Y | Y | - | Y | Y | Y |
| Plugins | Y | Y | Y | Y | Y | Y |
| Editor features | - | - | Y | - | - | Y |
| Streaming | - | Y | - | - | - | - |

## Which Should I Use?

- **Building a web app?** Use WASM
- **Building a desktop app in Rust?** Use the crates directly
- **Embedding in another language / host?** Use the **Component Model (WIT)**
  surface — it is the recommended, default embedding path. (The legacy JSON-RPC
  WASI FFI remains available as a transitional option, but is being retired in
  Phase 5.)
- **Writing shell scripts?** Use CLI with `--format json`
- **Building an editor plugin?** Use LSP
- **Need maximum performance?** Use Rust crates or the Component Model surface
