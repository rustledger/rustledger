# rustledger-ffi-wasi

A WASI module providing JSON-RPC 2.0 API for embedding Rustledger in any language.

## Overview

This crate compiles to a WebAssembly module that can be run via [wasmtime](https://wasmtime.dev/) or any WASI-compatible runtime. It provides a fast, portable way to use Rustledger's Beancount parsing, validation, and querying capabilities from any language.

## Usage

Send JSON-RPC 2.0 requests via stdin:

```bash
# Validate beancount source
echo '{"jsonrpc":"2.0","method":"ledger.validate","params":{"source":"2024-01-01 open Assets:Bank USD"},"id":1}' | \
    wasmtime rustledger-ffi-wasi.wasm

# Execute a BQL query
echo '{"jsonrpc":"2.0","method":"query.execute","params":{"source":"...","query":"SELECT account, sum(position) GROUP BY 1"},"id":1}' | \
    wasmtime rustledger-ffi-wasi.wasm

# Batch requests
echo '[
  {"jsonrpc":"2.0","method":"util.version","id":1},
  {"jsonrpc":"2.0","method":"util.types","id":2}
]' | wasmtime rustledger-ffi-wasi.wasm
```

## Available Methods

### Ledger Operations

| Method | Description |
|--------|-------------|
| `ledger.load` | Parse beancount source and return structured data |
| `ledger.loadFile` | Load and process a beancount file (with includes, booking, plugins) |
| `ledger.validate` | Validate beancount source and return errors |
| `ledger.validateFile` | Validate a beancount file |

### Query Operations

| Method | Description |
|--------|-------------|
| `query.execute` | Execute a BQL query on source |
| `query.executeFile` | Execute a BQL query on a file |
| `query.batch` | Execute multiple queries on source |
| `query.batchFile` | Execute multiple queries on a file |

### Format Operations

| Method | Description |
|--------|-------------|
| `format.source` | Format beancount source code |
| `format.file` | Format a beancount file |
| `format.entry` | Format a single entry from JSON |
| `format.entries` | Format multiple entries from JSON |

### Entry Operations

| Method | Description |
|--------|-------------|
| `entry.create` | Create an entry from JSON |
| `entry.createBatch` | Create multiple entries from JSON |
| `entry.filter` | Filter entries by date range |
| `entry.clamp` | Clamp entries to date range |

### Utility Operations

| Method | Description |
|--------|-------------|
| `util.version` | Get API and package version |
| `util.types` | Get supported directive types, booking methods |
| `util.isEncrypted` | Check if a file path is encrypted |
| `util.getAccountType` | Get account type from account name |

## Error Codes

### Standard JSON-RPC Errors

| Code | Message | When |
|------|---------|------|
| -32700 | Parse error (invalid JSON) | Transport-layer fault — the request envelope was not valid JSON. **Not** used for beancount-content syntax errors (see -32000 below). |
| -32600 | Invalid Request | Request envelope is valid JSON but not a valid JSON-RPC 2.0 Request object. |
| -32601 | Method not found | The requested method does not exist. |
| -32602 | Invalid params | The method's parameter shape is wrong. |
| -32603 | Internal error | Server-side fault (e.g., stdin read failure, response serialization failure). |

### Beancount-specific Errors

| Code | Message | When |
|------|---------|------|
| -32000 | Beancount parse error | Application-level: the beancount source the user submitted has syntax errors. Carries a structured `data` field — `{"errors": ParseErrorEntry[], "total": N, "truncated": bool}` — so clients can surface individual parse errors without scraping the free-form `message`. Distinct from -32700, which is reserved for malformed JSON. See the `ParseErrorEntry` section below for the per-error shape. |

### `ParseErrorEntry` shape

Each element of `error.data.errors` is an object with the following fields:

| Field       | Type           | Description |
|-------------|----------------|-------------|
| `message`   | string         | Rendered Display of the parser error. |
| `kind_code` | integer        | Stable numeric discriminant (1-26, see `openrpc.json`'s `ParseErrorEntry` schema). Use this for structural detection — e.g., `kind_code === 26` is `BomInDirectiveBody` (mid-file BOM; clients can surface a 'Remove BOM' quick-fix). |
| `hint`      | string \| null | Optional actionable suggestion (e.g., 'Remove the U+FEFF byte at this position…'). Render as a separate help/fix-it line below `message`. |
| `span`      | object         | `{start: integer, end: integer}` byte range into the source. |

Example error response:

```json
{
  "jsonrpc": "2.0",
  "error": {
    "code": -32000,
    "message": "cannot format source with 1 parse error(s)",
    "data": {
      "errors": [
        {
          "message": "parse error: Invalid token: UTF-8 BOM detected in directive body (only a leading BOM is permitted); did you concatenate two BOM-prefixed files or paste content with an embedded BOM?",
          "kind_code": 26,
          "hint": "remove the U+FEFF byte at this position; if the file is a concatenation of two BOM-prefixed exports, strip BOMs from the inner files before concatenating",
          "span": { "start": 32, "end": 64 }
        }
      ],
      "total": 1,
      "truncated": false
    }
  },
  "id": 1
}
```

> **Wire-shape note (v2.0):** prior to API version 2.0, `error.data.errors` was a `string[]` of rendered messages. As of 2.0 each entry is the `ParseErrorEntry` object above. The change is a wire-shape break and earned the major bump per the version policy on `API_VERSION`. Migration recipe for cross-version clients that want to bridge both: `errors.map(e => typeof e === 'string' ? { message: e, kind_code: null, hint: null, span: null } : e)`.
| -32001 | Beancount validation error | The directives parsed but validation (account openness, balance assertion, etc.) failed. |
| -32002 | BQL query error | The BQL query string did not parse or did not execute. |
| -32003 | File I/O error | Could not read/open the requested file path. |

## Examples

### Validate a Ledger

```bash
echo '{"jsonrpc":"2.0","method":"ledger.validate","params":{"source":"2024-01-01 open Assets:Bank USD\n2024-01-02 * \"Coffee\"\n  Expenses:Food 5 USD\n  Assets:Bank"},"id":1}' | wasmtime rustledger-ffi-wasi.wasm
```

Response:

```json
{"jsonrpc":"2.0","result":{"api_version":"2.0","valid":true,"errors":[]},"id":1}
```

### Execute a Query

```bash
echo '{"jsonrpc":"2.0","method":"query.execute","params":{"source":"2024-01-01 open Assets:Bank USD\n2024-01-01 open Expenses:Food\n2024-01-02 * \"Coffee\"\n  Expenses:Food 5 USD\n  Assets:Bank -5 USD","query":"SELECT account, sum(position) GROUP BY 1"},"id":1}' | wasmtime rustledger-ffi-wasi.wasm
```

### Create an Entry

```bash
echo '{"jsonrpc":"2.0","method":"entry.create","params":{"entry":{"type":"transaction","date":"2024-01-15","payee":"Grocery Store","narration":"Weekly groceries","postings":[{"account":"Expenses:Food","units":{"number":"50","currency":"USD"}},{"account":"Assets:Bank"}]}},"id":1}' | wasmtime rustledger-ffi-wasi.wasm
```

## OpenRPC Specification

An OpenRPC specification is available at `openrpc.json` for automatic client generation.

## Building

```bash
# Build for WASI target
cargo build -p rustledger-ffi-wasi --target wasm32-wasip1 --release

# The output will be at:
# target/wasm32-wasip1/release/rustledger-ffi-wasi.wasm
```

## License

GPL-3.0
