# Architecture Overview

This document describes rustledger's crate structure and data flow.

## Crate Dependency Graph

```
                                    ┌─────────────────┐
                                    │   rustledger    │
                                    │   (CLI binary)  │
                                    └────────┬────────┘
                                             │
              ┌──────────────────────────────┼──────────────────────────────┐
              │                              │                              │
              ▼                              ▼                              ▼
    ┌─────────────────┐           ┌─────────────────┐           ┌─────────────────┐
    │ rustledger-lsp  │           │ rustledger-query│           │rustledger-plugin│
    │  (LSP server)   │           │  (BQL engine)   │           │ (plugin system) │
    └────────┬────────┘           └────────┬────────┘           └────────┬────────┘
              │                              │                              │
              └──────────────────────────────┼──────────────────────────────┘
                                             │
                                             ▼
                                  ┌─────────────────┐
                                  │rustledger-loader│
                                  │ (file loading)  │
                                  └────────┬────────┘
                                             │
              ┌──────────────────────────────┼──────────────────────────────┐
              │                              │                              │
              ▼                              ▼                              ▼
    ┌─────────────────┐         ┌─────────────────────┐         ┌─────────────────┐
    │rustledger-parser│         │rustledger-validate  │         │rustledger-booking│
    │ (lexer/parser)  │         │ (validation engine) │         │ (7 booking modes)│
    └────────┬────────┘         └────────┬────────────┘         └────────┬────────┘
              │                              │                              │
              └──────────────────────────────┼──────────────────────────────┘
                                             │
                                             ▼
                                  ┌─────────────────┐
                                  │ rustledger-core │
                                  │  (core types)   │
                                  └─────────────────┘


    ┌─────────────────┐   ┌───────────────────┐   ┌───────────────────┐
    │ rustledger-wasm │   │rustledger-ffi-wasi│   │rustledger-importer│
    │ (JS/TS bindings)│   │ (JSON-RPC/WASI)   │   │    (CSV/OFX)      │
    └────────┬────────┘   └────────┬──────────┘   └────────┬──────────┘
              │                     │                       │
              │                     └──► core, booking, validate, plugin, query
              └────────────────────────► core, parser, booking, validate, loader, query
                                                            └──► core, ops

    ┌─────────────────────┐
    │   rustledger-ops    │
    │ (dedup, categorize, │
    │  reconcile, etc.)   │
    └────────┬────────────┘
              │
              └──► plugin-types only
```

## Crate Descriptions

### Core Layer

| Crate | Purpose | Key Types |
|-------|---------|-----------|
| `rustledger-core` | Fundamental types | `Amount`, `Position`, `Inventory`, `Decimal`, `Account`, `Currency` |
| `rustledger-parser` | Logos lexer + Winnow parser | `Directive`, `Transaction`, `Posting`, `ParseError` |

### Processing Layer

| Crate | Purpose | Key Types |
|-------|---------|-----------|
| `rustledger-loader` | File loading, includes, caching | `Loader`, `LoadedLedger`, `Options` |
| `rustledger-booking` | Cost basis and lot matching | `BookingMethod` (FIFO, LIFO, HIFO, etc.) |
| `rustledger-validate` | Validation rules | `ValidationError`, 28 error codes (E1001-E10002) |

### Feature Layer

| Crate | Purpose | Key Types |
|-------|---------|-----------|
| `rustledger-query` | BQL query engine | `Query`, `Executor`, `Table`, `Row` |
| `rustledger-plugin` | Native + WASM + Python plugins | `NativePlugin`, `NativePluginRegistry`, `PluginManager` |
| `rustledger-plugin-types` | WASM plugin interface types | `PluginInput`, `PluginOutput`, `DirectiveWrapper` |
| `rustledger-ops` | Pure operations on directives | `RulesEngine`, `find_structural_duplicates`, `structural_hash`, `Enrichment` |
| `rustledger-lsp` | Language Server Protocol | LSP handlers for all standard features |
| `rustledger-importer` | Bank statement import | `CsvImporter`, `OfxImporter`, `auto_extract`, `EnrichedImportResult` |

### Distribution Layer

| Crate | Purpose |
|-------|---------|
| `rustledger` | CLI binary (`rledger`, `bean-*` commands) |
| `rustledger-wasm` | WebAssembly bindings for JS/TS |
| `rustledger-ffi-wasi` | FFI via WASI JSON-RPC for embedding |

## Data Flow

### Validation Pipeline

```
Input File
    │
    ▼
┌─────────────────────────────────────┐
│ 1. PARSE (rustledger-parser)        │
│    - Lexer tokenizes input          │
│    - Parser builds AST              │
│    - Recovers from syntax errors    │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 2. LOAD (rustledger-loader)         │
│    - Process includes               │
│    - Parse options                  │
│    - Cache compiled directives      │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 3. SORT (rustledger-loader) +       │
│    BOOK (rustledger-booking)        │
│    - Loader sorts by                │
│      date/type/cost-reduce          │
│    - Booking interpolates amounts   │
│    - Booking matches lots           │
│      (FIFO/LIFO/etc)                │
│    - Booking computes cost basis    │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 4. PLUGINS (rustledger-plugin)      │
│    - Run native plugins (30+)       │
│    - Run WASM plugins (sandboxed)   │
│    - Run Python plugins (via WASI)  │
│    - Transform directives           │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 5. VALIDATE (rustledger-validate)   │
│    - Check balance assertions       │
│    - Verify account opens/closes    │
│    - Validate commodities           │
└─────────────────────────────────────┘
    │
    ▼
Output (errors or success)
```

### Query Pipeline

```
BQL Query String
    │
    ▼
┌─────────────────────────────────────┐
│ 1. PARSE QUERY                      │
│    - Tokenize SQL-like syntax       │
│    - Build query AST                │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 2. LOAD LEDGER                      │
│    - Full validation pipeline       │
│    - Build posting database         │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 3. EXECUTE                          │
│    - Filter (WHERE)                 │
│    - Group (GROUP BY)               │
│    - Aggregate (SUM, COUNT, etc)    │
│    - Sort (ORDER BY)                │
└─────────────────────────────────────┘
    │
    ▼
Result Table
```

## Key Design Decisions

### 1. Error Recovery Parser

The parser continues after syntax errors, collecting as many errors as possible in one pass. This provides a better user experience than stopping at the first error.

See: [ADR-0003: Parser Design](adr/0003-parser-design.md)

### 2. Crate Separation

Each crate has a single responsibility and can be used independently:

- Want just parsing? Use `rustledger-parser`
- Want validation? Use `rustledger-validate` (depends on parser)
- Want queries? Use `rustledger-query`

See: [ADR-0001: Crate Organization](adr/0001-crate-organization.md)

### 3. Error Types

Each crate defines its own error type. The CLI crate uses `anyhow` to unify them. Library crates use `thiserror` for precise error types.

See: [ADR-0002: Error Handling](adr/0002-error-handling.md)

### 4. Plugin System

Plugins are executed by `run_plugins()` in `rustledger-loader`, the single source of truth for all file-declared plugin execution (native, WASM, and Python). The CLI additionally supports `--plugin` flags for CLI-specified WASM plugins that run as post-processing. Three plugin backends:

- **Native plugins** (30+): Rust implementations, zero serialization overhead
- **WASM plugins**: Any language compiled to WASM, sandboxed via wasmtime
- **Python plugins**: CPython compiled to WASI, runs existing beancount plugins

Plugin execution order within the pipeline: after booking, before validation. This ensures plugins see fully-interpolated directives and validation checks plugin output.

### 5. Binary Cache

Parsed ledgers are cached to disk in a binary format (rkyv) so subsequent runs can skip parsing entirely. The cache is stored as a hidden dotfile alongside the source — `ledger.beancount` → `.ledger.beancount.cache` — matching Python beancount's `.{filename}.picklecache` convention.

The cache header stores a SHA-256 hash over every source file's path, modification time, and size (the main ledger and all transitively-`include`d files). On load, the hash is recomputed from the cached file list; any mismatch rejects the cache and the ledger is re-parsed. File contents themselves are not hashed — content-based invalidation is a possible future improvement but isn't currently implemented.

Two environment variables, both compatible with Python beancount, control the cache: `BEANCOUNT_DISABLE_LOAD_CACHE` to opt out entirely, and `BEANCOUNT_LOAD_CACHE_FILENAME` to redirect to a custom path (with `{filename}` substitution). See [`rledger check`](../commands/check.md#cache-file) for usage details.

## Performance Characteristics

| Operation | Complexity | Notes |
|-----------|------------|-------|
| Parsing | O(n) | Single pass, no backtracking |
| Validation | O(n) | Linear scan of directives |
| Balance query | O(n) | Aggregates all postings |
| Account lookup | O(1) | Hash map |
| Lot matching | O(m) | m = lots in inventory |

Memory usage is proportional to ledger size, typically 3-5x smaller than Python beancount due to:

- No Python object overhead
- Efficient string interning
- SmallVec for small collections
