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
    │ (lexer/parser)  │         │  (27 error codes)   │         │ (7 booking modes)│
    └────────┬────────┘         └────────┬────────────┘         └────────┬────────┘
              │                              │                              │
              └──────────────────────────────┼──────────────────────────────┘
                                             │
                                             ▼
                                  ┌─────────────────┐
                                  │ rustledger-core │
                                  │  (core types)   │
                                  └─────────────────┘


    ┌─────────────────┐           ┌─────────────────┐
    │ rustledger-wasm │           │rustledger-import│
    │ (JS/TS bindings)│           │  (CSV/OFX)      │
    └────────┬────────┘           └─────────────────┘
              │
              └─────────────────► rustledger-core, parser, query
```

## Crate Descriptions

### Core Layer

| Crate | Purpose | Key Types |
|-------|---------|-----------|
| `rustledger-core` | Fundamental types | `Amount`, `Position`, `Inventory`, `Decimal`, `Account`, `Currency` |
| `rustledger-parser` | Lexer and recursive descent parser | `Directive`, `Transaction`, `Posting`, `ParseError` |

### Processing Layer

| Crate | Purpose | Key Types |
|-------|---------|-----------|
| `rustledger-loader` | File loading, includes, caching | `Loader`, `LoadedLedger`, `Options` |
| `rustledger-booking` | Cost basis and lot matching | `BookingMethod` (FIFO, LIFO, HIFO, etc.) |
| `rustledger-validate` | Validation rules | `ValidationError`, 27 error codes (E0001-E0702) |

### Feature Layer

| Crate | Purpose | Key Types |
|-------|---------|-----------|
| `rustledger-query` | BQL query engine | `Query`, `Executor`, `Table`, `Row` |
| `rustledger-plugin` | Native + Python plugins | `NativePlugin`, `PluginRegistry` |
| `rustledger-lsp` | Language Server Protocol | LSP handlers for all standard features |
| `rustledger-importer` | Bank statement import | `CsvImporter`, `OfxImporter` |

### Distribution Layer

| Crate | Purpose |
|-------|---------|
| `rustledger` | CLI binary (`rledger`, `bean-*` commands) |
| `rustledger-wasm` | WebAssembly bindings for JS/TS |

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
│ 3. PLUGINS (rustledger-plugin)      │
│    - Run native plugins             │
│    - Run Python plugins (WASI)      │
│    - Transform directives           │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 4. BOOKING (rustledger-booking)     │
│    - Interpolate missing amounts    │
│    - Match lots (FIFO/LIFO/etc)     │
│    - Compute cost basis             │
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

### 4. Python Plugin Sandbox

Python plugins run in a WebAssembly sandbox (CPython compiled to WASI). This provides:
- Security: Plugins can't access filesystem or network
- Portability: No system Python needed
- Compatibility: Runs existing Python plugins

### 5. Binary Cache

Parsed ledgers are cached to disk in a binary format. Subsequent runs skip parsing if the source hasn't changed. Cache invalidation is based on file modification times.

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
