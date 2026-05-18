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
| `rustledger-validate` | Validation rules | `ValidationError`, 26 error codes (E1001-E10002) |

### Feature Layer

| Crate | Purpose | Key Types |
|-------|---------|-----------|
| `rustledger-query` | BQL query engine | `Query`, `Executor`, `Table`, `Row` |
| `rustledger-plugin` | Native + WASM + Python plugins | `NativePlugin`, `NativePluginRegistry`, `PluginManager`, `WasmPluginDirScanReport` (skip-and-collect dir scan via `PluginManager::register_wasm_dir`) |
| `rustledger-plugin-types` | WASM plugin interface types (directive plugins **and** WASM importers) | `PluginInput`, `PluginOutput`, `DirectiveWrapper`, `ImporterInput`, `ImporterOutput`, `EnrichedImporterOutput`, `wasm_plugin_main!`, `wasm_importer_main!` |
| `rustledger-ops` | Pure operations on directives | `RulesEngine`, `find_structural_duplicates`, `structural_hash`, `Enrichment` |
| `rustledger-lsp` | Language Server Protocol | LSP handlers for all standard features |
| `rustledger-importer` | Bank statement import | `Importer` trait, `ImporterRegistry`, `CsvImporter`, `OfxImporter`, `WasmImporter`, `WasmRuntimeConfig`, `WasmDirScanReport`, `auto_extract`, `EnrichedImportResult` |

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
│ PARSE (rustledger-parser)           │
│    - Lexer tokenizes input          │
│    - Parser builds AST              │
│    - Recovers from syntax errors    │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ LOAD (rustledger-loader)            │
│    - Process includes               │
│    - Parse options                  │
│    - Cache compiled directives      │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 1. SORT (rustledger-loader)         │
│    - Sort by date/type/lineno       │
│      (matches Python's              │
│      entry_sortkey())               │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 2. SYNTH PLUGINS                    │
│    (rustledger-plugin)              │
│    - Account-injecting plugins      │
│      run BEFORE Early validation    │
│    - e.g. auto_accounts,            │
│      document_discovery             │
│    - Selected via                   │
│      NativePlugin::is_synth()       │
│      → PluginPass::Synth            │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 3. EARLY VALIDATION                 │
│    (rustledger-validate)            │
│    - Account-presence checks        │
│      (Open before use, etc.) —      │
│      sees Opens synthesized by      │
│      synth plugins above            │
│    - Catches issues that would      │
│      otherwise be hidden by         │
│      booking interpolation          │
│      (see Python beancount #877)    │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 4. BOOK (rustledger-booking)        │
│    - Interpolate elided amounts     │
│    - Match lots (FIFO/LIFO/HIFO/…)  │
│    - Compute cost basis             │
│    - Fill in cost.number_per from   │
│      total cost specs               │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 5. PARTITION + REGULAR PLUGINS      │
│    (rustledger-plugin)              │
│    - All non-synth plugins run      │
│      AFTER booking, so cost-spec-   │
│      reading plugins see filled-in  │
│      number_per                     │
│    - Native + WASM + Python         │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 6. LATE VALIDATION                  │
│    (rustledger-validate)            │
│    - Balance assertions             │
│    - Commodity / currency checks    │
│    - Post-booking invariants        │
└─────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────┐
│ 7. FINALIZE + RE-MERGE              │
│    (rustledger-loader)              │
│    - Re-merge plugin-emitted        │
│      directives back into the       │
│      sorted stream                  │
│    - Build the final LoadedLedger   │
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

Plugin execution is **split across two passes** of the pipeline (see the seven-step diagram above). Plugins declare which pass they belong to via `NativePlugin::is_synth()`, which selects between the two `PluginPass` variants:

- **Synth plugins** (`PluginPass::Synth`) run **before Early validation**. These are account- or directive-injecting plugins like `auto_accounts` and `document_discovery`. Running them first means the Early validator's account-presence checks (Open-before-use) see the directives synth plugins inject — preventing false positives that would otherwise occur when a plugin is responsible for opening an account that subsequent transactions reference.

- **Regular plugins** (`PluginPass::Regular`) — every plugin where `is_synth()` returns `false` — run **after booking**. This is the right phase for plugins that consume booked output, particularly cost-spec readers that need `cost.number_per` filled in from a total cost spec (the booking engine computes this). Validators that need post-interpolation amounts also belong here.

After the regular pass, **Late validation** runs (balance assertions, commodity checks, post-booking invariants), then the loader finalizes the ledger by re-merging plugin-emitted directives into the sorted stream.

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
