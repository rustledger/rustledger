# rustledger-importer

Import framework for rustledger - extract transactions from bank files.

## Overview

This crate provides infrastructure for extracting Beancount transactions from
bank statements, credit card statements, and other financial documents. It
follows the design of Python beancount's `bean-extract`.

Importers come in two flavors:

- **Built-in importers** (CSV, OFX/QFX) — compiled into the crate.
- **WASM importers** — third-party `.wasm` modules loaded at runtime through
  the `WasmImporter` host loader. Sandboxed via wasmtime (no FS / network /
  WASI), so untrusted modules are safe to load. See
  [`examples/wasm-importer-csv-example`][csv-example] for a reference guest
  implementation built with the `wasm_importer_main!` macro in
  `rustledger-plugin-types`.

[csv-example]: ../../examples/wasm-importer-csv-example/

## Supported Formats

| Format | Source | Description |
|--------|--------|-------------|
| CSV | built-in | Configurable CSV importer with column mapping |
| OFX/QFX | built-in | Open Financial Exchange format |
| _any_ | WASM | Any format a third-party `.wasm` module implements |

## Example

```rust
use rustledger_importer::{ImporterConfig, ImporterRegistry};
use std::path::Path;

// Build the per-call config (CSV in this example).
let config = ImporterConfig::csv()
    .account("Assets:Bank:Checking")
    .currency("USD")
    .date_column("Date")
    .narration_column("Description")
    .amount_column("Amount")
    .build()?;

// Dispatch through the registry — `identify()` picks OfxImporter for
// .ofx/.qfx and CsvImporter for .csv. Add WASM importers via
// `register_wasm_from_path` / `register_wasm_dir`; once registered, they
// participate in the same identify-then-extract dispatch.
let registry = ImporterRegistry::with_builtins();
let result = registry.extract(Path::new("bank.csv"), &config)?;

for directive in result.directives {
    println!("{:?}", directive);
}
```

## Enriched Imports

The enrichment pipeline adds intelligence on top of basic CSV/OFX extraction:

- **Auto-inference** of CSV format (delimiter, date format, column roles)
- **Merchant dictionary** for automatic account categorization
- **Fingerprinting** for dedup against existing ledger entries
- **Confidence scores** on every enrichment decision

```rust
use rustledger_importer::auto_extract;
use std::path::Path;

// Zero-config: auto-detect format and enrich. Signature is
// `(path, account, currency)`.
let result = auto_extract(
    Path::new("bank.csv"),
    "Assets:Bank:Checking",
    "USD",
)?;

// `EnrichedImportResult.entries: Vec<(Directive, Enrichment)>`.
for (directive, enrichment) in &result.entries {
    println!(
        "{:?}: method={:?} (confidence {:.0}%)",
        directive,
        enrichment.method,
        enrichment.confidence * 100.0,
    );
}

// Or opt-in to enrichment via the builder. `use_merchant_dict` takes a
// bool — pass `true` to enable the built-in merchant dictionary fallback.
use rustledger_importer::ImporterConfig;
let config = ImporterConfig::csv()
    .account("Assets:Bank:Checking")
    .currency("USD")
    .use_merchant_dict(true)
    .build()?;
```

## WASM Importers

Load a third-party importer at runtime from a `.wasm` file:

```rust
use rustledger_importer::ImporterRegistry;

let mut registry = ImporterRegistry::with_builtins();

// Single-file load (uses default sandbox: 256 MiB memory, 30 s fuel).
let name = registry.register_wasm_from_path("/path/to/my-bank.wasm")?;
println!("loaded WASM importer: {name}");

// Or scan a directory — skip-and-collect: one broken module doesn't
// prevent the rest from loading.
let report = registry.register_wasm_dir("/etc/rustledger/importers.d")?;
println!("loaded {} WASM importers", report.loaded.len());
for (path, err) in &report.failures {
    eprintln!("failed to load {}: {err}", path.display());
}
```

To **author** a WASM importer, depend on `rustledger-plugin-types` with the
`guest` feature and use the `wasm_importer_main!` macro. See
[`examples/wasm-importer-csv-example`][csv-example] for a minimal but
realistic implementation and the macro's docs in `rustledger-plugin-types`.

## Key Types

| Type | Description |
|------|-------------|
| `Importer` | Trait for file importers — implemented by built-ins and WASM |
| `ImporterConfig` | Per-call configuration (target account, currency, format-specific) |
| `ImportResult` | Result containing directives and warnings |
| `EnrichedImportResult` | Result with `(Directive, Enrichment)` pairs and warnings |
| `ImporterRegistry` | Registry; dispatches by `identify()`; loads WASM importers |
| `OfxImporter` | Built-in OFX/QFX file importer |
| `WasmImporter` | Host loader for WASM-implemented importers |
| `WasmRuntimeConfig` | Per-call sandbox caps (memory, fuel) for `WasmImporter` |
| `WasmDirScanReport` | Return type of `register_wasm_dir` — loaded names + failures |
| `auto_extract()` | Zero-config import with format auto-detection |

## Importer Trait

Implement the `Importer` trait to add support for new file formats from
*inside* the workspace. (External authors should target the WASM ABI
instead — `wasm_importer_main!` in `rustledger-plugin-types`.)

```rust
use rustledger_importer::{Importer, ImportResult, ImporterConfig};
use std::path::Path;
use anyhow::Result;

struct MyImporter;

impl Importer for MyImporter {
    fn name(&self) -> &str { "my-importer" }

    fn identify(&self, path: &Path) -> bool {
        path.extension().is_some_and(|e| e == "myext")
    }

    fn extract(&self, _path: &Path, _config: &ImporterConfig) -> Result<ImportResult> {
        // Parse the file using `_config.account` / `_config.currency` and
        // return directives. Implementors should be stateless; per-call
        // configuration flows in via the `_config` parameter.
        //
        // `extract_enriched` has a default impl that wraps `extract` with
        // a `Default` categorization method and computed fingerprints.
        // Override it to surface real categorization confidence.
        Ok(ImportResult::empty())
    }
}
```

## License

GPL-3.0
