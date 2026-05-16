# rustledger-importer

Import framework for rustledger - extract transactions from bank files.

## Overview

This crate provides infrastructure for extracting Beancount transactions from bank statements, credit card statements, and other financial documents. It follows the design of Python beancount's `bean-extract`.

## Supported Formats

| Format | Description |
|--------|-------------|
| CSV | Configurable CSV importer with column mapping |
| OFX/QFX | Open Financial Exchange format |

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
// .ofx/.qfx and CsvImporter for .csv.
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
use rustledger_importer::{auto_extract, CsvConfigBuilder};
use std::path::Path;

// Zero-config: auto-detect format and enrich
let result = auto_extract(Path::new("bank.csv"), "Assets:Bank:Checking")?;

for entry in &result.enriched {
    println!("{}: {} (confidence {:.0}%)",
        entry.directive, entry.category, entry.confidence * 100.0);
}

// Or opt-in to enrichment via the builder
let config = CsvConfigBuilder::new()
    .account("Assets:Bank:Checking")
    .currency("USD")
    .use_merchant_dict()
    .build();
```

## Key Types

| Type | Description |
|------|-------------|
| `Importer` | Trait for file importers |
| `ImporterConfig` | Builder for configuring CSV imports |
| `ImportResult` | Result containing directives and warnings |
| `ImporterRegistry` | Registry of available importers |
| `OfxImporter` | OFX/QFX file importer |
| `EnrichedImportResult` | Result with confidence scores and fingerprints |
| `CsvConfigBuilder::use_merchant_dict()` | Enable built-in merchant dictionary |
| `auto_extract()` | Zero-config import with auto-detection |

## Importer Trait

Implement the `Importer` trait to add support for new file formats:

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
        Ok(ImportResult::empty())
    }
}
```

## License

GPL-3.0
