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
use rustledger_importer::{ImporterConfig, extract_from_file};
use std::path::Path;

// Create a CSV importer configuration
let config = ImporterConfig::csv()
    .account("Assets:Bank:Checking")
    .currency("USD")
    .date_column("Date")
    .narration_column("Description")
    .amount_column("Amount")
    .build();

// Extract transactions from a file
let result = extract_from_file(Path::new("bank.csv"), &config)?;

for directive in result.directives {
    println!("{:?}", directive);
}
```

## Key Types

| Type | Description |
|------|-------------|
| `Importer` | Trait for file importers |
| `ImporterConfig` | Builder for configuring CSV imports |
| `ImportResult` | Result containing directives and warnings |
| `ImporterRegistry` | Registry of available importers |
| `OfxImporter` | OFX/QFX file importer |

## Importer Trait

Implement the `Importer` trait to add support for new file formats:

```rust
use rustledger_importer::{Importer, ImportResult};
use std::path::Path;
use anyhow::Result;

struct MyImporter;

impl Importer for MyImporter {
    fn name(&self) -> &str { "my-importer" }

    fn identify(&self, path: &Path) -> bool {
        path.extension().is_some_and(|e| e == "myext")
    }

    fn extract(&self, path: &Path) -> Result<ImportResult> {
        // Parse file and return directives
        Ok(ImportResult::empty())
    }
}
```

## License

GPL-3.0
