# wasm-importer-csv-example

A minimal reference WASM importer for rustledger. Parses a 3-column CSV
(`Date,Description,Amount`) and emits one Beancount transaction per row.

This is an **example**, not a production importer. The host crate's
built-in `CsvImporter` is the right choice for real CSV imports — it
supports configurable column mappings, locale-aware amount parsing,
mapping rules, and dedup fingerprints. The example here exists to show
external authors what a real-world `extract` body looks like end to end.

## Building

```sh
rustup target add wasm32-unknown-unknown
cargo build --release --target wasm32-unknown-unknown
# Output: target/wasm32-unknown-unknown/release/wasm_importer_csv_example.wasm
```

## Using it from the host

```rust
// `Importer` is the trait that provides `extract` / `extract_enriched`
// / `identify`; without it the WasmImporter methods don't resolve.
use rustledger_importer::{Importer, ImporterConfig, WasmImporter};

let importer = WasmImporter::load(
    "target/wasm32-unknown-unknown/release/wasm_importer_csv_example.wasm",
)?;

// Now usable like any other Importer:
let config = ImporterConfig::csv()
    .account("Assets:Bank:Checking")
    .currency("USD")
    .build()?;

let result = importer.extract(std::path::Path::new("statement.csv"), &config)?;
for d in &result.directives {
    println!("{d:?}");
}
for w in &result.warnings {
    eprintln!("warning: {w}");
}
```

## Expected input format

```csv
Date,Description,Amount
2024-01-15,Coffee shop,-4.50
2024-01-16,Paycheck,2500.00
```

- Header row is required (and skipped).
- Amounts may be signed (`-4.50`, `+2500.00`, or `2500.00`).
- Negative amounts → debit posting against `Expenses:Unknown`.
- Positive amounts → credit posting against `Income:Unknown`.
- Malformed rows (wrong column count, unparsable amount) are emitted
  as per-row warnings rather than aborting the whole import — bank
  exports often contain trailing metadata that's better skipped than
  rejected.

## Limitations

The example uses a naive comma-splitter, so quoted fields containing
commas are **not** handled. For that you'd want a proper CSV library
(`csv` on crates.io); we omit it here to keep the example's `.wasm`
small and the source readable.
