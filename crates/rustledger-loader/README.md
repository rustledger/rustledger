# rustledger-loader

Beancount file loader with include resolution, options parsing, and binary caching.

## Features

- Recursive `include` directive resolution
- Option parsing and validation
- Plugin directive collection
- Binary cache for faster subsequent loads
- Path traversal protection

## Example

```rust
use rustledger_loader::{Loader, LoadOptions};
use std::path::Path;

// Simple loading (raw parse without processing)
let result = Loader::new().load(Path::new("ledger.beancount"))?;
println!("Loaded {} directives", result.directives.len());

// With full processing (booking, plugins, validation)
use rustledger_loader::load;
let ledger = load(Path::new("ledger.beancount"), &LoadOptions::default())?;
println!("Processed {} directives", ledger.directives.len());
```

## Cargo Features

- `cache` (default) - Enable rkyv-based binary caching for faster loads
- `full` (default) - Full processing pipeline (booking + plugins + validation); required for the `load` / `process` API used in the example above
- `booking` / `plugins` / `validation` - Individual processing features (enabled together by `full`)

## License

GPL-3.0
