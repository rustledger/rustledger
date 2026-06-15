# rustledger-parser

Fast Beancount parser built on a Logos lexer and a lossless Rowan CST.

## Features

- Full Beancount syntax support (all 12 directive types)
- Error recovery (continues parsing after errors)
- Precise source locations for error reporting
- SIMD-accelerated lexing via Logos

## Architecture

```
Source (&str) → Logos lexer → lossless CST (Rowan) → CST converter → Directives
```

## Example

```rust
use rustledger_parser::parse;

let source = r#"
2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food:Coffee  5.00 USD
  Assets:Cash
"#;

let result = parse(source);
assert!(result.errors.is_empty());
assert_eq!(result.directives.len(), 1);
```

## Cargo Features

- `rkyv` (default) - Enable rkyv serialization for binary caching

## License

GPL-3.0
