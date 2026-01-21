# Parser Crate Guidelines

This document provides context for AI assistants working on the rustledger-parser crate.

## Overview

This crate provides a Beancount parser using Logos (lexer) + Chumsky (parser combinators). It handles all 12 Beancount directive types with error recovery.

## Architecture

| File | Purpose |
|------|---------|
| `logos_lexer.rs` | Lexer using Logos - converts source to tokens |
| `token_parser.rs` | Chumsky parser - builds AST from tokens |
| `error.rs` | Parse error types and formatting |
| `span.rs` | Source location tracking |

## Critical Rules

### Security: No Panics on Malformed Input

The parser MUST handle any input gracefully:
- Never use `.unwrap()` on user input
- Use `recover_with()` for error recovery
- Test with fuzz inputs (`cargo fuzz run parser`)

### Error Recovery

The parser continues after errors to report multiple issues:
```rust
// Good: Use recovery to skip bad input
directive
    .recover_with(skip_then_retry_until([Token::Newline]))
```

### Error Messages

Error messages must include source location:
```rust
ParseError {
    kind: ParseErrorKind::InvalidDate,
    span: Span { start: 0, end: 10 },
    expected: vec!["YYYY-MM-DD".into()],
    found: Some("2024/01/15".into()),
}
```

## Testing

### Required Tests for Parser Changes

1. **Valid input**: Parse known-good beancount files
2. **Invalid input**: Verify error messages are helpful
3. **Error recovery**: Multiple errors reported, parsing continues
4. **Fuzz testing**: No panics on arbitrary input

### Test Commands

```bash
# Unit tests
cargo test -p rustledger-parser

# Snapshot tests (error messages)
cargo insta test -p rustledger-parser

# Fuzz testing (requires nightly)
cargo +nightly fuzz run parser
```

## Beancount Compatibility

When in doubt, check Python beancount behavior:
```bash
# Compare outputs
bean-check test.beancount
./target/debug/rledger-check test.beancount
```

Reference files in `spec/fixtures/` for expected behavior.

## Common Tasks

### Adding a New Token

1. Add variant to `Token` enum in `logos_lexer.rs`
2. Add regex pattern with `#[regex(...)]` attribute
3. Handle in `token_parser.rs`
4. Add tests for lexing and parsing

### Improving Error Messages

1. Add case to `ParseErrorKind` in `error.rs`
2. Update `Display` impl with user-friendly message
3. Add snapshot test for the error message
4. Run `cargo insta review` to approve
