# rustledger-cst

Lossless concrete syntax tree (CST) for Beancount, built on
[`rowan`](https://crates.io/crates/rowan).

Phase 1 of the parser-CST migration tracked in
[#1262](https://github.com/rustledger/rustledger/issues/1262). This
crate provides:

- `SyntaxKind`: every token and node kind in the Beancount grammar.
- `SyntaxNode` / `SyntaxToken`: `rowan` type aliases specialized to
  the Beancount language.
- `lossless_tokens(source)`: trivia-preserving adapter over
  `rustledger_parser::logos_lexer::tokenize`.
- `parse_flat(source)`: produce a flat `SOURCE_FILE` rowan tree whose
  text round-trips byte-identically with the input.

## Invariants

- For every input `source`, `parse_flat(source).text().to_string() == source`
  byte-for-byte. Exercised over the full ~700-file compatibility corpus
  in `tests/round_trip.rs`.
- The phase-1 tree is FLAT — every token is a direct child of
  `SOURCE_FILE`. Phase 2 will replace this driver with a structured
  parser that nests tokens under typed directive / posting / amount
  nodes, without changing the byte-preservation property.

See [#1262](https://github.com/rustledger/rustledger/issues/1262) for
the full migration plan, decision register, and phase-by-phase scope.
