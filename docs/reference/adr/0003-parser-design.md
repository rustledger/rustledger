# ADR-0003: Parser Design

## Status

Accepted (Updated June 2026)

> **Note (June 2026):** The Winnow-based parser described below was subsequently
> replaced by a hand-written Rowan-based lossless CST parser (`cst/parser.rs`);
> Logos is retained for lexing. The Winnow design is preserved here as the
> historical record — see the Changelog at the end.

## Context

The Beancount language has a relatively simple grammar but with some complexities:

- Date-prefixed directives
- Indentation-sensitive posting syntax
- Metadata can appear on many directive types
- String literals with escapes
- Multiple number formats (with comma grouping)

Options considered:

1. **Parser generator** (pest, lalrpop): Generate parser from grammar
1. **Parser combinator** (nom, winnow, chumsky): Compose small parsers
1. **Hand-written recursive descent**: Manual implementation

## Decision

Use **Logos for lexing** and **Winnow for parsing** (parser combinators).

### Lexer (Logos)

The lexer (`logos_lexer.rs`) uses Logos, a SIMD-accelerated lexer generator:

- Declarative token definitions via derive macros
- ~54x faster than hand-written character iteration
- Produces `Vec<(Token, Span)>` with byte offset spans

Tokens include:

- Keywords (open, close, balance, etc.)
- Dates, numbers, strings, accounts, currencies
- Operators and punctuation

### Parser (Winnow)

The parser (`cst/parser.rs`) uses a manual token stream with winnow-style parsing:

- Composable parsers for each directive type
- Manual token stream for simplicity and performance
- Error recovery continues parsing after errors
- Span tracking propagated through all parse results

Architecture:

```text
Source (&str) → Logos tokenize() → Vec<(Token, Span)> → CST parser → Directives
```

## Consequences

### Positive

- Logos provides excellent lexer performance (SIMD-accelerated)
- Winnow is lightweight with minimal compile-time overhead
- Manual token stream approach is simpler than trait-based streams
- Type-safe parser composition catches errors at compile time
- No external grammar DSL files to maintain

### Negative

- Manual token stream requires more boilerplate
- Less built-in error recovery than some frameworks
- Must handle overflow/edge cases explicitly (e.g., checked arithmetic)

### Neutral

- Parser is ~1500 lines, manageable for the grammar size
- Error messages require tuning for user-friendliness

## Notes

The parser is organized into sections:

1. Token stream types and helpers
1. Primitive parsers (date, number, string, account)
1. Expression parsers (arithmetic with checked overflow)
1. Amount and cost parsers
1. Directive parsers (transaction, balance, open, etc.)
1. Top-level file parser with error recovery

## History

- **Original decision**: Hand-written recursive descent parser
- **January 2026**: Migrated to Logos + Chumsky for better performance
- **February 2026**: Migrated from Chumsky to Winnow for faster compile times and simpler code
- **June 2026**: Replaced Winnow with a hand-written Rowan-based lossless CST parser (`cst/parser.rs`); Logos is retained for lexing
