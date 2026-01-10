# ADR-0003: Parser Design

## Status

Accepted

## Context

The Beancount language has a relatively simple grammar but with some complexities:

- Date-prefixed directives
- Indentation-sensitive posting syntax
- Metadata can appear on many directive types
- String literals with escapes
- Multiple number formats (with comma grouping)

Options considered:

1. **Parser generator** (pest, lalrpop): Generate parser from grammar
1. **Parser combinator** (nom, winnow): Compose small parsers
1. **Hand-written recursive descent**: Manual implementation

## Decision

Use a **hand-written recursive descent parser** with a separate lexer.

### Lexer

The lexer (`lexer.rs`) tokenizes input into:

- Keywords (open, close, balance, etc.)
- Dates, numbers, strings, accounts, currencies
- Operators and punctuation
- Indentation tracking

### Parser

The parser (`parser.rs`) consumes tokens and builds AST nodes:

- One method per directive type
- Error recovery by skipping to next date or newline
- Span tracking for all nodes

## Consequences

### Positive

- Full control over error messages and recovery
- No external grammar DSL to learn
- Easier to debug parsing issues
- No build-time code generation step
- Better error messages with context

### Negative

- More code to write and maintain
- Risk of bugs that a grammar would catch
- Changes to syntax require manual parser updates

### Neutral

- Parser is ~1500 lines, manageable for the grammar size
- Uses `Peekable<Iterator>` pattern for lookahead

## Notes

The parser is organized into sections:

1. Entry points (parse, parse_directive)
1. Directive parsers (transaction, balance, open, etc.)
1. Expression parsers (amount, metadata, postings)
1. Utility methods (expect, peek, advance)
