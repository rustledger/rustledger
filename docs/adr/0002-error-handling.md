# ADR-0002: Error Handling Strategy

## Status

Accepted

## Context

Accounting software needs robust error handling. Errors can occur during:

- Parsing (syntax errors, invalid dates, malformed amounts)
- Loading (file not found, include cycles, path traversal)
- Validation (unbalanced transactions, unknown accounts)
- Query execution (type mismatches, unknown columns)

We need to decide:

1. How to represent errors (enums, traits, strings)
1. Whether to fail-fast or collect multiple errors
1. How to provide good error messages with source locations

## Decision

### Error Representation

Use `thiserror` to derive `Error` implementations with strongly-typed error enums per crate:

- `ParseError` in rustledger-parser
- `LoadError` in rustledger-loader
- `ValidationError` in rustledger-validate
- `QueryError` in rustledger-query

Each error type includes relevant context (spans, file paths, expected vs found values).

### Error Collection vs Fail-Fast

**Parser**: Collect errors and continue parsing to report multiple issues at once. Return `ParseResult` with both `directives` and `errors` vectors.

**Loader**: Collect errors for parse failures and path issues, but fail-fast on include cycles (which would cause infinite loops).

**Validator**: Collect all validation errors to report everything wrong with a ledger in one pass.

**Query**: Fail-fast on query errors since partial results would be misleading.

### Source Locations

All errors that can occur at specific source locations include `Span` information (byte offsets). The `SourceMap` tracks file contents for error rendering.

## Consequences

### Positive

- Users see all syntax errors at once, not one at a time
- Typed errors enable programmatic handling
- Span information enables IDE-quality error messages
- `#[must_use]` on Result types prevents ignored errors

### Negative

- Error collection requires more complex parser recovery logic
- Multiple error types mean more code to write
- Must be careful to propagate errors correctly

### Neutral

- Using `thiserror` rather than manual `impl Error`
