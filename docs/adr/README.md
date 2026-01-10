# Architecture Decision Records

This directory contains Architecture Decision Records (ADRs) documenting significant design decisions in rustledger.

## Index

| ADR | Title | Status |
|-----|-------|--------|
| [0001](0001-crate-organization.md) | Crate Organization | Accepted |
| [0002](0002-error-handling.md) | Error Handling Strategy | Accepted |
| [0003](0003-parser-design.md) | Parser Design | Accepted |

## What is an ADR?

An Architecture Decision Record captures a significant architectural decision along with its context and consequences. ADRs help future contributors understand why certain design choices were made.

## ADR Template

```markdown
# ADR-NNNN: Title

## Status

[Proposed | Accepted | Deprecated | Superseded by ADR-XXXX]

## Context

What is the issue that we're seeing that is motivating this decision?

## Decision

What is the change that we're proposing and/or doing?

## Consequences

What becomes easier or more difficult to do because of this change?
```
