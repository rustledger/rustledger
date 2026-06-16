______________________________________________________________________

## title: Architecture Decision Records description: Key design decisions and rationale

# Architecture Decision Records

ADRs document significant architectural decisions made during rustledger development.

## Records

| ADR | Title | Status |
|-----|-------|--------|
| [ADR-0001](0001-crate-organization.md) | Crate Organization | Accepted |
| [ADR-0002](0002-error-handling.md) | Error Handling | Accepted |
| [ADR-0003](0003-parser-design.md) | Parser Design | Accepted |
| [ADR-0004](0004-ts-types-from-rust-dtos.md) | Generate wire-format bindings from Rust DTOs | Accepted (Phase 1 + 2 + 3) |
| [ADR-0005](0005-cst-conversion-performance.md) | CST Conversion Performance (parse cache; green-tree declined) | Accepted |
| [ADR-0006](0006-wit-component-model-embedding.md) | WIT / Component-Model embedding contract | Proposed |

## About ADRs

Architecture Decision Records capture the context, decision, and consequences of significant technical choices. They help future contributors understand why things are built the way they are.

## See Also

- [Architecture](../architecture.md) - Overall system architecture
- [Development Guide](../../development/index.md) - Contributing to rustledger
