# Documentation

This directory contains developer documentation for rustledger.

## Contents

### User Guides
| Document | Description |
|----------|-------------|
| [MIGRATION.md](MIGRATION.md) | Guide for migrating from Python beancount |
| [IMPORTING.md](IMPORTING.md) | CSV/OFX bank statement import tutorial |
| [BQL_REFERENCE.md](BQL_REFERENCE.md) | BQL query language quick reference |
| [VALIDATION_ERRORS.md](VALIDATION_ERRORS.md) | Reference for all validation error codes (E0001-E0702) |

### Developer Guides
| Document | Description |
|----------|-------------|
| [ARCHITECTURE.md](ARCHITECTURE.md) | Crate structure and data flow diagrams |
| [BENCHMARKING.md](BENCHMARKING.md) | How to run benchmarks and interpret results |
| [COMPATIBILITY_REPORT.md](COMPATIBILITY_REPORT.md) | Test results comparing rustledger to Python beancount |
| [TESTING.md](TESTING.md) | Testing guide and best practices |

### Roadmaps
| Document | Description |
|----------|-------------|
| [PERFORMANCE_ROADMAP.md](PERFORMANCE_ROADMAP.md) | Performance optimization phases and measured results |
| [TESTING_ROADMAP.md](TESTING_ROADMAP.md) | Testing infrastructure improvement plan |

## Architecture Decision Records

The [adr/](adr/) directory contains Architecture Decision Records documenting key design decisions:

- [ADR-0001: Crate Organization](adr/0001-crate-organization.md)
- [ADR-0002: Error Handling](adr/0002-error-handling.md)
- [ADR-0003: Parser Design](adr/0003-parser-design.md)

## Related Documentation

- **[spec/](../spec/)** - Technical specifications (syntax, algorithms, validation)
- **[spec/tla/](../spec/tla/)** - TLA+ formal specifications
- **[CONTRIBUTING.md](../CONTRIBUTING.md)** - Contribution guidelines
- **[ROADMAP.md](../ROADMAP.md)** - Project roadmap
