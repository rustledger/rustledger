# rustledger-validate

Beancount validation with 26 error codes for ledger correctness.

## Error Categories

| Range | Category |
|-------|----------|
| E1xxx | Account errors (not opened, already closed, etc.) |
| E2xxx | Balance/pad errors |
| E3xxx | Transaction errors (unbalanced, no postings) |
| E4xxx | Inventory/lot errors |
| E5xxx | Currency errors |
| E6xxx | Metadata errors |
| E7xxx | Option errors |
| E8xxx | Document errors |
| E10xxx | Date warnings |

## Example

Validation is run through a `ValidationSession`. Standalone callers
(LSP, FFI, tests on already-booked input) drive the two phases plus
`finalize` directly; the loader pipeline interleaves booking between
phases.

```rust
use rustledger_validate::{Phase, ValidationOptions, ValidationSession};
use rustledger_core::{Directive, naive_date};

let directives: Vec<Directive> = vec![/* parsed + booked input */];
let today = naive_date(2030, 1, 1).unwrap();

let mut session = ValidationSession::new(ValidationOptions::default());
let mut errors = session.run_phase(&directives, Phase::Early, today);
errors.extend(session.run_phase(&directives, Phase::Late, today));
errors.extend(session.finalize());

for error in errors {
    eprintln!("{}: {}", error.code(), error.message());
}
```

The previous free-function shortcuts (`validate`, `validate_with_options`)
were removed in #1116 when validation was split around booking. Callers
must now thread state through a `ValidationSession` so that `Phase::Late`
sees the inventory state accumulated during `Phase::Early`.

## Features

- Parallel validation with rayon
- Configurable error severity
- Rich error messages with source locations

## License

GPL-3.0
