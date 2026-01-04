# Directive Ordering Specification

This document specifies the exact ordering rules for directives.

## Overview

Beancount directives are sorted chronologically by date. When dates are equal, a secondary ordering determines the sequence.

## Primary Sort: Date

All directives are sorted by date ascending:

```
2024-01-01 ... (first)
2024-01-02 ...
2024-01-03 ... (last)
```

## Secondary Sort: Directive Type Priority

When dates are equal, directives are ordered by type priority:

| Priority | Directive Type | Rationale |
|----------|---------------|-----------|
| 0 | `open` | Accounts must exist before use |
| 1 | `commodity` | Commodities declared before use |
| 2 | `pad` | Padding before balance assertions |
| 3 | `balance` | Assertions checked at start of day |
| 4 | `transaction` | Main entries |
| 5 | `note` | Annotations after transactions |
| 6 | `document` | Attachments after transactions |
| 7 | `event` | State changes |
| 8 | `query` | Queries defined after data |
| 9 | `price` | Prices at end of day |
| 10 | `close` | Accounts closed after all activity |
| 11 | `custom` | User extensions last |

## Tertiary Sort: File Order

When date and type are equal, directives appear in file order (line number):

```beancount
; Same date, same type - file order preserved
2024-01-01 * "First transaction"
  ...

2024-01-01 * "Second transaction"
  ...
```

## Balance Assertion Timing

Balance assertions check the balance at the **beginning of the day** (midnight):

```beancount
2024-01-15 * "Deposit"
  Assets:Checking  100 USD
  Income:Salary

2024-01-15 balance Assets:Checking  100 USD  ; Checks BEFORE the deposit!
```

This assertion checks the balance **before** any transactions on 2024-01-15.

To check the balance **after** the deposit, use the next day:

```beancount
2024-01-15 * "Deposit"
  Assets:Checking  100 USD
  Income:Salary

2024-01-16 balance Assets:Checking  100 USD  ; Checks AFTER the deposit
```

## Pad and Balance Interaction

Pad directives must come before their corresponding balance assertion:

```beancount
2024-01-01 pad Assets:Checking Equity:Opening-Balances
2024-01-01 balance Assets:Checking  1000 USD
```

The pad is processed first (priority 2), then the balance assertion (priority 3).

## Open and Close Timing

- `open` is effective at the **start** of the day
- `close` is effective at the **end** of the day

```beancount
2024-01-01 open Assets:Checking

2024-01-01 * "Same day deposit is OK"
  Assets:Checking  100 USD
  Income:Salary

2024-12-31 * "Same day withdrawal is OK"
  Assets:Checking  -100 USD
  Expenses:Final

2024-12-31 close Assets:Checking
```

## Implementation

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DirectivePriority {
    Open = 0,
    Commodity = 1,
    Pad = 2,
    Balance = 3,
    Transaction = 4,
    Note = 5,
    Document = 6,
    Event = 7,
    Query = 8,
    Price = 9,
    Close = 10,
    Custom = 11,
}

impl Directive {
    pub fn priority(&self) -> DirectivePriority {
        match self {
            Directive::Open(_) => DirectivePriority::Open,
            Directive::Commodity(_) => DirectivePriority::Commodity,
            Directive::Pad(_) => DirectivePriority::Pad,
            Directive::Balance(_) => DirectivePriority::Balance,
            Directive::Transaction(_) => DirectivePriority::Transaction,
            Directive::Note(_) => DirectivePriority::Note,
            Directive::Document(_) => DirectivePriority::Document,
            Directive::Event(_) => DirectivePriority::Event,
            Directive::Query(_) => DirectivePriority::Query,
            Directive::Price(_) => DirectivePriority::Price,
            Directive::Close(_) => DirectivePriority::Close,
            Directive::Custom(_) => DirectivePriority::Custom,
        }
    }
}

pub fn sort_directives(directives: &mut [Directive]) {
    directives.sort_by(|a, b| {
        // Primary: date
        a.date().cmp(&b.date())
            // Secondary: type priority
            .then_with(|| a.priority().cmp(&b.priority()))
            // Tertiary: file order (line number)
            .then_with(|| a.location().line.cmp(&b.location().line))
    });
}
```

## Stable Sort Requirement

The sort must be **stable** to preserve file order for directives with equal date and type:

```rust
// Use stable sort, not unstable
directives.sort_by(...);  // stable
// NOT: directives.sort_unstable_by(...);
```

## Include File Ordering

When files are included, directives are merged and sorted globally:

```beancount
; main.beancount
include "2024-01.beancount"
include "2024-02.beancount"

; All directives from all files are sorted together
; File inclusion order does NOT affect final sort
```

## Edge Cases

### Same-Second Transactions

There's no sub-day ordering. Transactions on the same date are ordered by:
1. Type priority (transactions are all priority 4)
2. File line number

```beancount
; Line 10
2024-01-15 * "First"
  ...

; Line 20
2024-01-15 * "Second"
  ...

; "First" comes before "Second" due to line number
```

### Multiple Files, Same Date

When multiple files have transactions on the same date, they're interleaved by line number within each file, then by file processing order:

```
main.beancount:10  →  position 1
main.beancount:20  →  position 2
included.beancount:5   →  position 3 (processed after main)
included.beancount:15  →  position 4
```

For deterministic ordering across files, use the `lineno` from the merged source map.
