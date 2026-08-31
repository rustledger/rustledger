//! Same-date directives from different included files book in include order,
//! not in line-number order (#2149).
//!
//! `sort_directives` is a stable sort over `(date, priority)`, so directives
//! sharing both keep the order they were parsed in. Within one file that is
//! the same thing as Python's `(date, type_priority, lineno)`. Across
//! `include`s it is not: Python compares line numbers taken from DIFFERENT
//! files, so a directive on line 1 of a file included second sorts ahead of
//! one on line 5 of a file included first.
//!
//! The difference is observable in money. Two same-date buys enter the
//! inventory in different orders under the two rules, and a FIFO sale whose
//! lot-date comparison ties falls through to that order. Measured against
//! beancount 3.2.3 on this fixture:
//!
//! | include order | beancount | rustledger |
//! |---|---|---|
//! | first, second | -10.00 | **-20.00** |
//! | second, first | -10.00 | -10.00 |
//!
//! beancount is invariant because it re-sorts by line number; ours tracks how
//! the ledger was assembled. Neither errors nor warns.
//!
//! We keep include order deliberately. Comparing a line number from one file
//! against a line number from a different file is not a fact about the ledger:
//! adding a comment to one file silently changes which lot a sale in another
//! file consumes. Beancount's rule is not purely line-number driven either --
//! directives sharing a line number across files fall back to include order
//! through its own stable sort.
//!
//! This test exists because nothing pinned the behavior in either direction.
//! The three tests that exercise this ordering
//! (`test_sort_directives_by_date`, `test_sort_directives_by_type_same_date`,
//! `test_sort_directives_pad_before_balance`) do not mention a file or an
//! include, and the compatibility corpus cannot reach it: of 761 `.beancount`
//! files, one contains a single `include` and none contains two, so no corpus
//! file can express the shape.

use rustledger_core::Directive;
use rustledger_loader::{LoadOptions, Loader, process};

fn realized_gains(ledger: &std::path::Path) -> String {
    let raw = Loader::new().load(ledger).expect("fixture loads");
    let processed = process(raw, &LoadOptions::default()).expect("fixture books");
    let mut total = rustledger_core::Decimal::ZERO;
    let mut seen = false;
    for d in &processed.directives {
        if let Directive::Transaction(txn) = &d.value {
            for p in &txn.postings {
                if p.account.as_str() == "Income:Gains"
                    && let Some(n) = p
                        .units
                        .as_ref()
                        .and_then(rustledger_core::IncompleteAmount::number)
                {
                    total += n;
                    seen = true;
                }
            }
        }
    }
    assert!(seen, "fixture must produce an Income:Gains posting");
    total.to_string()
}

/// The fixture ships in-tree because the compatibility corpus cannot express
/// this shape, and because the number is only meaningful next to beancount's.
#[test]
fn cross_file_same_date_directives_keep_include_order() {
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/cross-file-order/ledger.beancount");

    // -20.00 means the 10.00 lot was consumed, i.e. the first INCLUDED file's
    // buy went in first. -10.00 would mean the 20.00 lot was consumed, which
    // is what sorting by line number across files produces and what beancount
    // reports. If this flips, the rule changed: update
    // `docs/reference/compatibility.md` and `sort_directives` with it, rather
    // than just re-pinning the number.
    assert_eq!(
        realized_gains(&fixture),
        "-20.00",
        "same-date buys from two included files must book in include order",
    );
}
