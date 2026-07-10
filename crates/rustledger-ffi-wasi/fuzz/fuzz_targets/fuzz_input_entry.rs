#![no_main]
//! Fuzz the FFI ingress boundary: `input_entry_to_directive` is the builder
//! behind the component's `entry.create`/`createBatch`, taking wire JSON
//! from untrusted embedders and hand-validating it (dates, account names,
//! cost-number arity, the `BookedCost` per-unit×units≈total invariant).
//! None of that validation was fuzzed before this target.
//!
//! Bytes are driven through the REAL wire path (serde_json → `InputEntry`),
//! so serde's lenient/strict corners (`deny_unknown_fields`, defaults,
//! tagged enums) are exercised exactly as embedders hit them. Beyond
//! no-panic, two invariants are asserted:
//!
//! 1. **The account gate holds**: any successfully converted directive
//!    carries only accounts the canonical lexer predicate accepts — a
//!    bypass here would readmit the un-round-trippable-account class the
//!    gate exists to block (#1739).
//! 2. **Conversion is deterministic**: converting the same entry twice
//!    gives the same Ok/Err disposition.
use libfuzzer_sys::fuzz_target;
use rustledger_core::Directive;
use rustledger_ffi_wasi::{InputEntry, input_entry_to_directive};
use rustledger_parser::is_valid_account_name;

/// Every account name carried by a converted directive.
fn accounts_of(d: &Directive) -> Vec<&str> {
    match d {
        Directive::Transaction(t) => t.postings.iter().map(|p| p.account.as_ref()).collect(),
        Directive::Open(x) => vec![x.account.as_ref()],
        Directive::Close(x) => vec![x.account.as_ref()],
        Directive::Balance(x) => vec![x.account.as_ref()],
        Directive::Pad(x) => vec![x.account.as_ref(), x.source_account.as_ref()],
        Directive::Note(x) => vec![x.account.as_ref()],
        Directive::Document(x) => vec![x.account.as_ref()],
        Directive::Commodity(_)
        | Directive::Price(_)
        | Directive::Event(_)
        | Directive::Query(_)
        | Directive::Custom(_) => Vec::new(),
    }
}

fuzz_target!(|data: &[u8]| {
    // Bound resource usage independent of runner flags: the CI job passes
    // -max_len=4096, but a local `cargo fuzz run` without it could feed
    // multi-megabyte inputs into serde (review catch). 64 KiB is far above
    // any realistic wire entry while keeping pathological JSON cheap.
    if data.len() > 64 * 1024 {
        return;
    }
    let Ok(entry) = serde_json::from_slice::<InputEntry>(data) else {
        return;
    };
    let first = input_entry_to_directive(&entry);
    match &first {
        Ok(directive) => {
            for account in accounts_of(directive) {
                assert!(
                    is_valid_account_name(account),
                    "account gate bypassed: {account:?} in a converted directive"
                );
            }
        }
        Err(msg) => {
            assert!(!msg.is_empty(), "error without a message");
        }
    }
    // Determinism: same entry, same disposition.
    let second = input_entry_to_directive(&entry);
    assert_eq!(
        first.is_ok(),
        second.is_ok(),
        "conversion disposition is nondeterministic"
    );
});
