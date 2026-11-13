//! Reading a long option number allocates in proportion to its length
//! (#2948 review).
//!
//! The scan counter in `options.rs` (`test_exact_decimal_linear_digit_scans_on_long_input`)
//! sees every scan of the value, but not work that is not a scan: a buffer
//! copied once per character (`cleaned = format!("{cleaned}{c}")`) is
//! quadratic in bytes allocated while scanning each character once. Counting
//! the bytes allocated catches that. It needs a counting global allocator,
//! which `dhat::Alloc` is, safely; an integration test is its own crate, so
//! installing one here touches neither the loader nor its
//! `#![forbid(unsafe_code)]`.
//!
//! dhat's profiler is process-global: two running at once panic, and any
//! allocation in another test thread would be counted against this one. So
//! this file holds exactly ONE test, which the test runner then runs on its
//! own, in its own process. Put another allocation test in its own file.

#[cfg(not(miri))]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

use rustledger_loader::Options;

/// The most bytes setting an option may allocate per byte of its value.
///
/// Measured: 10.1 bytes per byte for the long tolerance map (80,902 for
/// 8,005 bytes) and 9.2 for the long multiplier (73,487 for 8,001), both
/// rejected, so their error message, the E7002 message quoting it and the
/// warning's copy of the value each hold the value again; and 2.1 for the
/// separated value (24,704 for 12,003), which is accepted after a cleaned
/// copy and a filtered copy. 20 leaves room for a few more linear copies,
/// where a copy of the value per character it holds allocates thousands of
/// bytes per byte: building the cleaned copy by repeated `format!` allocated
/// 96,069,091 bytes for the 8,001-byte multiplier.
const MAX_BYTES_PER_INPUT_BYTE: u64 = 20;

#[test]
#[cfg_attr(
    miri,
    ignore = "dhat's global allocator and backtraces are not useful under Miri; \
              this test checks allocation volume, not memory safety"
)]
fn test_options_set_long_number_allocation_is_linear() {
    let zeros = "0".repeat(4_000);
    // Built before profiling starts, so only `set`'s own work is counted.
    let cases = [
        // A long tolerance map: `USD:` and 4,000 zeros a side of a `1`.
        ("inferred_tolerance_default", format!("USD:{zeros}1{zeros}")),
        // A long multiplier.
        ("tolerance_multiplier", format!("{zeros}1{zeros}")),
        // Separators and surrounding whitespace, dropped before the number
        // is read.
        (
            "tolerance_multiplier",
            format!("\t{}1\t", "_0,".repeat(4_000)),
        ),
    ];
    let mut options: Vec<Options> = cases.iter().map(|_| Options::new()).collect();

    let _profiler = dhat::Profiler::builder().testing().build();
    for ((key, value), options) in cases.iter().zip(&mut options) {
        let before = dhat::HeapStats::get().total_bytes;
        options.set(key, value);
        let allocated = dhat::HeapStats::get().total_bytes - before;
        let len = u64::try_from(value.len()).expect("a value length fits in u64");
        assert!(
            allocated <= MAX_BYTES_PER_INPUT_BYTE * len,
            "setting {key} allocated {allocated} bytes for a {len}-byte value"
        );
    }

    // The values were read, not skipped: the long ones are rejected (E7002),
    // the separated one is accepted as 1.
    let codes =
        |options: &Options| -> Vec<&str> { options.warnings.iter().map(|w| w.code).collect() };
    assert_eq!(codes(&options[0]), ["E7002"]);
    assert_eq!(codes(&options[1]), ["E7002"]);
    assert!(codes(&options[2]).is_empty(), "{:?}", options[2].warnings);
    assert_eq!(
        options[2].inferred_tolerance_multiplier,
        rust_decimal::Decimal::ONE
    );
}
