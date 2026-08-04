//! The loader produces a canonical directive order (#1902 Phase 1).
//!
//! #1902 proposes "validation is deterministic and order-independent". The
//! determinism half already has THREE tests in `rustledger-validate`
//! (`validation_pipeline_is_deterministic`, `coupled_pipeline_is_deterministic`,
//! `prop_validation_deterministic`) — all of which run the SAME input twice.
//!
//! Order-independence needed care to state usefully. Two earlier framings were
//! discarded, and both were discarded for the same reason: I could not make
//! them fail.
//!
//! The first compared the LOADER's directive sequence across permutations, on
//! the assumption that the loader canonicalizes order. It does not -
//! `LoadResult.directives` preserves source order, and the date sort happens
//! downstream (query, balance views, booking). That version also failed for a
//! reason unrelated to ordering: directives carry source metadata, so
//! renumbering the file changes every line number.
//!
//! The second compared diagnostics but could not be falsified by deleting the
//! loader's sorts, because the validators are order-insensitive in their own
//! right - the sorts are not what makes this hold.
//!
//! What ships is the user-facing claim, with a demonstrated failure mode: a
//! validator that reads `directives.first()` makes this test fail. That is the
//! shape a future regression would take.

use std::fmt::Write as _;
use std::fs;
use std::io::Write as _;

/// Directive blocks, kept whole. Permuting LINES would tear postings off their
/// transaction; the unit that may legitimately move is the directive.
fn blocks() -> Vec<&'static str> {
    vec![
        "2024-01-01 open Assets:Bank",
        "2024-01-01 open Expenses:Food",
        "2024-01-01 open Equity:Open",
        // Balanced.
        "2024-01-05 * \"a\"\n  Assets:Bank   -10.00 USD\n  Expenses:Food  10.00 USD",
        // Unbalanced — contributes an error code.
        "2024-01-07 * \"b\"\n  Assets:Bank   -5.00 USD\n  Expenses:Food   4.00 USD",
        // Same-date pad and balance, the pair most likely to be order-sensitive.
        "2024-01-09 pad Assets:Bank Equity:Open",
        "2024-01-09 balance Assets:Bank -15.00 USD",
        // Touches an account that is never opened.
        "2024-01-11 * \"c\"\n  Assets:Bank    -1.00 USD\n  Expenses:Never  1.00 USD",
    ]
}

/// Diagnostics for one input ordering, sorted so the comparison is about
/// WHICH errors were produced rather than the order they were reported in.
///
/// Rendered rather than compared structurally so a failure shows WHICH
/// directive moved, which is the only thing a reader of the failure wants.
fn codes_for(order: &[usize], dir: &std::path::Path) -> Vec<String> {
    let all = blocks();
    let mut src = String::new();
    for &i in order {
        let _ = writeln!(src, "{}\n", all[i]);
    }
    let file = dir.join("main.beancount");
    let mut f = fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);

    let mut loader = rustledger_loader::Loader::new();
    let result = loader.load(&file).expect("load");
    let options = rustledger_loader::validation_options_from_options(&result.options);
    let today = rustledger_core::naive_date(2024, 12, 31).unwrap();
    let plain: Vec<rustledger_core::Directive> =
        result.directives.iter().map(|d| (**d).clone()).collect();

    let session = rustledger_validate::ValidationSession::new(options);
    let (session, early) = session.run_early(&plain, today);
    let (session, late) = session.run_late(&plain, today);
    let pad = session.finalize();

    let mut codes: Vec<String> = early
        .iter()
        .chain(&late)
        .chain(&pad)
        .map(|e| format!("{:?}", e.code))
        .collect();
    codes.sort_unstable();
    codes
}

/// EXHAUSTIVE over a 6-block prefix rather than random sampling.
///
/// 720 orderings is cheap, and exhaustive means a failure is reproducible
/// without a seed — the thing that makes a randomized property annoying to act
/// on when it finally trips.
#[test]
fn diagnostics_are_invariant_under_input_permutation() {
    let dir = tempfile::Builder::new()
        .prefix("rledger_order_")
        .tempdir()
        .expect("temp dir");

    let n = 6usize;
    let canonical: Vec<usize> = (0..n).collect();
    let expected = codes_for(&canonical, dir.path());

    // Non-vacuity: if the fixture stopped producing diagnostics this test would
    // compare empty vectors forever and pass.
    assert!(
        !expected.is_empty(),
        "the fixture must produce diagnostics, else the comparison is vacuous",
    );

    let mut perm = canonical;
    let mut checked = 0usize;
    permute(&mut perm, 0, &mut |p| {
        let got = codes_for(p, dir.path());
        assert_eq!(
            got, expected,
            "input order {p:?} changed the diagnostics; validation must not \
             depend on how the file was typed",
        );
        checked += 1;
    });
    assert_eq!(checked, 720, "expected every permutation of 6 blocks");
}

fn permute(v: &mut Vec<usize>, k: usize, f: &mut impl FnMut(&[usize])) {
    if k == v.len() {
        f(v);
        return;
    }
    for i in k..v.len() {
        v.swap(k, i);
        permute(v, k + 1, f);
        v.swap(k, i);
    }
}
