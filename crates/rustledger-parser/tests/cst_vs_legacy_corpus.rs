//! Differential test: `parse_via_cst` vs the legacy state-machine
//! parser, over the compatibility corpus.
//!
//! Phase 3.2-3.4 of #1262. Builds the CST -> `ParseResult`
//! converter incrementally; this test measures how close the
//! two code paths agree, file-by-file, by hashing each
//! `ParseResult` through `__baseline_canonical_payload` and
//! comparing the two hashes.
//!
//! ## Modes
//!
//! - **Default** (no env var): produces a convergence report
//!   and never fails on observed divergence. Use to iterate on
//!   the converter without CI churn.
//! - `STRICT_DIFFERENTIAL=1`: fail on any divergence. This is
//!   the gate that flips when the converter is ready to become
//!   the default `parse()` implementation.
//! - `DIFFERENTIAL_REPORT_PATH=/tmp/foo.txt`: write a longer
//!   report (every divergent file path) to disk. Useful for
//!   bisecting which corpus class still diverges.
//! - `DIFFERENTIAL_VERBOSE=1`: print to stderr in default mode
//!   (otherwise the test stays quiet so unrelated `cargo test`
//!   runs don't get noisy).
//!
//! ## Categories
//!
//! Per file the test classifies the outcome into one of:
//!
//! - **Identical**: both parsers produced the same canonical
//!   payload hash. This is the target state for every file.
//! - **Divergent**: both parsers ran cleanly but produced
//!   different output. The bulk of the converter work is
//!   closing these.
//! - **Legacy-only panic**: legacy parser panicked; CST didn't.
//!   Counts as a CST-side improvement (we don't regress on
//!   panics) but means we can't compare on this file.
//! - **CST-only panic**: CST parser panicked; legacy didn't.
//!   Counts as a CST regression; STRICT mode fails on these.
//! - **Both panic**: both parsers panicked. Treated as
//!   identical for convergence accounting.
//! - **IO error**: file couldn't be read. Skipped.

use std::panic::AssertUnwindSafe;
use std::path::Path;

#[path = "baseline_common/mod.rs"]
mod baseline_common;

use baseline_common::{MIN_FULL_CORPUS_SIZE, discover_corpus_files, repo_root};

/// Cap on per-category file paths shown in stderr in verbose mode.
const SHOW: usize = 20;

/// Per-file outcome of the differential run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    Identical,
    Divergent,
    LegacyOnlyPanic,
    CstOnlyPanic,
    BothPanic,
    IoError,
}

fn classify_file(absolute_path: &Path) -> Outcome {
    let Ok(source) = std::fs::read_to_string(absolute_path) else {
        return Outcome::IoError;
    };

    let legacy = std::panic::catch_unwind(AssertUnwindSafe(|| rustledger_parser::parse(&source)));
    let cst = std::panic::catch_unwind(AssertUnwindSafe(|| {
        rustledger_parser::parse_via_cst(&source)
    }));

    match (legacy, cst) {
        (Ok(l), Ok(c)) => {
            let legacy_payload = rustledger_parser::__baseline_canonical_payload(&l);
            let cst_payload = rustledger_parser::__baseline_canonical_payload(&c);
            if legacy_payload == cst_payload {
                Outcome::Identical
            } else {
                Outcome::Divergent
            }
        }
        (Err(_), Err(_)) => Outcome::BothPanic,
        (Err(_), Ok(_)) => Outcome::LegacyOnlyPanic,
        (Ok(_), Err(_)) => Outcome::CstOnlyPanic,
    }
}

#[test]
fn cst_vs_legacy_corpus_convergence() {
    let files = discover_corpus_files();
    let strict = std::env::var_os("STRICT_DIFFERENTIAL").is_some();
    let verbose = std::env::var_os("DIFFERENTIAL_VERBOSE").is_some();
    let report_path = std::env::var_os("DIFFERENTIAL_REPORT_PATH");

    // `parse()` is env-gated: with `RUSTLEDGER_CST_PARSER` set,
    // BOTH `parse()` and `parse_via_cst()` go through the CST
    // path and this test would compare CST-vs-CST while
    // reporting 100% convergence — exactly the false signal we
    // built this test to catch. Fail fast and tell the user how
    // to re-run.
    assert!(
        std::env::var_os("RUSTLEDGER_CST_PARSER").is_none(),
        "RUSTLEDGER_CST_PARSER is set; this differential test \
         requires the env var unset so that `parse()` invokes \
         the legacy parser. Re-run with `RUSTLEDGER_CST_PARSER` \
         removed from the environment."
    );

    // Small-corpus guard mirrors corpus_baseline.rs: a fresh
    // checkout without `fetch-compat-test-files.sh` should not
    // be silently treated as a clean 100% pass.
    if files.len() < MIN_FULL_CORPUS_SIZE {
        assert!(
            !strict,
            "STRICT_DIFFERENTIAL: current corpus has {} files (need at \
             least {MIN_FULL_CORPUS_SIZE}). Did \
             `fetch-compat-test-files.sh` run?",
            files.len(),
        );
        eprintln!(
            "skipping: corpus has only {} file(s) (< {MIN_FULL_CORPUS_SIZE}); \
             run `tests/compatibility/scripts/fetch-compat-test-files.sh` to \
             populate.",
            files.len(),
        );
        return;
    }

    let root = repo_root();
    let mut counts = [0usize; 6];
    let mut divergent_paths: Vec<&Path> = Vec::new();
    let mut cst_panic_paths: Vec<&Path> = Vec::new();
    for rel in files {
        let absolute = root.join(rel);
        let outcome = classify_file(&absolute);
        let idx = match outcome {
            Outcome::Identical => 0,
            Outcome::Divergent => {
                divergent_paths.push(rel);
                1
            }
            Outcome::LegacyOnlyPanic => 2,
            Outcome::CstOnlyPanic => {
                cst_panic_paths.push(rel);
                3
            }
            Outcome::BothPanic => 4,
            Outcome::IoError => 5,
        };
        counts[idx] += 1;
    }
    let total = files.len();
    let identical = counts[0];
    let convergence_pct = (identical as f64 / total as f64) * 100.0;

    let summary = format!(
        "\nCST <-> legacy differential corpus report ({total} files):\n  \
         identical:           {ident:>5}  ({pct:.2}%)\n  \
         divergent:           {div:>5}\n  \
         legacy-only panic:   {lop:>5}\n  \
         cst-only panic:      {cop:>5}\n  \
         both panic:          {bp:>5}\n  \
         io error:            {io:>5}\n",
        ident = identical,
        pct = convergence_pct,
        div = counts[1],
        lop = counts[2],
        cop = counts[3],
        bp = counts[4],
        io = counts[5],
    );

    if verbose || strict {
        eprintln!("{summary}");
        if !divergent_paths.is_empty() {
            eprintln!(
                "First {} divergent file(s):",
                SHOW.min(divergent_paths.len())
            );
            for p in divergent_paths.iter().take(SHOW) {
                eprintln!("  {}", p.display());
            }
        }
        if !cst_panic_paths.is_empty() {
            eprintln!(
                "First {} CST-only-panic file(s):",
                SHOW.min(cst_panic_paths.len())
            );
            for p in cst_panic_paths.iter().take(SHOW) {
                eprintln!("  {}", p.display());
            }
        }
    }

    if let Some(report_path) = report_path {
        let mut out = summary.clone();
        out.push_str("\n--- All divergent files ---\n");
        for p in &divergent_paths {
            out.push_str(&format!("{}\n", p.display()));
        }
        out.push_str("\n--- All CST-only-panic files ---\n");
        for p in &cst_panic_paths {
            out.push_str(&format!("{}\n", p.display()));
        }
        std::fs::write(&report_path, out).expect("write report");
    }

    if strict {
        let bad = counts[1] + counts[3]; // divergent + cst-only-panic
        assert_eq!(
            bad, 0,
            "STRICT_DIFFERENTIAL: {bad} file(s) diverge or panic on the CST path.{summary}",
        );
    }
}
