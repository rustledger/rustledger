//! Byte-identical round-trip test for the phase-1 flat CST.
//!
//! For every `.beancount` file in the compatibility corpus, parse
//! with [`rustledger_cst::parse_flat`] and assert that the green
//! tree's text serialization equals the source byte-for-byte. The
//! round-trip property is the foundational invariant of #1262: it
//! means every byte of source is reachable from the CST, which
//! enables the formatter (phase 4) to produce byte-preserving
//! output and the refactor / rename / structural-search consumers
//! to operate without ambiguity.
//!
//! # Skip-when-corpus-absent
//!
//! Mirrors the parser baseline's behavior: the test treats the
//! corpus directory as not-downloaded when it contains fewer than
//! [`MIN_FULL_CORPUS_SIZE`] files and either:
//!
//! - Skips silently (default mode) — local devs without
//!   `./scripts/fetch-compat-test-files.sh` see the test pass with a
//!   warning on stderr.
//! - Fails loudly (`STRICT_BASELINE=1`) — CI uses this to ensure the
//!   gate is load-bearing.
//!
//! # Why no manifest
//!
//! Unlike the parser baseline this test compares input == output
//! pointwise; it has no committed expected hashes to drift against.
//! Phase 2 may add a baseline for the structural-CST output, but
//! phase 1 only needs the round-trip property.

use std::path::{Path, PathBuf};

use rustledger_cst::parse_flat;

const CORPUS_ROOT: &str = "tests/compatibility/files";
const MIN_FULL_CORPUS_SIZE: usize = 100;

/// Walk up from the test's `CARGO_MANIFEST_DIR` to the workspace
/// root. The marker is `tests/compatibility/files` (a directory) AND
/// a `Cargo.toml` containing a `[workspace]` table at line start.
fn repo_root() -> PathBuf {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        if p.join(CORPUS_ROOT).is_dir() && has_workspace_table(&p) {
            return p;
        }
        assert!(
            p.pop(),
            "could not locate repo root from {}",
            env!("CARGO_MANIFEST_DIR"),
        );
    }
}

fn has_workspace_table(dir: &Path) -> bool {
    let Ok(toml) = std::fs::read_to_string(dir.join("Cargo.toml")) else {
        return false;
    };
    toml.lines()
        .any(|line| line.trim_start().starts_with("[workspace]"))
}

fn discover_corpus_files(root: &Path) -> Vec<PathBuf> {
    let corpus_dir = root.join(CORPUS_ROOT);
    let mut out = Vec::new();
    if !corpus_dir.is_dir() {
        return out;
    }
    walk(&corpus_dir, &mut out);
    out.sort();
    out
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    // Panic on FS errors: a corpus discovery failure is exactly the
    // class of CI flake we want to surface, not absorb.
    let entries = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read_dir({}) failed: {e}", dir.display()));
    for entry in entries {
        let entry =
            entry.unwrap_or_else(|e| panic!("read_dir entry under {} failed: {e}", dir.display()));
        let path = entry.path();
        if path.is_dir() {
            walk(&path, out);
        } else if path.extension().and_then(|s| s.to_str()) == Some("beancount") {
            out.push(path);
        }
    }
}

#[test]
fn phase_1_flat_cst_round_trips_every_corpus_file() {
    let root = repo_root();
    let files = discover_corpus_files(&root);
    let strict = std::env::var_os("STRICT_BASELINE").is_some();

    if files.len() < MIN_FULL_CORPUS_SIZE {
        assert!(
            !strict,
            "STRICT_BASELINE: corpus has {} files (need at least \
             {MIN_FULL_CORPUS_SIZE}). Did `./scripts/fetch-compat-test-files.sh` run?",
            files.len(),
        );
        eprintln!(
            "corpus at `{CORPUS_ROOT}` has only {} files (need at least \
             {MIN_FULL_CORPUS_SIZE}). Run `./scripts/fetch-compat-test-files.sh`; \
             skipping phase-1 round-trip check. CI uses STRICT_BASELINE=1.",
            files.len(),
        );
        return;
    }

    let mut failures: Vec<(PathBuf, String)> = Vec::new();
    let mut read_errors: Vec<(PathBuf, String)> = Vec::new();
    for path in &files {
        let source = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                // Files that aren't valid UTF-8 (e.g.,
                // `fava/tests_data_invalid-unicode.beancount`) can't
                // be `&str`-typed and therefore can't be round-tripped
                // through `parse_flat`. The parser baseline records
                // them as `read-error:InvalidData` sentinels rather
                // than failing; we do the same — these fixtures exist
                // to test the parser's invalid-input handling, not
                // its byte-preservation property.
                read_errors.push((path.clone(), format!("read-error: {e}")));
                continue;
            }
        };
        // `parse_flat` shouldn't panic, but if a future change to the
        // lexer's post-processing produces a span the adapter doesn't
        // expect, the round-trip check below would still fail with a
        // clear diff. catch_unwind here so one bad file doesn't abort
        // the entire corpus run.
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            parse_flat(&source).text().to_string()
        }));
        match outcome {
            Ok(reconstructed) if reconstructed == source => {}
            Ok(reconstructed) => {
                // Show a useful diff in the failure: the first byte
                // offset where they diverge, plus a small window of
                // context.
                let diverge = source
                    .as_bytes()
                    .iter()
                    .zip(reconstructed.as_bytes())
                    .position(|(a, b)| a != b)
                    .unwrap_or_else(|| source.len().min(reconstructed.len()));
                failures.push((
                    path.clone(),
                    format!(
                        "round-trip drift at byte {diverge} (source len {}, \
                         reconstructed len {})",
                        source.len(),
                        reconstructed.len(),
                    ),
                ));
            }
            Err(payload) => {
                let msg = payload
                    .downcast_ref::<&'static str>()
                    .map(|s| (*s).to_string())
                    .or_else(|| payload.downcast_ref::<String>().cloned())
                    .unwrap_or_else(|| "<non-string panic payload>".to_string());
                failures.push((path.clone(), format!("panic: {msg}")));
            }
        }
    }

    if !failures.is_empty() {
        let mut report = String::new();
        for (p, msg) in failures.iter().take(10) {
            use std::fmt::Write;
            // Append directly into the report buffer instead of
            // collecting per-line `format!()` Strings (clippy's
            // `format_collect`).
            let _ = writeln!(&mut report, "  {}: {msg}", p.display());
        }
        panic!(
            "phase-1 round-trip failed on {} of {} corpus files (first 10):\n{report}",
            failures.len(),
            files.len(),
        );
    }

    if !read_errors.is_empty() {
        eprintln!(
            "info: {} of {} corpus files were skipped due to read errors \
             (typically invalid-UTF-8 fixtures that exist to exercise the \
              parser's error-handling path):",
            read_errors.len(),
            files.len(),
        );
        for (path, msg) in read_errors.iter().take(5) {
            eprintln!("  {}: {msg}", path.display());
        }
    }
}
