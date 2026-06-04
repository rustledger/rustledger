//! Formatter-output baseline for the compatibility corpus.
//!
//! Phase 0 sibling of `corpus_baseline.rs`. The formatter is what
//! #1252 is about; we need a CI gate that says "the formatter's
//! output on the corpus is what it is, and any change to it is
//! detected." Without this, the formatter migration in phase 4 of
//! #1262 can't make a credible claim of "we changed how the
//! formatter works but only in ways we meant to."
//!
//! Same manifest format as `corpus_baseline.rs`: one line per file,
//! sorted lexically, with two hashes:
//!
//! ```text
//! relative/path<TAB>source_blake3<TAB>format_output_blake3
//! ```
//!
//! Both hashes are present so the gate can distinguish "the
//! compatibility corpus drifted upstream" from "the formatter's
//! output changed." Files whose parser output contains zero
//! directives have nothing to format; the manifest omits them.
//! Files that fail to read are encoded as a `read-error:<kind>`
//! sentinel matching the parser baseline so a future readability
//! flip doesn't produce contradictory diagnostics across the two
//! manifests.
//!
//! ## Why `format_source`
//!
//! The CLI invokes
//! `rustledger_parser::format_source(&source, &parse_result, &config)`
//! (see `crates/rustledger/src/cmd/format.rs`). The lower-level
//! `rustledger_core::format::format_directives(directives, &config)`
//! takes a different path that pre-#1142 destroyed multi-line
//! metadata (the `format_source` route preserves it via posting
//! spans). The CLI is what users invoke, so the baseline gates
//! exactly that.
//!
//! ## Regeneration
//!
//! ```ignore
//! BASELINE_UPDATE=1 cargo test -p rustledger-parser --test \
//!   corpus_baseline_format
//! ```
//!
//! Review the diff and commit.

mod baseline_common;

use std::collections::HashSet;
use std::panic::AssertUnwindSafe;
use std::path::{Path, PathBuf};

use rustledger_core::format::FormatConfig;
use rustledger_parser::format_source;

use baseline_common::{
    CORPUS_ROOT, FileFingerprint, MIN_FULL_CORPUS_SIZE, compute_manifest, discover_corpus_files,
    is_in_tree_fixture, panic_payload_hash, read_committed_manifest, repo_root, write_manifest,
};

const MANIFEST_PATH: &str = "tests/baselines/format-corpus.manifest";

const MANIFEST_HEADER: &[&str] = &[
    "# Formatter-output baseline. See crates/rustledger-parser/tests/corpus_baseline_format.rs.",
    "# Format: path<TAB>source_hash<TAB>format_output_hash",
    "# Regenerate: BASELINE_UPDATE=1 cargo test -p rustledger-parser --test corpus_baseline_format",
];

/// Parse `path` (absolute), pass its directives through
/// [`format_source`] (the exact API the CLI uses), and return a
/// stable `(source, format_output)` fingerprint pair.
///
/// Returns `None` for files that parse to zero directives — there's
/// nothing for the formatter to produce and no useful drift signal.
/// Read failures are encoded as a `read-error:<kind>` sentinel to
/// mirror the parser baseline's behavior.
fn fingerprint(absolute_path: &Path) -> Option<FileFingerprint> {
    let source = match std::fs::read_to_string(absolute_path) {
        Ok(s) => s,
        Err(e) => {
            let tag = format!("read-error:{:?}", e.kind());
            return Some(FileFingerprint {
                source: tag.clone(),
                parser: tag,
            });
        }
    };
    let source_hash = blake3::hash(source.as_bytes()).to_hex().to_string();
    let outcome = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let result = rustledger_parser::parse(&source);
        if result.directives.is_empty() {
            return None;
        }
        Some(format_source(&source, &result, &FormatConfig::default()))
    }));
    let formatted_hash = match outcome {
        Ok(Some(text)) => blake3::hash(text.as_bytes()).to_hex().to_string(),
        Ok(None) => return None,
        Err(payload) => format!("panic:{}", panic_payload_hash(&*payload)),
    };
    Some(FileFingerprint {
        source: source_hash,
        parser: formatted_hash,
    })
}

#[test]
fn formatter_output_matches_baseline() {
    let manifest_abs = repo_root().join(MANIFEST_PATH);

    if std::env::var_os("BASELINE_UPDATE").is_some() {
        let current = compute_manifest(fingerprint);
        write_manifest(&manifest_abs, &current, MANIFEST_HEADER);
        return;
    }

    let current = compute_manifest(fingerprint);
    let committed = read_committed_manifest(&manifest_abs);
    let strict = std::env::var_os("STRICT_BASELINE").is_some();

    // Discovery uses the raw .beancount count to decide
    // populated-vs-not; current.len() is the *formattable* subset
    // (some corpus files parse to zero directives and produce no
    // baseline entry), which would always undercount.
    let total_corpus = discover_corpus_files().len();
    if total_corpus < MIN_FULL_CORPUS_SIZE {
        assert!(
            !strict,
            "STRICT_BASELINE: corpus has {total_corpus} files (need at \
             least {MIN_FULL_CORPUS_SIZE}). Did \
             `fetch-compat-test-files.sh` run?",
        );
        eprintln!(
            "corpus at `{CORPUS_ROOT}` has only {total_corpus} files (need \
             at least {MIN_FULL_CORPUS_SIZE}). Run \
             `./scripts/fetch-compat-test-files.sh`; skipping formatter \
             baseline. CI uses STRICT_BASELINE=1.",
        );
        return;
    }

    // Discover-on-disk tells us whether a missing-from-current file
    // is genuinely gone from the corpus OR still on disk but now
    // parses to zero directives (a parser regression we should
    // surface as drift, not silently warn about).
    let on_disk: HashSet<&PathBuf> = discover_corpus_files().iter().collect();

    let mut format_drift: Vec<(&PathBuf, &str, &str)> = Vec::new();
    let mut source_drift: Vec<&PathBuf> = Vec::new();
    // File missing from current AND from disk: corpus shrank. Warn.
    let mut removed_from_corpus: Vec<&PathBuf> = Vec::new();
    // File missing from current but still on disk: previously
    // formatted non-empty, now produces no directives. Real
    // regression. Strict mode treats this as drift.
    let mut became_empty: Vec<&PathBuf> = Vec::new();
    let mut missing_from_manifest: Vec<&PathBuf> = Vec::new();
    for (path, expected) in &committed {
        match current.get(path) {
            None if on_disk.contains(path) => became_empty.push(path),
            None => removed_from_corpus.push(path),
            Some(current_fp) if current_fp.source != expected.source => {
                source_drift.push(path);
            }
            Some(current_fp) if current_fp.parser != expected.parser => {
                format_drift.push((path, expected.parser.as_str(), current_fp.parser.as_str()));
            }
            Some(_) => {}
        }
    }
    for path in current.keys() {
        if !committed.contains_key(path) {
            missing_from_manifest.push(path);
        }
    }

    // Only escalate missing-from-manifest in-tree fixtures to strict
    // failure. Downloaded-corpus appearances are subject to upstream
    // race; we don't gate on them.
    let unmanifested_in_tree: Vec<&PathBuf> = missing_from_manifest
        .iter()
        .filter(|p| is_in_tree_fixture(p))
        .copied()
        .collect();
    let strict_fail = strict && (!unmanifested_in_tree.is_empty() || !became_empty.is_empty());
    if format_drift.is_empty() && !strict_fail {
        if !source_drift.is_empty() {
            eprintln!(
                "info: {} corpus file(s) have new upstream content; \
                 formatter output was NOT checked on those files. \
                 Regenerate when convenient:\n  BASELINE_UPDATE=1 \
                 cargo test -p rustledger-parser --test \
                 corpus_baseline_format",
                source_drift.len(),
            );
        }
        if !missing_from_manifest.is_empty() {
            eprintln!(
                "warning: {} corpus file(s) format to non-empty output \
                 but have no manifest entry.",
                missing_from_manifest.len(),
            );
        }
        if !became_empty.is_empty() {
            eprintln!(
                "warning: {} file(s) used to format non-empty and now \
                 parse to zero directives (a parser regression). CI \
                 fails on this under STRICT_BASELINE=1.",
                became_empty.len(),
            );
        }
        if !removed_from_corpus.is_empty() {
            eprintln!(
                "warning: {} manifest entry/entries refer to files no \
                 longer present in the corpus.",
                removed_from_corpus.len(),
            );
        }
        return;
    }

    let mut report = String::new();
    if !format_drift.is_empty() {
        report.push_str(&format!(
            "Formatter-output drift on {} file(s) with unchanged source \
             (first 10 shown):\n",
            format_drift.len(),
        ));
        for (path, expected, current) in format_drift.iter().take(10) {
            report.push_str(&format!(
                "  {path}\n    expected: {e}\n    current:  {c}\n",
                path = path.display(),
                e = &expected[..16.min(expected.len())],
                c = &current[..16.min(current.len())],
            ));
        }
    }
    if strict && !unmanifested_in_tree.is_empty() {
        report.push_str(&format!(
            "\n{} in-tree fixture(s) format non-empty but have no \
             manifest entry (first 10):\n",
            unmanifested_in_tree.len(),
        ));
        for path in unmanifested_in_tree.iter().take(10) {
            report.push_str(&format!("  {}\n", path.display()));
        }
    }
    if strict && !became_empty.is_empty() {
        report.push_str(&format!(
            "\n{} file(s) used to format non-empty but now parse to \
             zero directives (parser regression, first 10):\n",
            became_empty.len(),
        ));
        for path in became_empty.iter().take(10) {
            report.push_str(&format!("  {}\n", path.display()));
        }
    }
    panic!(
        "Formatter baseline drift:\n\n{report}\nIf this drift is \
         intentional, regenerate:\n  \
         BASELINE_UPDATE=1 cargo test -p rustledger-parser --test \
         corpus_baseline_format\n\nReview the diff against \
         `{MANIFEST_PATH}` and commit.",
    );
}
