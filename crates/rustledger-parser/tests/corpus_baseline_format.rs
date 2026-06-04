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
//! output changed." Files are omitted from the manifest only when
//! they parse to NO formattable content at all (no directives AND
//! no options AND no includes AND no plugins AND no comments) —
//! option-only and comment-only files are still tracked because
//! `format_source` renders those items and a regression on them
//! must be detected. Files that fail to read are encoded as a
//! `read-error:<kind>` sentinel matching the parser baseline so a
//! future readability flip doesn't produce contradictory diagnostics
//! across the two manifests.
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
//! ## Implicit gates beyond the formatter
//!
//! `format_source`'s contract (see its rustdoc) recommends callers
//! gate on `parse_result.errors.is_empty()`. The baseline deliberately
//! does NOT — it formats every corpus file, including ones with parse
//! errors. Consequences worth being explicit about:
//!
//! - For files with parse errors, the format output reflects the
//!   parser's error-recovery state. A change to error recovery (e.g.,
//!   different resync token, different span on a partial directive)
//!   shifts the format hash for those files. This baseline therefore
//!   ALSO gates changes to parser error recovery on the corpus, not
//!   just the formatter.
//! - For files with parse panics, see `parse-panic:` / `format-panic:`
//!   sentinels below.
//! - Default `FormatConfig::default()` is used. Changing the default
//!   of any `FormatConfig` field will shift hashes across many files.
//!   That's intentional — the gate IS the test that the default
//!   configuration's output is stable.
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

/// Parse `path` (absolute), pass its parse result through
/// [`format_source`] (the exact API the CLI uses), and return a
/// stable `(source, format_output)` fingerprint pair.
///
/// Returns `None` for files with no formattable content at all —
/// no directives, options, includes, plugins, or comments.
/// `format_source` produces a trailing-newline-only string for those
/// and no drift signal can hide in the output. Files with ONLY
/// options/plugins/includes/comments (and zero directives) are still
/// included: `format_source` renders those items, so a formatter
/// regression on an option-only file would otherwise pass silently.
///
/// Read failures are encoded as a `read-error:<kind>` sentinel to
/// mirror the parser baseline's behavior. Parse panics and format
/// panics are kept distinct (`parse-panic:` vs `format-panic:`) so
/// a future parser fix that uncovers a `format_source` panic does
/// not surface as misleading "formatter drift" against a hash that
/// actually captured a parser panic.
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

    let parse_outcome =
        std::panic::catch_unwind(AssertUnwindSafe(|| rustledger_parser::parse(&source)));
    let result = match parse_outcome {
        Ok(r) => r,
        Err(payload) => {
            return Some(FileFingerprint {
                source: source_hash,
                parser: format!("parse-panic:{}", panic_payload_hash(&*payload)),
            });
        }
    };

    if result.directives.is_empty()
        && result.options.is_empty()
        && result.includes.is_empty()
        && result.plugins.is_empty()
        && result.comments.is_empty()
    {
        return None;
    }

    let format_outcome = std::panic::catch_unwind(AssertUnwindSafe(|| {
        format_source(&source, &result, &FormatConfig::default())
    }));
    let formatted_hash = match format_outcome {
        Ok(text) => blake3::hash(text.as_bytes()).to_hex().to_string(),
        Err(payload) => format!("format-panic:{}", panic_payload_hash(&*payload)),
    };
    Some(FileFingerprint {
        source: source_hash,
        parser: formatted_hash,
    })
}

#[test]
fn formatter_output_matches_baseline() {
    let manifest_abs = repo_root().join(MANIFEST_PATH);
    let update = std::env::var_os("BASELINE_UPDATE").is_some();
    let strict = std::env::var_os("STRICT_BASELINE").is_some();

    // Discovery uses the raw .beancount count to decide
    // populated-vs-not; the formattable subset (current.len() below)
    // would always undercount because files with no formattable
    // content produce no baseline entry. Check size BEFORE the
    // BASELINE_UPDATE write path so a bare `BASELINE_UPDATE=1 cargo
    // test ...` invocation on a fresh checkout cannot truncate the
    // committed manifest down to a handful of in-tree fixtures.
    let total_corpus = discover_corpus_files().len();
    if total_corpus < MIN_FULL_CORPUS_SIZE {
        assert!(
            !strict,
            "STRICT_BASELINE: corpus has {total_corpus} files (need at \
             least {MIN_FULL_CORPUS_SIZE}). Did \
             `fetch-compat-test-files.sh` run?",
        );
        assert!(
            !update,
            "BASELINE_UPDATE=1 refusing to write a manifest from only \
             {total_corpus} files (need at least {MIN_FULL_CORPUS_SIZE}). \
             Run `./scripts/fetch-compat-test-files.sh` first; an \
             unguarded regen would silently truncate the committed manifest.",
        );
        eprintln!(
            "corpus at `{CORPUS_ROOT}` has only {total_corpus} files (need \
             at least {MIN_FULL_CORPUS_SIZE}). Run \
             `./scripts/fetch-compat-test-files.sh`; skipping formatter \
             baseline. CI uses STRICT_BASELINE=1.",
        );
        return;
    }

    let current = compute_manifest(fingerprint);

    if update {
        // Deliberately skip read_committed_manifest in update mode:
        // a corrupt or partially-written committed manifest must not
        // panic the very regen that would replace it.
        write_manifest(&manifest_abs, &current, MANIFEST_HEADER);
        return;
    }

    let committed = read_committed_manifest(&manifest_abs);

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
    // formatted non-empty, now produces no formattable content. Real
    // regression. Strict mode treats this as drift.
    let mut became_empty: Vec<&PathBuf> = Vec::new();
    // File missing from current but still on disk AND the committed
    // entry was a sentinel (`read-error:*`, `parse-panic:*`, or
    // `format-panic:*`). The file went from broken to readable-with-
    // no-formattable-content — an improvement, not a regression. Warn
    // only; never strict-fail. Without this distinction, fixing a
    // panicking parser or a panicking formatter would surface as a
    // false "parser regression" against the committed sentinel.
    let mut previously_broken_resolved: Vec<&PathBuf> = Vec::new();
    let mut missing_from_manifest: Vec<&PathBuf> = Vec::new();
    for (path, expected) in &committed {
        match current.get(path) {
            None if on_disk.contains(path) => {
                if expected.source.starts_with("read-error:")
                    || expected.parser.starts_with("read-error:")
                    || expected.parser.starts_with("parse-panic:")
                    || expected.parser.starts_with("format-panic:")
                {
                    previously_broken_resolved.push(path);
                } else {
                    became_empty.push(path);
                }
            }
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
    // Symmetric in-tree filter for source drift — see corpus_baseline.rs
    // for the rationale. An in-tree fixture edit is a PR-author action
    // and must fail strict, not be warn-skipped as upstream-race.
    let source_drift_in_tree: Vec<&PathBuf> = source_drift
        .iter()
        .filter(|p| is_in_tree_fixture(p))
        .copied()
        .collect();
    let strict_fail = strict
        && (!unmanifested_in_tree.is_empty()
            || !became_empty.is_empty()
            || !source_drift_in_tree.is_empty());
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
        if !previously_broken_resolved.is_empty() {
            eprintln!(
                "info: {} file(s) previously recorded as a sentinel \
                 (`read-error:*`, `parse-panic:*`, or `format-panic:*`) \
                 are now readable AND parse to no formattable items. \
                 Improvement, not regression; regenerate when convenient.",
                previously_broken_resolved.len(),
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
    if strict && !source_drift_in_tree.is_empty() {
        report.push_str(&format!(
            "\n{} in-tree fixture(s) have edited source without a \
             manifest regen (first 10):\n",
            source_drift_in_tree.len(),
        ));
        for path in source_drift_in_tree.iter().take(10) {
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
