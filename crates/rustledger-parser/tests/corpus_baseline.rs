//! Parser-output baseline for the compatibility corpus.
//!
//! Phase 0 of the parser-CST migration tracking issue (#1262). The
//! migration plan stands up a parallel parser in `rustledger-cst` and
//! gates equivalence via a differential test. Before any of that
//! work can start, we need a contract that says "the current parser's
//! output on the corpus is what it is, and any change to that output
//! is detected by CI." Without this baseline, a future PR could
//! silently shift parser output without anyone noticing until the
//! differential test starts firing for the wrong reasons.
//!
//! The baseline manifest is `tests/baselines/parser-corpus.manifest`:
//! one line per file, sorted lexically, with two hashes per line:
//!
//! ```text
//! relative/path<TAB>source_blake3<TAB>parser_output_blake3
//! ```
//!
//! Both hashes are present so the gate can distinguish "the
//! compatibility corpus drifted upstream" from "the parser's output
//! changed." Without that distinction CI fires on every push that
//! happens to land while an upstream beancount-related repo gets a
//! new commit, and the test stops being a useful gate.
//!
//! Drift policy:
//! - `source` matches AND `parser` matches: no change.
//! - `source` matches AND `parser` differs: real parser drift, fails.
//! - `source` differs: corpus content changed upstream; we warn and
//!   skip the parser check for that file. Strict mode does NOT
//!   treat this as failure because a corpus-fetch race is outside
//!   the PR author's control. Regenerate the manifest to refresh.
//! - File in manifest but absent from disk: warn (corpus shrank).
//! - File on disk but absent from manifest: warn in default mode;
//!   strict mode escalates ONLY for in-tree fixtures (new fixture
//!   without regen). Downloaded-corpus appearances are subject to
//!   upstream-fetch race and warn-only.
//!
//! ## Fingerprint stability
//!
//! `Directive` (in `rustledger-core::directive`) carries a
//! `meta: FxHashMap<String, MetaValue>` field, and `FxHashMap`'s
//! `Debug` iterates in hashbrown bucket order. That's deterministic
//! for a given hashbrown version but NOT stable across versions, so
//! a naive `format!("{:#?}", result)` hash would generate spurious
//! cross-file drift on every hashbrown bump.
//!
//! Instead we route directives through `serde_json::to_value`, whose
//! `Map` is backed by `BTreeMap` and therefore sorts metadata keys
//! deterministically regardless of source hashbrown order. All other
//! `ParseResult` fields are `Vec<_>` (or scalars like `has_leading_bom`)
//! with no map payloads inside, so `Debug` is deterministic for them.
//! See [`fingerprint_covers_every_parse_result_field`] for the
//! runtime guard that catches field omissions in [`parser_hash_of`].
//!
//! ## Regeneration
//!
//! When a parser-output change is intentional, regenerate the
//! manifest:
//!
//! ```ignore
//! BASELINE_UPDATE=1 cargo test -p rustledger-parser --test corpus_baseline
//! ```
//!
//! Review the diff and commit. CI must NOT regenerate on its own;
//! the whole point is that drift fails the build.
//!
//! ## TODO: phase-3-of-#1262 staleness
//!
//! When `rustledger-cst::parse` becomes the production parser
//! (phase 3.2 of #1262 swaps `rustledger-loader` to it), this gate
//! still runs against the OLD `rustledger-parser` until phase 5.1.
//! Between those phases the gate measures a parser users no longer
//! invoke. A phase-3.5+ PR should add a parallel CST baseline
//! alongside this one, or this gate should be removed when phase 5.1
//! lands. The new manifest scheme (`path` + `source_hash` +
//! `parser_hash`) lets a parallel CST baseline share corpus and
//! source hashes cheaply.

mod baseline_common;

use std::panic::AssertUnwindSafe;
use std::path::{Path, PathBuf};

use baseline_common::{
    CORPUS_ROOT, FileFingerprint, IN_TREE_FIXTURE_PREFIX, MIN_FULL_CORPUS_SIZE, compute_manifest,
    discover_corpus_files, is_in_tree_fixture, panic_payload_hash, read_committed_manifest,
    repo_root, write_manifest,
};

/// Relative path to the committed manifest from the repo root.
const MANIFEST_PATH: &str = "tests/baselines/parser-corpus.manifest";

/// Manifest header. Written verbatim by `BASELINE_UPDATE=1`.
const MANIFEST_HEADER: &[&str] = &[
    "# Parser-output baseline. See crates/rustledger-parser/tests/corpus_baseline.rs.",
    "# Format: path<TAB>source_hash<TAB>parser_output_hash",
    "# Regenerate: BASELINE_UPDATE=1 cargo test -p rustledger-parser --test corpus_baseline",
];

/// Parse `path` (absolute) and return its `(source, parser)`
/// fingerprint pair. See module rustdoc for the drift policy that
/// consumes these.
fn fingerprint(absolute_path: &Path) -> FileFingerprint {
    let source = match std::fs::read_to_string(absolute_path) {
        Ok(s) => s,
        Err(e) => {
            // Read error: both hashes encode the failure kind so the
            // manifest line is self-describing and the format
            // baseline's symmetric handling lines up.
            let tag = format!("read-error:{:?}", e.kind());
            return FileFingerprint {
                source: tag.clone(),
                parser: tag,
            };
        }
    };
    let source_hash = blake3::hash(source.as_bytes()).to_hex().to_string();
    let parse_outcome =
        std::panic::catch_unwind(AssertUnwindSafe(|| rustledger_parser::parse(&source)));
    let result = match parse_outcome {
        Ok(r) => r,
        Err(payload) => {
            return FileFingerprint {
                source: source_hash,
                parser: format!("panic:{}", panic_payload_hash(&*payload)),
            };
        }
    };
    FileFingerprint {
        source: source_hash,
        parser: parser_hash_of(&result),
    }
}

/// Hash a fully-formed `ParseResult` to the canonical parser
/// fingerprint.
///
/// The payload bytes come from
/// [`rustledger_parser::__baseline_canonical_payload`], a doc-hidden
/// helper inside the parser crate that performs an exhaustive
/// destructure of `ParseResult`. Because the destructure lives in the
/// defining crate, `#[non_exhaustive]` does not apply and the
/// compiler flags any added field — closing the BOM-flag-omission
/// class of bug at compile time, not just at test time. The runtime
/// coverage test [`fingerprint_covers_every_parse_result_field`]
/// remains as defense in depth.
fn parser_hash_of(result: &rustledger_parser::ParseResult) -> String {
    let payload = rustledger_parser::__baseline_canonical_payload(result);
    blake3::hash(&payload).to_hex().to_string()
}

/// The baseline test.
///
/// Modes:
/// - **Default** (no env var): compare current output against the
///   committed manifest. Mismatch fails. A corpus smaller than
///   [`MIN_FULL_CORPUS_SIZE`] files is treated as not-fully-populated
///   and skipped.
/// - `BASELINE_UPDATE=1`: regenerate the manifest. Use deliberately.
/// - `STRICT_BASELINE=1`: turn skip-on-small-corpus into a hard
///   failure, and escalate missing-from-manifest in-tree fixtures
///   to drift. Used by CI.
#[test]
fn parser_output_matches_baseline() {
    let manifest_abs = repo_root().join(MANIFEST_PATH);
    let fp = |p: &Path| Some(fingerprint(p));
    let update = std::env::var_os("BASELINE_UPDATE").is_some();
    let strict = std::env::var_os("STRICT_BASELINE").is_some();

    let current = compute_manifest(fp);

    // Corpus-size guard runs BEFORE the BASELINE_UPDATE write path so
    // a bare `BASELINE_UPDATE=1 cargo test ...` invocation (per the
    // module rustdoc's regeneration snippet) on a fresh checkout
    // cannot truncate the committed manifest down to the 3 in-tree
    // plugin fixtures. `scripts/regen-corpus-baselines.sh` has its
    // own outer guard; this is the inner one that protects the
    // direct-cargo-invocation path documented in the rustdoc.
    if current.len() < MIN_FULL_CORPUS_SIZE {
        assert!(
            !strict,
            "STRICT_BASELINE: current corpus has {} files (need at \
             least {MIN_FULL_CORPUS_SIZE}). Did \
             `fetch-compat-test-files.sh` run?",
            current.len(),
        );
        assert!(
            !update,
            "BASELINE_UPDATE=1 refusing to write a manifest from only \
             {} files (need at least {MIN_FULL_CORPUS_SIZE}). Run \
             `./scripts/fetch-compat-test-files.sh` first; an unguarded \
             regen would silently truncate the committed manifest.",
            current.len(),
        );
        eprintln!(
            "corpus at `{CORPUS_ROOT}` has only {} files (need at least \
             {MIN_FULL_CORPUS_SIZE}). Run \
             `./scripts/fetch-compat-test-files.sh`; skipping baseline \
             check. CI uses STRICT_BASELINE=1 to make this a hard \
             failure.",
            current.len(),
        );
        return;
    }

    if update {
        // Deliberately skip read_committed_manifest in update mode:
        // a corrupt or partially-written committed manifest must not
        // panic the very regen that would replace it.
        write_manifest(&manifest_abs, &current, MANIFEST_HEADER);
        return;
    }

    let committed = read_committed_manifest(&manifest_abs);

    // Source-aware drift classification. See module rustdoc.
    let mut parser_drift: Vec<(&PathBuf, &str, &str)> = Vec::new();
    let mut source_drift: Vec<&PathBuf> = Vec::new();
    let mut missing_from_corpus: Vec<&PathBuf> = Vec::new();
    let mut missing_from_manifest: Vec<&PathBuf> = Vec::new();
    // Committed sentinel (`panic:*` or `read-error:*`) now produces a
    // real hash: the file was broken, now it isn't. Improvement, not
    // regression. Warn only; never strict-fail. Symmetric with the
    // format baseline's `previously_broken_resolved` bucket.
    let mut previously_broken_resolved: Vec<&PathBuf> = Vec::new();

    for (path, expected) in &committed {
        match current.get(path) {
            None => missing_from_corpus.push(path),
            Some(current_fp) if current_fp.source != expected.source => {
                source_drift.push(path);
            }
            Some(current_fp) if current_fp.parser != expected.parser => {
                let was_broken = expected.parser.starts_with("panic:")
                    || expected.parser.starts_with("read-error:");
                let is_now_real = !current_fp.parser.starts_with("panic:")
                    && !current_fp.parser.starts_with("read-error:");
                if was_broken && is_now_real {
                    previously_broken_resolved.push(path);
                } else {
                    parser_drift.push((path, expected.parser.as_str(), current_fp.parser.as_str()));
                }
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
    // race; the CI gate would otherwise fire on legitimate upstream
    // pushes that have nothing to do with parser changes.
    let unmanifested_in_tree: Vec<&PathBuf> = missing_from_manifest
        .iter()
        .filter(|p| is_in_tree_fixture(p))
        .copied()
        .collect();
    // Symmetric in-tree filter for source drift: editing an in-tree
    // fixture IS a PR-author action (no upstream race), so source drift
    // on those files should fail strict mode the same way an
    // unmanifested in-tree fixture does. Without this filter a
    // contributor could edit `plugins/.../foo.beancount` in a way
    // that changes parser output and the source-drift bucket would
    // skip the parser check, leaving the manifest silently desynced.
    let source_drift_in_tree: Vec<&PathBuf> = source_drift
        .iter()
        .filter(|p| is_in_tree_fixture(p))
        .copied()
        .collect();
    let unprotected_in_strict =
        strict && (!unmanifested_in_tree.is_empty() || !source_drift_in_tree.is_empty());
    if parser_drift.is_empty() && !unprotected_in_strict {
        if !source_drift.is_empty() {
            eprintln!(
                "info: {} corpus file(s) have new upstream content \
                 (source hash changed). Parser output on those files \
                 was NOT checked. Regenerate when convenient:\n  \
                 BASELINE_UPDATE=1 cargo test -p rustledger-parser \
                 --test corpus_baseline",
                source_drift.len(),
            );
        }
        if !missing_from_manifest.is_empty() {
            eprintln!(
                "warning: {} corpus file(s) have no manifest entry.",
                missing_from_manifest.len(),
            );
        }
        if !missing_from_corpus.is_empty() {
            eprintln!(
                "warning: {} manifest entry/entries refer to files no \
                 longer present in the corpus.",
                missing_from_corpus.len(),
            );
        }
        if !previously_broken_resolved.is_empty() {
            eprintln!(
                "info: {} file(s) previously recorded as a sentinel \
                 (`panic:*` or `read-error:*`) now parse cleanly. \
                 Improvement, not regression; regenerate when convenient.",
                previously_broken_resolved.len(),
            );
        }
        return;
    }

    let mut report = String::new();
    if !parser_drift.is_empty() {
        report.push_str(&format!(
            "Parser-output drift on {} file(s) with unchanged source \
             (first 10 shown):\n",
            parser_drift.len(),
        ));
        for (path, expected, current) in parser_drift.iter().take(10) {
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
            "\n{} in-tree fixture(s) have no manifest entry (first 10):\n",
            unmanifested_in_tree.len(),
        ));
        for path in unmanifested_in_tree.iter().take(10) {
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
        "Parser baseline drift:\n\n{report}\nIf this drift is \
         intentional, regenerate:\n  \
         BASELINE_UPDATE=1 cargo test -p rustledger-parser --test \
         corpus_baseline\n\nReview the diff against `{MANIFEST_PATH}` \
         and commit.",
    );
}

/// Sanity check: discovery must find at least one in-tree fixture
/// under the `IN_TREE_FIXTURE_PREFIX` path. If this fails the corpus
/// path resolution is wrong and every other test in this file is
/// silently no-op. Routed through the const so renaming a specific
/// fixture (e.g., `plugins/implicit_prices/` → `plugins/foo/`) does
/// not break a test that's actually checking corpus discovery, not
/// that one fixture's presence.
#[test]
fn discovery_finds_in_tree_plugin_fixtures() {
    let files = discover_corpus_files();
    let has_plugin_fixture = files.iter().any(|p| p.starts_with(IN_TREE_FIXTURE_PREFIX));
    assert!(
        has_plugin_fixture,
        "expected to find at least one in-tree fixture under \
         `{IN_TREE_FIXTURE_PREFIX}`; got {} corpus files total. \
         Check CORPUS_ROOT resolution and the `.gitignore` exception.",
        files.len()
    );
}

/// Same-binary determinism guard.
///
/// The fingerprint algorithm assumes that the only `HashMap`-shaped
/// payload in `ParseResult` is `Directive.meta` / `Posting.meta`,
/// and that the canonicalization through `serde_json::to_value`
/// handles it. If a future PR adds a `HashMap`-bearing field to
/// `ParseResult`, `ParseError`, `ParseWarning`, or any nested type
/// reached by `Debug` formatting, the `Debug`-of-`HashMap` iteration
/// order would silently leak into the fingerprint. The regression
/// then only appears cross-machine on a hashbrown bump.
///
/// This test runs the fingerprint twice in the same binary on a
/// fixture that exercises every supported directive variant
/// (including metadata) and asserts byte equality. A non-deterministic
/// fingerprint fails here loudly, not weeks later in CI on a
/// dependabot PR.
#[test]
fn fingerprint_is_deterministic_within_one_binary() {
    let fixture = r#"
; Exercises directives with metadata to catch any HashMap-of-strings
; leaking iteration order into the fingerprint.
option "title" "T"
plugin "p"
include "i.beancount"

2024-01-01 open Assets:Bank USD
  meta-key-a: "a"
  meta-key-b: "b"
  meta-key-c: "c"

2024-01-02 * "Coffee"
  meta-on-txn: 1
  Assets:Bank  -3.50 USD
    meta-on-posting-1: "x"
    meta-on-posting-2: "y"
  Expenses:Food

2024-01-03 balance Assets:Bank -3.50 USD
2024-01-04 close Assets:Bank
"#;
    let tmp = std::env::temp_dir().join(format!(
        "corpus-baseline-determinism-{}.beancount",
        std::process::id()
    ));
    std::fs::write(&tmp, fixture).expect("write temp fixture");
    let h1 = fingerprint(&tmp);
    let h2 = fingerprint(&tmp);
    std::fs::remove_file(&tmp).ok();
    assert_eq!(
        h1, h2,
        "fingerprint() produced different hashes on identical input \
         within one binary. This usually means a HashMap-shaped field \
         in ParseResult (or one of its nested types) is leaking its \
         iteration order into Debug formatting. Update the fingerprint \
         to canonicalize the new field; see the module rustdoc."
    );
}

/// Field-coverage guard for [`parser_hash_of`].
///
/// `ParseResult` is `#[non_exhaustive]`, so the compiler will not
/// catch a future field added to it but missed in the fingerprint
/// (the BOM-flag omission caught by the round-3 review was exactly
/// this kind of bug). This test exercises each currently-known field
/// by mutating a baseline `ParseResult` along that single axis and
/// asserting the fingerprint changes.
///
/// When a new field lands on `ParseResult`, append it to
/// [`parser_hash_of`] AND add a `mutate` arm below. If you forget
/// the arm, the test still passes (silent for the new field). If you
/// forget the hash update, the new arm fails immediately.
fn assert_field_in_hash(
    baseline_hash: &str,
    baseline_src: &str,
    field_name: &str,
    mutate: impl FnOnce(&mut rustledger_parser::ParseResult),
) {
    let mut variant = rustledger_parser::parse(baseline_src);
    mutate(&mut variant);
    let variant_hash = parser_hash_of(&variant);
    assert_ne!(
        variant_hash, baseline_hash,
        "field `{field_name}` is not covered by parser_hash_of(): mutating \
         it produced an identical fingerprint. Add it to parser_hash_of()."
    );
}

#[test]
fn fingerprint_covers_every_parse_result_field() {
    let baseline_src = "; comment line\n\
                        option \"title\" \"T\"\n\
                        plugin \"p\"\n\
                        include \"i.beancount\"\n\
                        2024-01-01 open Assets:Bank USD\n\
                        2024-01-02 * \"x\"\n  Assets:Bank  1 USD\n  Income:Other\n";
    let baseline = rustledger_parser::parse(baseline_src);
    let baseline_hash = parser_hash_of(&baseline);

    assert_field_in_hash(&baseline_hash, baseline_src, "directives", |v| {
        v.directives.clear();
    });
    assert_field_in_hash(&baseline_hash, baseline_src, "options", |v| {
        v.options.clear();
    });
    assert_field_in_hash(&baseline_hash, baseline_src, "includes", |v| {
        v.includes.clear();
    });
    assert_field_in_hash(&baseline_hash, baseline_src, "plugins", |v| {
        v.plugins.clear();
    });
    assert_field_in_hash(&baseline_hash, baseline_src, "comments", |v| {
        v.comments.clear();
    });
    assert_field_in_hash(&baseline_hash, baseline_src, "errors", |v| {
        use rustledger_parser::{ParseError, ParseErrorKind, Span};
        v.errors.push(ParseError::new(
            ParseErrorKind::UnexpectedEof,
            Span::new(0, 0),
        ));
    });
    assert_field_in_hash(&baseline_hash, baseline_src, "warnings", |v| {
        use rustledger_parser::{ParseWarning, Span};
        v.warnings
            .push(ParseWarning::new("synthetic", Span::new(0, 0)));
    });
    assert_field_in_hash(&baseline_hash, baseline_src, "currency_occurrences", |v| {
        v.currency_occurrences.clear();
    });
    assert_field_in_hash(&baseline_hash, baseline_src, "has_leading_bom", |v| {
        v.has_leading_bom = !v.has_leading_bom;
    });
}
