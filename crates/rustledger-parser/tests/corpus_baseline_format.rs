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
//! `relative/path/from/repo-root<TAB>hex-hash`, sorted lexically.
//! Files whose parser output contains zero directives (parse errors,
//! empty file) are skipped: there's nothing for the formatter to
//! produce, and the manifest stays tight.
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

use std::collections::BTreeMap;
use std::panic::AssertUnwindSafe;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use rustledger_core::format::FormatConfig;
use rustledger_parser::format_source;

const CORPUS_ROOT: &str = "tests/compatibility/files";
const MANIFEST_PATH: &str = "tests/baselines/format-corpus.manifest";

/// Minimum corpus size we consider "fully populated." Matches the
/// parser baseline (see `corpus_baseline.rs`).
const MIN_FULL_CORPUS_SIZE: usize = 100;

type FileHash = String;

fn repo_root() -> &'static Path {
    static ROOT: OnceLock<PathBuf> = OnceLock::new();
    ROOT.get_or_init(|| {
        // Two-condition anchor (corpus dir + workspace Cargo.toml)
        // avoids halting at a coincidentally-named parent.
        // See corpus_baseline.rs::repo_root() for rationale.
        let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        loop {
            if p.join("tests/compatibility/files").is_dir()
                && std::fs::read_to_string(p.join("Cargo.toml"))
                    .is_ok_and(|s| s.contains("[workspace]"))
            {
                return p;
            }
            assert!(p.pop(), "could not locate repo root");
        }
    })
}

fn discover_corpus_files() -> Vec<PathBuf> {
    let corpus_dir = repo_root().join(CORPUS_ROOT);
    let mut out = Vec::new();
    if !corpus_dir.is_dir() {
        return out;
    }
    walk(&corpus_dir, &mut out);
    out.sort();
    out
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            walk(&path, out);
        } else if path.extension().and_then(|s| s.to_str()) == Some("beancount") {
            let rel = path
                .strip_prefix(repo_root())
                .expect("corpus paths under repo_root")
                .to_path_buf();
            out.push(rel);
        }
    }
}

/// Parse `path` (absolute), pass its directives through
/// [`format_source`] (the exact API the CLI uses), and return a
/// stable hash of the formatted text.
///
/// Files that parse to zero directives return `None`. These are
/// pure-comment files, empty files, or files whose every directive
/// failed to parse; `format_source` would produce a degenerate
/// output and there's no useful drift signal.
///
/// Parser or formatter panics are encoded as a stable sentinel hash
/// so a panicking file doesn't kill visibility on the other ~700.
fn fingerprint(absolute_path: &Path) -> Option<FileHash> {
    let source = std::fs::read_to_string(absolute_path).ok()?;
    let outcome = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let result = rustledger_parser::parse(&source);
        if result.directives.is_empty() {
            return None;
        }
        Some(format_source(&source, &result, &FormatConfig::default()))
    }));
    match outcome {
        Ok(Some(text)) => Some(blake3::hash(text.as_bytes()).to_hex().to_string()),
        Ok(None) => None,
        Err(payload) => {
            let msg = payload
                .downcast_ref::<&'static str>()
                .copied()
                .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
                .unwrap_or("<non-string panic payload>");
            Some(format!("panic:{}", blake3::hash(msg.as_bytes()).to_hex()))
        }
    }
}

fn compute_manifest() -> BTreeMap<PathBuf, FileHash> {
    let root = repo_root();
    discover_corpus_files()
        .into_iter()
        .filter_map(|rel| fingerprint(&root.join(&rel)).map(|h| (rel, h)))
        .collect()
}

fn read_committed_manifest() -> BTreeMap<PathBuf, FileHash> {
    let path = repo_root().join(MANIFEST_PATH);
    let contents = std::fs::read_to_string(&path).unwrap_or_default();
    let mut out = BTreeMap::new();
    for line in contents.lines() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let Some((path_str, hash)) = line.split_once('\t') else {
            continue;
        };
        out.insert(PathBuf::from(path_str), hash.to_string());
    }
    out
}

fn render_manifest(manifest: &BTreeMap<PathBuf, FileHash>) -> String {
    let mut out = String::new();
    out.push_str("# Formatter-output baseline. See crates/rustledger-parser/tests/corpus_baseline_format.rs.\n");
    out.push_str("# Regenerate: BASELINE_UPDATE=1 cargo test -p rustledger-parser --test corpus_baseline_format\n");
    for (path, hash) in manifest {
        out.push_str(&path.to_string_lossy());
        out.push('\t');
        out.push_str(hash);
        out.push('\n');
    }
    out
}

fn write_manifest(manifest: &BTreeMap<PathBuf, FileHash>) {
    let path = repo_root().join(MANIFEST_PATH);
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).expect("create baseline dir");
    }
    std::fs::write(&path, render_manifest(manifest)).expect("write manifest");
    eprintln!("wrote {} entries to {}", manifest.len(), MANIFEST_PATH);
}

#[test]
fn formatter_output_matches_baseline() {
    if std::env::var_os("BASELINE_UPDATE").is_some() {
        let current = compute_manifest();
        write_manifest(&current);
        return;
    }

    let current = compute_manifest();
    let committed = read_committed_manifest();
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

    // Bidirectional drift check (see corpus_baseline.rs for the
    // rationale). The formatter manifest can legitimately have fewer
    // entries than the corpus has files (files that parse to zero
    // directives have no baseline). We only flag missing-from-manifest
    // for files that DO parse non-empty.
    let mut hash_changes: Vec<(PathBuf, &FileHash, &FileHash)> = Vec::new();
    let mut missing_from_corpus: Vec<&PathBuf> = Vec::new();
    let mut missing_from_manifest: Vec<&PathBuf> = Vec::new();
    for (path, expected_hash) in &committed {
        match current.get(path) {
            Some(current_hash) if current_hash != expected_hash => {
                hash_changes.push((path.clone(), expected_hash, current_hash));
            }
            Some(_) => {}
            None => missing_from_corpus.push(path),
        }
    }
    for path in current.keys() {
        if !committed.contains_key(path) {
            missing_from_manifest.push(path);
        }
    }

    let unprotected_in_strict = strict && !missing_from_manifest.is_empty();
    if hash_changes.is_empty() && !unprotected_in_strict {
        if !missing_from_manifest.is_empty() {
            eprintln!(
                "warning: {} corpus file(s) format to non-empty output \
                 but have no manifest entry. Regenerate to extend \
                 coverage:\n  BASELINE_UPDATE=1 cargo test -p \
                 rustledger-parser --test corpus_baseline_format",
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
        return;
    }

    let mut report = String::new();
    if !hash_changes.is_empty() {
        report.push_str(&format!(
            "Hash mismatch on {} file(s) (first 10 shown):\n",
            hash_changes.len(),
        ));
        for (path, expected, current) in hash_changes.iter().take(10) {
            report.push_str(&format!(
                "  {path}\n    expected: {e}\n    current:  {c}\n",
                path = path.display(),
                e = &expected[..16],
                c = &current[..16],
            ));
        }
    }
    if unprotected_in_strict {
        report.push_str(&format!(
            "\n{} corpus file(s) format non-empty but have no manifest \
             entry (first 10):\n",
            missing_from_manifest.len(),
        ));
        for path in missing_from_manifest.iter().take(10) {
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
