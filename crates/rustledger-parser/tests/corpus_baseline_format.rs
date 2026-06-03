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

/// Per-file fingerprint: source-content hash plus formatted-output
/// hash. The source hash lets the gate distinguish "upstream pushed
/// a new version of this corpus file" from "the formatter changed."
/// See `corpus_baseline.rs::FileFingerprint`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct FileFingerprint {
    source: String,
    parser: String,
}

fn repo_root() -> &'static Path {
    static ROOT: OnceLock<PathBuf> = OnceLock::new();
    ROOT.get_or_init(|| {
        // Two-condition anchor (corpus dir + workspace Cargo.toml)
        // avoids halting at a coincidentally-named parent.
        // See corpus_baseline.rs::repo_root() for rationale.
        let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        loop {
            if p.join("tests/compatibility/files").is_dir() && has_workspace_table(&p) {
                return p;
            }
            assert!(p.pop(), "could not locate repo root");
        }
    })
}

/// See `corpus_baseline.rs::is_in_tree_fixture` for rationale.
fn is_in_tree_fixture(rel: &Path) -> bool {
    rel.starts_with("tests/compatibility/files/plugins/")
}

fn has_workspace_table(dir: &Path) -> bool {
    let Ok(toml) = std::fs::read_to_string(dir.join("Cargo.toml")) else {
        return false;
    };
    toml.lines()
        .any(|line| line.trim_start().starts_with("[workspace]"))
}

fn discover_corpus_files() -> &'static [PathBuf] {
    // Cached: the formatter test calls discovery from both
    // compute_manifest and the small-corpus guard. See
    // corpus_baseline.rs::discover_corpus_files for rationale.
    static DISCOVERED: OnceLock<Vec<PathBuf>> = OnceLock::new();
    DISCOVERED.get_or_init(|| {
        let corpus_dir = repo_root().join(CORPUS_ROOT);
        let mut out = Vec::new();
        if !corpus_dir.is_dir() {
            return out;
        }
        walk(&corpus_dir, &mut out);
        out.sort();
        out
    })
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
fn fingerprint(absolute_path: &Path) -> Option<FileFingerprint> {
    let source = std::fs::read_to_string(absolute_path).ok()?;
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

/// See `corpus_baseline.rs::panic_payload_hash` for the rationale.
/// Duplicated here rather than lifted to a shared module to keep
/// each test binary self-contained.
fn panic_payload_hash(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        return blake3::hash(s.as_bytes()).to_hex().to_string();
    }
    if let Some(s) = payload.downcast_ref::<String>() {
        return blake3::hash(s.as_bytes()).to_hex().to_string();
    }
    let mut h = blake3::Hasher::new();
    h.update(b"non-string-panic:");
    h.update(format!("{:?}", payload.type_id()).as_bytes());
    h.finalize().to_hex().to_string()
}

fn compute_manifest() -> BTreeMap<PathBuf, FileFingerprint> {
    let root = repo_root();
    discover_corpus_files()
        .iter()
        .filter_map(|rel| fingerprint(&root.join(rel)).map(|fp| (rel.clone(), fp)))
        .collect()
}

fn read_committed_manifest() -> BTreeMap<PathBuf, FileFingerprint> {
    let path = repo_root().join(MANIFEST_PATH);
    let contents = std::fs::read_to_string(&path).unwrap_or_default();
    let mut out = BTreeMap::new();
    for line in contents.lines() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut parts = line.split('\t');
        let (Some(path_str), Some(source), Some(parser)) =
            (parts.next(), parts.next(), parts.next())
        else {
            continue;
        };
        out.insert(
            PathBuf::from(path_str),
            FileFingerprint {
                source: source.to_string(),
                parser: parser.to_string(),
            },
        );
    }
    out
}

fn render_manifest(manifest: &BTreeMap<PathBuf, FileFingerprint>) -> String {
    let mut out = String::new();
    out.push_str("# Formatter-output baseline. See crates/rustledger-parser/tests/corpus_baseline_format.rs.\n");
    out.push_str("# Format: path<TAB>source_hash<TAB>format_output_hash\n");
    out.push_str("# Regenerate: BASELINE_UPDATE=1 cargo test -p rustledger-parser --test corpus_baseline_format\n");
    for (path, fp) in manifest {
        out.push_str(&path.to_string_lossy());
        out.push('\t');
        out.push_str(&fp.source);
        out.push('\t');
        out.push_str(&fp.parser);
        out.push('\n');
    }
    out
}

fn write_manifest(manifest: &BTreeMap<PathBuf, FileFingerprint>) {
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
    // Discover-on-disk tells us whether a missing-from-current file
    // is genuinely gone from the corpus OR still on disk but now
    // parses to zero directives (a parser regression we should
    // surface as drift, not silently warn about).
    let on_disk: std::collections::HashSet<&PathBuf> = discover_corpus_files().iter().collect();

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
    // failure (see corpus_baseline.rs comment for rationale).
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
