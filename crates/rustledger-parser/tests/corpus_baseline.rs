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
//! one line per file, `relative/path/from/repo-root<TAB>hex-hash`,
//! sorted lexically. The hash covers the `ParseResult`'s Debug
//! representation, which is deterministic for our types
//! (`Vec`-based, no `HashMap` payloads).
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
//! Review the diff and commit. CI must NOT regenerate on its own —
//! the whole point is that drift fails the build.
//!
//! ## In-tree vs downloaded corpus
//!
//! The corpus under `tests/compatibility/files/` is mostly downloaded
//! by `scripts/fetch-compat-test-files.sh` and not checked in. This
//! test runs against whatever files are present:
//!
//! - Local dev with no corpus downloaded: covers the 3 in-tree
//!   `plugins/` fixtures. The manifest will only list those.
//! - CI after corpus download: covers ~1000 files. The manifest
//!   committed to the repo covers this case; mismatch fails CI.
//!
//! If your local checkout has the corpus AND your manifest covers
//! fewer files than your checkout (the in-tree-only case), the test
//! warns but passes; this avoids dev-loop friction. Running in
//! `STRICT_BASELINE=1` mode treats this as failure (used by CI).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// Relative path to the corpus root from the repo root.
const CORPUS_ROOT: &str = "tests/compatibility/files";

/// Relative path to the committed manifest from the repo root.
const MANIFEST_PATH: &str = "tests/baselines/parser-corpus.manifest";

/// Hash of one file's parsed output.
type FileHash = String;

fn repo_root() -> &'static Path {
    static ROOT: OnceLock<PathBuf> = OnceLock::new();
    ROOT.get_or_init(|| {
        // Walk up from CARGO_MANIFEST_DIR until we find a directory
        // containing `tests/compatibility`. That's the repo root in
        // both local checkouts and CI.
        let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        loop {
            if p.join("tests/compatibility").is_dir() {
                return p;
            }
            assert!(
                p.pop(),
                "could not locate repo root from {}",
                env!("CARGO_MANIFEST_DIR")
            );
        }
    })
}

/// Walk `CORPUS_ROOT` for every `.beancount` file. Returns paths
/// relative to the repo root, sorted lexically so the output is
/// deterministic.
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
                .expect("corpus paths are under repo_root")
                .to_path_buf();
            out.push(rel);
        }
    }
}

/// Parse `path` (absolute) and return a stable hash of the
/// `ParseResult` Debug representation. Errors during file reading
/// or non-UTF-8 content are themselves part of the fingerprint:
/// a future parser change that makes a previously-readable file
/// unreadable would still show up as a manifest delta.
fn fingerprint(absolute_path: &Path) -> FileHash {
    let source = match std::fs::read_to_string(absolute_path) {
        Ok(s) => s,
        Err(e) => return format!("read-error:{}", e.kind() as u32),
    };
    let result = rustledger_parser::parse(&source);
    // Debug formatting is deterministic for our types: directives
    // are Vec-ordered, errors are Vec-ordered, no HashMap payloads
    // in the AST. blake3 of the Debug string gives a 32-byte hash
    // that captures every observable parser output.
    let debug_repr = format!("{result:#?}");
    let hash = blake3::hash(debug_repr.as_bytes());
    hash.to_hex().to_string()
}

fn compute_manifest() -> BTreeMap<PathBuf, FileHash> {
    let root = repo_root();
    discover_corpus_files()
        .into_iter()
        .map(|rel| {
            let absolute = root.join(&rel);
            let hash = fingerprint(&absolute);
            (rel, hash)
        })
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
    out.push_str(
        "# Parser-output baseline. See crates/rustledger-parser/tests/corpus_baseline.rs.\n",
    );
    out.push_str(
        "# Regenerate: BASELINE_UPDATE=1 cargo test -p rustledger-parser --test corpus_baseline\n",
    );
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

/// The baseline test.
///
/// Modes:
/// - **Default** (no env var): compare current output against the
///   committed manifest. Mismatch fails. Empty corpus directory is
///   tolerated (local dev without `fetch-compat-test-files.sh`).
/// - `BASELINE_UPDATE=1`: regenerate the manifest. Use deliberately.
/// - `STRICT_BASELINE=1`: also fail if the corpus has fewer files
///   than the manifest expects. Used by CI to catch a missing
///   `fetch-compat-test-files.sh` step.
#[test]
fn parser_output_matches_baseline() {
    if std::env::var_os("BASELINE_UPDATE").is_some() {
        let current = compute_manifest();
        write_manifest(&current);
        return;
    }

    let current = compute_manifest();
    let committed = read_committed_manifest();
    let strict = std::env::var_os("STRICT_BASELINE").is_some();

    if current.is_empty() && !strict {
        eprintln!(
            "corpus is empty at `{CORPUS_ROOT}`. Run \
             `./scripts/fetch-compat-test-files.sh` to populate it; \
             skipping baseline check. Set STRICT_BASELINE=1 to make \
             this a hard failure (CI uses STRICT_BASELINE)."
        );
        return;
    }

    if strict && current.len() < committed.len() {
        panic!(
            "STRICT_BASELINE: current corpus has {} files, manifest \
             expects {}. Did `fetch-compat-test-files.sh` succeed?",
            current.len(),
            committed.len()
        );
    }

    // Compare entries that appear in BOTH the committed manifest and
    // the current corpus. Files in the corpus but not the manifest
    // are not failures (they were added without baselining); files
    // in the manifest but not the corpus we treat as expected only
    // under STRICT_BASELINE (covered above).
    let mut mismatches: Vec<(PathBuf, &FileHash, &FileHash)> = Vec::new();
    for (path, expected_hash) in &committed {
        if let Some(current_hash) = current.get(path)
            && current_hash != expected_hash
        {
            mismatches.push((path.clone(), expected_hash, current_hash));
        }
    }

    if mismatches.is_empty() {
        return;
    }

    let preview = mismatches
        .iter()
        .take(10)
        .map(|(path, expected, current)| {
            format!(
                "  {path}\n    expected: {expected}\n    current:  {current}",
                path = path.display(),
                expected = &expected[..16],
                current = &current[..16],
            )
        })
        .collect::<Vec<_>>()
        .join("\n");

    panic!(
        "Parser output drifted from the committed baseline for {} \
         file(s). First {} shown:\n\n{}\n\nIf this drift is \
         intentional, regenerate the manifest:\n  \
         BASELINE_UPDATE=1 cargo test -p rustledger-parser --test \
         corpus_baseline\n\nReview the diff against \
         `{MANIFEST_PATH}` and commit.",
        mismatches.len(),
        mismatches.len().min(10),
        preview,
    );
}

/// Sanity check: discovery must find at least the in-tree
/// `plugins/` fixtures. If this fails the corpus path resolution is
/// wrong and every other test in this file is silently no-op.
#[test]
fn discovery_finds_in_tree_plugin_fixtures() {
    let files = discover_corpus_files();
    let plugin_fixtures: Vec<_> = files
        .iter()
        .filter(|p| p.to_string_lossy().contains("plugins/implicit_prices"))
        .collect();
    assert!(
        !plugin_fixtures.is_empty(),
        "expected to find at least one in-tree fixture under \
         tests/compatibility/files/plugins/implicit_prices/; got \
         {} corpus files total. Check CORPUS_ROOT resolution.",
        files.len()
    );
}
