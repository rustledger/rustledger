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
//! ## Regeneration
//!
//! ```ignore
//! BASELINE_UPDATE=1 cargo test -p rustledger-parser --test \
//!   corpus_baseline_format
//! ```
//!
//! Review the diff and commit.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use rustledger_core::format::{FormatConfig, format_directives};

const CORPUS_ROOT: &str = "tests/compatibility/files";
const MANIFEST_PATH: &str = "tests/baselines/format-corpus.manifest";

type FileHash = String;

fn repo_root() -> &'static Path {
    static ROOT: OnceLock<PathBuf> = OnceLock::new();
    ROOT.get_or_init(|| {
        let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        loop {
            if p.join("tests/compatibility").is_dir() {
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

/// Parse `path` (absolute), pass its directives through the default
/// formatter, return a stable hash of the formatted text.
///
/// Files that parse to zero directives return `None`. These are
/// either pure-comment files, empty files, or files whose every
/// directive failed to parse; the formatter has nothing to emit
/// in any of these cases, and there is no useful baseline.
fn fingerprint(absolute_path: &Path) -> Option<FileHash> {
    let source = std::fs::read_to_string(absolute_path).ok()?;
    let result = rustledger_parser::parse(&source);
    if result.directives.is_empty() {
        return None;
    }
    // The formatter API takes &Directive; the parser hands us
    // Spanned<Directive>. Deref through .value.
    let directives = result.directives.iter().map(|s| &s.value);
    let formatted = format_directives(directives, &FormatConfig::default());
    Some(blake3::hash(formatted.as_bytes()).to_hex().to_string())
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

    if current.is_empty() && !strict {
        eprintln!(
            "corpus is empty at `{CORPUS_ROOT}`. Run \
             `./scripts/fetch-compat-test-files.sh` to populate it; \
             skipping formatter baseline check. Set STRICT_BASELINE=1 \
             to make this a hard failure (CI uses STRICT_BASELINE)."
        );
        return;
    }

    if strict && current.len() < committed.len() {
        panic!(
            "STRICT_BASELINE: current corpus produces {} formattable \
             files, manifest expects {}. Either the corpus shrank or \
             previously-parseable files now fail to parse.",
            current.len(),
            committed.len()
        );
    }

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
        "Formatter output drifted from the committed baseline for {} \
         file(s). First {} shown:\n\n{}\n\nIf this drift is \
         intentional, regenerate:\n  \
         BASELINE_UPDATE=1 cargo test -p rustledger-parser --test \
         corpus_baseline_format\n\nReview the diff against \
         `{MANIFEST_PATH}` and commit.",
        mismatches.len(),
        mismatches.len().min(10),
        preview,
    );
}
