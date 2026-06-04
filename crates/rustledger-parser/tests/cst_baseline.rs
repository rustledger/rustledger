//! CST baseline gate for `#1262` phase 1.
//!
//! For every `.beancount` file in `tests/compatibility/files/`, hash:
//!
//! 1. The byte-identical round-trip of `parse_flat(source).text()` —
//!    must equal the source. This is the primary CST invariant.
//! 2. The KIND SEQUENCE: the ordered list of every emitted
//!    `(SyntaxKind, byte_range)`. A misclassification (BOM emitted as
//!    `ERROR_TOKEN`, INDENT mistaken for content WHITESPACE, line-start
//!    `#` not folded into COMMENT, etc.) round-trips equally well at
//!    the byte level but produces a different kind sequence — which
//!    the manifest catches.
//!
//! The kind-sequence hash is the gate the round-1 architecture review
//! demanded: a pure byte-round-trip is trivially provable from the
//! adapter's tile-and-cover property, so it doesn't catch the
//! interesting bugs (label drift). Hashing the kind sequence does.
//!
//! Manifest format (one line per file, sorted lexically):
//!
//! ```text
//! relative/path<TAB>source_blake3<TAB>kind_sequence_blake3
//! ```
//!
//! Same shape as the AST-level baseline in `parser-corpus.manifest`,
//! so a phase-2+ contributor adding structural nodes regenerates with
//! `BASELINE_UPDATE=1` and the diff localizes to the files they
//! changed behavior on.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use rustledger_parser::{SyntaxKind, parse_flat};

const CORPUS_ROOT: &str = "tests/compatibility/files";
const MIN_FULL_CORPUS_SIZE: usize = 100;
const MANIFEST_PATH: &str = "tests/baselines/cst-corpus.manifest";

const MANIFEST_HEADER: &[&str] = &[
    "# CST baseline (#1262 phase 1). See crates/rustledger-parser/tests/cst_baseline.rs.",
    "# Format: path<TAB>source_blake3<TAB>kind_sequence_blake3",
    "# Regenerate: BASELINE_UPDATE=1 cargo test -p rustledger-parser --test cst_baseline",
];

#[derive(Debug, Clone, PartialEq, Eq)]
struct Fingerprint {
    source: String,
    kinds: String,
}

fn repo_root() -> &'static Path {
    static ROOT: OnceLock<PathBuf> = OnceLock::new();
    ROOT.get_or_init(|| {
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
    })
}

fn has_workspace_table(dir: &Path) -> bool {
    let Ok(toml) = std::fs::read_to_string(dir.join("Cargo.toml")) else {
        return false;
    };
    toml.lines()
        .any(|line| line.trim_start().starts_with("[workspace]"))
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
    let entries = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read_dir({}) failed: {e}", dir.display()));
    for entry in entries {
        let entry =
            entry.unwrap_or_else(|e| panic!("read_dir entry under {} failed: {e}", dir.display()));
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

/// Compute the fingerprint pair for a single corpus file. Returns
/// `None` for files that can't be UTF-8-decoded (e.g.,
/// `fava/tests_data_invalid-unicode.beancount`); those are recorded
/// as a `read-error:<kind>` sentinel matching the AST baseline.
fn fingerprint(rel: &Path) -> Fingerprint {
    let abs = repo_root().join(rel);
    let source = match std::fs::read_to_string(&abs) {
        Ok(s) => s,
        Err(e) => {
            let tag = format!("read-error:{:?}", e.kind());
            return Fingerprint {
                source: tag.clone(),
                kinds: tag,
            };
        }
    };
    let source_hash = blake3::hash(source.as_bytes()).to_hex().to_string();

    // Round-trip is part of the contract: a divergence here is a hard
    // failure of the CST builder, recorded as a sentinel so the
    // manifest diff is visible.
    let tree = parse_flat(&source);
    let reconstructed = tree.text().to_string();
    if reconstructed != source {
        return Fingerprint {
            source: source_hash,
            kinds: "round-trip-failure".to_string(),
        };
    }

    let kinds_hash = hash_kind_sequence(&tree);
    Fingerprint {
        source: source_hash,
        kinds: kinds_hash,
    }
}

/// Hash the ordered `(SyntaxKind, byte_offset)` sequence of every
/// token in the tree. This is what makes the gate catch
/// classification bugs that pure round-trip can't.
fn hash_kind_sequence(tree: &rustledger_parser::SyntaxNode) -> String {
    let mut hasher = blake3::Hasher::new();
    let mut offset = 0u32;
    for elem in tree.preorder_with_tokens() {
        if let rowan::WalkEvent::Enter(rowan::NodeOrToken::Token(tok)) = elem {
            let kind = tok.kind() as u16;
            let len = u32::try_from(usize::from(tok.text_range().len())).unwrap_or(u32::MAX);
            // u16 kind, u32 length, u32 cumulative offset — fixed
            // layout so any insertion/deletion/reordering produces a
            // different hash.
            hasher.update(&kind.to_le_bytes());
            hasher.update(&len.to_le_bytes());
            hasher.update(&offset.to_le_bytes());
            offset = offset.saturating_add(len);
        } else if let rowan::WalkEvent::Enter(rowan::NodeOrToken::Node(node)) = elem {
            // Hash node kinds too, with a sentinel length, so a
            // future phase-2 PR that introduces a new node kind moves
            // the affected files in the manifest.
            let kind = SyntaxKind::SOURCE_FILE as u16; // sentinel marker for "node enter"
            hasher.update(&kind.to_le_bytes());
            hasher.update(&u32::MAX.to_le_bytes());
            hasher.update(&(node.kind() as u16).to_le_bytes());
        }
    }
    hasher.finalize().to_hex().to_string()
}

fn read_committed_manifest() -> BTreeMap<PathBuf, Fingerprint> {
    let path = repo_root().join(MANIFEST_PATH);
    let contents = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => String::new(),
        Err(e) => panic!("failed to read {}: {e}", path.display()),
    };
    let mut out = BTreeMap::new();
    for (lineno, line) in contents.lines().enumerate() {
        let lineno = lineno + 1;
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut parts = line.split('\t');
        let (Some(path_str), Some(source), Some(kinds), None) =
            (parts.next(), parts.next(), parts.next(), parts.next())
        else {
            panic!(
                "{}:{lineno}: malformed manifest line: {line:?}",
                path.display(),
            );
        };
        out.insert(
            PathBuf::from(path_str),
            Fingerprint {
                source: source.to_string(),
                kinds: kinds.to_string(),
            },
        );
    }
    out
}

fn write_manifest(manifest: &BTreeMap<PathBuf, Fingerprint>) {
    let path = repo_root().join(MANIFEST_PATH);
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).expect("create baseline dir");
    }
    let mut out = String::new();
    for line in MANIFEST_HEADER {
        out.push_str(line);
        out.push('\n');
    }
    for (rel, fp) in manifest {
        use std::fmt::Write;
        let _ = writeln!(
            &mut out,
            "{}\t{}\t{}",
            rel.to_string_lossy(),
            fp.source,
            fp.kinds,
        );
    }
    std::fs::write(&path, out).expect("write manifest");
    eprintln!("wrote {} entries to {}", manifest.len(), path.display());
}

#[test]
fn cst_output_matches_baseline() {
    let strict = std::env::var_os("STRICT_BASELINE").is_some();
    let update = std::env::var_os("BASELINE_UPDATE").is_some();

    let files = discover_corpus_files();

    if files.len() < MIN_FULL_CORPUS_SIZE {
        assert!(
            !strict,
            "STRICT_BASELINE: corpus has {} files (need at least \
             {MIN_FULL_CORPUS_SIZE}). Did `fetch-compat-test-files.sh` run?",
            files.len(),
        );
        assert!(
            !update,
            "BASELINE_UPDATE=1 refusing to write manifest from only {} \
             files. Run `./scripts/fetch-compat-test-files.sh` first.",
            files.len(),
        );
        eprintln!(
            "corpus at `{CORPUS_ROOT}` has only {} files; skipping. \
             CI uses STRICT_BASELINE=1.",
            files.len(),
        );
        return;
    }

    let current: BTreeMap<PathBuf, Fingerprint> = files
        .iter()
        .map(|rel| (rel.clone(), fingerprint(rel)))
        .collect();

    if update {
        write_manifest(&current);
        return;
    }

    let committed = read_committed_manifest();

    let mut drift: Vec<(PathBuf, String, String)> = Vec::new();
    let mut source_drift: Vec<PathBuf> = Vec::new();
    let mut round_trip_failures: Vec<PathBuf> = Vec::new();
    let mut missing_from_corpus: Vec<PathBuf> = Vec::new();
    let mut missing_from_manifest: Vec<PathBuf> = Vec::new();

    for (path, expected) in &committed {
        match current.get(path) {
            None => missing_from_corpus.push(path.clone()),
            Some(c) if c.source != expected.source => source_drift.push(path.clone()),
            Some(c) if c.kinds == "round-trip-failure" => round_trip_failures.push(path.clone()),
            Some(c) if c.kinds != expected.kinds => {
                drift.push((path.clone(), expected.kinds.clone(), c.kinds.clone()));
            }
            Some(_) => {}
        }
    }
    for path in current.keys() {
        if !committed.contains_key(path) {
            missing_from_manifest.push(path.clone());
        }
    }

    if drift.is_empty() && round_trip_failures.is_empty() {
        if !source_drift.is_empty() {
            eprintln!(
                "info: {} corpus file(s) have new source hashes; CST \
                 kind hash NOT checked for those. Regenerate when \
                 convenient: BASELINE_UPDATE=1 cargo test -p \
                 rustledger-parser --test cst_baseline",
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
        return;
    }

    let mut report = String::new();
    if !round_trip_failures.is_empty() {
        use std::fmt::Write;
        let _ = writeln!(
            &mut report,
            "Round-trip failed on {} file(s):",
            round_trip_failures.len(),
        );
        for path in round_trip_failures.iter().take(10) {
            let _ = writeln!(&mut report, "  {}", path.display());
        }
    }
    if !drift.is_empty() {
        use std::fmt::Write;
        let _ = writeln!(
            &mut report,
            "Kind-sequence drift on {} file(s) with unchanged source (first 10):",
            drift.len(),
        );
        for (path, expected, current) in drift.iter().take(10) {
            let _ = writeln!(
                &mut report,
                "  {}\n    expected: {}\n    current:  {}",
                path.display(),
                &expected[..16.min(expected.len())],
                &current[..16.min(current.len())],
            );
        }
    }
    panic!(
        "CST baseline drift:\n\n{report}\nIf this drift is intentional, \
         regenerate:\n  BASELINE_UPDATE=1 cargo test -p rustledger-parser \
         --test cst_baseline\n\nReview the diff against `{MANIFEST_PATH}` \
         and commit.",
    );
}
