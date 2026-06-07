//! CST baseline gate for `#1262`, switched to `parse_structured` at
//! phase 2.1a.
//!
//! For every `.beancount` file in `tests/compatibility/files/`,
//! hash:
//!
//! 1. The byte-identical round-trip of
//!    `parse_structured(source).text()` — must equal the source.
//!    Primary CST invariant.
//! 2. `token_seq_blake3` — ordered `(kind, len)` of LEAF tokens
//!    only. Stable across phase 2+ structural PRs — adding parent
//!    nodes around token runs doesn't change the token sequence.
//!    Only token-classification changes move this hash.
//! 3. `node_shape_blake3` — preorder node-ENTER sequence (kinds,
//!    no tokens). Phase 1 produced one entry per file
//!    (`SOURCE_FILE`). Phase 2.0 added the `DIRECTIVE` umbrella
//!    kind but didn't emit it from the parser. Phase 2.1a emits
//!    specific `*_DIRECTIVE` kinds for 14 single-line directives,
//!    so this column churns on every file that contains any
//!    recognized directive.
//!
//! Manifest format (one line per file, sorted lexically):
//!
//! ```text
//! relative/path<TAB>source_blake3<TAB>token_seq_blake3<TAB>node_shape_blake3
//! ```
//!
//! The split keeps phase-2 review surface honest: a structural PR
//! diffs the node column (expected, every file), and reviewers can
//! verify the token column is unchanged (any drift there is a real
//! regression).

mod baseline_common;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use baseline_common::is_in_tree_fixture;
use rustledger_parser::parse_structured;

const CORPUS_ROOT: &str = "tests/compatibility/files";
const MIN_FULL_CORPUS_SIZE: usize = 100;
const MANIFEST_PATH: &str = "tests/baselines/cst-corpus.manifest";

const MANIFEST_HEADER: &[&str] = &[
    "# CST baseline (#1262 phase 2.3, parse_structured). See crates/rustledger-parser/tests/cst_baseline.rs.",
    "# Format: path<TAB>source_blake3<TAB>token_seq_blake3<TAB>node_shape_blake3",
    "# Regenerate: BASELINE_UPDATE=1 cargo test -p rustledger-parser --test cst_baseline",
];

#[derive(Debug, Clone, PartialEq, Eq)]
struct Fingerprint {
    source: String,
    tokens: String,
    nodes: String,
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

/// Compute the fingerprint triple for a single corpus file. Files
/// that can't be UTF-8-decoded (e.g.,
/// `fava/tests_data_invalid-unicode.beancount`) get a
/// `read-error:<kind>` sentinel in every column matching the AST
/// baseline.
fn fingerprint(rel: &Path) -> Fingerprint {
    let abs = repo_root().join(rel);
    let source = match std::fs::read_to_string(&abs) {
        Ok(s) => s,
        Err(e) => {
            let tag = format!("read-error:{:?}", e.kind());
            return Fingerprint {
                source: tag.clone(),
                tokens: tag.clone(),
                nodes: tag,
            };
        }
    };
    let source_hash = blake3::hash(source.as_bytes()).to_hex().to_string();

    // Round-trip is part of the contract: a divergence here is a hard
    // failure of the CST builder, recorded as a sentinel so the
    // manifest diff is visible.
    let tree = parse_structured(&source);
    let reconstructed = tree.text().to_string();
    if reconstructed != source {
        return Fingerprint {
            source: source_hash,
            tokens: "round-trip-failure".to_string(),
            nodes: "round-trip-failure".to_string(),
        };
    }

    Fingerprint {
        source: source_hash,
        tokens: hash_token_sequence(&tree),
        nodes: hash_node_shape(&tree),
    }
}

/// Hash the ordered `(kind, len)` sequence of LEAF tokens. Stable
/// across phase 2+ structural changes because wrapping tokens in
/// parent nodes doesn't change the token sequence itself. The gate
/// for token-classification bugs (BOM misread as `ERROR_TOKEN`, Comment
/// vs Hash confusion, etc.).
fn hash_token_sequence(tree: &rustledger_parser::SyntaxNode) -> String {
    let mut hasher = blake3::Hasher::new();
    for elem in tree.preorder_with_tokens() {
        if let rowan::WalkEvent::Enter(rowan::NodeOrToken::Token(tok)) = elem {
            let kind = tok.kind() as u16;
            let len = u32::try_from(usize::from(tok.text_range().len())).unwrap_or(u32::MAX);
            hasher.update(&kind.to_le_bytes());
            hasher.update(&len.to_le_bytes());
        }
    }
    hasher.finalize().to_hex().to_string()
}

/// Hash the preorder sequence of node ENTER events (kinds only, no
/// tokens). Phase 1 emits exactly one entry per file (the root
/// `SOURCE_FILE`). Phase 2 PRs that wrap token runs in
/// `DIRECTIVE`/`POSTING`/etc. nodes change this column on every file
/// — that's the expected churn. The split lets reviewers verify
/// `token_seq_blake3` stays put while `node_shape_blake3` moves.
fn hash_node_shape(tree: &rustledger_parser::SyntaxNode) -> String {
    let mut hasher = blake3::Hasher::new();
    for elem in tree.preorder_with_tokens() {
        if let rowan::WalkEvent::Enter(rowan::NodeOrToken::Node(node)) = elem {
            let kind = node.kind() as u16;
            hasher.update(&kind.to_le_bytes());
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
        let (Some(path_str), Some(source), Some(tokens), Some(nodes), None) = (
            parts.next(),
            parts.next(),
            parts.next(),
            parts.next(),
            parts.next(),
        ) else {
            panic!(
                "{}:{lineno}: malformed manifest line: {line:?}",
                path.display(),
            );
        };
        out.insert(
            PathBuf::from(path_str),
            Fingerprint {
                source: source.to_string(),
                tokens: tokens.to_string(),
                nodes: nodes.to_string(),
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
            "{}\t{}\t{}\t{}",
            rel.to_string_lossy(),
            fp.source,
            fp.tokens,
            fp.nodes,
        );
    }
    std::fs::write(&path, out).expect("write manifest");
    eprintln!("wrote {} entries to {}", manifest.len(), path.display());
}

/// The baseline test.
///
/// Modes (mirrors `corpus_baseline.rs`):
///
/// - **Default**: compare against the committed manifest. Token or
///   node drift on an unchanged-source file fails. A corpus smaller
///   than `MIN_FULL_CORPUS_SIZE` is skipped (warn).
/// - `BASELINE_UPDATE=1`: regenerate the manifest from current output.
/// - `STRICT_BASELINE=1`: turn the corpus-too-small skip into a hard
///   failure, AND escalate two in-tree-fixture conditions into drift:
///   (a) in-tree fixture present without a manifest entry; (b) in-
///   tree fixture with edited source whose manifest entry was not
///   regenerated. Downloaded-corpus equivalents stay warn-only (race
///   with upstream pushes is not the PR author's fault).
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

    let mut token_drift: Vec<(PathBuf, String, String)> = Vec::new();
    let mut node_drift: Vec<(PathBuf, String, String)> = Vec::new();
    let mut source_drift: Vec<PathBuf> = Vec::new();
    let mut round_trip_failures: Vec<PathBuf> = Vec::new();
    let mut missing_from_corpus: Vec<PathBuf> = Vec::new();
    let mut missing_from_manifest: Vec<PathBuf> = Vec::new();

    for (path, expected) in &committed {
        match current.get(path) {
            None => missing_from_corpus.push(path.clone()),
            Some(c) if c.source != expected.source => source_drift.push(path.clone()),
            Some(c) if c.tokens == "round-trip-failure" => {
                round_trip_failures.push(path.clone());
            }
            Some(c) => {
                if c.tokens != expected.tokens {
                    token_drift.push((path.clone(), expected.tokens.clone(), c.tokens.clone()));
                }
                if c.nodes != expected.nodes {
                    node_drift.push((path.clone(), expected.nodes.clone(), c.nodes.clone()));
                }
            }
        }
    }
    for path in current.keys() {
        if !committed.contains_key(path) {
            missing_from_manifest.push(path.clone());
        }
    }

    // Mirror corpus_baseline.rs: only ESCALATE in-tree-fixture problems
    // to strict-mode failure. Downloaded-corpus appearances are subject
    // to upstream race; an unmanifested-or-edited downloaded fixture
    // shouldn't fail CI on PRs that don't touch it. But edits under
    // `tests/compatibility/files/plugins/` ARE PR-author actions
    // (committed in-tree), and a missing manifest entry or source
    // drift there means the contributor forgot to regenerate
    // — exactly the silent-manifest-desync class of bug strict mode
    // exists to catch.
    let unmanifested_in_tree: Vec<&PathBuf> = missing_from_manifest
        .iter()
        .filter(|p| is_in_tree_fixture(p))
        .collect();
    let source_drift_in_tree: Vec<&PathBuf> = source_drift
        .iter()
        .filter(|p| is_in_tree_fixture(p))
        .collect();
    let unprotected_in_strict =
        strict && (!unmanifested_in_tree.is_empty() || !source_drift_in_tree.is_empty());

    if token_drift.is_empty()
        && node_drift.is_empty()
        && round_trip_failures.is_empty()
        && !unprotected_in_strict
    {
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
    if !token_drift.is_empty() {
        use std::fmt::Write;
        let _ = writeln!(
            &mut report,
            "Token-sequence drift on {} file(s) with unchanged source (first 10):",
            token_drift.len(),
        );
        for (path, expected, current) in token_drift.iter().take(10) {
            let _ = writeln!(
                &mut report,
                "  {}\n    expected: {}\n    current:  {}",
                path.display(),
                &expected[..16.min(expected.len())],
                &current[..16.min(current.len())],
            );
        }
    }
    if !node_drift.is_empty() {
        use std::fmt::Write;
        let _ = writeln!(
            &mut report,
            "Node-shape drift on {} file(s) with unchanged source (first 10):",
            node_drift.len(),
        );
        for (path, expected, current) in node_drift.iter().take(10) {
            let _ = writeln!(
                &mut report,
                "  {}\n    expected: {}\n    current:  {}",
                path.display(),
                &expected[..16.min(expected.len())],
                &current[..16.min(current.len())],
            );
        }
    }
    if strict && !unmanifested_in_tree.is_empty() {
        use std::fmt::Write;
        let _ = writeln!(
            &mut report,
            "\n{} in-tree fixture(s) have no manifest entry (first 10):",
            unmanifested_in_tree.len(),
        );
        for path in unmanifested_in_tree.iter().take(10) {
            let _ = writeln!(&mut report, "  {}", path.display());
        }
    }
    if strict && !source_drift_in_tree.is_empty() {
        use std::fmt::Write;
        let _ = writeln!(
            &mut report,
            "\n{} in-tree fixture(s) have edited source without a manifest regen (first 10):",
            source_drift_in_tree.len(),
        );
        for path in source_drift_in_tree.iter().take(10) {
            let _ = writeln!(&mut report, "  {}", path.display());
        }
    }
    panic!(
        "CST baseline drift:\n\n{report}\nIf this drift is intentional, \
         regenerate:\n  BASELINE_UPDATE=1 cargo test -p rustledger-parser \
         --test cst_baseline\n\nReview the diff against `{MANIFEST_PATH}` \
         and commit.",
    );
}
