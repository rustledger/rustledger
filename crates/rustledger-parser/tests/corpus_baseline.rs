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
//! - File on disk but absent from manifest: warn in default mode,
//!   fail in strict mode (new fixture without regen).
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
//! `ParseResult` fields are `Vec<_>` with no map payloads inside
//! (verified across `Options`, `Include`, `Plugin`, `Comment`,
//! `ParseError`, `ParseWarning`, `currency_occurrences`) and use
//! `Debug` directly.
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
//! ## In-tree vs downloaded corpus
//!
//! The corpus under `tests/compatibility/files/` is mostly downloaded
//! by `scripts/fetch-compat-test-files.sh` and not checked in. The
//! repo commits 3 in-tree `plugins/` fixtures regardless. To avoid
//! dev-loop friction, the test treats anything with fewer than
//! [`MIN_FULL_CORPUS_SIZE`] files as "not the full corpus" and skips
//! drift checks; CI sets `STRICT_BASELINE=1` to make this a hard
//! failure.

use std::collections::BTreeMap;
use std::panic::AssertUnwindSafe;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// Relative path to the corpus root from the repo root.
const CORPUS_ROOT: &str = "tests/compatibility/files";

/// Relative path to the committed manifest from the repo root.
const MANIFEST_PATH: &str = "tests/baselines/parser-corpus.manifest";

/// Minimum corpus size we consider "fully populated." Below this,
/// the test treats the corpus as not-downloaded and either skips
/// (default mode) or fails (`STRICT_BASELINE=1`). 100 matches the
/// CI workflow's sanity threshold; values below mean
/// `fetch-compat-test-files.sh` either wasn't run or partially
/// failed.
const MIN_FULL_CORPUS_SIZE: usize = 100;

/// Per-file fingerprint: source-content hash plus parser-output hash.
/// The source hash lets the gate distinguish "upstream pushed a new
/// version of this corpus file" from "the parser's output changed."
#[derive(Debug, Clone, PartialEq, Eq)]
struct FileFingerprint {
    source: String,
    parser: String,
}

fn repo_root() -> &'static Path {
    static ROOT: OnceLock<PathBuf> = OnceLock::new();
    ROOT.get_or_init(|| {
        // Walk up from CARGO_MANIFEST_DIR until we find a directory
        // containing BOTH `tests/compatibility/files` AND a top-level
        // `Cargo.toml` that declares a workspace. The two-condition
        // anchor avoids halting at a coincidentally-named parent
        // directory (e.g., a sibling clone organizing fixtures the
        // same way).
        let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        loop {
            if p.join("tests/compatibility/files").is_dir() && has_workspace_table(&p) {
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

/// Return true if `dir/Cargo.toml` declares a `[workspace]` table
/// at top-of-line. A substring check is too loose: a comment like
/// `# inherits parent [workspace]` or a string literal like
/// `description = "helper for [workspace] testing"` would false-
/// positive. This matches `[workspace]` only when it's the leading
/// non-whitespace text on its line, which is how TOML headers look.
/// Returns true if `rel` is an in-tree fixture (committed under
/// `tests/compatibility/files/plugins/` per the `.gitignore`
/// exception), false if it came from `fetch-compat-test-files.sh`.
///
/// The strict-mode gate uses this to distinguish "the contributor
/// added a fixture and forgot to regenerate" (which we DO want to
/// catch) from "upstream pushed a new file between the regen and
/// CI's fetch" (which we DON'T want to gate on, because the corpus
/// race is outside the PR author's control).
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

/// Walk `CORPUS_ROOT` for every `.beancount` file. Returns paths
/// relative to the repo root, sorted lexically so the output is
/// deterministic.
///
/// Cached behind a `OnceLock` because the test invokes discovery
/// from both `compute_manifest` and the small-corpus guard, and a
/// re-walk of ~700 nested entries is a measurable chunk of the
/// strict-mode CI run on a slow runner.
fn discover_corpus_files() -> &'static [PathBuf] {
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
                .expect("corpus paths are under repo_root")
                .to_path_buf();
            out.push(rel);
        }
    }
}

/// Parse `path` (absolute) and return a stable hash of the
/// `ParseResult` content. Read errors, non-UTF-8 content, and parser
/// panics are encoded as distinct sentinel hashes so any of them
/// becoming or ceasing to occur shows up as a manifest delta on
/// exactly that file (not as a missing entry).
///
/// Hash inputs:
/// - Directives serialized via `serde_json::to_value` (whose `Map`
///   sorts keys via `BTreeMap`, so the `Metadata` `FxHashMap` cannot
///   leak its iteration order into the hash).
/// - Other `ParseResult` fields (`options`, `includes`, `plugins`,
///   `comments`, `errors`, `warnings`, `currency_occurrences`)
///   formatted with `Debug` — they're all `Vec<_>` with no map
///   payloads inside, so `Debug` is deterministic for them.
fn fingerprint(absolute_path: &Path) -> FileFingerprint {
    let source = match std::fs::read_to_string(absolute_path) {
        Ok(s) => s,
        Err(e) => {
            // Read error: both hashes encode the failure kind. Same
            // semantics as a real hash but tagged so the manifest
            // line is self-describing in CI logs.
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
    let mut hasher = blake3::Hasher::new();
    // Directives route through serde_json::Value (BTreeMap-backed
    // for objects), neutralizing FxHashMap iteration order in
    // `Directive.meta` / `Posting.meta`.
    let directives_json = serde_json::to_value(&result.directives)
        .map_or_else(|e| format!("serialize-error:{e}"), |v| v.to_string());
    hasher.update(b"directives:");
    hasher.update(directives_json.as_bytes());
    // Remaining fields are Vec-of-leaf-types with no map payloads
    // inside; Debug is deterministic.
    hasher.update(b"\noptions:");
    hasher.update(format!("{:?}", &result.options).as_bytes());
    hasher.update(b"\nincludes:");
    hasher.update(format!("{:?}", &result.includes).as_bytes());
    hasher.update(b"\nplugins:");
    hasher.update(format!("{:?}", &result.plugins).as_bytes());
    hasher.update(b"\ncomments:");
    hasher.update(format!("{:?}", &result.comments).as_bytes());
    hasher.update(b"\nerrors:");
    hasher.update(format!("{:?}", &result.errors).as_bytes());
    hasher.update(b"\nwarnings:");
    hasher.update(format!("{:?}", &result.warnings).as_bytes());
    hasher.update(b"\ncurrency_occurrences:");
    hasher.update(format!("{:?}", &result.currency_occurrences).as_bytes());
    let parser_hash = hasher.finalize().to_hex().to_string();
    FileFingerprint {
        source: source_hash,
        parser: parser_hash,
    }
}

/// Distill a panic payload to a stable hex string.
///
/// Handles three cases:
/// - `&'static str` and `String` payloads: hash the message text.
///   Most parser panics today carry one of these.
/// - Anything else (`panic_any(MyError)`, `anyhow::Error`, custom
///   panic hooks): tag the hash with the payload's `TypeId` so two
///   structurally different non-string panics produce different
///   sentinels. Without this, all non-string panics collapsed into
///   one sentinel hash and a regression that fixed one of two
///   panic sites would not surface as drift.
///
/// We deliberately don't include line numbers or backtrace text:
/// the goal is "this file's parse behavior changed," not "incidental
/// position info encoded into a hash."
fn panic_payload_hash(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        return blake3::hash(s.as_bytes()).to_hex().to_string();
    }
    if let Some(s) = payload.downcast_ref::<String>() {
        return blake3::hash(s.as_bytes()).to_hex().to_string();
    }
    let mut h = blake3::Hasher::new();
    h.update(b"non-string-panic:");
    // TypeId's Debug renders an opaque but stable identifier; that's
    // sufficient to distinguish two distinct payload types within a
    // single binary. The identifier is NOT stable across rustc
    // versions, so a toolchain bump could shift these hashes; that
    // matches Debug's behavior on the rest of the result.
    h.update(format!("{:?}", payload.type_id()).as_bytes());
    h.finalize().to_hex().to_string()
}

fn compute_manifest() -> BTreeMap<PathBuf, FileFingerprint> {
    let root = repo_root();
    discover_corpus_files()
        .iter()
        .map(|rel| (rel.clone(), fingerprint(&root.join(rel))))
        .collect()
}

fn read_committed_manifest() -> BTreeMap<PathBuf, FileFingerprint> {
    let path = repo_root().join(MANIFEST_PATH);
    let contents = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => String::new(),
        // Any other error (permissions, I/O) must NOT be swallowed:
        // a manifest that's present-but-unreadable would silently
        // disable the gate. Treat as a test infrastructure bug.
        Err(e) => panic!("failed to read {}: {e}", path.display()),
    };
    let mut out = BTreeMap::new();
    for (lineno, line) in contents.lines().enumerate() {
        let lineno = lineno + 1;
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        // path<TAB>source<TAB>parser
        let mut parts = line.split('\t');
        let (Some(path_str), Some(source), Some(parser), None) =
            (parts.next(), parts.next(), parts.next(), parts.next())
        else {
            // Malformed line is a manifest corruption, not something
            // to silently skip. A missing tab or extra column means
            // the manifest format drifted and the gate would lose
            // coverage on the affected lines.
            panic!(
                "{}:{lineno}: malformed manifest line (expected \
                 `path<TAB>source<TAB>parser`): {line:?}",
                path.display(),
            );
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
    out.push_str(
        "# Parser-output baseline. See crates/rustledger-parser/tests/corpus_baseline.rs.\n",
    );
    out.push_str("# Format: path<TAB>source_hash<TAB>parser_output_hash\n");
    out.push_str(
        "# Regenerate: BASELINE_UPDATE=1 cargo test -p rustledger-parser --test corpus_baseline\n",
    );
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

/// The baseline test.
///
/// Modes:
/// - **Default** (no env var): compare current output against the
///   committed manifest. Mismatch fails. A corpus smaller than
///   [`MIN_FULL_CORPUS_SIZE`] files is treated as not-fully-populated
///   and skipped (the in-tree fixtures alone are 3 files and are
///   committed, so "empty" never really happens; the min-size check
///   is what makes the skip actually fire).
/// - `BASELINE_UPDATE=1`: regenerate the manifest. Use deliberately.
/// - `STRICT_BASELINE=1`: turn skip-on-small-corpus into a hard
///   failure, and additionally fail if any file present in the
///   corpus has no entry in the manifest (catches "added a fixture
///   but forgot to regen"). Used by CI.
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

    if current.len() < MIN_FULL_CORPUS_SIZE {
        assert!(
            !strict,
            "STRICT_BASELINE: current corpus has {} files (need at \
             least {MIN_FULL_CORPUS_SIZE}). Did \
             `fetch-compat-test-files.sh` run?",
            current.len(),
        );
        eprintln!(
            "corpus at `{CORPUS_ROOT}` has only {} files (need at least \
             {}). Run `./scripts/fetch-compat-test-files.sh` to populate \
             it; skipping baseline check. CI uses STRICT_BASELINE=1 \
             to make this a hard failure.",
            current.len(),
            MIN_FULL_CORPUS_SIZE,
        );
        return;
    }

    // Source-aware drift classification. See module rustdoc.
    //
    // parser_drift: source matches but parser output differs.
    // This is the only "real" drift signal.
    let mut parser_drift: Vec<(&PathBuf, &str, &str)> = Vec::new();
    // source_drift: corpus content changed upstream. We don't gate
    // on this because it's outside the PR author's control; just
    // warn that the manifest is now partially stale.
    let mut source_drift: Vec<&PathBuf> = Vec::new();
    // Missing-from-corpus: file in manifest but no longer on disk.
    let mut missing_from_corpus: Vec<&PathBuf> = Vec::new();
    // Missing-from-manifest: file on disk but no manifest entry.
    // Strict mode treats this as drift (new fixture without regen).
    let mut missing_from_manifest: Vec<&PathBuf> = Vec::new();

    for (path, expected) in &committed {
        match current.get(path) {
            None => missing_from_corpus.push(path),
            Some(current_fp) if current_fp.source != expected.source => {
                source_drift.push(path);
            }
            Some(current_fp) if current_fp.parser != expected.parser => {
                parser_drift.push((path, expected.parser.as_str(), current_fp.parser.as_str()));
            }
            Some(_) => {}
        }
    }
    for path in current.keys() {
        if !committed.contains_key(path) {
            missing_from_manifest.push(path);
        }
    }

    // Files added upstream (downloaded by fetch-compat-test-files.sh)
    // appear and disappear with that script's race against upstream
    // pushes; we don't gate on those. Only escalate missing-from-
    // manifest to a strict failure for in-tree paths (under `plugins/`
    // per the .gitignore exception), where appearance means a real
    // contributor added a fixture and forgot to regenerate.
    let unmanifested_in_tree: Vec<&PathBuf> = missing_from_manifest
        .iter()
        .filter(|p| is_in_tree_fixture(p))
        .copied()
        .collect();
    let unprotected_in_strict = strict && !unmanifested_in_tree.is_empty();
    if parser_drift.is_empty() && !unprotected_in_strict {
        if !source_drift.is_empty() {
            eprintln!(
                "info: {} corpus file(s) have new upstream content \
                 (source hash changed). Parser output on those files \
                 was NOT checked against the manifest because they're \
                 different inputs. Regenerate when convenient:\n  \
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
    if unprotected_in_strict {
        report.push_str(&format!(
            "\n{} in-tree fixture(s) have no manifest entry (first 10):\n",
            unmanifested_in_tree.len(),
        ));
        for path in unmanifested_in_tree.iter().take(10) {
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

/// Sanity check: discovery must find at least the in-tree
/// `plugins/` fixtures. If this fails the corpus path resolution is
/// wrong and every other test in this file is silently no-op.
#[test]
fn discovery_finds_in_tree_plugin_fixtures() {
    let files = discover_corpus_files();
    let has_plugin_fixture = files
        .iter()
        .any(|p| p.to_string_lossy().contains("plugins/implicit_prices"));
    assert!(
        has_plugin_fixture,
        "expected to find at least one in-tree fixture under \
         tests/compatibility/files/plugins/implicit_prices/; got \
         {} corpus files total. Check CORPUS_ROOT resolution.",
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
