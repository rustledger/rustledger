//! Shared scaffolding for the parser-output and formatter-output
//! corpus baselines (#1262 phase 0).
//!
//! Each baseline binary (`corpus_baseline.rs`,
//! `corpus_baseline_format.rs`) carries:
//!
//! - its own `MANIFEST_PATH`
//! - its own `fingerprint()` closure (parser vs formatter)
//! - its own drift-classification rules (the formatter has a
//!   `became_empty` case the parser doesn't)
//!
//! Everything else lives here. Without this module, both files
//! duplicated ~150 lines: the `FileFingerprint` struct, repo-root
//! resolution, corpus discovery, panic-payload hashing, manifest
//! read/write/render, and the in-tree fixture prefix. A future fix
//! that needs to land in both (e.g., the next round-1-review BOM-
//! flag-style omission) had two places to update; one missed
//! update would silently desync the two baselines.

#![allow(dead_code)]
// Each binary uses a different subset of the shared API. `dead_code`
// is silenced here because Cargo compiles each `tests/*.rs` binary
// independently, so any code one binary doesn't reference looks dead
// from that binary's perspective even though the other binary uses it.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// Relative path to the corpus root from the repo root.
pub const CORPUS_ROOT: &str = "tests/compatibility/files";

/// Minimum corpus size we consider "fully populated." Below this,
/// the test treats the corpus as not-downloaded and either skips
/// (default mode) or fails (`STRICT_BASELINE=1`). 100 matches the
/// CI workflow's sanity threshold; values below mean
/// `fetch-compat-test-files.sh` either wasn't run or partially
/// failed.
pub const MIN_FULL_CORPUS_SIZE: usize = 100;

/// Prefix of in-tree corpus fixtures (committed under
/// `tests/compatibility/files/plugins/` per the `.gitignore`
/// exception, see `tests/compatibility/files/.gitignore`). Single
/// source of truth: if you rename the in-tree directory, update this
/// const AND verify the `.gitignore` exception still matches.
pub const IN_TREE_FIXTURE_PREFIX: &str = "tests/compatibility/files/plugins/";

/// Per-file fingerprint: source-content hash plus output hash.
/// The source hash lets the gate distinguish "upstream pushed a new
/// version of this corpus file" from "the parser or formatter
/// changed." See the module rustdocs of `corpus_baseline.rs` and
/// `corpus_baseline_format.rs` for the policy that consumes these.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileFingerprint {
    pub source: String,
    /// Naming holdover: this field carries the parser-output hash in
    /// `corpus_baseline.rs` and the formatter-output hash in
    /// `corpus_baseline_format.rs`. The render layer labels it
    /// appropriately per binary; the struct stays generic.
    pub parser: String,
}

/// Locate the repo root by walking up from `CARGO_MANIFEST_DIR`.
/// Anchored on the corpus directory AND a top-of-line `[workspace]`
/// in a sibling `Cargo.toml`, so a coincidentally-named ancestor
/// directory cannot misanchor the walk.
pub fn repo_root() -> &'static Path {
    static ROOT: OnceLock<PathBuf> = OnceLock::new();
    ROOT.get_or_init(|| {
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

/// Return true iff `dir/Cargo.toml` declares a `[workspace]` table
/// at top-of-line. A substring check is too loose: a comment like
/// `# inherits parent [workspace]` or a string literal like
/// `description = "helper for [workspace] testing"` would false-
/// positive. This matches `[workspace]` only when it's the leading
/// non-whitespace text on its line, which is how TOML headers look.
pub fn has_workspace_table(dir: &Path) -> bool {
    let Ok(toml) = std::fs::read_to_string(dir.join("Cargo.toml")) else {
        return false;
    };
    toml.lines()
        .any(|line| line.trim_start().starts_with("[workspace]"))
}

/// Walk `CORPUS_ROOT` for every `.beancount` file. Returns paths
/// relative to the repo root, sorted lexically so the output is
/// deterministic. Cached: the per-binary callers invoke this from
/// both `compute_manifest` and the small-corpus guard.
pub fn discover_corpus_files() -> &'static [PathBuf] {
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
    // Panic on read errors instead of swallowing. A silently-skipped
    // subdirectory (stale NFS handle, permission glitch, broken
    // symlink) would shrink the discovered corpus under the workflow's
    // slack=50 floor and let strict-mode CI pass on a degraded run.
    // For a test binary, a hard failure surfaces the FS issue
    // immediately; the alternative (`entries.flatten()`) drops per-
    // entry errors with no diagnostic.
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
                .expect("corpus paths are under repo_root")
                .to_path_buf();
            out.push(rel);
        }
    }
}

/// Returns true if `rel` is an in-tree fixture (committed per the
/// `.gitignore` exception), false if it came from
/// `fetch-compat-test-files.sh`. The strict-mode gate uses this to
/// distinguish "the contributor added a fixture and forgot to
/// regenerate" (which we DO want to catch) from "upstream pushed a
/// new file between the regen and CI's fetch" (which we DON'T want
/// to gate on, because the corpus race is outside the PR author's
/// control).
pub fn is_in_tree_fixture(rel: &Path) -> bool {
    rel.starts_with(IN_TREE_FIXTURE_PREFIX)
}

/// Reject corpus paths the manifest serializer cannot represent.
/// The manifest format is one entry per line, `path<TAB>...<TAB>...`,
/// so a path containing a tab corrupts the round trip; a path
/// containing `\n` or `\r` would split into multiple lines on read
/// (with the first fragment surfacing a confusing "malformed manifest
/// line" panic that hides the real cause); a path starting with `#`
/// is misread as a comment. Today the corpus contains none of these,
/// but rejecting up front beats writing a manifest the strict reader
/// will panic on far from where the bad name was introduced.
pub fn validate_path(rel: &Path) {
    let s = rel.to_string_lossy();
    assert!(
        !s.contains('\t'),
        "corpus path contains a TAB character, which the manifest \
         serializer cannot represent: {}",
        rel.display(),
    );
    assert!(
        !s.contains('\n'),
        "corpus path contains a newline, which would split the \
         manifest entry across lines: {}",
        rel.display(),
    );
    assert!(
        !s.contains('\r'),
        "corpus path contains a carriage return, which would corrupt \
         the line-oriented manifest format: {}",
        rel.display(),
    );
    assert!(
        !s.starts_with('#'),
        "corpus path starts with `#`, which the manifest reader would \
         treat as a comment: {}",
        rel.display(),
    );
}

/// Distill a panic payload to a stable hex string.
///
/// Handles three cases:
/// - `&'static str` and `String` payloads: hash the message text.
///   Most parser panics today carry one of these.
/// - Anything else (`panic_any(MyError)`, `anyhow::Error`, custom
///   panic hooks): tag the hash with the payload's `TypeId`. Two
///   panics of DIFFERENT types produce different sentinels; two
///   panics of the SAME non-string type (e.g.,
///   `panic_any(MyErr { msg: "a" })` vs `panic_any(MyErr { msg:
///   "b" })`) currently collapse to one hash because `Any` exposes
///   no payload-state introspection. Today no parser path uses
///   `panic_any`, so this is latent. If a future panic site uses a
///   structured payload, the panic-site author should hash its
///   Debug representation explicitly.
///
/// We deliberately don't include line numbers or backtrace text:
/// the goal is "this file's parse behavior changed," not "incidental
/// position info encoded into a hash."
pub fn panic_payload_hash(payload: &(dyn std::any::Any + Send)) -> String {
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

/// Read a committed manifest at `manifest_path` (absolute) into a
/// `BTreeMap`. `NotFound` is treated as no-committed-manifest; any
/// other read error panics (a manifest-present-but-unreadable
/// condition would silently disable the gate). Malformed lines
/// (missing tab, extra column) panic with the line number.
pub fn read_committed_manifest(manifest_path: &Path) -> BTreeMap<PathBuf, FileFingerprint> {
    let contents = match std::fs::read_to_string(manifest_path) {
        Ok(s) => s,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => String::new(),
        Err(e) => panic!("failed to read {}: {e}", manifest_path.display()),
    };
    let mut out = BTreeMap::new();
    for (lineno, line) in contents.lines().enumerate() {
        let lineno = lineno + 1;
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        // path<TAB>source<TAB>parser, NO trailing column
        let mut parts = line.split('\t');
        let (Some(path_str), Some(source), Some(parser), None) =
            (parts.next(), parts.next(), parts.next(), parts.next())
        else {
            panic!(
                "{}:{lineno}: malformed manifest line (expected \
                 `path<TAB>source<TAB>parser`): {line:?}",
                manifest_path.display(),
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

/// Render a manifest to its on-disk text. `header_lines` is a list
/// of leading `#`-prefixed comment lines, written verbatim.
pub fn render_manifest(
    manifest: &BTreeMap<PathBuf, FileFingerprint>,
    header_lines: &[&str],
) -> String {
    let mut out = String::new();
    for line in header_lines {
        out.push_str(line);
        out.push('\n');
    }
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

/// Write a manifest to `manifest_path` (absolute), creating parent
/// directories as needed. Used only in `BASELINE_UPDATE=1` mode.
pub fn write_manifest(
    manifest_path: &Path,
    manifest: &BTreeMap<PathBuf, FileFingerprint>,
    header_lines: &[&str],
) {
    if let Some(parent) = manifest_path.parent() {
        std::fs::create_dir_all(parent).expect("create baseline dir");
    }
    std::fs::write(manifest_path, render_manifest(manifest, header_lines)).expect("write manifest");
    eprintln!(
        "wrote {} entries to {}",
        manifest.len(),
        manifest_path.display(),
    );
}

/// Build the on-disk manifest by walking the corpus and calling
/// `fingerprint_fn` for each file. The fingerprinter returns `None`
/// for files that should be excluded from the manifest entirely
/// (e.g., the format baseline's "no formattable content at all"
/// case — files with no directives, options, includes, plugins, or
/// comments).
pub fn compute_manifest<F>(fingerprint_fn: F) -> BTreeMap<PathBuf, FileFingerprint>
where
    F: Fn(&Path) -> Option<FileFingerprint>,
{
    let root = repo_root();
    discover_corpus_files()
        .iter()
        .filter_map(|rel| {
            validate_path(rel);
            fingerprint_fn(&root.join(rel)).map(|fp| (rel.clone(), fp))
        })
        .collect()
}
