//! Shared `.wasm` directory scanner.
//!
//! Both [`crate::PluginManager::register_wasm_dir`] and
//! `rustledger_importer::ImporterRegistry::register_wasm_dir` walk a
//! directory looking for `.wasm` files to register. (The latter isn't
//! an intra-doc link because that crate sits downstream of this one
//! in the dep graph — link from text on the importer side instead.)
//! The two used to
//! be near-copies — same listing, filtering, sorting, and per-entry
//! error handling logic, only the error wrapping and per-file load fn
//! differed. This module factors out the shared listing-and-filtering
//! step.
//!
//! # What's shared
//!
//! - `read_dir` + iteration
//! - `is_file()` + case-insensitive `.wasm` extension filter
//! - Per-entry I/O errors collected (not propagated, so a single
//!   permission-denied inode doesn't abort the scan)
//! - Lexicographic sort by path so load order is deterministic across
//!   filesystems and platforms
//!
//! # What stays caller-side
//!
//! - **Dir-level `read_dir` error wrapping**: each caller has its own
//!   error type and preferred context message ("failed to read plugin
//!   dir ..." vs `WasmImporterError::Io`).
//! - **Per-file load**: the importer calls
//!   `register_wasm_from_path`, the plugin manager calls `load`.
//!   Their return values and error shapes are different (importer
//!   returns the module's declared name; plugin returns an index +
//!   uses the registered Plugin's `name()`).
//!
//! Both kept caller-side because forcing them through a generic
//! adapter would add more code than it saved.

use std::path::{Path, PathBuf};

/// Outcome of [`collect_wasm_paths`].
///
/// `sorted_paths` is what callers iterate to do the actual loading;
/// `entry_failures` carries per-entry I/O errors (broken-during-iter
/// inodes) that callers fold into their own failure-tracking shape.
#[derive(Debug, Default)]
pub struct WasmDirScan {
    /// `.wasm` files found in the directory, sorted lexicographically
    /// by full path. Sorting at this layer means callers don't have
    /// to think about deterministic load order.
    pub sorted_paths: Vec<PathBuf>,
    /// Per-entry I/O errors from the `read_dir` iterator (rare —
    /// permission denied on a single inode, broken symlinks the
    /// dirent-read step caught). Paired with the dir path because
    /// the per-entry `Err` doesn't carry the inode's name.
    pub entry_failures: Vec<(PathBuf, std::io::Error)>,
}

/// Collect `.wasm` files from `dir` (one level, no recursion) and
/// sort them lexicographically.
///
/// Filter rules:
/// - Skips subdirectories (matches `path.is_file()`).
/// - Skips files whose `path.is_file()` returns false for any reason
///   — broken symlinks, transient metadata errors, etc. (`is_file`
///   swallows the underlying I/O error; this is a documented
///   limitation, not a bug.)
/// - Extension matching is case-insensitive: `foo.wasm`, `BAR.WASM`,
///   and `mixed.Wasm` all match.
/// - Per-entry I/O errors (where the `read_dir` iterator itself
///   returns an `Err`) are collected into
///   [`WasmDirScan::entry_failures`] rather than aborting the scan.
///
/// # Errors
///
/// Returns the dir-level `read_dir` error verbatim. Callers wrap it
/// with whatever context they need ("failed to read importer dir ...",
/// `WasmImporterError::Io { path, source }`, etc.).
pub fn collect_wasm_paths(dir: &Path) -> std::io::Result<WasmDirScan> {
    let entries = std::fs::read_dir(dir)?;
    let mut scan = WasmDirScan::default();
    for entry in entries {
        match entry {
            Ok(e) => {
                let path = e.path();
                if path.is_file()
                    && path
                        .extension()
                        .is_some_and(|ext| ext.eq_ignore_ascii_case("wasm"))
                {
                    scan.sorted_paths.push(path);
                }
            }
            Err(source) => {
                // Per-entry I/O error — the `read_dir` iterator's
                // `next()` can return `Err` for a single inode (rare;
                // usually permission denied or a broken symlink)
                // without exposing the entry name. Tag with the dir
                // path so the caller's report is useful for debugging.
                scan.entry_failures.push((dir.to_path_buf(), source));
            }
        }
    }
    scan.sorted_paths.sort();
    Ok(scan)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn touch(path: &Path) {
        std::fs::write(path, b"placeholder").expect("write fixture");
    }

    #[test]
    fn collects_only_top_level_wasm_files_in_sorted_order() {
        let dir = tempfile::tempdir().expect("tempdir");
        let p = dir.path();
        touch(&p.join("b_second.wasm"));
        touch(&p.join("a_first.wasm"));
        touch(&p.join("README.md")); // wrong extension
        touch(&p.join(".gitignore")); // no extension
        // Subdir with a .wasm inside — should NOT be picked up.
        std::fs::create_dir(p.join("sub")).expect("subdir");
        touch(&p.join("sub").join("recursed.wasm"));

        let scan = collect_wasm_paths(p).expect("scan succeeds");
        let names: Vec<_> = scan
            .sorted_paths
            .iter()
            .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        assert_eq!(names, vec!["a_first.wasm", "b_second.wasm"]);
        assert!(scan.entry_failures.is_empty());
    }

    #[test]
    fn extension_match_is_case_insensitive() {
        let dir = tempfile::tempdir().expect("tempdir");
        touch(&dir.path().join("upper.WASM"));
        touch(&dir.path().join("mixed.Wasm"));
        let scan = collect_wasm_paths(dir.path()).expect("scan succeeds");
        assert_eq!(scan.sorted_paths.len(), 2);
    }

    #[test]
    fn missing_dir_propagates_read_dir_error() {
        let dir = tempfile::tempdir().expect("tempdir");
        let nonexistent = dir.path().join("does-not-exist");
        let err = collect_wasm_paths(&nonexistent)
            .expect_err("missing dir should error at the read_dir step, not in entry_failures");
        assert_eq!(err.kind(), std::io::ErrorKind::NotFound);
    }
}
