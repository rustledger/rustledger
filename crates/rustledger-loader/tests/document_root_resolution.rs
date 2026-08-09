//! `option "documents"` roots resolve against the ledger file, not the CWD.
//!
//! Regression tests for #1999. `Options::set` used to run the E7006 existence
//! check itself with `Path::new(value).exists()`. Option parsing has no idea
//! where the ledger lives, so that asked about the *process* CWD: a document
//! root sitting right next to the ledger was reported missing whenever `check`
//! was invoked from anywhere else, and the identical ledger passed when the
//! CWD happened to be its own directory. Beancount resolves `documents`
//! relative to the ledger file, as `include` does, and is CWD-independent.
//!
//! These tests never call `set_current_dir` — that is process-global and would
//! race the rest of the suite. Instead they load through an *absolute* path
//! into a tempdir, so the CWD (the crate root, under `cargo test`) is
//! guaranteed not to contain the relative root under test. That is precisely
//! the configuration the old code got wrong.
//!
//! Sabotage-checked — every failure direction was induced and observed:
//!
//! | sabotage | `relative_root` | `missing_root` | `only_in_cwd` | `absolute_root` | `file_where_root` | `virtual_fs` |
//! |---|---|---|---|---|---|---|
//! | reinstate CWD check in `Options::set` | **FAIL** | **FAIL** | pass | **FAIL** | pass | pass |
//! | gut `document_root_warnings` | pass | **FAIL** | **FAIL** | **FAIL** | **FAIL** | pass |
//! | `VirtualFileSystem::dir_exists` → `exists` | pass | pass | pass | pass | pass | **FAIL** |
//! | `DiskFileSystem::dir_exists` → `exists` | pass | pass | pass | pass | **FAIL** | pass |
//!
//! Row 1 is the #1999 regression itself, caught by
//! `relative_root_next_to_ledger_is_found`; it also trips the count assertions
//! because the reinstated check double-warns alongside the canonical one. Row 2
//! is the "did you just delete the feature" direction. Rows 3 and 4 pin the two
//! filesystem-backend answers independently — each is held by exactly one test,
//! so neither can rot behind the other. No column is held only by a test that
//! cannot fail.

use rustledger_loader::Loader;

/// Build a ledger dir containing `ledger.bean` with the given `documents`
/// value, plus whichever subdirectories the caller wants created.
fn fixture(documents: &str, subdirs: &[&str]) -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    for sub in subdirs {
        std::fs::create_dir_all(dir.path().join(sub)).unwrap();
    }
    std::fs::write(
        dir.path().join("ledger.bean"),
        format!("option \"documents\" \"{documents}\"\n\n2020-01-01 open Assets:Cash USD\n"),
    )
    .unwrap();
    dir
}

fn e7006_warnings(dir: &tempfile::TempDir) -> Vec<String> {
    let result = Loader::new()
        .load(&dir.path().join("ledger.bean"))
        .expect("ledger loads");
    result
        .options
        .warnings
        .iter()
        .filter(|w| w.code == "E7006")
        .map(|w| w.message.clone())
        .collect()
}

/// The #1999 bug: a root that exists beside the ledger must not warn, even
/// though it does not exist relative to the CWD we are running from.
#[test]
fn relative_root_next_to_ledger_is_found() {
    let dir = fixture("docs", &["docs"]);
    assert!(
        !std::path::Path::new("docs").exists(),
        "precondition: the test CWD must not contain a `docs` dir, or this \
         test would pass even with the CWD-relative bug reinstated"
    );
    assert_eq!(
        e7006_warnings(&dir),
        Vec::<String>::new(),
        "a `documents` root beside the ledger must resolve, regardless of CWD"
    );
}

/// The check must still be able to fire — a genuinely absent root warns.
#[test]
fn missing_root_still_warns() {
    let dir = fixture("nosuchdir", &[]);
    let warnings = e7006_warnings(&dir);
    assert_eq!(warnings.len(), 1, "expected one E7006, got {warnings:?}");
    assert!(
        warnings[0].contains("nosuchdir")
            && warnings[0].contains(&dir.path().display().to_string()),
        "the warning should name the root and where it resolved to: {}",
        warnings[0]
    );
}

/// The other half of correctness: a root that exists relative to the CWD but
/// not beside the ledger must warn. The old code passed this ledger silently.
#[test]
fn root_present_only_in_cwd_still_warns() {
    // `src` exists in the crate root (our CWD under `cargo test`) but is not
    // created inside the tempdir, so it is CWD-present and ledger-absent.
    assert!(
        std::path::Path::new("src").exists(),
        "precondition: expected to run from the crate root, where `src` exists"
    );
    let dir = fixture("src", &[]);
    let warnings = e7006_warnings(&dir);
    assert_eq!(
        warnings.len(),
        1,
        "a root that only exists in the CWD is not a valid document root: {warnings:?}"
    );
}

/// Absolute roots are unaffected by any of this.
#[test]
fn absolute_root_is_checked_as_given() {
    let present = tempfile::tempdir().unwrap();
    let dir = fixture(&present.path().display().to_string(), &[]);
    assert_eq!(e7006_warnings(&dir), Vec::<String>::new());

    let dir = fixture(&present.path().join("gone").display().to_string(), &[]);
    assert_eq!(e7006_warnings(&dir).len(), 1);
}

/// A regular file is not a document root. The check uses `is_dir`, not
/// `exists`, so a file sitting where the root should be is a warning rather
/// than a false pass.
#[test]
fn file_where_the_root_should_be_warns() {
    let dir = fixture("docs", &[]);
    std::fs::write(dir.path().join("docs"), "not a directory").unwrap();
    assert_eq!(
        e7006_warnings(&dir).len(),
        1,
        "a plain file named `docs` must not satisfy a documents root"
    );
}

/// In-memory loads must not manufacture E7006.
///
/// A [`VirtualFileSystem`] is a flat map of file paths to contents with no
/// directory entries in it, so any host-filesystem probe — or any probe
/// through `FileSystem::exists`, which consults that same file map — reports
/// every document root as missing. The check therefore goes through
/// `dir_exists`, which the virtual backend answers "yes" to because it cannot
/// disprove the root. Without this, every WASM/in-memory load of a ledger
/// carrying `option "documents"` would emit a spurious error.
#[test]
fn virtual_filesystem_load_does_not_warn() {
    let mut vfs = rustledger_loader::VirtualFileSystem::new();
    vfs.add_file(
        "/mem/ledger.bean",
        "option \"documents\" \"docs\"\n\n2020-01-01 open Assets:Cash USD\n",
    );
    let result = Loader::new()
        .with_filesystem(Box::new(vfs))
        .load(std::path::Path::new("/mem/ledger.bean"))
        .expect("in-memory ledger loads");
    let warnings: Vec<_> = result
        .options
        .warnings
        .iter()
        .filter(|w| w.code == "E7006")
        .collect();
    assert!(
        warnings.is_empty(),
        "in-memory load must not warn about document roots it cannot see: {warnings:?}"
    );
}
