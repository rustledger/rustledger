//! Document discovery follows symlinked subtrees, as beancount does.
//!
//! Regression tests for #1997. Discovery used `symlink_metadata` and skipped
//! every symlink outright, so a linked subtree was never visited — not walked
//! and filtered, but never reached. An entire document tree could be absent
//! with no error, no warning, and nothing to distinguish it from an empty
//! folder.
//!
//! Beancount follows them: `beancount/ops/documents.py` walks with
//! `account.walk(directory)`, and that function's signature is
//! `walk(root_directory, followlinks: bool = True)`.
//!
//! The issue was reported for Windows directory junctions, and the mechanism
//! there is a real asymmetry — Rust's `FileType::is_symlink` is true for
//! name-surrogate reparse points while Python's `os.path.islink` is false for
//! them, so a junction is where the two disagree even under `followlinks=False`.
//! But `followlinks` defaults to `True`, so the divergence is not
//! Windows-specific: it covers ordinary POSIX symlinks, which is what these
//! tests use. Measured against beancount on Linux before the fix — beancount
//! found 2 documents in `symlinked_subtree_is_discovered`'s shape, rledger
//! found 1.
//!
//! Unix-gated because creating a symlink on Windows needs elevation or
//! Developer Mode. The Windows manifestation is a junction, which needs
//! neither, but is not creatable from `std`.
#![cfg(unix)]

use rustledger_loader::{LoadOptions, load};
use std::os::unix::fs::symlink;
use std::path::Path;

/// Build a ledger dir with `option "documents" "docs"` and the given open
/// accounts, returning the tempdir.
fn fixture(opens: &[&str]) -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    std::fs::create_dir_all(dir.path().join("docs")).unwrap();
    let mut open_lines = String::new();
    for account in opens {
        open_lines.push_str("2020-01-01 open ");
        open_lines.push_str(account);
        open_lines.push('\n');
    }
    std::fs::write(
        dir.path().join("ledger.bean"),
        format!("option \"documents\" \"docs\"\n\n{open_lines}"),
    )
    .unwrap();
    dir
}

fn touch(path: &Path) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, "dummy").unwrap();
}

/// Discovered documents, as `(account, filename)`, sorted.
fn discovered(dir: &tempfile::TempDir) -> Vec<(String, String)> {
    let ledger =
        load(&dir.path().join("ledger.bean"), &LoadOptions::default()).expect("ledger loads");
    let mut found: Vec<(String, String)> = ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            rustledger_core::Directive::Document(doc) => {
                Some((doc.account.as_ref().to_string(), doc.path.clone()))
            }
            _ => None,
        })
        .collect();
    found.sort();
    found
}

fn warnings(dir: &tempfile::TempDir) -> Vec<String> {
    let ledger =
        load(&dir.path().join("ledger.bean"), &LoadOptions::default()).expect("ledger loads");
    ledger.errors.iter().map(|e| e.message.clone()).collect()
}

/// The #1997 bug: a subtree reached through a symlink must be walked.
#[test]
fn symlinked_subtree_is_discovered() {
    let dir = fixture(&["Expenses:Direct", "Expenses:Bar"]);
    touch(
        &dir.path()
            .join("docs/Expenses/Direct/2026-07-07 control.pdf"),
    );

    // The linked-to tree lives outside `docs/`, which is the real shape: a
    // document library that cannot share a root with the ledger.
    touch(&dir.path().join("library/2026-07-07 behind.pdf"));
    symlink(
        dir.path().join("library"),
        dir.path().join("docs/Expenses/Bar"),
    )
    .unwrap();

    let found = discovered(&dir);
    assert_eq!(
        found.len(),
        2,
        "the linked subtree must be walked, not skipped: {found:?}"
    );
    assert!(
        found.iter().any(|(account, _)| account == "Expenses:Bar"),
        "expected a document under Expenses:Bar: {found:?}"
    );
}

/// A skipped subtree used to be indistinguishable from an empty one. An
/// unopened account under the link proves the walk actually entered it.
#[test]
fn a_walked_subtree_reports_its_unopened_accounts() {
    let dir = fixture(&["Expenses:Direct"]);
    touch(
        &dir.path()
            .join("docs/Expenses/Direct/2026-07-07 control.pdf"),
    );
    touch(&dir.path().join("library/2026-07-07 other.pdf"));
    // `Expenses:Nope` is deliberately not opened.
    symlink(
        dir.path().join("library"),
        dir.path().join("docs/Expenses/Nope"),
    )
    .unwrap();

    assert!(
        warnings(&dir)
            .iter()
            .any(|w| w.contains("Expenses:Nope") && w.contains("unknown account")),
        "walking the link should surface its unopened account, got: {:?}",
        warnings(&dir)
    );
}

/// Two accounts may link to the same physical folder, and beancount emits one
/// document per account. This is why the cycle guard tracks the ancestor chain
/// rather than a global visited-set: a set also terminates, but would walk
/// whichever link came first and silently drop the other.
#[test]
fn two_links_to_the_same_target_are_both_discovered() {
    let dir = fixture(&["Expenses:Alpha", "Expenses:Beta"]);
    std::fs::create_dir_all(dir.path().join("docs/Expenses")).unwrap();
    touch(&dir.path().join("shared/2026-07-07 shared.pdf"));
    symlink(
        dir.path().join("shared"),
        dir.path().join("docs/Expenses/Alpha"),
    )
    .unwrap();
    symlink(
        dir.path().join("shared"),
        dir.path().join("docs/Expenses/Beta"),
    )
    .unwrap();

    let accounts: Vec<String> = discovered(&dir).into_iter().map(|(a, _)| a).collect();
    assert_eq!(
        accounts,
        vec!["Expenses:Alpha".to_string(), "Expenses:Beta".to_string()],
        "the same folder reached by two links belongs to both accounts"
    );
}

/// A cycle must terminate and say so. Beancount's `os.walk(followlinks=True)`
/// has no cycle guard and hangs on this shape (verified: it did not finish in
/// 45s), so this is deliberately stricter than the behavior it matches.
#[test]
fn symlink_cycle_terminates_and_warns() {
    let dir = fixture(&["Expenses:Deep"]);
    touch(&dir.path().join("docs/Expenses/Deep/2026-07-07 real.pdf"));
    // Points back at the documents root, and at its own parent.
    symlink(
        dir.path().join("docs"),
        dir.path().join("docs/Expenses/Loop"),
    )
    .unwrap();
    symlink(
        dir.path().join("docs/Expenses"),
        dir.path().join("docs/Expenses/Self"),
    )
    .unwrap();

    // Reaching this line at all is most of the assertion: before the guard,
    // this recurses until the depth cap and does 32 redundant walks; without
    // any guard it does not return.
    let found = discovered(&dir);
    assert_eq!(
        found.len(),
        1,
        "the real document, discovered exactly once: {found:?}"
    );

    let warns = warnings(&dir);
    assert!(
        warns
            .iter()
            .any(|w| w.contains("links back into a directory")),
        "a skipped cycle must not be silent, got: {warns:?}"
    );
}

/// A dangling link is skipped, not an error: a walk that cannot enter it does
/// the same thing.
#[test]
fn dangling_symlink_is_skipped() {
    let dir = fixture(&["Expenses:Direct"]);
    touch(
        &dir.path()
            .join("docs/Expenses/Direct/2026-07-07 control.pdf"),
    );
    symlink(
        dir.path().join("nowhere"),
        dir.path().join("docs/Expenses/Broken"),
    )
    .unwrap();

    assert_eq!(discovered(&dir).len(), 1);
}
