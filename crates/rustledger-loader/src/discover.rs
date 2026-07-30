//! Finding a ledger's root journal without being told where it is.
//!
//! Both the language server and `rledger format` need this: neither is
//! handed a root, but both must resolve options (`render_commas`,
//! per-commodity declarations) that only exist there. The list of names
//! lives here so the two cannot disagree about what a root looks like —
//! a file the LSP formats one way and the CLI another is precisely the
//! failure this is meant to prevent.

use std::path::{Path, PathBuf};

/// Common root journal filenames, in priority order.
pub const COMMON_ROOT_NAMES: &[&str] = &[
    "main.bean",
    "main.beancount",
    "ledger.bean",
    "ledger.beancount",
    "journal.bean",
    "journal.beancount",
    "index.bean",
    "index.beancount",
];

/// The root journal directly inside `dir`, if one is there.
///
/// Checks [`COMMON_ROOT_NAMES`] in order and returns the first that exists
/// as a file. Does not recurse and does not walk upward — see
/// [`discover_journal_upward`] for that.
#[must_use]
pub fn discover_journal_file(dir: &Path) -> Option<PathBuf> {
    for name in COMMON_ROOT_NAMES {
        let candidate = dir.join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

/// The nearest root journal at or above `start`.
///
/// Walks toward the filesystem root and returns the first directory that
/// holds one. Nearest wins, so a nested sub-ledger with its own root beats
/// an outer one — the same "most specific enclosing scope" rule an editor
/// or a version-control tool uses.
///
/// `start` is a DIRECTORY. Callers with a file path should pass its parent.
#[must_use]
pub fn discover_journal_upward(start: &Path) -> Option<PathBuf> {
    let mut dir = Some(start);
    while let Some(d) = dir {
        if let Some(found) = discover_journal_file(d) {
            return Some(found);
        }
        dir = d.parent();
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finds_a_root_beside_the_file_and_prefers_the_nearest() {
        let dir = tempfile::tempdir().expect("tempdir");
        let outer = dir.path();
        let inner = outer.join("sub/deeper");
        std::fs::create_dir_all(&inner).expect("mkdir");

        std::fs::write(outer.join("main.beancount"), "").expect("write outer");
        assert_eq!(
            discover_journal_upward(&inner),
            Some(outer.join("main.beancount")),
            "walks up when nothing is nearer"
        );

        let nested = outer.join("sub").join("ledger.beancount");
        std::fs::write(&nested, "").expect("write inner");
        assert_eq!(
            discover_journal_upward(&inner),
            Some(nested),
            "a nearer root wins over an outer one"
        );
    }

    #[test]
    fn name_priority_is_stable_and_directories_do_not_count() {
        let dir = tempfile::tempdir().expect("tempdir");
        // A DIRECTORY named like a root must not be mistaken for one.
        std::fs::create_dir(dir.path().join("main.bean")).expect("mkdir");
        assert_eq!(discover_journal_file(dir.path()), None);

        std::fs::write(dir.path().join("journal.beancount"), "").expect("write");
        std::fs::write(dir.path().join("main.beancount"), "").expect("write");
        assert_eq!(
            discover_journal_file(dir.path()),
            Some(dir.path().join("main.beancount")),
            "`main.beancount` outranks `journal.beancount`"
        );
    }

    #[test]
    fn returns_none_when_there_is_no_ledger_anywhere_above() {
        let dir = tempfile::tempdir().expect("tempdir");
        let deep = dir.path().join("a/b/c");
        std::fs::create_dir_all(&deep).expect("mkdir");
        // The walk reaches the filesystem root and stops; tempdirs live
        // under /tmp, which has no journal.
        assert_eq!(discover_journal_upward(&deep), None);
    }
}
