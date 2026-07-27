//! An absolute path that cannot be canonicalized.
//!
//! Two invariants this crate kept re-learning, moved from prose into the type.
//!
//! **Absolute.** A relative path has no `file:` URI, and inventing one resolves
//! it against whatever the process's working directory happens to be. Six tests
//! hard-coded `/home/user/ledger`, which is absolute on Unix and RELATIVE on
//! Windows, and so asserted nothing there — they panicked before reaching their
//! subject.
//!
//! **Never canonicalized.** This is the one worth a type. `canonicalize` reads
//! the filesystem, fails outright for a file that does not exist yet, and
//! resolves symlinks the user may have opened deliberately, so using it to
//! decide "same file" makes identity depend on the disk at that instant. The
//! reasoning was written into a doc comment on `MainLoopState::diagnostics`
//! first; rust-analyzer's equivalent newtype makes its `canonicalize` return
//! the never type instead, which is the better mechanism — this PR has already
//! shipped several comments that stopped being true while nothing complained.
//!
//! # Why not camino
//!
//! rust-analyzer's `AbsPathBuf` wraps `camino::Utf8PathBuf`, buying UTF-8
//! paths. That is exactly wrong here. A Unix filename is arbitrary bytes, this
//! crate has a test asserting all 254 legal ones survive a URI round trip, and
//! the headline bug this module's crate fixed was non-ASCII paths resolving to
//! directories that do not exist. Requiring UTF-8 would reintroduce that class
//! by construction, so this wraps `PathBuf` and keeps the bytes.

use crate::PathUriError;
use std::borrow::Borrow;
use std::path::{Path, PathBuf};

/// An owned path guaranteed absolute, and deliberately not canonicalizable.
///
/// Derefs to [`Path`], so ordinary reads need no conversion. [`Borrow<Path>`]
/// means a `HashMap<AbsPathBuf, _>` can still be looked up by `&Path`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AbsPathBuf(PathBuf);

impl AbsPathBuf {
    /// Wrap a path, checking it is absolute.
    ///
    /// # Errors
    /// [`PathUriError::NotAbsolute`] if it is not.
    pub fn new(path: impl Into<PathBuf>) -> Result<Self, PathUriError> {
        let path = path.into();
        if path.is_absolute() {
            Ok(Self(path))
        } else {
            Err(PathUriError::NotAbsolute)
        }
    }

    /// Borrow as a plain [`Path`].
    #[must_use]
    pub fn as_path(&self) -> &Path {
        &self.0
    }

    /// Unwrap to a [`PathBuf`], for APIs that take one by value.
    #[must_use]
    pub fn into_path_buf(self) -> PathBuf {
        self.0
    }

    /// The loader's spelling of this path, for cross-referencing its source map.
    ///
    /// This is NOT identity, and it is a different question from the one
    /// [`Self::canonicalize`] refuses. `rustledger_loader`'s `DiskFileSystem`
    /// canonicalizes every path it records, so a lookup against `source_map`
    /// has to be made in the loader's spelling or it simply misses. That is
    /// interop with another component's representation, and it is allowed to
    /// touch the disk because the file it asks about is one the loader already
    /// read.
    ///
    /// Deciding "are these the same file" for a cache key is the other
    /// question, and the one that must not depend on the filesystem. Keeping
    /// the two under different names is the whole point: `grep` for this one
    /// and every loader cross-reference is listed; anything still calling
    /// `canonicalize` is trying to establish identity and does not compile.
    ///
    /// `None` when the path does not exist, which for a source-map lookup is
    /// the same answer as "not in the ledger".
    #[must_use]
    pub fn canonical_for_loader_lookup(&self) -> Option<PathBuf> {
        self.0.canonicalize().ok()
    }

    /// Not available, by design — see the module docs.
    ///
    /// Returning `!` and deprecating it together make any use a compile error
    /// under this workspace's `-D warnings`: `deprecated` fails the build on
    /// the mere mention, and `!` fails `?`/`.unwrap()` on the value even
    /// without it. An inherent method shadows the one reached through `Deref`,
    /// so `abs_path.canonicalize()` resolves here rather than to
    /// [`Path::canonicalize`].
    ///
    /// If you need to know whether two paths are the same file THROUGH
    /// symlinks, that is a different question from identity and belongs at the
    /// call site that actually needs it, with its failure mode handled.
    ///
    /// # Panics
    /// Always, in the impossible case that a caller silences the lint.
    #[deprecated(
        note = "canonicalizing makes file identity depend on the filesystem at that instant: it \
                fails for a path that does not exist yet and resolves symlinks the user opened on \
                purpose. Compare AbsPathBuf values directly."
    )]
    pub fn canonicalize(&self) -> ! {
        panic!("AbsPathBuf::canonicalize is not available by design; see abs_path.rs")
    }
}

impl std::ops::Deref for AbsPathBuf {
    type Target = Path;

    fn deref(&self) -> &Path {
        &self.0
    }
}

impl AsRef<Path> for AbsPathBuf {
    fn as_ref(&self) -> &Path {
        &self.0
    }
}

/// Lets a `HashMap<AbsPathBuf, _>` be probed with a `&Path`, which is what the
/// VFS and the loader's source map hand out.
impl Borrow<Path> for AbsPathBuf {
    fn borrow(&self) -> &Path {
        &self.0
    }
}

/// Cross-type comparison, mirroring what std provides among `Path`/`PathBuf`.
/// Without these every assertion against a plain path needs an `.as_path()`,
/// which is noise that obscures where the invariant genuinely matters.
impl PartialEq<Path> for AbsPathBuf {
    fn eq(&self, other: &Path) -> bool {
        self.0 == other
    }
}

impl PartialEq<PathBuf> for AbsPathBuf {
    fn eq(&self, other: &PathBuf) -> bool {
        self.0 == *other
    }
}

impl PartialEq<AbsPathBuf> for PathBuf {
    fn eq(&self, other: &AbsPathBuf) -> bool {
        *self == other.0
    }
}

impl PartialEq<&Path> for AbsPathBuf {
    fn eq(&self, other: &&Path) -> bool {
        self.0 == *other
    }
}

impl std::fmt::Display for AbsPathBuf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.display().fmt(f)
    }
}

impl TryFrom<PathBuf> for AbsPathBuf {
    type Error = PathUriError;

    fn try_from(path: PathBuf) -> Result<Self, PathUriError> {
        Self::new(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_relative_path_is_refused() {
        assert_eq!(
            AbsPathBuf::new("relative/x.bean"),
            Err(PathUriError::NotAbsolute)
        );
        assert_eq!(AbsPathBuf::new(""), Err(PathUriError::NotAbsolute));
    }

    #[test]
    fn an_absolute_path_is_accepted_and_reads_as_a_path() {
        let p = crate::test_abs("tmp/x.bean");
        let abs = AbsPathBuf::new(p.clone()).expect("absolute");
        assert_eq!(abs.as_path(), p);
        assert_eq!(abs.file_name().expect("name"), "x.bean"); // via Deref
        assert_eq!(abs.into_path_buf(), p);
    }

    /// Two spellings of one path are one key; a `&Path` finds it.
    #[test]
    fn it_is_a_map_key_reachable_by_path() {
        let mut map = std::collections::HashMap::new();
        let p = crate::test_abs("tmp/rl/x.bean");
        map.insert(AbsPathBuf::new(p.clone()).expect("absolute"), 1);
        assert_eq!(map.get(p.as_path()), Some(&1), "Borrow<Path> must work");
    }
}
