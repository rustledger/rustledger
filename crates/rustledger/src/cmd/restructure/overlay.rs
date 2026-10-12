//! A filesystem that shows the loader a planned layout before it exists.
//!
//! The equivalence check has to load the ledger exactly as it WILL be, at the
//! paths it will have, before anything is written: include resolution, the
//! source map, and the directory a relative `document` path resolves against
//! all depend on where each file lives. This overlay answers reads for the
//! planned files from memory, hides the files the plan removes, and passes
//! everything else through to the disk.

use rustledger_loader::{DiskFileSystem, FileSystem, LoadError};
use std::collections::{HashMap, HashSet};
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

/// Disk, with some files replaced, added or removed in memory.
#[derive(Debug, Default)]
pub(super) struct OverlayFs {
    files: HashMap<PathBuf, Arc<str>>,
    removed: HashSet<PathBuf>,
}

impl OverlayFs {
    /// An overlay that changes nothing: the ledger as it is on disk, but
    /// normalized through the same rules as a planned one, so the two loads
    /// compare like with like.
    pub(super) fn disk() -> Self {
        Self::default()
    }

    /// Answer reads of `path` with `content`.
    pub(super) fn add(&mut self, path: &Path, content: &str) {
        let key = normalize(path);
        self.removed.remove(&key);
        self.files.insert(key, Arc::from(content));
    }

    /// Make `path` look absent.
    pub(super) fn remove(&mut self, path: &Path) {
        let key = normalize(path);
        self.files.remove(&key);
        self.removed.insert(key);
    }
}

/// Absolute, symlink-resolved where the path exists, and lexically cleaned
/// where it does not yet: the nearest existing ancestor is canonicalized and
/// the rest appended. A planned file in a directory that does not exist yet
/// therefore gets the same spelling the disk will give it once written, and
/// the same spelling the loader gives its includer.
pub(super) fn normalize(path: &Path) -> PathBuf {
    if let Ok(c) = path.canonicalize() {
        return c;
    }
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().map_or_else(|_| path.to_path_buf(), |cwd| cwd.join(path))
    };
    let mut clean = PathBuf::new();
    for component in absolute.components() {
        match component {
            Component::ParentDir => {
                clean.pop();
            }
            Component::CurDir => {}
            other => clean.push(other.as_os_str()),
        }
    }
    // Canonicalize the longest prefix that exists.
    let mut existing = clean.clone();
    let mut rest: Vec<std::ffi::OsString> = Vec::new();
    while !existing.exists() {
        match existing.file_name() {
            Some(name) => {
                rest.push(name.to_os_string());
                existing.pop();
            }
            None => return clean,
        }
    }
    let mut out = existing.canonicalize().unwrap_or(existing);
    for name in rest.iter().rev() {
        out.push(name);
    }
    out
}

fn not_found(path: &Path) -> LoadError {
    LoadError::Io {
        path: path.to_path_buf(),
        error: std::io::Error::new(std::io::ErrorKind::NotFound, "No such file or directory"),
        include_site: None,
    }
}

impl FileSystem for OverlayFs {
    fn read(&self, path: &Path) -> Result<Arc<str>, LoadError> {
        let key = normalize(path);
        if let Some(content) = self.files.get(&key) {
            return Ok(Arc::clone(content));
        }
        if self.removed.contains(&key) {
            return Err(not_found(path));
        }
        DiskFileSystem.read(path)
    }

    fn exists(&self, path: &Path) -> bool {
        let key = normalize(path);
        self.files.contains_key(&key) || (!self.removed.contains(&key) && path.exists())
    }

    fn dir_exists(&self, path: &Path) -> bool {
        if path.is_dir() {
            return true;
        }
        let key = normalize(path);
        self.files.keys().any(|f| f.starts_with(&key) && f != &key)
    }

    fn is_encrypted(&self, path: &Path) -> bool {
        let key = normalize(path);
        if self.files.contains_key(&key) {
            return false;
        }
        DiskFileSystem.is_encrypted(path)
    }

    fn normalize(&self, path: &Path) -> PathBuf {
        normalize(path)
    }

    fn glob(&self, pattern: &str) -> Result<Vec<PathBuf>, String> {
        // Planned files are keyed by their resolved path, but the loader
        // passes the pattern as written under the including file's directory
        // (`/ledger/./sub/*.beancount`, `/ledger/../x/*`). Resolve the part
        // before the first glob character the same way the keys were, or a
        // planned file the real glob will find goes unseen.
        let resolved = match pattern.find(['*', '?', '[']) {
            Some(at) => match pattern[..at].rfind(['/', std::path::MAIN_SEPARATOR]) {
                Some(sep) => format!(
                    "{}/{}",
                    normalize(Path::new(&pattern[..sep])).to_string_lossy(),
                    &pattern[sep + 1..]
                ),
                None => pattern.to_string(),
            },
            None => normalize(Path::new(pattern)).to_string_lossy().into_owned(),
        };
        let pat = glob::Pattern::new(&resolved).map_err(|e| e.to_string())?;
        let mut matched: Vec<PathBuf> = DiskFileSystem
            .glob(pattern)?
            .into_iter()
            .filter(|p| !self.removed.contains(&normalize(p)))
            .collect();
        // A planned file the pattern matches is part of the planned ledger: a
        // root that already includes `ledger/*.beancount` would pick up period
        // files written into `ledger/`, and the check must see that.
        for planned in self.files.keys() {
            if pat.matches_path(planned) {
                matched.push(planned.clone());
            }
        }
        matched.sort();
        matched.dedup_by(|a, b| normalize(a) == normalize(b));
        Ok(matched)
    }

    fn decrypt(&self, path: &Path) -> Result<Arc<str>, LoadError> {
        DiskFileSystem.decrypt(path)
    }
}
