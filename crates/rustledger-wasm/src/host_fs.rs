//! A [`FileSystem`] backed by host callbacks.
//!
//! The loader never touches a filesystem itself — it asks its [`FileSystem`]
//! for files. `DiskFileSystem` answers from the disk, `VirtualFileSystem` from
//! a map handed over in one go, and this one asks the JS host, one path at a
//! time, as the loader walks the include graph.
//!
//! # Why this exists
//!
//! Handing over a map first means the host has to know which files to hand
//! over, which means the host has to walk `include` directives itself — a
//! second, approximate implementation of the thing the loader already does.
//! The MCP server carried one, and it was wrong four separate ways before it
//! was replaced (#2100): globs unexpanded, a file reached twice counted twice,
//! a symlinked include counted twice, a symlinked entry point resolved against
//! the wrong directory. None of those are beancount questions.
//!
//! With this, the host supplies `readFile`, `glob` and `realpath` — primitives
//! that encode nothing about beancount — and include semantics have one
//! implementation, the same one `rledger check` runs (#2101).
//!
//! # Why the callbacks live in a `thread_local` and not in the struct
//!
//! [`FileSystem`] requires `Send + Sync`, because the loader hands it to rayon
//! when the backend permits parallel reads. `js_sys::Function` is neither, and
//! this crate is `#![forbid(unsafe_code)]`, so it cannot be asserted away.
//!
//! [`HostFs`] therefore holds NOTHING — a unit struct is `Send + Sync` for
//! free — and reads the callbacks from a thread-local installed for the
//! duration of one call. That mirrors how the WASI component satisfies the
//! same trait for `host.decrypt` (#1667): the capability is an ambient host
//! function, not a handle carried around in the struct.
//!
//! `supports_parallel_read` answers `false`, so the rayon path this bound
//! exists for is never taken here anyway; wasm is single-threaded.

use std::cell::RefCell;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustledger_loader::{FileSystem, LoadError};
use wasm_bindgen::JsValue;

/// The host functions installed for the duration of one entry-point call.
struct HostCallbacks {
    /// The object the callbacks came from, used as their `this`. A host is
    /// free to write `{ readFile(p) { return this.cache.get(p); } }`, and
    /// calling that with a null receiver breaks it at runtime.
    receiver: JsValue,
    /// `(path: string) => string | null` — contents, or null if unreadable.
    read_file: js_sys::Function,
    /// `(pattern: string) => string[]` — optional; without it a glob include
    /// reports the same "does not match any files" the disk backend does.
    glob: Option<js_sys::Function>,
    /// `(path: string) => string` — optional. This is where symlink and
    /// case-fold collapsing belongs: the loader de-duplicates by the path this
    /// returns, so a host that answers with a real path gets a file reached
    /// two ways loaded once, for free.
    realpath: Option<js_sys::Function>,
}

thread_local! {
    static HOST: RefCell<Option<HostCallbacks>> = const { RefCell::new(None) };
}

/// Installs host callbacks for as long as it is alive, and clears them on
/// drop — including on an early return, so a failed load cannot leave a stale
/// callback installed for the next call.
pub struct HostScope;

impl HostScope {
    /// Reads `readFile`, `glob` and `realpath` off a JS object and installs
    /// them.
    ///
    /// # Errors
    ///
    /// When `readFile` is absent or is not callable. The other two are
    /// optional; the loader degrades the way a backend without them does.
    pub fn install(host: &JsValue) -> Result<Self, String> {
        // Refuse rather than clobber. An inner scope would overwrite the outer
        // one's callbacks and then clear them on drop, leaving the OUTER load
        // to fail with "no host filesystem installed" — a confusing error a
        // long way from its cause. This can only happen if a host callback
        // re-enters, which is legal but not something the loader can be in the
        // middle of.
        let occupied = HOST.with(|h| h.borrow().is_some());
        if occupied {
            return Err(
                "a host filesystem is already installed — a host callback cannot re-enter \
                 `validateWithHost` or `queryWithHost` while a load is in progress"
                    .to_string(),
            );
        }

        let read_file = js_fn(host, "readFile")?
            .ok_or_else(|| "host must provide a `readFile(path) => string | null`".to_string())?;
        let glob = js_fn(host, "glob")?;
        let realpath = js_fn(host, "realpath")?;

        HOST.with(|h| {
            *h.borrow_mut() = Some(HostCallbacks {
                receiver: host.clone(),
                read_file,
                glob,
                realpath,
            });
        });
        Ok(Self)
    }
}

impl Drop for HostScope {
    fn drop(&mut self) {
        HOST.with(|h| {
            *h.borrow_mut() = None;
        });
    }
}

/// Reads an optional function-valued property, erroring when it is present but
/// not callable — a silent skip there would look like an unsupported
/// capability rather than a typo.
fn js_fn(host: &JsValue, name: &str) -> Result<Option<js_sys::Function>, String> {
    let value = js_sys::Reflect::get(host, &JsValue::from_str(name))
        .map_err(|_| format!("could not read `{name}` from the host object"))?;
    if value.is_undefined() || value.is_null() {
        return Ok(None);
    }
    value
        .dyn_into::<js_sys::Function>()
        .map(Some)
        .map_err(|_| format!("host property `{name}` is not a function"))
}

use wasm_bindgen::JsCast;

/// A [`FileSystem`] that asks the JS host for each file as the loader reaches
/// it. See the module docs for why it is a unit struct.
#[derive(Debug)]
pub struct HostFs;

impl HostFs {
    fn call1(f: &js_sys::Function, receiver: &JsValue, arg: &str) -> Result<JsValue, String> {
        f.call1(receiver, &JsValue::from_str(arg)).map_err(|e| {
            e.as_string()
                .unwrap_or_else(|| "host callback threw".to_string())
        })
    }
}

impl FileSystem for HostFs {
    fn read(&self, path: &Path) -> Result<Arc<str>, LoadError> {
        let display = path.display().to_string();
        // Clone the handle out and DROP the borrow before calling into JS. A
        // callback is free to re-enter — a caching or logging host might — and
        // re-entering while this borrow is live panics the `RefCell`. Cloning
        // a `js_sys::Function` copies a handle, not a function.
        let pair = HOST.with(|h| {
            h.borrow()
                .as_ref()
                .map(|host| (host.read_file.clone(), host.receiver.clone()))
        });
        let (f, receiver) = pair.ok_or_else(|| not_found(path, "no host filesystem installed"))?;
        let value =
            Self::call1(&f, &receiver, &display).map_err(|message| not_found(path, &message))?;
        value
            .as_string()
            .map(Arc::from)
            // `null` is the host saying it cannot read this path. It is NOT an
            // error to raise here — a missing include is reported against the
            // file that asked for it, with that file's span.
            .ok_or_else(|| not_found(path, "file not found"))
    }

    fn exists(&self, path: &Path) -> bool {
        self.read(path).is_ok()
    }

    fn dir_exists(&self, _path: &Path) -> bool {
        // Same answer as the virtual backend: there are no directories to
        // interrogate, and answering `false` would warn on every
        // `option "documents"` root. See `FileSystem::dir_exists`.
        true
    }

    fn is_encrypted(&self, _path: &Path) -> bool {
        // The host hands over contents, not ciphertext; if it wants to serve a
        // `.gpg` ledger it decrypts before returning, as the WASI component's
        // embedder does for `host.decrypt`.
        false
    }

    fn normalize(&self, path: &Path) -> PathBuf {
        let display = path.display().to_string();
        let pair = HOST.with(|h| {
            h.borrow()
                .as_ref()
                .and_then(|host| host.realpath.clone().map(|f| (f, host.receiver.clone())))
        });
        match pair
            .and_then(|(f, r)| Self::call1(&f, &r, &display).ok())
            .and_then(|v| v.as_string())
        {
            Some(real) => PathBuf::from(real),
            // No `realpath`, or the host could not resolve it. Fall back to
            // the same textual normalization the virtual backend applies, so
            // `./j/x` and `j/x` stay ONE file — otherwise the loader reads it
            // twice and doubles everything in it. What this cannot collapse is
            // a symlink or a case-fold, which is what `realpath` is for.
            None => textual_normalize(&display),
        }
    }

    fn supports_parallel_read(&self) -> bool {
        // Never: the callbacks are JS, wasm is single-threaded, and the
        // `Send + Sync` bound this would exercise is satisfied only because
        // the struct is empty.
        false
    }

    fn glob(&self, pattern: &str) -> Result<Vec<PathBuf>, String> {
        // Same reason as `read`: the borrow must not span the JS call.
        let pair = HOST.with(|h| {
            h.borrow()
                .as_ref()
                .and_then(|host| host.glob.clone().map(|f| (f, host.receiver.clone())))
        });
        let Some((f, receiver)) = pair else {
            return Err("glob is not supported by this filesystem".to_string());
        };
        let value = Self::call1(&f, &receiver, pattern)?;
        let array = js_sys::Array::from(&value);
        let mut matched: Vec<PathBuf> = array
            .iter()
            .filter_map(|v| v.as_string())
            .map(PathBuf::from)
            .collect();
        // Sorted for the same reason the disk backend sorts: the assembled
        // ledger must not depend on the order a host happened to list in.
        matched.sort();
        Ok(matched)
    }
}

/// The clean-up the virtual backend applies: forward slashes, no leading
/// `./`, `..` resolved. Mirrors the loader's private `normalize_vfs_path`; if
/// the two drift, a path spelled two ways is two files here and one there.
fn textual_normalize(path: &str) -> PathBuf {
    let normalized = path.replace('\\', "/");
    let stripped = normalized.strip_prefix("./").unwrap_or(&normalized);
    let mut components: Vec<&str> = Vec::new();
    for part in stripped.split('/') {
        match part {
            "" | "." => {}
            ".." => {
                components.pop();
            }
            other => components.push(other),
        }
    }
    let joined = components.join("/");
    PathBuf::from(if stripped.starts_with('/') {
        format!("/{joined}")
    } else {
        joined
    })
}

fn not_found(path: &Path, message: &str) -> LoadError {
    LoadError::Io {
        path: path.to_path_buf(),
        source: std::io::Error::new(std::io::ErrorKind::NotFound, message.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::textual_normalize;
    use std::path::PathBuf;

    #[test]
    fn the_fallback_collapses_paths_that_name_one_file() {
        // Without a host `realpath`, this is all that keeps `./j/x` and `j/x`
        // from being two entries in the loader's "already loaded" set — and
        // two entries means the file's directives are read twice and every
        // amount in it doubles.
        for spelling in [
            "j/x.beancount",
            "./j/x.beancount",
            "j/./x.beancount",
            "j/y/../x.beancount",
        ] {
            assert_eq!(
                textual_normalize(spelling),
                PathBuf::from("j/x.beancount"),
                "{spelling} names the same file"
            );
        }
        assert_eq!(
            textual_normalize("j\\x.beancount"),
            PathBuf::from("j/x.beancount"),
            "a Windows separator names the same file too"
        );
    }

    #[test]
    fn the_fallback_keeps_an_absolute_path_absolute() {
        assert_eq!(
            textual_normalize("/ledger/./j/../main.beancount"),
            PathBuf::from("/ledger/main.beancount")
        );
    }
}
