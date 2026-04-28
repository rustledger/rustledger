//! Tests for the `BEANCOUNT_LOAD_CACHE_FILENAME` env-var integration of
//! `cache_path`. Mutating process env requires `unsafe` since Rust 2024;
//! this test binary opts out of the workspace's `unsafe_code = "deny"` so
//! the env-var path can be exercised end-to-end.

#![cfg(feature = "cache")]
#![allow(unsafe_code)]

use rustledger_loader::{
    CACHE_FILENAME_ENV, CacheEntry, CachedOptions, DISABLE_CACHE_ENV, Options, cache_path,
    load_cache_entry, save_cache_entry,
};
use std::path::{Path, PathBuf};
use std::sync::Mutex;

// Serialize all env-touching tests in this binary so they can't race.
static ENV_LOCK: Mutex<()> = Mutex::new(());

/// Sets `key` to `value` for the duration of the guard's lifetime, restoring
/// the prior state on drop — including when the test panics. Without this, a
/// panicking test would leak its mutated env into the next test in the binary.
struct EnvGuard<'a> {
    key: &'a str,
    prior: Option<String>,
    // Hold the mutex for the lifetime of the guard so other threads can't
    // observe the mutated env while a test is running.
    _lock: std::sync::MutexGuard<'a, ()>,
}

impl<'a> EnvGuard<'a> {
    fn new(key: &'a str, value: Option<&str>) -> Self {
        let lock = ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let prior = std::env::var(key).ok();
        // SAFETY: env access is serialized via ENV_LOCK; the guard holds the
        // mutex until drop so no concurrent reader/writer in this test binary
        // can race.
        unsafe {
            match value {
                Some(v) => std::env::set_var(key, v),
                None => std::env::remove_var(key),
            }
        }
        Self {
            key,
            prior,
            _lock: lock,
        }
    }
}

impl Drop for EnvGuard<'_> {
    fn drop(&mut self) {
        // SAFETY: same invariant as `EnvGuard::new`.
        unsafe {
            match &self.prior {
                Some(p) => std::env::set_var(self.key, p),
                None => std::env::remove_var(self.key),
            }
        }
    }
}

fn with_env<F, R>(key: &str, value: Option<&str>, body: F) -> R
where
    F: FnOnce() -> R,
{
    let _guard = EnvGuard::new(key, value);
    body()
}

#[test]
fn cache_path_default_is_hidden_dotfile() {
    with_env(CACHE_FILENAME_ENV, None, || {
        let source = Path::new("/tmp/ledger.beancount");
        assert_eq!(
            cache_path(source),
            PathBuf::from("/tmp/.ledger.beancount.cache")
        );

        let relative = Path::new("relative/path/my.beancount");
        assert_eq!(
            cache_path(relative),
            PathBuf::from("relative/path/.my.beancount.cache")
        );
    });
}

#[test]
fn cache_path_env_pattern_is_honored() {
    with_env(
        CACHE_FILENAME_ENV,
        Some("/var/cache/rledger/{filename}.cache"),
        || {
            let source = Path::new("/home/user/main.beancount");
            assert_eq!(
                cache_path(source),
                PathBuf::from("/var/cache/rledger/main.beancount.cache")
            );
        },
    );
}

#[test]
fn cache_path_relative_env_pattern_resolves_against_source_dir() {
    with_env(CACHE_FILENAME_ENV, Some(".cache/{filename}.bin"), || {
        let source = Path::new("/home/user/finances/main.beancount");
        assert_eq!(
            cache_path(source),
            PathBuf::from("/home/user/finances/.cache/main.beancount.bin")
        );
    });
}

#[test]
fn cache_path_empty_env_pattern_falls_back_to_default() {
    // Empty pattern is treated as unset so users can't accidentally collapse
    // every ledger's cache to the same file.
    with_env(CACHE_FILENAME_ENV, Some(""), || {
        let source = Path::new("/tmp/ledger.beancount");
        assert_eq!(
            cache_path(source),
            PathBuf::from("/tmp/.ledger.beancount.cache")
        );
    });
}

fn empty_cache_entry(file: &Path) -> CacheEntry {
    CacheEntry {
        directives: vec![],
        options: CachedOptions::from(&Options::new()),
        plugins: vec![],
        files: vec![file.to_string_lossy().into_owned()],
    }
}

#[test]
fn save_creates_missing_parent_directory() {
    // Regression for Copilot review on PR #945: if BEANCOUNT_LOAD_CACHE_FILENAME
    // points into a directory that doesn't exist yet, save_cache_entry should
    // create it instead of silently failing.
    let temp = std::env::temp_dir().join("rustledger_save_creates_parent");
    let _ = std::fs::remove_dir_all(&temp);

    let pattern = format!("{}/nested/dir/{{filename}}.cache", temp.display());
    with_env(CACHE_FILENAME_ENV, Some(&pattern), || {
        let source = std::env::temp_dir().join("save_parent_test.beancount");
        save_cache_entry(&source, &empty_cache_entry(&source))
            .expect("save should create the missing parent directory");

        let expected = temp
            .join("nested")
            .join("dir")
            .join("save_parent_test.beancount.cache");
        assert!(expected.exists(), "cache should land at {expected:?}");
    });

    let _ = std::fs::remove_dir_all(&temp);
}

#[test]
fn disable_env_makes_load_return_none_and_save_no_op() {
    // Regression for Copilot review on PR #945: BEANCOUNT_DISABLE_LOAD_CACHE
    // must be honored at the loader level, not only by the CLI.
    let temp = std::env::temp_dir().join("rustledger_disable_env_test");
    let _ = std::fs::create_dir_all(&temp);
    let source = temp.join("disable.beancount");
    std::fs::write(&source, "; placeholder").unwrap();

    // Step 1: with the disable env unset, write a real cache so we have
    // something for load to discover.
    {
        let _g = EnvGuard::new(DISABLE_CACHE_ENV, None);
        save_cache_entry(&source, &empty_cache_entry(&source)).expect("save should succeed");
        assert!(cache_path(&source).exists(), "cache should be written");
    }

    // Step 2: with the disable env set, load must return None even though a
    // valid cache exists on disk, and save must not overwrite it (no-op).
    {
        let _g = EnvGuard::new(DISABLE_CACHE_ENV, Some(""));
        assert!(
            load_cache_entry(&source).is_none(),
            "load should return None when disabled, even with a valid cache present"
        );

        // Touch the cache to mtime-shift it; if save weren't a no-op, it
        // would replace the file. We verify by snapshotting the modified
        // time before and after.
        let before = std::fs::metadata(cache_path(&source))
            .unwrap()
            .modified()
            .unwrap();
        save_cache_entry(&source, &empty_cache_entry(&source))
            .expect("save should be a no-op when disabled");
        let after = std::fs::metadata(cache_path(&source))
            .unwrap()
            .modified()
            .unwrap();
        assert_eq!(
            before, after,
            "save should not modify the cache file when disabled"
        );
    }

    let _ = std::fs::remove_dir_all(&temp);
}

#[test]
fn empty_disable_env_value_still_disables() {
    // Python beancount disables on any presence of the env var (`is None`
    // check), including empty value. We mirror that.
    let temp = std::env::temp_dir().join("rustledger_disable_empty_test");
    let _ = std::fs::create_dir_all(&temp);
    let source = temp.join("empty_disable.beancount");
    std::fs::write(&source, "; placeholder").unwrap();

    let _g = EnvGuard::new(DISABLE_CACHE_ENV, Some(""));
    save_cache_entry(&source, &empty_cache_entry(&source))
        .expect("save should be a no-op with empty disable env");
    assert!(
        !cache_path(&source).exists(),
        "empty BEANCOUNT_DISABLE_LOAD_CACHE should still disable the cache"
    );

    let _ = std::fs::remove_dir_all(&temp);
}
