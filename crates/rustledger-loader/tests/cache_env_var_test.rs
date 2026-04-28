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

fn with_env<F, R>(key: &str, value: Option<&str>, body: F) -> R
where
    F: FnOnce() -> R,
{
    let _guard = ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let prior = std::env::var(key).ok();
    // SAFETY: env access is serialized via ENV_LOCK; no other code in this
    // test binary reads or writes these vars outside `with_env`.
    unsafe {
        match value {
            Some(v) => std::env::set_var(key, v),
            None => std::env::remove_var(key),
        }
    }
    let result = body();
    // SAFETY: same invariant as above.
    unsafe {
        match prior {
            Some(p) => std::env::set_var(key, p),
            None => std::env::remove_var(key),
        }
    }
    result
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

    with_env(DISABLE_CACHE_ENV, Some("1"), || {
        // save is a no-op, so cache file must not appear
        save_cache_entry(&source, &empty_cache_entry(&source))
            .expect("save should be a no-op when disabled");
        assert!(
            !cache_path(&source).exists(),
            "no cache file should be written when disabled"
        );

        // load returns None even if a stale cache happens to be on disk
        assert!(
            load_cache_entry(&source).is_none(),
            "load should return None when disabled"
        );
    });

    let _ = std::fs::remove_dir_all(&temp);
}
