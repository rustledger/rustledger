//! Tests for the `BEANCOUNT_LOAD_CACHE_FILENAME` env-var integration of
//! `cache_path`. Mutating process env requires `unsafe` since Rust 2024;
//! this test binary opts out of the workspace's `unsafe_code = "deny"` so
//! the env-var path can be exercised end-to-end.

#![cfg(feature = "cache")]
#![allow(unsafe_code)]

use rustledger_loader::{CACHE_FILENAME_ENV, cache_path};
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
