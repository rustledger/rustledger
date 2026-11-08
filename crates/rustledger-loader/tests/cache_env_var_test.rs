//! Tests for the `BEANCOUNT_LOAD_CACHE_FILENAME` and
//! `BEANCOUNT_DISABLE_LOAD_CACHE` settings of the binary cache.
//!
//! The settings are injected as a [`CacheEnv`] value into the `*_in`
//! functions, and the variables are read through [`CacheEnv::from_lookup`]
//! with an injected lookup, so nothing here mutates the process environment
//! (`set_var` races with every other thread that reads it, AGENTS.md).
//! Each test writes only under its own temporary directory.

#![cfg(feature = "cache")]

use rustledger_loader::{
    CACHE_FILENAME_ENV, CacheEntry, CacheEnv, CachedOptions, DISABLE_CACHE_ENV, Options,
    cache_path_in, load_cache_entry_in, save_cache_entry_in,
};
use std::ffi::OsString;
use std::path::{Path, PathBuf};

/// Settings with a filename pattern and nothing else.
fn with_pattern(pattern: &str) -> CacheEnv {
    CacheEnv {
        filename_pattern: Some(pattern.to_string()),
        disabled: false,
    }
}

/// The settings a lookup holding exactly `vars` reads.
fn from_vars(vars: &[(&str, &str)]) -> CacheEnv {
    CacheEnv::from_lookup(|key| {
        vars.iter()
            .find(|(k, _)| *k == key)
            .map(|(_, v)| OsString::from(v))
    })
}

#[test]
fn cache_path_default_is_hidden_dotfile() {
    let env = CacheEnv::default();
    let source = Path::new("/tmp/ledger.beancount");
    assert_eq!(
        cache_path_in(source, &env),
        PathBuf::from("/tmp/.ledger.beancount.cache")
    );

    let relative = Path::new("relative/path/my.beancount");
    assert_eq!(
        cache_path_in(relative, &env),
        PathBuf::from("relative/path/.my.beancount.cache")
    );
}

#[test]
fn cache_path_env_pattern_is_honored() {
    let source = Path::new("/home/user/main.beancount");
    assert_eq!(
        cache_path_in(source, &with_pattern("/var/cache/rledger/{filename}.cache")),
        PathBuf::from("/var/cache/rledger/main.beancount.cache")
    );
}

#[test]
fn cache_path_relative_env_pattern_resolves_against_source_dir() {
    let source = Path::new("/home/user/finances/main.beancount");
    assert_eq!(
        cache_path_in(source, &with_pattern(".cache/{filename}.bin")),
        PathBuf::from("/home/user/finances/.cache/main.beancount.bin")
    );
}

/// The two variables are read under their documented names, and an empty
/// pattern is treated as unset so users can't accidentally collapse every
/// ledger's cache to the same file. Any value of the disable variable,
/// including empty, disables, as Python beancount's `is None` check does.
#[test]
fn cache_env_reads_the_two_variables() {
    assert_eq!(from_vars(&[]), CacheEnv::default());
    assert_eq!(
        from_vars(&[(CACHE_FILENAME_ENV, "/c/{filename}")]),
        with_pattern("/c/{filename}")
    );
    assert_eq!(from_vars(&[(CACHE_FILENAME_ENV, "")]), CacheEnv::default());
    for value in ["", "1", "no"] {
        assert!(
            from_vars(&[(DISABLE_CACHE_ENV, value)]).disabled,
            "{value:?}"
        );
    }
    assert_eq!(CACHE_FILENAME_ENV, "BEANCOUNT_LOAD_CACHE_FILENAME");
    assert_eq!(DISABLE_CACHE_ENV, "BEANCOUNT_DISABLE_LOAD_CACHE");
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
    let temp = tempfile::tempdir().expect("create a temp dir");
    let pattern = format!("{}/nested/dir/{{filename}}.cache", temp.path().display());
    let source = temp.path().join("save_parent_test.beancount");
    save_cache_entry_in(
        &source,
        &empty_cache_entry(&source),
        &with_pattern(&pattern),
    )
    .expect("save should create the missing parent directory");

    let expected = temp
        .path()
        .join("nested")
        .join("dir")
        .join("save_parent_test.beancount.cache");
    assert!(expected.exists(), "cache should land at {expected:?}");
}

#[test]
fn disable_env_makes_load_return_none_and_save_no_op() {
    // Regression for Copilot review on PR #945: BEANCOUNT_DISABLE_LOAD_CACHE
    // must be honored at the loader level, not only by the CLI.
    let temp = tempfile::tempdir().expect("create a temp dir");
    let source = temp.path().join("disable.beancount");
    std::fs::write(&source, "; placeholder").expect("write the source");
    let enabled = CacheEnv::default();
    let disabled = CacheEnv {
        disabled: true,
        ..CacheEnv::default()
    };

    // Step 1: with the cache enabled, write a real cache so there is
    // something for load to discover.
    save_cache_entry_in(&source, &empty_cache_entry(&source), &enabled)
        .expect("save should succeed");
    let cache = cache_path_in(&source, &enabled);
    assert!(cache.exists(), "cache should be written");

    // Step 2: disabled, load must return None even though a valid cache
    // exists on disk, and save must not overwrite it (no-op).
    assert!(
        load_cache_entry_in(&source, &disabled).is_none(),
        "load should return None when disabled, even with a valid cache present"
    );
    let before = std::fs::metadata(&cache)
        .and_then(|m| m.modified())
        .expect("cache mtime");
    save_cache_entry_in(&source, &empty_cache_entry(&source), &disabled)
        .expect("save should be a no-op when disabled");
    let after = std::fs::metadata(&cache)
        .and_then(|m| m.modified())
        .expect("cache mtime");
    assert_eq!(
        before, after,
        "save should not modify the cache file when disabled"
    );
}

#[test]
fn empty_disable_env_value_still_disables() {
    // Python beancount disables on any presence of the env var (`is None`
    // check), including empty value. We mirror that.
    let temp = tempfile::tempdir().expect("create a temp dir");
    let source = temp.path().join("empty_disable.beancount");
    std::fs::write(&source, "; placeholder").expect("write the source");

    let env = from_vars(&[(DISABLE_CACHE_ENV, "")]);
    save_cache_entry_in(&source, &empty_cache_entry(&source), &env)
        .expect("save should be a no-op with empty disable env");
    assert!(
        !cache_path_in(&source, &env).exists(),
        "empty BEANCOUNT_DISABLE_LOAD_CACHE should still disable the cache"
    );
}
