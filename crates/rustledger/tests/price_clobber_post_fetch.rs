//! Integration test for the `--clobber` post-fetch dedup path.
//!
//! The pre-fetch `--clobber` skip uses the *requested* date. Some sources
//! return a different effective date for "latest" (ECB on weekends, JSON
//! source-cmd output carrying its own date), so duplicates can still slip
//! past the pre-fetch check. The post-fetch re-check uses the response's
//! actual date — this test exercises that path via a `--source-cmd` stub
//! that emits a date deliberately *different* from the requested date.

#![cfg(unix)]

use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::Command;
use tempfile::{NamedTempFile, TempDir};

fn stub_emitting_date(date: &str) -> (TempDir, PathBuf) {
    let dir = TempDir::new().unwrap();
    let path = dir.path().join("stub-source.sh");
    // Beancount-form output: `<date> price <ticker> <amount> <currency>`.
    // The source-cmd parser picks up the date from this line. Args (ticker,
    // currency) are ignored — we always emit the same line so we can assert
    // the dedup behavior is driven by the *response* date.
    let body = format!("#!/usr/bin/env bash\necho '{date} price AAPL 150.00 USD'\n");
    std::fs::write(&path, body).unwrap();
    let mut perms = std::fs::metadata(&path).unwrap().permissions();
    perms.set_mode(0o755);
    std::fs::set_permissions(&path, perms).unwrap();
    (dir, path)
}

fn write_fixture(content: &str) -> NamedTempFile {
    let f = tempfile::Builder::new()
        .suffix(".beancount")
        .tempfile()
        .unwrap();
    std::fs::write(f.path(), content).unwrap();
    f
}

/// Source returns 2024-01-10 even though we asked for 2024-01-15. The
/// fixture has an existing `price` directive dated 2024-01-10. With the
/// pre-fetch check alone, the duplicate would slip through (pre-check uses
/// 2024-01-15, which has no existing directive). The post-fetch re-check
/// catches the response.date = 2024-01-10 collision.
#[test]
fn clobber_post_fetch_skips_when_response_date_matches_existing() {
    let fixture = "\
2024-01-01 commodity AAPL
  price: \"USD:yahoo/AAPL\"

2024-01-01 open Assets:Brokerage
2024-01-01 open Equity:Open

2024-01-15 * \"buy\"
  Assets:Brokerage  10 AAPL {150 USD}
  Equity:Open

; existing price for the date the stub will return (NOT the requested date)
2024-01-10 price AAPL 150.00 USD
";
    let f = write_fixture(fixture);
    let (_dir, stub_path) = stub_emitting_date("2024-01-10");
    let stub_arg = shell_words::quote(stub_path.to_str().unwrap()).into_owned();

    let out = Command::new(env!("CARGO_BIN_EXE_rledger"))
        .args([
            "price",
            "-f",
            f.path().to_str().unwrap(),
            "--beancount",
            "--source-cmd",
            &stub_arg,
            "--date",
            "2024-01-15",
        ])
        .output()
        .expect("rledger price should execute");

    assert!(
        out.status.success(),
        "rledger exited non-zero: stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    let new_directive_count = stdout.lines().filter(|l| l.contains("price AAPL")).count();
    assert_eq!(
        new_directive_count, 0,
        "post-fetch --clobber re-check should suppress the duplicate. \
         Requested date: 2024-01-15, response date: 2024-01-10, \
         existing directive at 2024-01-10. stdout was:\n{stdout}"
    );
}

/// Same scenario but with `--clobber` set: the duplicate should be emitted.
/// Verifies the post-fetch skip is gated on `!args.clobber`.
#[test]
fn clobber_post_fetch_emits_duplicate_when_clobber_is_set() {
    let fixture = "\
2024-01-01 commodity AAPL
  price: \"USD:yahoo/AAPL\"

2024-01-01 open Assets:Brokerage
2024-01-01 open Equity:Open

2024-01-15 * \"buy\"
  Assets:Brokerage  10 AAPL {150 USD}
  Equity:Open

2024-01-10 price AAPL 150.00 USD
";
    let f = write_fixture(fixture);
    let (_dir, stub_path) = stub_emitting_date("2024-01-10");
    let stub_arg = shell_words::quote(stub_path.to_str().unwrap()).into_owned();

    let out = Command::new(env!("CARGO_BIN_EXE_rledger"))
        .args([
            "price",
            "-f",
            f.path().to_str().unwrap(),
            "--beancount",
            "--source-cmd",
            &stub_arg,
            "--date",
            "2024-01-15",
            "--clobber",
        ])
        .output()
        .expect("rledger price should execute");

    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("price AAPL"),
        "with --clobber, the duplicate should be emitted: stdout was:\n{stdout}"
    );
}

/// Cache-hit dedup (Copilot review on PR #985): the cache only stores
/// fresh-fetch responses (the source-cmd path doesn't cache). To exercise
/// the cache-hit branch we redirect `XDG_CACHE_HOME` to a temp dir and
/// pre-write a `prices.json` whose entry's date (2024-01-10) doesn't match
/// the requested date (2024-01-15) but DOES match an existing directive in
/// the file. Without the cache-hit dedup check, the cached price would be
/// re-emitted as a duplicate; with it, the run skips and emits nothing.
///
/// Triggered via `--source coinbase`: the cache lookup uses that source
/// name and hits the entry we wrote, never reaching the network.
///
/// Linux-only: the `dirs` crate honors `XDG_CACHE_HOME` only on Linux
/// (macOS uses `~/Library/Caches` via `NSSearchPathForDirectoriesInDomains`,
/// Windows uses `FOLDERID_LocalAppData`). On those platforms the spawned
/// rledger would read the wrong cache file, miss our pre-warmed entry,
/// and try to fetch from the real coinbase API.
#[cfg(target_os = "linux")]
#[test]
fn clobber_cache_hit_skips_when_cached_date_matches_existing() {
    use std::collections::HashMap;
    let cache_dir = TempDir::new().unwrap();
    let rledger_cache_dir = cache_dir.path().join("rledger");
    std::fs::create_dir_all(&rledger_cache_dir).unwrap();
    let cache_file = rledger_cache_dir.join("prices.json");

    // cache_key format (cache.rs:142): "<source>:<ticker>:<currency>:<YYYY-MM-DD>"
    // Date is "2024-01-15" because that's what we'll request via --date.
    // The cached *response* date is 2024-01-10 — different from the key's
    // requested date, simulating a "latest" source that returned an older
    // effective date which then got persisted in the cache.
    let cached_at = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs();
    let mut entries: HashMap<String, serde_json::Value> = HashMap::new();
    entries.insert(
        "coinbase:AAPL:USD:2024-01-15".to_string(),
        serde_json::json!({
            "price": "150.00",
            "currency": "USD",
            "date": "2024-01-10",
            "source": "coinbase",
            "cached_at": cached_at,
        }),
    );
    std::fs::write(&cache_file, serde_json::to_string(&entries).unwrap()).unwrap();

    let fixture = "\
2024-01-01 commodity AAPL
  price: \"USD:yahoo/AAPL\"

2024-01-01 open Assets:Brokerage
2024-01-01 open Equity:Open

2024-01-15 * \"buy\"
  Assets:Brokerage  10 AAPL {150 USD}
  Equity:Open

; existing price at the cached response date
2024-01-10 price AAPL 150.00 USD
";
    let f = write_fixture(fixture);

    let out = Command::new(env!("CARGO_BIN_EXE_rledger"))
        .env("XDG_CACHE_HOME", cache_dir.path())
        .args([
            "price",
            "-f",
            f.path().to_str().unwrap(),
            "--beancount",
            "--source",
            "coinbase",
            "--date",
            "2024-01-15",
        ])
        .output()
        .expect("rledger price should execute");

    assert!(
        out.status.success(),
        "rledger exited non-zero: stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    let new_directive_count = stdout.lines().filter(|l| l.contains("price AAPL")).count();
    assert_eq!(
        new_directive_count, 0,
        "cache-hit dedup must suppress the duplicate when cached date \
         matches an existing directive. Cached date: 2024-01-10, \
         existing directive at 2024-01-10. stdout was:\n{stdout}"
    );
}
