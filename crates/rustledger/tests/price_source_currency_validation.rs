//! `rledger price -b` writes a price source's currency into ledger text, so a
//! currency that is not a beancount commodity must be refused, naming the
//! source, instead of written (#2715).
//!
//! The fake source is a `--source-cmd` that prints a fixed JSON line (JSON,
//! so the currency can hold any character), and a pre-written cache entry
//! for the cached path.

#![cfg(unix)]

use std::path::Path;
use std::process::{Command, Output};
use tempfile::TempDir;

/// A `--source-cmd` that prints `line` whatever it is asked (`sh -c`, not a
/// shebang script, as `price_clobber_post_fetch.rs` explains).
fn stub_cmd(dir: &Path, line: &str) -> String {
    let out = dir.join("quote.txt");
    std::fs::write(&out, format!("{line}\n")).unwrap();
    let body = format!("cat {}", shell_words::quote(out.to_str().unwrap()));
    format!("sh -c {}", shell_words::quote(&body))
}

fn run_price(dir: &TempDir, json_line: &str, beancount: bool) -> Output {
    let cmd = stub_cmd(dir.path(), json_line);
    let mut args = vec![
        "price",
        "AAPL",
        "--source-cmd",
        &cmd,
        "--date",
        "2024-01-15",
    ];
    if beancount {
        args.push("-b");
    }
    Command::new(env!("CARGO_BIN_EXE_rledger"))
        // Keep the run away from the user's cache.
        .env("XDG_CACHE_HOME", dir.path())
        .args(&args)
        .output()
        .expect("rledger price should execute")
}

/// Every currency here would break the written line or change its meaning.
#[test]
fn price_b_refuses_a_source_currency_that_is_not_a_commodity() {
    let bad = [
        ("a space", "US D"),
        ("a quote", "\"USD\""),
        ("a newline", "USD\n2024-01-01 open Assets:Injected"),
        ("a control character", "US\u{07}D"),
        ("an escape sequence", "USD\u{1b}[2J"),
        ("lower case", "usd"),
        ("nothing", ""),
    ];
    for (what, currency) in bad {
        let dir = TempDir::new().unwrap();
        let line = serde_json::json!({ "price": "150.00", "currency": currency }).to_string();
        let out = run_price(&dir, &line, true);
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            !stdout.contains("price AAPL"),
            "a currency with {what} ({currency:?}) must not be written; stdout:\n{stdout}"
        );
        assert!(
            !stdout.contains("Injected"),
            "nothing of the currency may reach the ledger text; stdout:\n{stdout}"
        );
        // The refusal names the source (`sh`, the stub's program) and the
        // currency, escaped by `{:?}` so the message itself stays one line.
        let expected = format!(
            "price source `sh` returned the currency {currency:?}, which is not a valid beancount commodity"
        );
        assert!(
            stderr.contains(&expected),
            "the refusal for {what} must name the source and the currency; stderr:\n{stderr}"
        );
        assert!(
            !stderr.contains('\u{07}') && !stderr.contains('\u{1b}'),
            "the refusal must not print the control characters raw; stderr:\n{stderr:?}"
        );
    }
}

/// A valid currency is written; the plain (non-`-b`) form is display, not
/// ledger text, and keeps printing what the source returned.
#[test]
fn price_b_writes_a_valid_currency_and_plain_output_is_unchecked() {
    let dir = TempDir::new().unwrap();
    let out = run_price(&dir, r#"{"price": "150.00", "currency": "USD"}"#, true);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(stdout, "2024-01-15 price AAPL 150.00 USD\n");

    let dir = TempDir::new().unwrap();
    let out = run_price(&dir, r#"{"price": "150.00", "currency": "usd"}"#, false);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(stdout, "AAPL: 150.00 usd\n");
}

/// A response served from the cache (written by an older rledger, or by a
/// plain run, which does not check it) is checked before it is written too.
#[cfg(target_os = "linux")]
#[test]
fn price_b_refuses_a_cached_currency_that_is_not_a_commodity() {
    let dir = TempDir::new().unwrap();
    let cache_dir = dir.path().join("rledger");
    std::fs::create_dir_all(&cache_dir).unwrap();
    let cached_at = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs();
    let envelope = serde_json::json!({
        "version": rustledger::cmd::price::cache::CACHE_SCHEMA_VERSION,
        "entries": {
            "coinbase:AAPL:USD:2024-01-15": {
                "price": "150.00",
                "currency": "USD\n2024-01-01 open Assets:Injected",
                "date": "2024-01-15",
                "source": "coinbase",
                "cached_at": cached_at,
            }
        }
    });
    std::fs::write(
        cache_dir.join("prices.json"),
        serde_json::to_string(&envelope).unwrap(),
    )
    .unwrap();

    let out = Command::new(env!("CARGO_BIN_EXE_rledger"))
        .env("XDG_CACHE_HOME", dir.path())
        .args([
            "price",
            "AAPL",
            "-b",
            "--source",
            "coinbase",
            "--date",
            "2024-01-15",
            "--verbose",
        ])
        .output()
        .expect("rledger price should execute");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("cached (source: coinbase)"),
        "the cached path must be the one taken; stderr:\n{stderr}"
    );
    assert!(
        !stdout.contains("price AAPL") && !stdout.contains("Injected"),
        "a cached bad currency must not be written; stdout:\n{stdout}"
    );
    assert!(
        stderr.contains("price source `coinbase` returned the currency"),
        "the refusal must name the source; stderr:\n{stderr}"
    );
}
