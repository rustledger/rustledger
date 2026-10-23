//! The written price is labeled with the quote currency the pair declared,
//! as bean-price writes it, whatever the source calls the unit (#2731).
//!
//! Yahoo labels a London pence quote `GBp` on its historical endpoint and
//! `GBP` on its latest — both return pence numbers — so `price:
//! "GBX:yahoo/BNZL.L"` must write `price BNZL 2770.0 GBX` from either, where
//! it used to write the source's word (`GBp`, refused since #2715) or `GBP`
//! on a pence number. With **nothing** declared (no `price:` metadata, no
//! config mapping, no `--currency`), the source's own word stays the label,
//! as before #2731: the request's `USD` fallback is not a claim about the
//! number's unit. The fake source is a `--source-cmd` that prints a fixed
//! JSON line, like `price_source_currency_validation.rs`.

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

fn run_price(dir: &TempDir, json_line: &str, declared: Option<&str>, beancount: bool) -> Output {
    let cmd = stub_cmd(dir.path(), json_line);
    let mut args = vec![
        "price".to_string(),
        "BNZL".to_string(),
        "--source-cmd".to_string(),
        cmd,
        "--date".to_string(),
        "2024-01-15".to_string(),
    ];
    if let Some(declared) = declared {
        args.push("--currency".to_string());
        args.push(declared.to_string());
    }
    if beancount {
        args.push("-b".to_string());
    }
    Command::new(env!("CARGO_BIN_EXE_rledger"))
        // Keep the run away from the user's cache.
        .env("XDG_CACHE_HOME", dir.path())
        .args(&args)
        .output()
        .expect("rledger price should execute")
}

/// A run against `-f` `file`, for the dedup cases: the file's own `price`
/// directives are what `--clobber` compares against.
fn run_price_with_file(dir: &TempDir, file: &Path, declared: &str, beancount: bool) -> Output {
    let cmd = stub_cmd(dir.path(), r#"{"price": "2770.0", "currency": "GBP"}"#);
    let mut args = vec![
        "price".to_string(),
        "BNZL".to_string(),
        "--source-cmd".to_string(),
        cmd,
        "--date".to_string(),
        "2024-01-15".to_string(),
        "--currency".to_string(),
        declared.to_string(),
        "-f".to_string(),
        file.to_str().unwrap().to_string(),
        "--verbose".to_string(),
    ];
    if beancount {
        args.push("-b".to_string());
    }
    Command::new(env!("CARGO_BIN_EXE_rledger"))
        .env("XDG_CACHE_HOME", dir.path())
        .args(&args)
        .output()
        .expect("rledger price should execute")
}

/// Yahoo's two spellings for one pence quote, a `GBX:` pair declaring pence:
/// the directive is labeled `GBX` either way, the number unchanged.
#[test]
fn declared_gbx_labels_a_pence_quote_whatever_the_source_calls_it() {
    for currency in ["GBP", "GBp"] {
        let dir = TempDir::new().unwrap();
        let line = serde_json::json!({ "price": "2770.0", "currency": currency }).to_string();
        let out = run_price(&dir, &line, Some("GBX"), true);
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("2024-01-15 price BNZL 2770.0 GBX"),
            "a source calling the unit {currency:?} must be labeled with the declared GBX; stdout:\n{stdout}"
        );
        assert!(
            !stdout.contains(currency),
            "the source's word {currency:?} must not reach the directive; stdout:\n{stdout}"
        );
    }
}

/// The plain (non-`-b`) form is display and keeps printing the source's own
/// word, unchecked, as #2715 documented; the label rule is the ledger text's.
#[test]
fn plain_output_keeps_printing_the_source_word() {
    let dir = TempDir::new().unwrap();
    let line = serde_json::json!({ "price": "2770.0", "currency": "GBp" }).to_string();
    let out = run_price(&dir, &line, Some("GBX"), false);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(stdout, "BNZL: 2770.0 GBp\n");
}

/// The other pence/cents spellings follow the same rule.
#[test]
fn subunit_spellings_label_with_the_declared_major() {
    for (currency, declared) in [("ZAc", "ZAR"), ("ILA", "ILS")] {
        let dir = TempDir::new().unwrap();
        let line = serde_json::json!({ "price": "123.0", "currency": currency }).to_string();
        let out = run_price(&dir, &line, Some(declared), true);
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains(&format!("price BNZL 123.0 {declared}")),
            "a source calling the unit {currency:?} must be labeled {declared}; stdout:\n{stdout}"
        );
    }
}

/// A valid commodity from another family is a mismatch to refuse, not
/// relabel: the source answered with something other than the pair asked for.
#[test]
fn a_currency_from_another_family_is_refused_not_relabelled() {
    let dir = TempDir::new().unwrap();
    let line = serde_json::json!({ "price": "2770.0", "currency": "EUR" }).to_string();
    let out = run_price(&dir, &line, Some("GBX"), true);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !stdout.contains("price BNZL"),
        "a EUR quote must not be labeled GBX; stdout:\n{stdout}"
    );
    assert!(
        stderr.contains("returned a price in EUR for the GBX pair"),
        "the refusal names the source's currency and the pair; stderr:\n{stderr}"
    );
}

/// #2715's contract is unchanged: a source currency that is not a beancount
/// commodity and names no known subunit spelling is still refused, naming the
/// source and the currency.
#[test]
fn non_commodity_source_currency_is_still_refused() {
    for currency in ["usd", "US D", ""] {
        let dir = TempDir::new().unwrap();
        let line = serde_json::json!({ "price": "150.00", "currency": currency }).to_string();
        let out = run_price(&dir, &line, Some("USD"), true);
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            !stdout.contains("price BNZL"),
            "a currency of {currency:?} must not be written; stdout:\n{stdout}"
        );
        let expected = format!(
            "price source `sh` returned the currency {currency:?}, which is not a valid beancount commodity"
        );
        assert!(
            stderr.contains(&expected),
            "the refusal for {currency:?} must name the source and the currency; stderr:\n{stderr}"
        );
    }
}

/// An exact match is the ordinary path, label and number unchanged.
#[test]
fn an_exact_match_is_written_as_it_always_was() {
    let dir = TempDir::new().unwrap();
    let line = serde_json::json!({ "price": "150.00", "currency": "USD" }).to_string();
    let out = run_price(&dir, &line, Some("USD"), true);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("2024-01-15 price BNZL 150.00 USD"),
        "stdout:\n{stdout}"
    );
}

/// With nothing declared — no `price:` metadata, no config mapping, no
/// `--currency` — the written price keeps the source's own word, as it did
/// before #2731: the request's `USD` fallback is a request default, not a
/// claim about the unit, and relabeling a `GBP` quote `USD` would be worse
/// than the bug being fixed.
#[test]
fn no_declared_quote_keeps_the_source_word() {
    let dir = TempDir::new().unwrap();
    let line = serde_json::json!({ "price": "2770.0", "currency": "GBP" }).to_string();
    let out = run_price(&dir, &line, None, true);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("2024-01-15 price BNZL 2770.0 GBP"),
        "stdout:\n{stdout}"
    );
}

/// A response served from the cache is labeled by the same rule: an entry a
/// pre-#2731 run cached carries the source's word (`GBP`) under the declared
/// key (`GBX`), and the directive is still labeled `GBX`.
#[test]
fn the_cached_path_labels_with_the_declared_quote_too() {
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
            "coinbase:BNZL:GBX:2024-01-15": {
                "price": "2770.0",
                "currency": "GBP",
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
            "BNZL",
            "-b",
            "--source",
            "coinbase",
            "--date",
            "2024-01-15",
            "--currency",
            "GBX",
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
        stdout.contains("2024-01-15 price BNZL 2770.0 GBX"),
        "a cached GBP quote is labeled with the declared GBX; stdout:\n{stdout}"
    );
}

/// The `--clobber` dedup keys on the label the directive would carry: a
/// `GBX` directive already in the file is matched and the fetch is skipped.
#[test]
fn an_existing_declared_label_is_deduplicated() {
    let dir = TempDir::new().unwrap();
    let file = dir.path().join("main.beancount");
    std::fs::write(
        &file,
        "2024-01-01 commodity BNZL\n2024-01-15 price BNZL 2770.0 GBX\n",
    )
    .unwrap();
    let out = run_price_with_file(&dir, &file, "GBX", true);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("skipped (existing price for 2024-01-15 GBX;"),
        "the existing GBX directive must be recognized; stderr:\n{stderr}"
    );
    assert!(
        !stdout.contains("price BNZL"),
        "nothing may be written when the ledger already has the price; stdout:\n{stdout}"
    );
}

/// The other half of the same rule, and the upgrade hazard it names: a
/// directive an older rledger wrote with the source's word (`GBP`) does NOT
/// match, so the correctly-labeled `GBX` directive is written beside it —
/// the stale one is the user's to delete (or refetch with `--clobber`).
#[test]
fn a_stale_source_label_does_not_hide_the_declared_one() {
    let dir = TempDir::new().unwrap();
    let file = dir.path().join("main.beancount");
    std::fs::write(
        &file,
        "2024-01-01 commodity BNZL\n2024-01-15 price BNZL 2770.0 GBP\n",
    )
    .unwrap();
    let out = run_price_with_file(&dir, &file, "GBX", true);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("2024-01-15 price BNZL 2770.0 GBX"),
        "the declared label is written even beside a stale GBP directive; stdout:\n{stdout}"
    );
}

/// A declared quote that is itself not a commodity is refused by name — the
/// declaration is the problem, and the message must not blame the source,
/// which said something else entirely.
#[test]
fn a_bad_declared_quote_is_named_as_the_declaration() {
    let dir = TempDir::new().unwrap();
    let line = serde_json::json!({ "price": "2770.0", "currency": "GBP" }).to_string();
    let out = run_price(&dir, &line, Some("GBp"), true);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(!stdout.contains("price BNZL"), "stdout:\n{stdout}");
    assert!(
        stderr.contains("the declared quote currency \"GBp\" is not a valid beancount commodity"),
        "the refusal names the declaration; stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("price source `sh` returned the currency \"GBp\""),
        "the source returned GBP, not GBp — it must not be blamed; stderr:\n{stderr}"
    );
}
