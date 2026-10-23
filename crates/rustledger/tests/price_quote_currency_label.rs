//! The written price is labeled with the quote currency the pair declared,
//! as bean-price writes it, whatever the source calls the unit (#2731).
//!
//! Yahoo labels a London pence quote `GBp` on its historical endpoint and
//! `GBP` on its latest — both return pence numbers — so `price:
//! "GBX:yahoo/BNZL.L"` must write `price BNZL 2770.0 GBX` from either, where
//! it used to write the source's word (`GBp`, refused since #2715) or `GBP`
//! on a pence number. The fake source is a `--source-cmd` that prints a fixed
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

fn run_price(dir: &TempDir, json_line: &str, declared: &str, beancount: bool) -> Output {
    let cmd = stub_cmd(dir.path(), json_line);
    let mut args = vec![
        "price",
        "BNZL",
        "--source-cmd",
        &cmd,
        "--date",
        "2024-01-15",
        "--currency",
        declared,
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

/// Yahoo's two spellings for one pence quote, a `GBX:` pair declaring pence:
/// the directive is labeled `GBX` either way, the number unchanged.
#[test]
fn declared_gbx_labels_a_pence_quote_whatever_the_source_calls_it() {
    for currency in ["GBP", "GBp"] {
        let dir = TempDir::new().unwrap();
        let line = serde_json::json!({ "price": "2770.0", "currency": currency }).to_string();
        let out = run_price(&dir, &line, "GBX", true);
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
    let out = run_price(&dir, &line, "GBX", false);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(stdout, "BNZL: 2770.0 GBp\n");
}

/// The other pence/cents spellings follow the same rule.
#[test]
fn subunit_spellings_label_with_the_declared_major() {
    for (currency, declared) in [("ZAc", "ZAR"), ("ILA", "ILS")] {
        let dir = TempDir::new().unwrap();
        let line = serde_json::json!({ "price": "123.0", "currency": currency }).to_string();
        let out = run_price(&dir, &line, declared, true);
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
    let out = run_price(&dir, &line, "GBX", true);
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
        let out = run_price(&dir, &line, "USD", true);
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
    let out = run_price(&dir, &line, "USD", true);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("2024-01-15 price BNZL 150.00 USD"),
        "stdout:\n{stdout}"
    );
}
