//! Where `^` means bean-price's inversion (#2866).
//!
//! bean-price's source-spec grammar, `CURRENCY:module/[^]TICKER`, is the
//! grammar of a commodity's `price:` metadata, and only there does a leading
//! `^` invert the quote. A config mapping, `--mapping` and `--source` send
//! their ticker as written, as on main: Yahoo's index tickers (`^GSPC`,
//! `^DJI`, `^VIX`) start with `^`.
//!
//! The source is a config-defined command source that answers by
//! `$RLEDGER_TICKER`, so each run shows the ticker the fetch was made with.

#![cfg(unix)]

use std::path::Path;
use std::process::{Command, Output};
use tempfile::TempDir;

/// A config with a `stub` command source: `^GSPC` is 5000.12 USD, `USDCHF`
/// is 0.8 CHF, `EURUSD` is 1.08 USD, and any other ticker fails.
fn config_dir(extra: &str) -> TempDir {
    let dir = TempDir::new().unwrap();
    let script = "case \"$RLEDGER_TICKER\" in \
        '^GSPC') echo '{\"price\": \"5000.12\", \"currency\": \"USD\"}' ;; \
        USDCHF) echo '{\"price\": \"0.8\", \"currency\": \"CHF\"}' ;; \
        EURUSD) echo '{\"price\": \"1.08\", \"currency\": \"USD\"}' ;; \
        *) echo \"no quote for $RLEDGER_TICKER\" >&2; exit 1 ;; \
        esac";
    let config = format!(
        "[price.sources.stub]\ntype = \"command\"\ncommand = [\"sh\", \"-c\", {script:?}]\n\n{extra}"
    );
    std::fs::write(dir.path().join("config.toml"), config).unwrap();
    dir
}

fn run(dir: &TempDir, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rledger"))
        .arg("price")
        .args(args)
        .args(["--no-cache", "-b"])
        // The config can only come from this directory; the cache stays
        // away from the user's.
        .current_dir(dir.path())
        .env("RLEDGER_CONFIG_DIR", dir.path())
        .env("PROGRAMDATA", dir.path())
        .env("XDG_CACHE_HOME", dir.path())
        .output()
        .expect("rledger price should execute")
}

/// The written directive, without its date, or a description of the run.
fn written(out: &Output) -> String {
    let stdout = String::from_utf8_lossy(&out.stdout);
    stdout
        .lines()
        .find_map(|line| line.split_once(' ').map(|(_, rest)| rest.to_string()))
        .unwrap_or_else(|| {
            format!(
                "nothing written; stderr: {}",
                String::from_utf8_lossy(&out.stderr)
            )
        })
}

fn ledger(dir: &Path, price_meta: &str) -> String {
    let path = dir.join("ledger.beancount");
    std::fs::write(
        &path,
        format!("2024-01-01 commodity CHF\n  price: \"{price_meta}\"\n"),
    )
    .unwrap();
    path.to_str().unwrap().to_string()
}

#[test]
fn test_price_config_mapping_keeps_caret_ticker() {
    let dir = config_dir("[price.mapping.SPX]\nsource = \"stub\"\nticker = \"^GSPC\"\n");
    let out = run(&dir, &["SPX"]);
    assert_eq!(written(&out), "price SPX 5000.12 USD");
}

#[test]
fn test_price_cli_mapping_keeps_caret_ticker() {
    let dir = config_dir("[price]\ndefault_source = \"stub\"\n");
    let out = run(&dir, &["SPX", "--mapping", "SPX:^GSPC"]);
    assert_eq!(written(&out), "price SPX 5000.12 USD");
}

#[test]
fn test_price_source_flag_keeps_caret_ticker() {
    let dir = config_dir("");
    let out = Command::new(env!("CARGO_BIN_EXE_rledger"))
        .args(["price", "^GSPC", "--source", "stub", "--no-cache"])
        .current_dir(dir.path())
        .env("RLEDGER_CONFIG_DIR", dir.path())
        .env("PROGRAMDATA", dir.path())
        .env("XDG_CACHE_HOME", dir.path())
        .output()
        .expect("rledger price should execute");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("5000.12"),
        "stdout: {stdout}\nstderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// In `price:` metadata, `^` inverts: CHF with `USD:stub/^USDCHF` is the
/// inverse of 0.8 CHF per USD.
#[test]
fn test_price_metadata_spec_inverts_caret_ticker() {
    let dir = config_dir("");
    let file = ledger(dir.path(), "USD:stub/^USDCHF");
    let out = run(&dir, &["-f", &file, "--inactive"]);
    assert_eq!(written(&out), "price CHF 1.25 USD");
}

/// The inverse of a USD quote is a price of USD, not of CHF: refused, as
/// the #2731 label check refuses the same mismatch without `^`.
#[test]
fn test_price_metadata_spec_refuses_inverse_of_another_commodity() {
    let dir = config_dir("");
    let file = ledger(dir.path(), "GBP:stub/^EURUSD");
    let out = run(&dir, &["-f", &file, "--inactive"]);
    assert!(out.stdout.is_empty(), "{}", written(&out));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains(
            "`^EURUSD` inverts a price in USD, which is a price of USD, not of CHF; \
             refusing to write it as a CHF price"
        ),
        "stderr: {stderr}"
    );
    // The refusal names the `^` as bean-price's inversion, and the way to
    // keep a literal `^` ticker.
    assert!(
        stderr.contains("is kept literal in `[price.mapping]` or `--mapping SYMBOL:^TICKER`"),
        "stderr: {stderr}"
    );
}
