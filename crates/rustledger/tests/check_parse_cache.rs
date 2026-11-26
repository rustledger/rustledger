//! `rledger check` caches a load that has option warnings, and a cache hit
//! reports exactly the diagnostics the cold run reported (#3002).
//!
//! Before #3002 any option warning blocked the cache write, so a ledger whose
//! included file sets its own `option "title"` (E7009) re-parsed on every run.

mod common;

use std::path::Path;
use std::process::{Command, Output};

const CHILD: &str = "2020-01-01 open Assets:Cash
2020-01-01 open Expenses:Food

2020-01-01 * \"Store\" \"a purchase\"
  Expenses:Food   10.00 USD
  Assets:Cash
";

/// The issue's four files: two parents that differ only in whether the
/// included child sets one `option`.
fn write_issue_fixture(dir: &Path) {
    std::fs::write(dir.join("child_noopt.beancount"), CHILD).expect("write child_noopt");
    std::fs::write(
        dir.join("child_opt.beancount"),
        format!("option \"title\" \"Some Ledger\"\n{CHILD}"),
    )
    .expect("write child_opt");
    std::fs::write(
        dir.join("parent_noopt.beancount"),
        "include \"child_noopt.beancount\"\n",
    )
    .expect("write parent_noopt");
    std::fs::write(
        dir.join("parent_opt.beancount"),
        "include \"child_opt.beancount\"\n",
    )
    .expect("write parent_opt");
}

/// `rledger check` with the cache at its default path next to the source:
/// hermetic against any cache env the developer or CI has set.
fn check(bin: &Path, file: &Path, extra: &[&str]) -> Output {
    Command::new(bin)
        .arg("check")
        .arg(file)
        .args(extra)
        .env_remove("BEANCOUNT_DISABLE_LOAD_CACHE")
        .env_remove("BEANCOUNT_LOAD_CACHE_FILENAME")
        .env("NO_COLOR", "1")
        .output()
        .expect("run rledger check")
}

#[test]
fn test_check_option_warning_is_cached_and_replayed() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().expect("tempdir");
    write_issue_fixture(dir.path());
    let parent = dir.path().join("parent_opt.beancount");
    let cache_file = dir.path().join(".parent_opt.beancount.cache");

    // Cold run: parses, reports the E7009, and now writes the cache.
    let cold = check(&bin, &parent, &["--format", "json"]);
    assert!(
        cold.status.success(),
        "a warning must not fail check: {}",
        String::from_utf8_lossy(&cold.stderr)
    );
    let cold_json: serde_json::Value =
        serde_json::from_slice(&cold.stdout).expect("cold run prints JSON");
    let diagnostics = cold_json["diagnostics"]
        .as_array()
        .expect("diagnostics array");
    assert_eq!(diagnostics.len(), 1, "{cold_json:#}");
    let warning = &diagnostics[0];
    assert_eq!(warning["code"], "E7009");
    assert_eq!(warning["severity"], "warning");
    assert_eq!(warning["line"], 1);
    assert!(
        warning["file"]
            .as_str()
            .is_some_and(|f| f.ends_with("child_opt.beancount")),
        "E7009 points at the child's option line: {warning:#}"
    );
    assert!(
        cache_file.exists(),
        "a load whose only diagnostic is an option warning must write the cache"
    );

    // Warm run: a cache hit, with byte-identical diagnostics.
    let warm = check(&bin, &parent, &["--format", "json", "--verbose"]);
    assert!(warm.status.success());
    let warm_err = String::from_utf8_lossy(&warm.stderr);
    assert!(
        warm_err.contains("from cache"),
        "the second run must be a cache hit; stderr was:\n{warm_err}"
    );
    assert_eq!(
        String::from_utf8_lossy(&warm.stdout),
        String::from_utf8_lossy(&cold.stdout),
        "a cache hit must report exactly the diagnostics of the cold run"
    );

    // The text output, which the issue observed, agrees too.
    let text_hit = check(&bin, &parent, &["--verbose"]);
    let text_nocache = check(&bin, &parent, &["--no-cache"]);
    let text_hit_out = String::from_utf8_lossy(&text_hit.stdout);
    assert!(
        text_hit_out.contains("(from cache)"),
        "expected a cache hit: {text_hit_out}"
    );
    for out in [&text_hit, &text_nocache] {
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("warning[E7009]") && stdout.contains("1 warning"),
            "both runs report the E7009: {stdout}"
        );
    }
}

/// The parent without the option was already cached; it still is.
#[test]
fn test_check_without_option_warning_still_cached() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().expect("tempdir");
    write_issue_fixture(dir.path());
    let parent = dir.path().join("parent_noopt.beancount");

    assert!(check(&bin, &parent, &[]).status.success());
    let warm = check(&bin, &parent, &["--verbose"]);
    assert!(warm.status.success());
    assert!(
        String::from_utf8_lossy(&warm.stdout).contains("(from cache)"),
        "the second run must be a cache hit"
    );
}

/// A load error still blocks the cache write: `CacheEntry` archives no load
/// errors, so a hit would drop them.
#[test]
fn test_check_load_error_is_not_cached() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("broken.beancount");
    std::fs::write(
        &file,
        "option \"title\" \"T\"\ninclude \"missing.beancount\"\n2020-01-01 open Assets:Cash\n",
    )
    .expect("write ledger");

    let out = check(&bin, &file, &[]);
    assert!(!out.status.success(), "a missing include is an error");
    assert!(
        !dir.path().join(".broken.beancount.cache").exists(),
        "a load with errors must not write the cache"
    );
}

/// A cache hit ranks the files in beancount's breadth-first parse order as
/// the cold run does (#2936): the cache archives which file includes which,
/// so a tie between entries from different files breaks the same way.
/// `main` includes `x` then `y`, and `x` includes `z`; each opens an account
/// on line 2. bean-check 3.2.3 prints `(1 XXX, 1 YYY, 1 ZZZ, ...)`.
#[test]
fn test_check_cache_hit_keeps_the_breadth_first_file_order() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().expect("tempdir");
    let main = "include \"x.beancount\"\ninclude \"y.beancount\"\n\
        2024-01-01 open Assets:A\n2024-01-01 open Assets:Cash\n2024-01-01 open Equity:O\n\
        2024-02-01 * \"lot\"\n  Assets:A  10 STK {10 USD}\n  Assets:Cash  -100 USD\n\
        2024-02-02 * \"g\"\n  Assets:A:X  1 XXX\n  Assets:A:Y  1 YYY\n  Assets:A:Z  1 ZZZ\n\
        \x20 Equity:O  -1 XXX\n  Equity:O  -1 YYY\n  Equity:O  -1 ZZZ\n\
        2024-02-03 pad Assets:A Equity:O\n2024-02-10 balance Assets:A 11 STK\n";
    for (name, text) in [
        ("main.beancount", main),
        (
            "x.beancount",
            "include \"z.beancount\"\n2024-01-01 open Assets:A:X\n",
        ),
        ("y.beancount", "; y\n2024-01-01 open Assets:A:Y\n"),
        ("z.beancount", "; z\n2024-01-01 open Assets:A:Z\n"),
    ] {
        std::fs::write(dir.path().join(name), text).expect("write");
    }
    let path = dir.path().join("main.beancount");
    let expected = "(1 XXX, 1 YYY, 1 ZZZ, 10 STK {10 USD, 2024-02-01})";

    let cold = check(&bin, &path, &[]);
    let warm = check(&bin, &path, &["--verbose"]);
    let warm_out = String::from_utf8_lossy(&warm.stdout);
    assert!(
        warm_out.contains("(from cache)"),
        "the second run must be a cache hit: {warm_out}"
    );
    for (run, out) in [("cold", &cold), ("warm", &warm)] {
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains(expected),
            "{run} run lists the tied positions breadth first: {stdout}"
        );
    }
}
