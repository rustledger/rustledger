//! `rledger format --ledger` reads display declarations from a ledger root and
//! applies them to the files it formats (#1892).
//!
//! The declarations live in the root while the postings usually live in an
//! `include`d file, so a per-file formatter cannot see them. Naming the root is
//! deterministic regardless of which files are listed or in what order — which
//! matters because pre-commit hooks pass whichever files changed.

mod common;

use std::io::Write;
use std::process::Command;

/// Write a two-file ledger: a root carrying the declarations, and an included
/// file carrying the postings. Returns (dir, root, included).
fn ledger() -> (tempfile::TempDir, String, String) {
    let dir = tempfile::Builder::new()
        .prefix("fmt-commas-")
        .tempdir()
        .expect("tempdir");
    let root = dir.path().join("main.beancount");
    let inc = dir.path().join("postings.beancount");
    let mut f = std::fs::File::create(&root).expect("create root");
    f.write_all(
        b"option \"operating_currency\" \"USD\"\n\
          option \"render_commas\" \"TRUE\"\n\
          \n\
          2020-01-01 commodity USD\n\
          \x20 render_commas: FALSE\n\
          2020-01-01 commodity IQD\n\
          \n\
          2020-01-01 open Assets:Local\n\
          2020-01-01 open Assets:Dollars\n\
          include \"postings.beancount\"\n",
    )
    .expect("write root");
    let mut g = std::fs::File::create(&inc).expect("create include");
    g.write_all(
        b"2020-01-02 * \"local\"\n\
          \x20 Assets:Local    1234567.89 IQD\n\
          \x20 Assets:Local   -1234567.89 IQD\n\
          2020-01-03 * \"dollars\"\n\
          \x20 Assets:Dollars  1234567.89 USD\n\
          \x20 Assets:Dollars -1234567.89 USD\n",
    )
    .expect("write include");
    (
        dir,
        root.to_str().expect("utf8").to_owned(),
        inc.to_str().expect("utf8").to_owned(),
    )
}

fn run(bin: &std::path::Path, args: &[&str]) -> String {
    let out = Command::new(bin).args(args).output().expect("run rledger");
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// Without `--ledger`, output is exactly what it has always been. Every
/// existing invocation and CI gate is unaffected.
#[test]
fn without_the_flag_output_is_unchanged() {
    let bin = require_rledger!();
    let (_d, _root, inc) = ledger();
    let out = run(bin.as_ref(), &["format", &inc]);
    assert!(
        !out.contains(','),
        "no declarations in scope means no separators: {out}"
    );
}

/// With `--ledger`, the ROOT's declarations reach the INCLUDED file — the case
/// a per-file formatter fundamentally cannot serve. And the per-commodity
/// override wins over the ledger-wide default.
#[test]
fn the_root_declarations_reach_an_included_file() {
    let bin = require_rledger!();
    let (_d, root, inc) = ledger();
    let out = run(bin.as_ref(), &["format", "--ledger", &root, &inc]);
    assert!(
        out.contains("1,234,567.89 IQD"),
        "IQD takes the ledger-wide default: {out}"
    );
    assert!(
        out.contains("1234567.89 USD") && !out.contains("1,234,567.89 USD"),
        "USD declared `render_commas: FALSE` and must stay bare: {out}"
    );
}

/// The grouped file is CANONICAL for that ledger: formatting is idempotent and
/// `--check` accepts it. Without this the option would leave every file
/// permanently "unformatted" — the trap the reporter identified.
#[test]
fn grouped_output_is_canonical_and_check_accepts_it() {
    let bin = require_rledger!();
    let (_d, root, inc) = ledger();

    let once = run(bin.as_ref(), &["format", "--ledger", &root, &inc]);
    std::fs::write(&inc, once.as_bytes()).expect("rewrite include");
    let twice = run(bin.as_ref(), &["format", "--ledger", &root, &inc]);
    assert_eq!(once, twice, "grouped formatting must be idempotent");

    let status = Command::new(&bin)
        .args(["format", "--check", "--ledger", &root, &inc])
        .status()
        .expect("run --check");
    assert!(
        status.success(),
        "a grouped file must be canonical for a ledger that asked for grouping"
    );

    // And the grouped source still loads: the formatter may not emit text its
    // own parser rejects.
    let status = Command::new(&bin)
        .args(["check", "--no-cache", &root])
        .status()
        .expect("run check");
    assert!(
        status.success(),
        "grouped source must still parse and check"
    );
}
