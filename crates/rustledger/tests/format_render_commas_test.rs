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
    assert!(
        out.status.success(),
        "rledger {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
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

/// The reporter's actual shape: ONE hyperinflated commodity declares grouping,
/// with no global option, so everything else is untouched (#1892).
///
/// Also exercises the metadata path for `TRUE`. An uppercase bare word's token
/// classification depends on context, so all the spellings a ledger author
/// might write are accepted — silently ignoring the declaration is the failure
/// mode that makes a display option look broken.
#[test]
fn a_single_commodity_can_opt_in_via_metadata() {
    let bin = require_rledger!();
    for spelling in ["TRUE", "\"TRUE\"", "true"] {
        let dir = tempfile::Builder::new()
            .prefix("fmt-opt-in-")
            .tempdir()
            .expect("tempdir");
        let root = dir.path().join("main.beancount");
        let inc = dir.path().join("p.beancount");

        // Built line-by-line on purpose: a multi-line literal with `\`
        // continuations silently bakes the source indentation into the fixture,
        // which indents the DATE lines and makes the file a parse error.
        let root_text = [
            "2020-01-01 commodity IQD".to_string(),
            format!("  render_commas: {spelling}"),
            "2020-01-01 open Assets:Local".to_string(),
            "2020-01-01 open Assets:Dollars".to_string(),
            "include \"p.beancount\"".to_string(),
        ]
        .join("\n")
            + "\n";
        let inc_text = [
            "2020-01-02 * \"local\"",
            "  Assets:Local     1234567.89 IQD",
            "  Assets:Local    -1234567.89 IQD",
            "2020-01-03 * \"dollars\"",
            "  Assets:Dollars   1234567.89 USD",
            "  Assets:Dollars  -1234567.89 USD",
        ]
        .join("\n")
            + "\n";
        std::fs::write(&root, root_text).expect("write root");
        std::fs::write(&inc, inc_text).expect("write include");

        let out = run(
            bin.as_ref(),
            &[
                "format",
                "--ledger",
                root.to_str().expect("utf8"),
                inc.to_str().expect("utf8"),
            ],
        );
        assert!(
            out.contains("1,234,567.89 IQD"),
            "`render_commas: {spelling}` must opt IQD in: {out}"
        );
        assert!(
            out.contains("1234567.89 USD") && !out.contains("1,234,567.89 USD"),
            "USD declared nothing and the global default is off: {out}"
        );
    }
}

/// Grouping must not change a single VALUE.
///
/// Formatting with grouping and then formatting the result WITHOUT it must
/// reproduce the plain-formatted original byte for byte. That is a much
/// stronger check than "the output still parses": it catches a grouped numeral
/// that re-reads as a different number, which is the one way this feature could
/// corrupt a ledger.
#[test]
fn grouping_round_trips_without_changing_any_value() {
    let bin = require_rledger!();
    let dir = tempfile::Builder::new()
        .prefix("fmt-roundtrip-")
        .tempdir()
        .expect("tempdir");
    let root = dir.path().join("main.beancount");
    let inc = dir.path().join("p.beancount");

    // Magnitudes and shapes chosen to straddle every group boundary, plus a
    // trailing decimal point and a 28-digit value at the `Decimal` ceiling.
    let vals = [
        "0",
        "1",
        "12",
        "123",
        "1234",
        "12345",
        "123456",
        "1234567",
        "1000",
        "1000000",
        "0.5",
        "0.05",
        "1.0",
        "1.",
        "123456789.123456789",
        "1234567890123456789012345678",
        "999",
        "1000.001",
        "10.10",
        "100000000",
    ];
    let mut body = String::new();
    for (i, v) in vals.iter().enumerate() {
        let day = (i % 27) + 2;
        body.push_str(&format!(
            "2020-01-{day:02} * \"v{i}\"\n  Assets:A   {v} USD\n  Assets:B  -{v} USD\n"
        ));
        body.push_str(&format!(
            "2020-02-{day:02} balance Assets:A 0.00 ~ {v} USD\n"
        ));
        body.push_str(&format!("2020-03-{day:02} custom \"c\" {v} USD\n"));
    }
    std::fs::write(&inc, &body).expect("write include");
    std::fs::write(
        &root,
        "option \"render_commas\" \"TRUE\"\n         2020-01-01 open Assets:A\n         2020-01-01 open Assets:B\n         include \"p.beancount\"\n",
    )
    .expect("write root");

    let plain = run(bin.as_ref(), &["format", inc.to_str().expect("utf8")]);
    let grouped = run(
        bin.as_ref(),
        &[
            "format",
            "--ledger",
            root.to_str().expect("utf8"),
            inc.to_str().expect("utf8"),
        ],
    );
    assert!(
        grouped.contains(','),
        "the fixture must actually exercise grouping"
    );

    // Ungroup the grouped output and compare to the plain baseline.
    let regrouped = dir.path().join("grouped.beancount");
    std::fs::write(&regrouped, grouped.as_bytes()).expect("write grouped");
    let ungrouped = run(bin.as_ref(), &["format", regrouped.to_str().expect("utf8")]);
    assert_eq!(
        ungrouped, plain,
        "group-then-ungroup must reproduce the original values exactly"
    );
}
