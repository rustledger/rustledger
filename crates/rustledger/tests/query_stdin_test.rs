//! `rledger query FILE < query.bql` reads stdin whole, as ONE query (#2578).
//!
//! bean-query reads all of a piped or redirected stdin as one query
//! (`query = sys.stdin.read()` when stdin is not a TTY). rledger sent it to
//! the interactive shell, which ran it line by line, so a query spread over
//! lines failed (`SELECT account,` alone is a syntax error) or ran in pieces.

mod common;

use std::io::Write;
use std::process::{Command, Output, Stdio};

const LEDGER: &str = r#"2024-01-01 open Assets:Cash USD
2024-01-01 open Expenses:Food USD
2024-01-01 open Expenses:Rent USD

2024-01-02 * "lunch"
  Expenses:Food  12.50 USD
  Assets:Cash

2024-01-03 * "rent"
  Expenses:Rent  900.00 USD
  Assets:Cash
"#;

/// A query over three lines, with a comment: line by line, its first line
/// (`SELECT account,`) is a syntax error on its own.
const QUERY: &str = "SELECT account,\n       sum(position) AS total  /* per account */\nWHERE account ~ 'Expenses'\nGROUP BY account\nORDER BY account\n";

fn run(bin: &std::path::Path, dir: &std::path::Path, args: &[&str], stdin: &str) -> Output {
    let file = dir.join("ledger.beancount");
    std::fs::write(&file, LEDGER).expect("write ledger");
    let mut child = Command::new(bin)
        .arg("query")
        .arg("--no-cache")
        .arg(&file)
        .args(args)
        .env("HOME", dir)
        .env("XDG_CONFIG_HOME", dir)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run rledger query");
    child
        .stdin
        .take()
        .expect("stdin")
        .write_all(stdin.as_bytes())
        .expect("write stdin");
    child.wait_with_output().expect("wait")
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).expect("utf8")
}

#[test]
fn a_multi_line_query_on_stdin_runs_as_one_like_the_query_file() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().expect("tempdir");

    let piped = run(&bin, dir.path(), &[], QUERY);
    let piped_out = text(&piped.stdout);
    assert!(piped.status.success(), "{piped:?}");
    assert!(text(&piped.stderr).trim().is_empty(), "{piped:?}");

    let query_file = dir.path().join("query.bql");
    std::fs::write(&query_file, QUERY).expect("write query");
    let from_file = run(
        &bin,
        dir.path(),
        &["-F", query_file.to_str().expect("utf8 path")],
        "",
    );
    assert!(from_file.status.success(), "{from_file:?}");

    assert_eq!(piped_out, text(&from_file.stdout), "stdin and -F agree");
    // And it is the one result, not the shell's banner or a piece of it.
    let lines: Vec<&str> = piped_out.lines().collect();
    assert!(lines[0].starts_with("account"), "{piped_out}");
    let rows: Vec<String> = lines
        .iter()
        .filter(|l| l.starts_with("Expenses:"))
        .map(|l| l.split_whitespace().collect::<Vec<_>>().join(" "))
        .collect();
    assert_eq!(
        rows,
        ["Expenses:Food 12.50 USD", "Expenses:Rent 900.00 USD"],
        "{piped_out}"
    );
    assert!(!piped_out.contains("Ready with"), "{piped_out}");
}

#[test]
fn empty_stdin_runs_nothing() {
    // bean-query's shell does nothing with an empty command: no output, and
    // a clean exit. A comment alone is no query either.
    let bin = require_rledger!();
    let dir = tempfile::tempdir().expect("tempdir");
    for input in ["", "\n\n", "/* nothing to run */\n"] {
        let out = run(&bin, dir.path(), &[], input);
        assert!(out.status.success(), "{input:?}: {out:?}");
        assert_eq!(text(&out.stdout), "", "{input:?}");
        assert_eq!(text(&out.stderr), "", "{input:?}");
    }
}

#[test]
fn a_bad_query_on_stdin_fails_like_one_given_as_an_argument() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().expect("tempdir");
    let out = run(&bin, dir.path(), &[], "SELECT FROM WHERE\n");
    assert!(!out.status.success(), "{out:?}");
    assert!(text(&out.stderr).contains("parse"), "{out:?}");
}
