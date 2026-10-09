//! The `rledger query` shell keeps one executor for the session (#2518).
//!
//! A table one statement creates is there for the next, as in bean-query's
//! shell, whose connection lives as long as the shell. The shell built a new
//! executor for every statement, so `CREATE TABLE t AS SELECT ...` followed
//! by `SELECT ... FROM t` failed with "table 't' does not exist", and no
//! user surface could reach a created table at all.

mod common;

use std::io::Write;
use std::process::{Command, Stdio};

const LEDGER: &str = r#"2024-01-01 open Assets:E
2024-01-01 open Assets:C
2024-01-01 open Assets:B X "FIFO"

2024-01-02 * "priced"
  Assets:E  10 EUR @ 1.10 USD
  Assets:C

2024-01-03 * "total lot"
  Assets:B  3 X {{500 USD}}
  Assets:C
"#;

/// Feed `input` to the shell line by line (stdin is not a terminal, so the
/// shell reads it as typed lines) and return (stdout, stderr).
fn shell(bin: &std::path::Path, input: &str) -> (String, String) {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("ledger.beancount");
    std::fs::write(&file, LEDGER).expect("write ledger");
    let mut child = Command::new(bin)
        .arg("query")
        .arg("--no-cache")
        .arg(&file)
        .env("HOME", dir.path())
        .env("XDG_CONFIG_HOME", dir.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run rledger query");
    child
        .stdin
        .take()
        .expect("stdin")
        .write_all(input.as_bytes())
        .expect("write the session");
    let out = child.wait_with_output().expect("wait");
    assert!(out.status.success(), "the shell exits cleanly: {out:?}");
    (
        String::from_utf8(out.stdout).expect("utf8"),
        String::from_utf8(out.stderr).expect("utf8"),
    )
}

#[test]
fn a_created_table_is_there_for_the_next_statement() {
    let bin = require_rledger!();
    let (stdout, stderr) = shell(
        &bin,
        "CREATE TABLE t AS SELECT account, position WHERE account != 'Assets:C'\n\
         SELECT account, weight(position), cost(position) FROM t ORDER BY account\n",
    );
    assert!(!stderr.contains("does not exist"), "{stderr}");
    assert!(stderr.trim().is_empty(), "no error: {stderr}");
    assert!(stdout.contains("Created table 't'"), "{stdout}");
    // And it answers from the posting (#2441): the priced posting weighs
    // 11.00 USD, the `{{500 USD}}` lot exactly 500 USD.
    let row = |account: &str| {
        stdout
            .lines()
            .find(|l| l.starts_with(account))
            .unwrap_or_else(|| panic!("no {account} row: {stdout}"))
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    // (Rendered at the ledger's USD precision, two places.)
    assert_eq!(row("Assets:E"), "Assets:E 11.00 USD 10 EUR");
    assert_eq!(row("Assets:B"), "Assets:B 500.00 USD 500.00 USD");
}

/// A table lives as long as the session: creating it again is refused, and
/// inserting into it adds to the one created.
#[test]
fn the_table_lives_for_the_session() {
    let bin = require_rledger!();
    let (stdout, stderr) = shell(
        &bin,
        "CREATE TABLE t (name)\n\
         INSERT INTO t VALUES ('a')\n\
         INSERT INTO t VALUES ('b')\n\
         CREATE TABLE t (name)\n\
         SELECT count(*) AS n FROM t\n",
    );
    assert!(stderr.contains("table 't' already exists"), "{stderr}");
    let n = stdout
        .lines()
        .skip_while(|l| !l.trim_start().starts_with('n'))
        .nth(2)
        .unwrap_or_else(|| panic!("no count row: {stdout}"));
    assert_eq!(n.trim(), "2", "{stdout}");
}
