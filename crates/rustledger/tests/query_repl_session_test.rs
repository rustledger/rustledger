//! The `rledger query` shell keeps one executor for the session (#2518).
//!
//! A table one statement creates is there for the next, as in bean-query's
//! shell, whose connection lives as long as the shell. The shell built a new
//! executor for every statement, so `CREATE TABLE t AS SELECT ...` followed
//! by `SELECT ... FROM t` failed with "table 't' does not exist", and no
//! user surface could reach a created table at all.
//!
//! The shell runs only on a terminal: a piped stdin is one query, read whole,
//! as bean-query reads it (#2578). So these drive the shell through a
//! pseudo-terminal, util-linux `script`, typing each statement once the
//! prompt for it is up. Linux only, which is where this crate's tests run.
#![cfg(target_os = "linux")]

mod common;

use std::io::{Read, Write};
use std::process::{Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

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

const PROMPT: &str = "beanquery> ";

/// Single-quote `s` for `sh -c`.
fn sh_quote(s: &str) -> String {
    format!("'{}'", s.replace('\'', "'\\''"))
}

/// Type `input` into the shell on a terminal, one line per prompt, then
/// `.quit`, and return (what the terminal showed, stderr).
///
/// Each line is written only once the shell's prompt for it is showing:
/// line editing reads the terminal raw from then on, and typing ahead of it
/// can be discarded when it switches modes.
fn shell(bin: &std::path::Path, input: &str) -> (String, String) {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("ledger.beancount");
    std::fs::write(&file, LEDGER).expect("write ledger");
    let err_file = dir.path().join("stderr.txt");
    let command = format!(
        "exec {} query --no-cache {} 2>{}",
        sh_quote(bin.to_str().expect("utf8 path")),
        sh_quote(file.to_str().expect("utf8 path")),
        sh_quote(err_file.to_str().expect("utf8 path")),
    );
    // `script` gives the shell a pseudo-terminal; a missing `script` fails
    // the test rather than skipping it.
    let mut child = Command::new("script")
        .args(["-q", "-e", "-c", &command, "/dev/null"])
        .env("HOME", dir.path())
        .env("XDG_CONFIG_HOME", dir.path())
        .env("TERM", "dumb")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run `script` (util-linux) to give the shell a terminal");
    let shown = Arc::new(Mutex::new(Vec::<u8>::new()));
    let mut stdout = child.stdout.take().expect("stdout");
    let reader = {
        let shown = Arc::clone(&shown);
        std::thread::spawn(move || {
            let mut buf = [0u8; 4096];
            while let Ok(n) = stdout.read(&mut buf) {
                if n == 0 {
                    break;
                }
                shown.lock().expect("lock").extend_from_slice(&buf[..n]);
            }
        })
    };
    let prompts = || {
        String::from_utf8_lossy(&shown.lock().expect("lock"))
            .matches(PROMPT)
            .count()
    };
    let mut stdin = child.stdin.take().expect("stdin");
    for (i, line) in input.lines().chain([".quit"]).enumerate() {
        let deadline = Instant::now() + Duration::from_secs(60);
        while prompts() <= i {
            assert!(
                Instant::now() < deadline,
                "no prompt for line {i}: {}",
                String::from_utf8_lossy(&shown.lock().expect("lock"))
            );
            std::thread::sleep(Duration::from_millis(20));
        }
        stdin
            .write_all(format!("{line}\r").as_bytes())
            .expect("type a line");
        stdin.flush().expect("flush");
    }
    let status = child.wait().expect("wait");
    drop(stdin);
    reader.join().expect("reader");
    assert!(status.success(), "the shell exits cleanly: {status:?}");
    let shown = String::from_utf8(shown.lock().expect("lock").clone()).expect("utf8");
    let stderr = std::fs::read_to_string(&err_file).unwrap_or_default();
    (shown.replace('\r', ""), stderr)
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
