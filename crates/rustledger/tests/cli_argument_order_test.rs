//! `rledger report`'s file position, `rledger add` without a terminal, and
//! `rledger price -f`.

use std::path::Path;
use std::process::{Command, Output, Stdio};

fn rledger() -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_rledger"));
    // No user config: its default file or aliases must not leak in.
    cmd.env(
        "RLEDGER_CONFIG_DIR",
        std::env::temp_dir().join("rledger-no-config"),
    )
    .env("NO_COLOR", "1");
    cmd
}

const LEDGER: &str = "2024-01-01 open Assets:Cash USD\n\
                      2024-01-01 open Expenses:Food USD\n\n\
                      2024-01-02 * \"Lunch\"\n  \
                      Assets:Cash  -5.00 USD\n  \
                      Expenses:Food\n";

fn write_ledger(dir: &Path) -> String {
    let path = dir.join("ledger.beancount");
    std::fs::write(&path, LEDGER).unwrap();
    path.to_str().unwrap().to_string()
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// `rledger report balances FILE` was a usage error: the file had to come
/// before the report name. Both orders work now and give the same report,
/// with options anywhere.
#[test]
fn test_report_file_after_report_name_matches_file_first() {
    let dir = tempfile::tempdir().unwrap();
    let file = write_ledger(dir.path());
    let run = |args: &[&str]| {
        let output = rledger().arg("report").args(args).output().unwrap();
        assert!(
            output.status.success(),
            "{args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        stdout(&output)
    };
    let file_first = run(&[&file, "balances", "--no-pager"]);
    assert!(file_first.contains("Expenses:Food"), "{file_first}");
    for args in [
        vec!["balances", &file, "--no-pager"],
        vec!["--no-pager", "balances", &file],
        vec!["bal", &file, "--no-pager"],
    ] {
        let out = run(&args);
        if args.contains(&"bal") {
            assert!(out.contains("Expenses") || out.contains("Assets"), "{out}");
        } else {
            assert_eq!(out, file_first, "{args:?}");
        }
    }
    let json = run(&["balances", &file, "-f", "json", "-a", "Expenses"]);
    assert!(json.contains("\"account\": \"Expenses:Food\""), "{json}");
    assert!(!json.contains("Assets:Cash"), "{json}");
}

/// `rledger add` without `-y` appended when stdin was not a terminal: the
/// confirmation prompt read end-of-file as its default "yes". Now nothing
/// is written unless the answer is an explicit yes.
#[test]
fn test_add_without_yes_and_no_terminal_does_not_append() {
    let dir = tempfile::tempdir().unwrap();
    let file = write_ledger(dir.path());
    let quick = [
        "--quick",
        "Cafe",
        "Coffee",
        "Expenses:Food",
        "3.00 USD",
        "Assets:Cash",
    ];

    for piped in [false, true] {
        let stdin = if piped { Stdio::piped() } else { Stdio::null() };
        let mut child = rledger()
            .args(["add", &file])
            .args(quick)
            .stdin(stdin)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        if piped {
            // An empty line is not an answer either.
            use std::io::Write;
            child.stdin.take().unwrap().write_all(b"\n").unwrap();
        }
        let output = child.wait_with_output().unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(1), "{stderr}");
        assert!(stderr.contains("--yes"), "{stderr}");
        assert_eq!(std::fs::read_to_string(&file).unwrap(), LEDGER);
    }

    // An explicit answer still works, and `-y` appends without one.
    let mut child = rledger()
        .args(["add", &file])
        .args(quick)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    {
        use std::io::Write;
        child.stdin.take().unwrap().write_all(b"n\n").unwrap();
    }
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    assert!(stdout(&output).contains("Cancelled."));
    assert_eq!(std::fs::read_to_string(&file).unwrap(), LEDGER);

    let output = rledger()
        .args(["add", &file, "-y"])
        .args(quick)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        std::fs::read_to_string(&file)
            .unwrap()
            .contains("\"Cafe\" \"Coffee\"")
    );
}

/// `-f` is `--file` on `price` (every other command uses it for
/// `--format`). It stays, since `price` has no `--format`; written as a
/// format, it now says why it failed.
#[test]
fn test_price_f_named_like_a_format_explains_itself() {
    let dir = tempfile::tempdir().unwrap();
    let output = rledger()
        .current_dir(dir.path())
        .args(["price", "-f", "json", "--dry-run"])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{stderr}");
    assert!(stderr.contains("-f is --file"), "{stderr}");
}
