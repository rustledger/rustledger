//! CLI output edges: a closed stdout pipe, and the commands `doctor` tells
//! the user to run.

use std::path::Path;
use std::process::{Command, Stdio};

fn rledger() -> Command {
    Command::new(env!("CARGO_BIN_EXE_rledger"))
}

fn write_ledger(dir: &Path, text: &str) -> String {
    let path = dir.join("ledger.beancount");
    std::fs::write(&path, text).unwrap();
    path.to_str().unwrap().to_string()
}

/// Run `rledger <args>` with stdout a pipe whose reader is already gone,
/// as `rledger ... | head` is once `head` exits. Returns (exit code,
/// stderr).
fn run_into_closed_pipe(args: &[&str]) -> (Option<i32>, String) {
    let (reader, writer) = std::io::pipe().expect("pipe");
    drop(reader);
    let output = rledger()
        .args(args)
        .stdout(Stdio::from(writer))
        .stderr(Stdio::piped())
        .output()
        .expect("spawn rledger");
    (
        output.status.code(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// `rledger explain | head` and `rledger doctor list-options | head` printed
/// `error: Broken pipe (os error 32)` and exited 1. A closed pipe is not an
/// error, for any command: they all exit 0 silently, as `check` and
/// `query` already did.
#[test]
fn test_main_broken_pipe_is_not_an_error_for_any_command() {
    let dir = tempfile::tempdir().unwrap();
    let file = write_ledger(
        dir.path(),
        "2024-01-01 open Assets:Cash USD\n2024-01-01 open Expenses:Food USD\n",
    );
    for args in [
        vec!["explain"],
        vec!["explain", "E2001"],
        vec!["doctor", "list-options"],
        vec!["doctor", "context", &file, "1"],
        vec!["check", &file],
        vec!["report", &file, "accounts", "--no-pager"],
    ] {
        let (code, stderr) = run_into_closed_pipe(&args);
        assert!(
            !stderr.contains("Broken pipe") && !stderr.contains("error"),
            "{args:?}: {stderr}"
        );
        assert_eq!(code, Some(0), "{args:?}: {stderr}");
    }
}

/// `doctor roundtrip` told the user to run `rledger format --diff`, which
/// is a usage error (`--diff` requires `--check`). The command it suggests
/// must run.
#[test]
fn test_doctor_roundtrip_suggested_format_command_runs() {
    let dir = tempfile::tempdir().unwrap();
    // Unaligned amounts, so `format` would reflow the file.
    let file = write_ledger(
        dir.path(),
        "2024-01-01 open Assets:Cash USD\n\
         2024-01-01 open Expenses:Food USD\n\n\
         2024-01-02 * \"Lunch\"\n  Assets:Cash -5 USD\n  Expenses:Food    5 USD\n",
    );
    let output = rledger()
        .args(["doctor", "roundtrip", &file])
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let suggestion = stdout
        .split("run `")
        .nth(1)
        .and_then(|rest| rest.split('`').next())
        .unwrap_or_else(|| panic!("no suggested command in:\n{stdout}"));
    let mut words = suggestion.split_whitespace();
    assert_eq!(words.next(), Some("rledger"), "{suggestion}");
    let output = rledger().args(words).arg(&file).output().unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    // 1 = the file would change; 2 would be a usage error.
    assert_eq!(output.status.code(), Some(1), "`{suggestion}`: {stderr}");
    let shown = format!("{}{stderr}", String::from_utf8_lossy(&output.stdout));
    assert!(shown.contains("+++"), "the diff is shown: {shown}");
}
