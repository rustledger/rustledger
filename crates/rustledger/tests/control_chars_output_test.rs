//! Control characters in ledger strings on output (#2538).
//!
//! Human-readable output escapes them (`\u{1b}`), so a narration carrying an
//! escape sequence cannot act on the reader's terminal: `check` diagnostics
//! (message and source snippet), query tables, `report` text. Output that is
//! data keeps them: CSV, `PRINT`, `rledger format`; JSON keeps the value and
//! escapes the characters as `\uXXXX`. `extract` neutralizes them in what it
//! imports, and `rledger lint control-chars` finds them.

mod common;

use std::path::Path;
use std::process::Command;

/// OSC 52 (write the clipboard), a CSI color, a C1 CSI, DEL and a bidi
/// override: what a hostile merchant name could carry.
const HOSTILE: &str = "\u{1b}]52;c;aGk=\u{7}\u{1b}[31mred\u{9b}2J\u{7f}\u{202e}x";

/// A ledger with [`HOSTILE`] in a payee, a narration and a metadata value,
/// and an unopened account so `check` reports the transaction.
fn ledger() -> String {
    format!(
        "2024-01-01 open Assets:Cash\n\
         2024-01-02 * \"{HOSTILE}\" \"lunch {HOSTILE}\"\n  \
         memo: \"m {HOSTILE}\"\n  \
         Assets:Cash  -1.00 USD\n  \
         Expenses:Unopened\n"
    )
}

/// Whether `text` holds a character a terminal would act on, other than the
/// line breaks and tabs of ordinary output.
fn has_raw_control(text: &str) -> bool {
    text.chars()
        .any(|c| !matches!(c, '\n' | '\t') && rustledger_core::format::is_display_unsafe(c))
}

fn run(bin: &Path, args: &[&str]) -> (String, String) {
    let output = Command::new(bin)
        .args(args)
        .env("NO_COLOR", "1")
        .output()
        .expect("run rledger");
    (
        String::from_utf8(output.stdout).expect("utf-8 stdout"),
        String::from_utf8(output.stderr).expect("utf-8 stderr"),
    )
}

fn write_ledger(dir: &Path) -> String {
    let path = dir.join("ledger.beancount");
    std::fs::write(&path, ledger()).unwrap();
    path.to_str().unwrap().to_string()
}

#[test]
fn check_escapes_messages_and_snippets() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let path = write_ledger(dir.path());
    let (out, err) = run(&bin, &["check", &path]);
    let all = format!("{out}{err}");
    assert!(all.contains("Expenses:Unopened"), "{all}");
    assert!(!has_raw_control(&all), "raw control character in:\n{all:?}");
    // The snippet shows the line, escaped visibly.
    assert!(all.contains("\\u{1b}]52;c;aGk=\\u{7}"), "{all}");
    assert!(all.contains("\\u{9b}2J\\u{7f}\\u{202e}x"), "{all}");
}

#[test]
fn check_json_keeps_the_value_and_escapes_c1() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    // The control characters in a message: a missing document's path.
    let path = dir.path().join("ledger.beancount");
    std::fs::write(
        &path,
        format!(
            "2024-01-01 open Assets:Cash\n\
             2024-01-02 document Assets:Cash \"missing{HOSTILE}.pdf\"\n"
        ),
    )
    .unwrap();
    let (out, _) = run(&bin, &["check", "-f", "json", path.to_str().unwrap()]);
    assert!(!has_raw_control(&out), "raw control character in:\n{out:?}");
    let json: serde_json::Value = serde_json::from_str(&out).expect("valid JSON");
    let messages: Vec<&str> = json["diagnostics"]
        .as_array()
        .expect("diagnostics")
        .iter()
        .filter_map(|d| d["message"].as_str())
        .collect();
    assert!(
        messages.iter().any(|m| m.contains(HOSTILE)),
        "JSON keeps the message as it is: {messages:?}"
    );
}

#[test]
fn query_table_escapes_and_data_formats_keep_the_value() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let path = write_ledger(dir.path());
    let q = "SELECT payee, narration, entry_meta('memo') WHERE account ~ 'Cash'";

    let (table, _) = run(&bin, &["query", &path, q]);
    assert!(!has_raw_control(&table), "{table:?}");
    assert!(table.contains("\\u{1b}[31mred\\u{9b}2J"), "{table}");

    let (csv, _) = run(&bin, &["query", "-f", "csv", &path, q]);
    assert!(csv.contains(HOSTILE), "CSV keeps the value: {csv:?}");

    let (json, _) = run(&bin, &["query", "-f", "json", &path, q]);
    assert!(
        !json.contains('\u{9b}') && !json.contains('\u{7f}'),
        "{json:?}"
    );
    let value: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
    assert_eq!(value["rows"][0][0], HOSTILE, "{json}");
}

/// `PRINT` and `rledger format` write ledger text, which must parse back to
/// the same strings: beancount has no escape for these characters, so they
/// are written as they are.
#[test]
fn print_and_format_round_trip_byte_identically() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let path = write_ledger(dir.path());

    let (formatted, err) = run(&bin, &["format", &path]);
    assert!(
        formatted.contains(&format!("\"{HOSTILE}\" \"lunch {HOSTILE}\"")),
        "{formatted:?} {err}"
    );
    assert!(
        formatted.contains(&format!("memo: \"m {HOSTILE}\"")),
        "{formatted:?}"
    );

    let (printed, _) = run(&bin, &["query", &path, "PRINT"]);
    assert!(
        printed.contains(&format!("\"{HOSTILE}\" \"lunch {HOSTILE}\"")),
        "{printed:?}"
    );
    assert!(
        printed.contains(&format!("memo: \"m {HOSTILE}\"")),
        "{printed:?}"
    );
}

#[test]
fn report_text_escapes_and_csv_keeps_the_value() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let path = write_ledger(dir.path());

    let (text, _) = run(&bin, &["report", "--no-pager", &path, "journal"]);
    assert!(!has_raw_control(&text), "{text:?}");
    assert!(text.contains("lunch \\u{1b}]52;c;aGk="), "{text}");

    let (csv, _) = run(&bin, &["report", "-f", "csv", &path, "journal"]);
    assert!(csv.contains(&format!("lunch {HOSTILE}")), "{csv:?}");

    let (json, _) = run(&bin, &["report", "-f", "json", &path, "journal"]);
    assert!(!has_raw_control(&json), "{json:?}");
    let value: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
    assert_eq!(value[0]["narration"], format!("lunch {HOSTILE}"), "{json}");
}

#[test]
fn extract_neutralizes_imported_text_and_warns() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let csv = dir.path().join("statement.csv");
    std::fs::write(
        &csv,
        format!(
            "Date,Description,Amount\n\
             2024-01-02,\"SHOP{HOSTILE}\",-4.00\n\
             2024-01-03,\"two\nlines\",-1.00\n\
             2024-01-04,Plain,-2.00\n"
        ),
    )
    .unwrap();
    let output = Command::new(&bin)
        .arg("extract")
        .arg(&csv)
        .args(["-a", "Assets:Bank", "--currency", "USD"])
        .output()
        .expect("run extract");
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(output.status.success(), "stderr: {stderr}");
    assert!(!has_raw_control(&stdout), "{stdout:?}");
    assert!(
        stdout.contains(
            "\"SHOP\u{fffd}]52;c;aGk=\u{fffd}\u{fffd}[31mred\u{fffd}2J\u{fffd}\u{fffd}x\""
        ),
        "{stdout}"
    );
    // A newline in a cell becomes a space.
    assert!(stdout.contains("\"two lines\""), "{stdout}");
    // One warning per affected row, naming the row and the field.
    let warned: Vec<&str> = stderr
        .lines()
        .filter(|l| l.contains("control characters in"))
        .collect();
    assert_eq!(warned.len(), 2, "stderr: {stderr}");
    assert!(warned[0].contains("Row 1"), "{stderr}");
    assert!(warned[1].contains("Row 2"), "{stderr}");
}

#[test]
fn lint_control_chars_finds_them() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let path = write_ledger(dir.path());
    let (out, err) = run(&bin, &["lint", "control-chars", &path]);
    assert!(!has_raw_control(&out), "{out:?}");
    for field in ["payee", "narration", "metadata \"memo\""] {
        assert!(
            out.contains(&format!(":2: control character in {field}:")),
            "{field}: {out}{err}"
        );
    }
}

/// #2714: every `rledger doctor` subcommand's text is escaped: the source
/// lines `context` shows and the narrations `region` prints.
#[test]
fn doctor_text_escapes() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let path = write_ledger(dir.path());
    for args in [
        vec!["doctor", "context", &path, "2"],
        vec!["doctor", "region", &path, "1", "6"],
    ] {
        let (out, err) = run(&bin, &args);
        let all = format!("{out}{err}");
        assert!(all.contains("lunch"), "{args:?}: {all}");
        assert!(!has_raw_control(&all), "{args:?}: raw control in:\n{all:?}");
        assert!(all.contains("\\u{1b}]52;c;aGk=\\u{7}"), "{args:?}: {all}");
    }
}

/// #2714: a narration carrying a newline prints as one line in `doctor`:
/// the newline is escaped too, where the doctor's writer keeps line breaks.
#[test]
fn doctor_narrations_stay_one_line() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("ledger.beancount");
    // The `\\n` in the source decodes to a newline in the narration.
    std::fs::write(
        &path,
        format!(
            "2024-01-01 open Assets:Cash\n\
             2024-01-01 open Expenses:Food\n\
             2024-01-02 * \"lunch\\n{HOSTILE}\" ^trip\n  \
               Assets:Cash  -5.00 USD\n  \
               Expenses:Food\n"
        ),
    )
    .unwrap();
    let path = path.to_str().unwrap();
    for args in [
        vec!["doctor", "region", path, "1", "20"],
        vec!["doctor", "linked", path, "^trip"],
    ] {
        let (out, err) = run(&bin, &args);
        let all = format!("{out}{err}");
        assert!(all.contains("lunch"), "{args:?}: {all}");
        assert!(all.contains("lunch\\u{a}"), "{args:?}: {all}");
        assert!(
            !all.contains("lunch\n"),
            "{args:?}: the narration split the line:\n{all:?}"
        );
        assert!(!has_raw_control(&all), "{args:?}: raw control in:\n{all:?}");
    }
}

/// #2714: `rledger explain` echoes an unknown code escaped.
#[test]
fn explain_escapes_the_code_it_echoes() {
    let bin = require_rledger!();
    let (out, err) = run(&bin, &["explain", HOSTILE]);
    let all = format!("{out}{err}");
    assert!(all.contains("unknown error code"), "{all}");
    assert!(!has_raw_control(&all), "raw control in:\n{all:?}");
    assert!(all.contains("\\u{9b}2J\\u{7f}\\u{202e}x"), "{all}");
}

/// #2714: `rledger add` escapes the preview it shows, and `--dry-run`, which
/// prints the transaction as it would be written, keeps it as it is.
#[test]
fn add_preview_escapes_and_dry_run_keeps_the_value() {
    let bin = require_rledger!();
    let dir = tempfile::tempdir().unwrap();
    let path = write_ledger(dir.path());
    let quick = [
        "--quick",
        HOSTILE,
        "lunch",
        "Expenses:Food",
        "5.00 USD",
        "Assets:Cash",
    ];
    // The preview, answered "no".
    let mut child = Command::new(&bin)
        .args(["add", &path, "--no-completion"])
        .args(quick)
        .env("NO_COLOR", "1")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("run rledger add");
    {
        use std::io::Write;
        child.stdin.take().unwrap().write_all(b"n\n").unwrap();
    }
    let output = child.wait_with_output().unwrap();
    let out = String::from_utf8(output.stdout).unwrap();
    assert!(
        out.contains("Preview:") && out.contains("Cancelled."),
        "{out}"
    );
    assert!(!has_raw_control(&out), "raw control in:\n{out:?}");
    assert!(out.contains("\\u{1b}]52;c;aGk=\\u{7}"), "{out}");
    // The ledger is untouched.
    assert_eq!(std::fs::read_to_string(&path).unwrap(), ledger());

    // `--dry-run` is the text `add` would append: the payee as it is.
    let (out, _) = run(
        &bin,
        &[&["add", &path, "--dry-run"][..], &quick[..]].concat(),
    );
    assert!(out.contains(HOSTILE), "{out:?}");
}
