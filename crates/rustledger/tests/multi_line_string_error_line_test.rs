//! `rledger check` reports a syntax error at a multi-line string on the line
//! the string ends, as bean-check 3.2.3 does (#2994), in its JSON output and
//! in its text header. The LSP's line is pinned to the same span lookup in
//! `rustledger-lsp/tests/multi_line_string_error_line.rs`.

use std::process::Command;

#[test]
fn test_check_multi_line_string_error_is_on_its_last_line() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("ledger.beancount");
    // The issue's fourth row. bean-check 3.2.3: errors on lines 4 and 5.
    std::fs::write(
        &path,
        "2024-01-01 open Assets:A\noption \"title\" \"a\nb\" \"c\nd\"\n  2024-02-30 5\n",
    )
    .expect("write");
    let path = path.to_str().expect("utf8");
    let bin = env!("CARGO_BIN_EXE_rledger");

    let out = Command::new(bin)
        .args(["check", "--format", "json", path])
        .output()
        .expect("run check");
    assert!(!out.status.success(), "the ledger has parse errors");
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).expect("JSON output");
    let lines: Vec<u64> = json["diagnostics"]
        .as_array()
        .expect("diagnostics")
        .iter()
        .filter(|d| d["phase"] == "parse")
        .map(|d| d["line"].as_u64().expect("line"))
        .collect();
    assert_eq!(lines, [4, 5], "{json}");

    let out = Command::new(bin)
        .args(["check", path])
        .output()
        .expect("run check");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(text.contains(&format!("{path}:4:")), "{text}");
}
