//! `rledger check` reports exactly the diagnostics the FFI component's
//! `load`, `load-file`, `validate` and `validate-file` report (#2929, #2935).
//!
//! The CLI side of the drift guard: the ledgers in `ffi_check_parity/cases.rs`
//! must give exactly their `diagnostics` here, as they must through the
//! component (`rustledger-ffi-component`'s `check_parity` tests and the wasip2
//! harness in `rustledger-ffi-component-tests`).

mod common;

include!("ffi_check_parity/cases.rs");

use std::process::Command;

/// One diagnostic as compared: code, severity, file (relative to the case's
/// directory), line, message.
type Row = (String, String, Option<String>, Option<u32>, String);

#[test]
fn test_check_reports_the_ffi_parity_diagnostics() {
    let bin = require_rledger!();
    for case in CHECK_PARITY_CASES {
        let dir = tempfile::tempdir().expect("tempdir");
        for (path, text) in case.files {
            std::fs::write(dir.path().join(path), text).expect("write");
        }
        // The entry by its relative name, from its directory: `check` names a
        // diagnostic with no location by the path it was given (this one,
        // at line 1), and a located one by the loader's absolute path, so
        // the two cannot be confused.
        let out = Command::new(&bin)
            .current_dir(dir.path())
            .args(["check", "--format", "json", "--no-cache"])
            .arg(case.entry)
            .output()
            .expect("run rledger check");
        assert_eq!(
            out.status.code(),
            Some(1),
            "{}: stderr {}",
            case.name,
            String::from_utf8_lossy(&out.stderr)
        );
        let json: serde_json::Value = serde_json::from_slice(&out.stdout).expect("JSON output");
        let mut got: Vec<Row> = json["diagnostics"]
            .as_array()
            .expect("diagnostics")
            .iter()
            .map(|d| {
                let file = d["file"].as_str().expect("file");
                let line = u32::try_from(d["line"].as_u64().expect("line")).expect("u32");
                let code = d["code"].as_str().expect("code").to_string();
                // A diagnostic with no location: `check` prints its stand-in,
                // the entry as given, at line 1 (see `cases.rs`).
                let (file, line) = if file == case.entry {
                    assert!(line == 1, "{}: {code} at {file}:{line}", case.name);
                    (None, None)
                } else {
                    let relative = std::path::Path::new(file)
                        .strip_prefix(dir.path())
                        .unwrap_or_else(|_| std::path::Path::new(file));
                    (Some(relative.display().to_string()), Some(line))
                };
                (
                    code,
                    d["severity"].as_str().expect("severity").to_string(),
                    file,
                    line,
                    d["message"].as_str().expect("message").to_string(),
                )
            })
            .collect();
        let mut want: Vec<Row> = case
            .diagnostics
            .iter()
            .map(|d| {
                (
                    d.code.to_string(),
                    d.severity.to_string(),
                    d.file.map(str::to_string),
                    d.line,
                    d.message.to_string(),
                )
            })
            .collect();
        got.sort();
        want.sort();
        assert_eq!(got, want, "{}", case.name);
    }
}
