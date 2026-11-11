//! `rledger check` reports exactly the findings every other diagnostic
//! surface reports, on the same ledgers (#2937).
//!
//! The CLI side of the drift guard whose cases are
//! `rustledger-loader/tests/surface_agreement/cases.rs`; WASM, the FFI
//! component and the LSP run the same cases. The expected findings are
//! bean-check 3.2.3's, so this side pins that the reference is right.

mod common;

include!("../../rustledger-loader/tests/surface_agreement/cases.rs");

use std::process::Command;

#[test]
fn test_check_reports_the_shared_findings() {
    let bin = require_rledger!();
    for case in SURFACE_CASES {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("ledger.beancount");
        std::fs::write(&path, case.source).expect("write");
        let out = Command::new(&bin)
            .args(["check", "--no-cache", "--format", "json"])
            .arg(&path)
            .output()
            .expect("run rledger check");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let context = format!(
            "{}: status {:?}\nstdout:\n{stdout}\nstderr:\n{}",
            case.name,
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
        let value: serde_json::Value =
            serde_json::from_str(&stdout).unwrap_or_else(|e| panic!("{e}: {context}"));
        let mut got: Vec<(String, u64, String)> = value["diagnostics"]
            .as_array()
            .unwrap_or_else(|| panic!("no diagnostics array: {context}"))
            .iter()
            .map(|d| {
                (
                    d["code"].as_str().unwrap_or_default().to_string(),
                    d["line"].as_u64().unwrap_or_default(),
                    d["message"].as_str().unwrap_or_default().to_string(),
                )
            })
            .collect();
        got.sort();
        let mut want: Vec<&Finding> = case.findings.iter().collect();
        want.sort_by_key(|f| (f.code, f.line));
        assert_eq!(got.len(), want.len(), "{context}");
        for ((code, line, message), finding) in got.iter().zip(&want) {
            assert_eq!(code, finding.code, "{context}");
            assert_eq!(*line, u64::from(finding.line), "{context}");
            assert!(message.starts_with(finding.message), "{context}");
        }
        assert_eq!(
            out.status.code(),
            Some(i32::from(!case.findings.is_empty())),
            "{context}"
        );

        // The E1004 the other surfaces dropped is real: the lint finds it.
        let lint = Command::new(&bin)
            .args(["lint", "closed-nonempty"])
            .arg(&path)
            .output()
            .expect("run rledger lint");
        let lint_out = String::from_utf8_lossy(&lint.stdout);
        assert_eq!(
            lint_out.contains("Cannot close account Assets:Bank with non-zero balance"),
            case.closes_nonempty,
            "{}: lint closed-nonempty:\n{lint_out}",
            case.name
        );
    }
}
