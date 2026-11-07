//! `rledger query` answers despite load errors exactly when the other
//! file-based query surfaces do (#2861).
//!
//! The drift guard for the CLI side of the rule
//! (`LoadError::blocks_queries`, `LedgerError::blocks_queries`): the same
//! ledgers the loader, WASM and FFI tests run (`query_answer_rule/cases.rs` in
//! `rustledger-loader`) must give exactly the same rows here, or refuse, with
//! the same load error on stderr. The CLI does not confine includes, so it
//! runs the cases for an unconfined surface.

mod common;

include!("../../rustledger-loader/tests/query_answer_rule/cases.rs");

use std::process::Command;

#[test]
fn test_query_answers_or_refuses_by_the_shared_rule() {
    let bin = require_rledger!();
    for case in QUERY_RULE_CASES {
        if case.confinement == Confinement::ConfinedOnly {
            continue;
        }
        let dir = tempfile::tempdir().expect("tempdir");
        for (path, text) in case.files {
            let path = dir.path().join(path);
            std::fs::create_dir_all(path.parent().expect("parent")).expect("mkdir");
            std::fs::write(&path, text).expect("write");
        }
        let out = Command::new(&bin)
            .args(["query", "--no-cache", "-f", "json"])
            .arg(dir.path().join(case.entry))
            .arg(QUERY_RULE_QUERY)
            .output()
            .expect("run rledger query");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        let context = format!(
            "{}: status {:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            case.name, out.status
        );
        if let Some(rows) = case.rows {
            assert!(out.status.success(), "{context}");
            let value: serde_json::Value =
                serde_json::from_str(&stdout).unwrap_or_else(|e| panic!("{e}: {context}"));
            let got: Vec<&str> = value["rows"]
                .as_array()
                .unwrap_or_else(|| panic!("no rows array: {context}"))
                .iter()
                .map(|row| row[0].as_str().unwrap_or_else(|| panic!("{context}")))
                .collect();
            assert_eq!(got, rows, "{context}");
        } else {
            // Exit 1 with the gate's own message: a panic (exit 101, as a
            // debug assertion behind a no-op gate gives) is not a refusal,
            // and a release build would answer there.
            assert_eq!(out.status.code(), Some(1), "{context}");
            assert!(stderr.contains("refusing"), "{context}");
            assert!(
                stdout.trim().is_empty(),
                "a refusal prints no rows: {context}"
            );
        }
        if let Some(error) = case.error {
            assert!(stderr.contains(error), "`{error}` not reported: {context}");
        }
    }
}
