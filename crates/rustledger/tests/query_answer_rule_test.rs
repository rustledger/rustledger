//! `rledger query` answers despite load errors exactly when every other query
//! surface does (#2861).
//!
//! The drift guard for the CLI side of the one rule
//! (`LoadError::blocks_queries`, `LedgerError::blocks_queries`): the same
//! ledgers the loader, WASM and FFI tests run (`query_answer_rule/cases.rs` in
//! `rustledger-loader`) must answer or refuse here as they do there. A missing
//! include, an include cycle, a duplicate include, an empty glob and an
//! include outside the ledger's directory answer, with the load error on
//! stderr, as bean-query answers; a parse or booking error refuses.

mod common;

include!("../../rustledger-loader/tests/query_answer_rule/cases.rs");

use std::process::Command;

#[test]
fn test_query_answers_or_refuses_by_the_shared_rule() {
    let bin = require_rledger!();
    for case in QUERY_RULE_CASES {
        let dir = tempfile::tempdir().expect("tempdir");
        for (path, text) in case.files {
            let path = dir.path().join(path);
            std::fs::create_dir_all(path.parent().expect("parent")).expect("mkdir");
            std::fs::write(&path, text).expect("write");
        }
        let out = Command::new(&bin)
            .arg("query")
            .arg("--no-cache")
            .arg(dir.path().join(case.entry))
            .arg(QUERY_RULE_QUERY)
            .output()
            .expect("run rledger query");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let answered = out.status.success() && stdout.contains("pay");
        assert_eq!(
            answered,
            case.answers,
            "{}: status {:?}\nstdout:\n{stdout}\nstderr:\n{}",
            case.name,
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
        // An answer over a load error still reports it. (The CLI does not
        // confine includes, so the out-of-root include is read and is no
        // error here.)
        if case.answers && !matches!(case.name, "clean" | "include outside the root") {
            let stderr = String::from_utf8_lossy(&out.stderr);
            assert!(
                stderr.contains("LOAD"),
                "{}: the load error must be reported: {stderr}",
                case.name
            );
        }
    }
}
