//! The one rule for whether a query answers despite load errors (#2861),
//! pinned on the canonical predicates themselves.
//!
//! Every query surface (the CLI, WASM, the FFI) decides with
//! `LoadError::blocks_queries` and `LedgerError::blocks_queries`. Their
//! drift-guard tests run the same cases (`query_answer_rule/cases.rs`); this
//! one checks the predicates give each case's expected answer, and that the
//! load errors other than a parse error are still REPORTED.

include!("query_answer_rule/cases.rs");

use rustledger_loader::{LedgerError, LoadError, LoadOptions, load, load_raw};

/// Write `case`'s files under a fresh directory and return it with the
/// entry file's path.
fn write_case(case: &QueryRuleCase) -> (tempfile::TempDir, std::path::PathBuf) {
    let dir = tempfile::tempdir().expect("tempdir");
    for (path, text) in case.files {
        let path = dir.path().join(path);
        std::fs::create_dir_all(path.parent().expect("parent")).expect("mkdir");
        std::fs::write(&path, text).expect("write");
    }
    let entry = dir.path().join(case.entry);
    (dir, entry)
}

#[test]
fn test_blocks_queries_gives_each_case_its_answer() {
    for case in QUERY_RULE_CASES {
        let (_dir, entry) = write_case(case);
        let options = LoadOptions {
            validate: true,
            ..Default::default()
        };
        let ledger = load(&entry, &options).expect("load");
        let refuses = ledger.errors.iter().any(LedgerError::blocks_queries);
        assert_eq!(
            !refuses,
            case.answers,
            "{}: errors {:?}",
            case.name,
            ledger
                .errors
                .iter()
                .map(|e| (&e.code, &e.message))
                .collect::<Vec<_>>()
        );

        // The pre-processing half: only a parse error blocks.
        let raw = load_raw(&entry).expect("load_raw");
        let raw_blocks = raw.errors.iter().any(LoadError::blocks_queries);
        assert_eq!(raw_blocks, case.name == "parse error", "{}", case.name);

        // A load error that does not block is still reported.
        if case.answers && case.name != "clean" && case.name != "include outside the root" {
            assert!(
                ledger.errors.iter().any(|e| e.code == "LOAD"),
                "{}: the load error must be reported",
                case.name
            );
        }
    }
}

/// With the include graph confined to the entry's directory, an include
/// outside it is a load error, and the query still answers, as bean-query
/// answers over every load error but a parse error.
#[test]
fn test_blocks_queries_answers_over_a_confined_include() {
    let case = QUERY_RULE_CASES
        .iter()
        .find(|c| c.name == "include outside the root")
        .expect("case");
    let (_dir, entry) = write_case(case);
    let options = LoadOptions {
        validate: true,
        path_security: true,
        ..Default::default()
    };
    let ledger = load(&entry, &options).expect("load");
    assert!(
        ledger.errors.iter().any(|e| e.code == "LOAD"),
        "the confined include must be reported: {:?}",
        ledger.errors
    );
    assert!(!ledger.errors.iter().any(LedgerError::blocks_queries));
}
