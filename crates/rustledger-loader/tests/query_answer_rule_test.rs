//! The rule for whether a file-based query answers despite load errors
//! (#2861), pinned on the canonical predicates themselves.
//!
//! Every file-based query surface (the CLI, WASM, the FFI) decides with
//! `LoadError::blocks_queries` and `LedgerError::blocks_queries`. Their
//! drift-guard tests run the same cases (`query_answer_rule/cases.rs`); this
//! one checks the predicates give each case its expected answer, confined and
//! not, and that each case's load error is REPORTED either way.

include!("query_answer_rule/cases.rs");

use rustledger_loader::{LedgerError, LoadError, LoadOptions, load};

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
    for confined in [false, true] {
        for case in QUERY_RULE_CASES {
            let applies = match case.confinement {
                Confinement::Any => true,
                Confinement::ConfinedOnly => confined,
                Confinement::UnconfinedOnly => !confined,
            };
            if !applies {
                continue;
            }
            let (_dir, entry) = write_case(case);
            let options = LoadOptions {
                validate: true,
                path_security: confined,
                ..Default::default()
            };
            let ledger = load(&entry, &options).expect("load");
            let messages: Vec<&str> = ledger.errors.iter().map(|e| e.message.as_str()).collect();
            let refuses = ledger.errors.iter().any(LedgerError::blocks_queries);
            assert_eq!(
                !refuses,
                case.rows.is_some(),
                "{} (confined: {confined}): {messages:?}",
                case.name
            );
            if let Some(error) = case.error {
                assert!(
                    messages.iter().any(|m| m.contains(error)),
                    "{} (confined: {confined}): `{error}` not reported in {messages:?}",
                    case.name
                );
            } else if case.rows.is_some() {
                assert!(
                    messages.is_empty(),
                    "{} (confined: {confined}): {messages:?}",
                    case.name
                );
            }
        }
    }
}

/// The load-error half of the rule, variant by variant: a parse error, a
/// decryption failure and an I/O error other than not-found block (bean-query
/// fails on the last two with an uncaught `OSError`); a missing file, an
/// include cycle, a duplicate include, an empty glob and a confined include do
/// not.
#[test]
fn test_load_error_blocks_queries_by_variant() {
    use std::io::{Error, ErrorKind};
    use std::path::PathBuf;
    let io = |kind| LoadError::Io {
        path: PathBuf::from("x.beancount"),
        error: Error::new(kind, "os error"),
        include_site: None,
    };
    assert!(!io(ErrorKind::NotFound).blocks_queries());
    assert!(io(ErrorKind::IsADirectory).blocks_queries());
    assert!(io(ErrorKind::PermissionDenied).blocks_queries());
    assert!(
        LoadError::Decryption {
            path: PathBuf::from("x.gpg"),
            message: "no secret key".to_string(),
        }
        .blocks_queries()
    );
    assert!(
        !LoadError::IncludeCycle {
            cycle: vec!["a".to_string(), "a".to_string()],
        }
        .blocks_queries()
    );
    assert!(
        !LoadError::DuplicateInclude {
            path: "a".to_string(),
        }
        .blocks_queries()
    );
    assert!(
        !LoadError::GlobNoMatch {
            pattern: "*.bean".to_string(),
        }
        .blocks_queries()
    );
    assert!(
        !LoadError::PathTraversal {
            include_path: "../x".to_string(),
            base_dir: PathBuf::from("/ledger"),
        }
        .blocks_queries()
    );
}
