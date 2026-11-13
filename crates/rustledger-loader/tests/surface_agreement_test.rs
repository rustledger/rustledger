//! The validating loader, the pipeline `rledger check` runs, gives each
//! surface-agreement case its findings (#2937, #2949), and records the transactions
//! booking refused (`Ledger::booking_refused`), which the WASM single-source
//! surfaces read to validate as it does. The other surfaces' drift-guard
//! tests run the same cases (`surface_agreement/cases.rs`).

#![cfg(all(feature = "validation", feature = "plugins"))]

include!("surface_agreement/cases.rs");

use rustledger_core::Directive;
use rustledger_loader::{LoadError, LoadOptions, load, load_raw};

#[test]
fn test_validating_load_gives_each_case_its_findings() {
    for case in SURFACE_CASES {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("ledger.beancount");
        std::fs::write(&path, case.source).expect("write");
        let ledger = load(&path, &LoadOptions::default()).expect("load");
        let context = format!("{}: {:?}", case.name, ledger.errors);

        // E1004 is raised, and left out by `check` (`is_advisory_only_code`).
        assert_eq!(
            ledger.errors.iter().any(|e| e.code == "E1004"),
            case.closes_nonempty,
            "{context}"
        );
        // The parse errors as `check` reports them: one by one, from the raw
        // load, before `process`, which folds a file's parse errors into the
        // one `LOAD` error left out below. Validation runs over what parsed,
        // so the other findings are there beside them (#2949).
        let raw = load_raw(&path).expect("load_raw");
        let index = rustledger_loader::LineIndex::new(case.source);
        let parse_errors: Vec<(String, usize, String)> = raw
            .errors
            .iter()
            .flat_map(|e| match e {
                LoadError::ParseErrors { errors, .. } => errors.as_slice(),
                _ => &[],
            })
            .map(|e| {
                (
                    format!("P{:04}", e.kind_code()),
                    index.line_col(e.span.start).0,
                    e.message(),
                )
            })
            .collect();
        let folded = format!("parse errors in {}", path.display());
        let mut got: Vec<(&str, usize, &str)> = ledger
            .errors
            .iter()
            .filter(|e| !rustledger_validate::is_advisory_only_code(&e.code))
            .filter(|e| !(e.code == "LOAD" && e.message == folded))
            .map(|e| {
                (
                    e.code.as_str(),
                    e.location.as_ref().map_or(0, |l| l.line),
                    e.message.as_str(),
                )
            })
            .chain(
                parse_errors
                    .iter()
                    .map(|(code, line, message)| (code.as_str(), *line, message.as_str())),
            )
            .collect();
        got.sort_unstable();
        let mut want: Vec<&Finding> = case.findings.iter().collect();
        want.sort_by_key(|f| (f.code, f.line));
        assert_eq!(got.len(), want.len(), "{context}");
        for ((code, line, message), finding) in got.iter().zip(&want) {
            assert_eq!(*code, finding.code, "{context}");
            assert_eq!(*line, finding.line as usize, "{context}");
            assert!(message.starts_with(finding.message), "{context}");
        }

        // `booking_refused` names exactly the transactions a booking failure
        // refused, at their index in the finalized stream.
        let refused: Vec<&str> = ledger
            .booking_refused
            .iter()
            .map(|&i| match &ledger.directives[i].value {
                Directive::Transaction(t) => t.narration.as_str(),
                other => panic!("{}: refused a {other:?}", case.name),
            })
            .collect();
        let failures = ledger
            .errors
            .iter()
            .filter(|e| e.is_booking_failure())
            .count();
        assert_eq!(refused.len(), failures, "{context}");
        if failures > 0 {
            assert_eq!(refused, ["sell"], "{context}");
        }
    }
}
