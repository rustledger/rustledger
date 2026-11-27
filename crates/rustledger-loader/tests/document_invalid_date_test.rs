//! A document file named like a date that is not one is reported and
//! skipped, and the other documents are still discovered.
//!
//! beancount's `find_documents` reports `Invalid date on document file
//! '<name>': <reason>` at the main file's line 0 and goes on scanning.
//! Discovery used to turn `2020-13-45.pdf` into a `document` with an invalid
//! date, and the loader then refused the plugin's whole output ("plugin
//! returned an entry that is not valid"), so every other discovered document
//! was lost too.

#![cfg(all(feature = "validation", feature = "plugins"))]

use rustledger_core::Directive;
use rustledger_loader::{LoadOptions, load};

#[test]
fn test_document_discovery_reports_an_invalid_date_and_keeps_the_rest() {
    let dir = tempfile::tempdir().expect("tempdir");
    let cash = dir.path().join("docs/Assets/Cash");
    std::fs::create_dir_all(&cash).expect("mkdir");
    for name in [
        "2020-13-45.bad-month.pdf",
        "2021-02-30.bad-day.pdf",
        "2020-01-15.statement.pdf",
    ] {
        std::fs::write(cash.join(name), b"").expect("touch");
    }
    let ledger_path = dir.path().join("ledger.beancount");
    std::fs::write(
        &ledger_path,
        "option \"documents\" \"docs\"\n2020-01-01 open Assets:Cash\n",
    )
    .expect("write ledger");

    let ledger = load(&ledger_path, &LoadOptions::default()).expect("loads");

    let documents: Vec<_> = ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Document(doc) => Some(doc.path.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(documents.len(), 1, "{documents:?}");
    assert!(
        documents[0].ends_with("2020-01-15.statement.pdf"),
        "{documents:?}"
    );

    let mut errors: Vec<_> = ledger
        .errors
        .iter()
        .map(|e| {
            let line = e.location.as_ref().map(|l| l.line);
            (e.code.clone(), e.message.clone(), line)
        })
        .collect();
    errors.sort();
    assert_eq!(
        errors,
        [
            (
                "PLUGIN".to_string(),
                "Invalid date on document file '2020-13-45.bad-month.pdf': month must be in 1..12"
                    .to_string(),
                Some(0),
            ),
            (
                "PLUGIN".to_string(),
                "Invalid date on document file '2021-02-30.bad-day.pdf': day is out of range for month"
                    .to_string(),
                Some(0),
            ),
        ]
    );
}
