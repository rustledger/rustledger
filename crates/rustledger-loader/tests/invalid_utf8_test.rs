//! A file on disk with bytes that are not UTF-8 loads (lossily, so nothing
//! panics) and reports them where beancount does: an invalid token outside
//! strings, an undecodable string, nothing in a comment. It used to load
//! with no error at all.

use rustledger_loader::{LoadError, Loader, line_col_in};

#[test]
fn test_load_reports_bytes_that_are_not_utf8() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("latin1.beancount");
    std::fs::write(
        &path,
        b"; zur\xe9\n2020-01-01 open Assets:Zur\xe9\n2020-01-01 open Equity:O\n\
          2020-01-02 * \"zur\xe9\"\n  Equity:O  1 USD\n  Equity:O\n",
    )
    .expect("write");
    let result = Loader::new().load(&path).expect("loads");
    let source = result.source_map.files()[0].source.clone();
    let found: Vec<(usize, String)> = result
        .errors
        .iter()
        .filter_map(|e| match e {
            LoadError::ParseErrors { errors, .. } => Some(errors),
            _ => None,
        })
        .flatten()
        .map(|e| (line_col_in(&source, e.span.start).0, e.message()))
        .collect();
    assert_eq!(found.len(), 2, "{found:?}");
    assert_eq!(found[0].0, 2, "{found:?}");
    assert!(found[0].1.contains("invalid token"), "{found:?}");
    assert_eq!(found[1].0, 4, "{found:?}");
    assert!(found[1].1.contains("string"), "{found:?}");
}
