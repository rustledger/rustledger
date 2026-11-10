//! A mid-line BOM in an included file is reported once, in that file, as it
//! is in the top-level one (#2928): the BOM-led invalid token is the broken
//! directive's one error, and the directives around it still load.

use rustledger_loader::{LoadError, Loader};
use rustledger_parser::ParseErrorKind;

#[test]
fn test_load_included_file_with_mid_line_bom_reports_one_error() {
    let dir = tempfile::tempdir().expect("tempdir");
    let main = dir.path().join("main.beancount");
    let child = dir.path().join("child.beancount");
    std::fs::write(
        &main,
        "include \"child.beancount\"\n2024-01-01 open Assets:A\n",
    )
    .expect("write main");
    std::fs::write(
        &child,
        "2024-01-01 commodity USD\n2024-01-02 price USD 1 \u{FEFF}EUR\n2024-01-03 commodity EUR\n",
    )
    .expect("write child");

    let result = Loader::new().load(&main).expect("loads");
    let parse_errors: Vec<_> = result
        .errors
        .iter()
        .filter_map(|e| match e {
            LoadError::ParseErrors { path, errors } => Some((path.clone(), errors.clone())),
            _ => None,
        })
        .collect();
    assert_eq!(parse_errors.len(), 1, "{:?}", result.errors);
    let (path, errors) = &parse_errors[0];
    assert!(path.ends_with("child.beancount"), "{path:?}");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        matches!(errors[0].kind, ParseErrorKind::BomInDirectiveBody),
        "{errors:?}"
    );
    // The open and both commodities load; the broken price does not.
    assert_eq!(result.directives.len(), 3, "{:?}", result.directives);
}
