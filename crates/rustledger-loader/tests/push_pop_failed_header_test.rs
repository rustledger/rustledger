//! A `pushtag`, `poptag`, `pushmeta` or `popmeta` whose line has an error
//! changes no state, through the whole pipeline (#2995).
//!
//! beancount 3.2.3 never reduces a statement whose line fails, an invalid
//! date included, so the push or pop does not happen: a failed push leaves
//! the transactions after it untagged and its pop reports the absent tag, a
//! failed pop leaves the tag on and the push unbalanced. These load the
//! ledger (book, plugins, validate) and read the booked transactions' tags
//! and metadata, and each error's code and line, as `rledger check` reports
//! them. Each was checked against `bean-check` 3.2.3
//! (`beancount.loader.load_string`): its line 0 for an unbalanced push is
//! the push's line here.

use std::io::Write as _;

use rustledger_core::Directive;

struct Loaded {
    /// `(code, line)` of every error, in order.
    errors: Vec<(String, usize)>,
    /// Each transaction's tags and `kk` metadata value, in date order.
    txns: Vec<(Vec<String>, Option<String>)>,
}

fn load(src: &str) -> Loaded {
    let dir = tempfile::Builder::new()
        .prefix("rledger_2995_")
        .tempdir()
        .expect("temp dir");
    let path = dir.path().join("main.beancount");
    let mut f = std::fs::File::create(&path).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    // The parse errors one by one, as `rledger check` reports them (left in,
    // `process` reports a file's as one line-less error), then the rest.
    let mut raw = rustledger_loader::Loader::new().load(&path).expect("load");
    let parse_errors: Vec<_> = raw
        .take_parse_errors()
        .iter()
        .flat_map(|failure| {
            rustledger_loader::parse_errors_to_ledger_errors(failure, &raw.source_map)
        })
        .collect();
    let ledger = rustledger_loader::process(raw, &rustledger_loader::LoadOptions::default())
        .expect("process");
    let errors = parse_errors
        .iter()
        .chain(&ledger.errors)
        .map(|e| (e.code.clone(), e.location.as_ref().map_or(0, |l| l.line)))
        .collect();
    let txns = ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            Directive::Transaction(t) => Some((
                t.tags.iter().map(ToString::to_string).collect(),
                t.meta.get("kk").map(ToString::to_string),
            )),
            _ => None,
        })
        .collect();
    Loaded { errors, txns }
}

const P: &str = "2024-01-01 open Assets:A\n";
const T: &str = "2024-01-02 * \"n\"\n  Assets:A 1 USD\n  Assets:A -1 USD\n";

fn err(code: &str, line: usize) -> (String, usize) {
    (code.to_string(), line)
}

/// The issue's row: a push with a date error tags nothing and is not left
/// unpopped. bean-check: line 2 only, the transaction untagged.
#[test]
fn test_load_failed_pushtag_tags_nothing() {
    let loaded = load(&format!("{P}pushtag #a 2024-02-30\n{T}"));
    assert_eq!(loaded.errors, [err("P0015", 2)]);
    assert_eq!(loaded.txns, [(vec![], None)]);
}

/// A pop with a date error does not pop: the tag stays on the transaction
/// after it and the push is unbalanced. bean-check: line 3 and the unbalanced
/// push, the transaction tagged `#a`.
#[test]
fn test_load_failed_poptag_keeps_the_tag() {
    let loaded = load(&format!("{P}pushtag #a\npoptag #a 2024-02-30\n{T}"));
    assert_eq!(loaded.errors, [err("P0021", 2), err("P0015", 3)]);
    assert_eq!(loaded.txns, [(vec!["a".to_string()], None)]);
}

/// The same for metadata: the key stays on the transaction after a failed
/// `popmeta`. bean-check: line 3 and the unbalanced key, `kk: "v"`.
#[test]
fn test_load_failed_popmeta_keeps_the_key() {
    let loaded = load(&format!(
        "{P}pushmeta kk: \"v\"\npopmeta kk: 2024-02-30\n{T}"
    ));
    assert_eq!(loaded.errors, [err("P0023", 2), err("P0015", 3)]);
    assert_eq!(loaded.txns, [(vec![], Some("\"v\"".to_string()))]);
}

/// A pop of a tag whose push failed is reported on the pop's own line, past
/// the comment line before it. bean-check: 2 and 4.
#[test]
fn test_load_pop_after_failed_push_is_on_the_pop_line() {
    let loaded = load(&format!("{P}pushtag #a $\n  ; c\npoptag #a\n{T}"));
    assert_eq!(loaded.errors, [err("P0012", 2), err("P0020", 4)]);
    assert_eq!(loaded.txns, [(vec![], None)]);
}
