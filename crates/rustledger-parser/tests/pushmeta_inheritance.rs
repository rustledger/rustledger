//! Where `pushmeta` and `pushtag` apply, as in beancount 3.2.3 (#2812).
//!
//! Beancount's grammar reads its pushed-metadata stack in `transaction()` and
//! nowhere else, applies it first and the transaction's own metadata on top,
//! and gives postings none. Pushed tags go to transactions, notes and
//! documents. rledger attached pushed metadata to every directive kind and
//! let it override a key the transaction wrote. Every expectation below is
//! what beancount's loader returns for the same ledger.

use rustledger_core::{Directive, MetaValue};
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::parse;

/// Each directive's date, kind, `key` metadata value and tags, on both paths.
fn observed(src: &str, key: &str) -> Vec<(String, &'static str, Option<String>, Vec<String>)> {
    let result = parse(src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let red = parse_red_only(src);
    assert_eq!(
        format!("{:?}", result.directives),
        format!("{:?}", red.directives),
        "green and red disagree"
    );
    result
        .directives
        .iter()
        .map(|d| {
            let (kind, meta, tags): (&str, _, Vec<String>) = match &d.value {
                Directive::Transaction(t) => (
                    "transaction",
                    t.meta.as_map().get(key).cloned(),
                    t.tags.iter().map(ToString::to_string).collect(),
                ),
                Directive::Open(o) => ("open", o.meta.as_map().get(key).cloned(), vec![]),
                Directive::Note(n) => (
                    "note",
                    n.meta.as_map().get(key).cloned(),
                    n.tags.iter().map(ToString::to_string).collect(),
                ),
                Directive::Document(n) => (
                    "document",
                    n.meta.as_map().get(key).cloned(),
                    n.tags.iter().map(ToString::to_string).collect(),
                ),
                Directive::Balance(b) => ("balance", b.meta.as_map().get(key).cloned(), vec![]),
                Directive::Event(e) => ("event", e.meta.as_map().get(key).cloned(), vec![]),
                Directive::Price(p) => ("price", p.meta.as_map().get(key).cloned(), vec![]),
                Directive::Commodity(c) => ("commodity", c.meta.as_map().get(key).cloned(), vec![]),
                Directive::Custom(c) => ("custom", c.meta.as_map().get(key).cloned(), vec![]),
                Directive::Close(c) => ("close", c.meta.as_map().get(key).cloned(), vec![]),
                Directive::Pad(p) => ("pad", p.meta.as_map().get(key).cloned(), vec![]),
                Directive::Query(q) => ("query", q.meta.as_map().get(key).cloned(), vec![]),
            };
            let meta = meta.map(|v| match v {
                MetaValue::String(s) => s,
                other => format!("{other:?}"),
            });
            let mut tags = tags;
            tags.sort();
            (d.value.date().to_string(), kind, meta, tags)
        })
        .collect()
}

fn row(
    date: &str,
    kind: &'static str,
    loc: Option<&str>,
    tags: &[&str],
) -> (String, &'static str, Option<String>, Vec<String>) {
    (
        date.to_string(),
        kind,
        loc.map(str::to_string),
        tags.iter().map(|t| (*t).to_string()).collect(),
    )
}

/// The probe checked with beancount 3.2.3's loader: pushed metadata reaches
/// transactions only, a transaction's own key wins, a later push of the same
/// key wins over an earlier one, and pushed tags reach transactions and notes.
#[test]
fn test_parse_applies_pushmeta_to_transactions_only_with_the_written_key_winning() {
    let src = "\
pushmeta loc: \"Lausanne\"
pushtag #trip
2024-01-01 open Assets:A
2024-01-01 open Assets:B
2024-01-02 * \"t\" #own
  loc: \"Paris\"
  Assets:A  1 USD
  Assets:B
2024-01-03 * \"u\"
  Assets:A  1 USD
  Assets:B
2024-01-04 note Assets:A \"n\"
2024-01-05 balance Assets:A 2 USD
2024-01-06 event \"e\" \"v\"
2024-01-07 price HOOL 1 USD
2024-01-08 commodity HOOL
2024-01-09 custom \"c\" \"v\"
2024-01-09 document Assets:A \"x.pdf\"
2024-01-09 close Assets:B
pushmeta loc: \"Bern\"
2024-01-10 * \"w\"
  Assets:A  1 USD
  Assets:B
popmeta loc:
2024-01-11 * \"x\"
  Assets:A  1 USD
  Assets:B
popmeta loc:
poptag #trip
";
    let mut got = observed(src, "loc");
    got.sort();
    let mut want = vec![
        row("2024-01-01", "open", None, &[]),
        row("2024-01-01", "open", None, &[]),
        row("2024-01-02", "transaction", Some("Paris"), &["own", "trip"]),
        row("2024-01-03", "transaction", Some("Lausanne"), &["trip"]),
        row("2024-01-04", "note", None, &["trip"]),
        row("2024-01-05", "balance", None, &[]),
        row("2024-01-06", "event", None, &[]),
        row("2024-01-07", "price", None, &[]),
        row("2024-01-08", "commodity", None, &[]),
        row("2024-01-09", "custom", None, &[]),
        row("2024-01-09", "document", None, &["trip"]),
        row("2024-01-09", "close", None, &[]),
        row("2024-01-10", "transaction", Some("Bern"), &["trip"]),
        row("2024-01-11", "transaction", Some("Lausanne"), &["trip"]),
    ];
    want.sort();
    assert_eq!(got, want);
}

/// Postings never receive pushed metadata.
#[test]
fn test_parse_gives_postings_no_pushed_metadata() {
    let result = parse(
        "pushmeta loc: \"Lausanne\"\n2024-01-02 * \"t\"\n  Assets:A  1 USD\n  Assets:B\npopmeta loc:\n",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let Directive::Transaction(t) = &result.directives[0].value else {
        panic!("expected a transaction");
    };
    for p in &t.postings {
        assert!(p.value.meta.as_map().get("loc").is_none(), "{p:?}");
    }
}

/// The lima fixtures from the issue, with their beancount values asserted
/// (the CLI fixture test only checks that they parse).
#[test]
fn test_parse_lima_pushmeta_fixtures_give_beancounts_values() {
    let dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/lima-tests");
    for (file, want) in [
        (
            "PushPopMeta.PushmetaShadow.beancount",
            vec!["Paris, France"],
        ),
        (
            "PushPopMeta.PushmetaOverride.beancount",
            vec!["Lausanne, Switzerland", "Paris, France"],
        ),
        (
            "PushPopMeta.PushmetaNormal.beancount",
            vec!["Lausanne, Switzerland"],
        ),
    ] {
        let src = std::fs::read_to_string(dir.join(file))
            .unwrap_or_else(|e| panic!("{file} must exist in tests/fixtures/lima-tests: {e}"));
        let got: Vec<String> = observed(&src, "location")
            .into_iter()
            .filter_map(|(_, kind, loc, _)| (kind == "transaction").then_some(loc).flatten())
            .collect();
        assert_eq!(got, want, "{file}");
    }
}
