//! Tags and links are a sorted, deduplicated set on every path that builds an
//! entry (#2545, #2544).
//!
//! Beancount's tags and links are `frozenset`s. rledger keeps them in
//! `rustledger_core::SortedSet`, whose constructors all sort and dedup, so the
//! invariant holds by type. These properties check it end to end on each path
//! that builds an entry: the parser (written tags, written twice, and
//! `pushtag`, which now also reaches `document` and `note` as in beancount 3),
//! the plugin wire round trip (a plugin may return any order or duplicates),
//! and the FFI input conversion. They also pin the consequence for identity:
//! `meta.hash` no longer depends on the order tags were written in.

use proptest::prelude::*;
use rustledger_core::Directive;
use rustledger_ffi_wasi::{InputEntry, compute_directive_hash, input_entry_to_directive};
use rustledger_plugin::types::DirectiveData;
use rustledger_plugin::{directive_to_wrapper, wrapper_to_directive};

/// Lowercase names from a tiny alphabet, so duplicates are common.
fn names() -> impl Strategy<Value = Vec<String>> {
    prop::collection::vec("[a-c]{1,2}", 0..6)
}

fn set(v: impl IntoIterator<Item = String>) -> Vec<String> {
    let mut v: Vec<String> = v.into_iter().collect();
    v.sort();
    v.dedup();
    v
}

/// The entry's tags and links as strings, in stored order.
fn tags_links(d: &Directive) -> (Vec<String>, Vec<String>) {
    let (t, l) = match d {
        Directive::Transaction(x) => (&x.tags, &x.links),
        Directive::Document(x) => (&x.tags, &x.links),
        Directive::Note(x) => (&x.tags, &x.links),
        other => panic!("no tags on {other:?}"),
    };
    (
        t.iter().map(ToString::to_string).collect(),
        l.iter().map(ToString::to_string).collect(),
    )
}

fn prefixed(v: &[String], sigil: &str) -> String {
    v.iter().fold(String::new(), |mut out, s| {
        out.push(' ');
        out.push_str(sigil);
        out.push_str(s);
        out
    })
}

fn hashes(v: &[String]) -> String {
    prefixed(v, "#")
}

fn carets(v: &[String]) -> String {
    prefixed(v, "^")
}

proptest! {
    /// Parser + pushtag: each of transaction, document and note gets exactly
    /// the sorted union of its written tags and the pushed ones.
    #[test]
    fn parsed_entries_hold_the_set(
        pushed in names(),
        tags in names(),
        links in names(),
    ) {
        let mut src = String::from("2024-01-01 open Assets:Cash\n");
        for p in &pushed {
            src.push_str(&format!("pushtag #{p}\n"));
        }
        let (t, l) = (hashes(&tags), carets(&links));
        src.push_str(&format!(
            "2024-01-02 * \"x\"{t}{l}\n  Assets:Cash  1 USD\n  Assets:Cash  -1 USD\n\
             2024-01-03 document Assets:Cash \"r.pdf\"{t}{l}\n\
             2024-01-04 note Assets:Cash \"hi\"{t}{l}\n"
        ));
        for p in pushed.iter().rev() {
            src.push_str(&format!("poptag #{p}\n"));
        }
        let parsed = rustledger_parser::parse(&src);
        prop_assert!(parsed.errors.is_empty(), "{src}\n{:?}", parsed.errors);

        let want_tags = set(tags.iter().chain(&pushed).cloned());
        let want_links = set(links.iter().cloned());
        let mut seen = 0;
        for d in &parsed.directives {
            if matches!(d.value, Directive::Open(_)) {
                continue;
            }
            seen += 1;
            let (got_t, got_l) = tags_links(&d.value);
            prop_assert_eq!(&got_t, &want_tags, "{}", src);
            prop_assert_eq!(&got_l, &want_links, "{}", src);
        }
        prop_assert_eq!(seen, 3);
    }

    /// Plugin round trip: whatever order and duplicates a plugin returns, the
    /// entry converted back holds the set.
    #[test]
    fn plugin_output_is_normalized(tags in names(), links in names()) {
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();
        for original in [
            Directive::Transaction(rustledger_core::Transaction::new(date, "x")),
            Directive::Document(rustledger_core::Document::new(date, "Assets:A", "r.pdf")),
        ] {
            let mut w = directive_to_wrapper(&original);
            match &mut w.data {
                DirectiveData::Transaction(t) => {
                    t.tags.clone_from(&tags);
                    t.links.clone_from(&links);
                }
                DirectiveData::Document(d) => {
                    d.tags.clone_from(&tags);
                    d.links.clone_from(&links);
                }
                _ => unreachable!(),
            }
            let back = wrapper_to_directive(&w).expect("converts");
            let (got_t, got_l) = tags_links(&back);
            prop_assert_eq!(got_t, set(tags.iter().cloned()));
            prop_assert_eq!(got_l, set(links.iter().cloned()));
        }
    }

    /// FFI input: a host-built transaction or document holds the set.
    #[test]
    fn ffi_input_is_normalized(tags in names(), links in names()) {
        for kind in ["transaction", "document"] {
            let json = serde_json::json!({
                "type": kind,
                "date": "2024-01-01",
                "account": "Assets:A",
                "path": "r.pdf",
                "tags": tags,
                "links": links,
            });
            let entry: InputEntry = serde_json::from_value(json).expect("valid input");
            let d = input_entry_to_directive(&entry).expect("converts");
            let (got_t, got_l) = tags_links(&d);
            prop_assert_eq!(got_t, set(tags.iter().cloned()));
            prop_assert_eq!(got_l, set(links.iter().cloned()));
        }
    }

    /// `meta.hash` is order-independent: the same tags and links written in
    /// any order, or written twice, are the same entry.
    #[test]
    fn hash_ignores_written_order(tags in names(), links in names()) {
        let entry = |t: &[String], l: &[String]| {
            let src = format!(
                "2024-01-02 * \"x\"{}{}\n  Assets:Cash  1 USD\n  Assets:Cash  -1 USD\n",
                hashes(t),
                carets(l),
            );
            let parsed = rustledger_parser::parse(&src);
            compute_directive_hash(&parsed.directives[0].value)
        };
        let mut rt = tags.clone();
        rt.reverse();
        rt.extend(tags.iter().cloned());
        let mut rl = links.clone();
        rl.reverse();
        prop_assert_eq!(entry(&tags, &links), entry(&rt, &rl));
    }
}
