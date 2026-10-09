//! Property tests for the WASM importer id link, `wasm-<importer>/<id>`
//! (#2519): every link the encoder can emit is a valid beancount link that
//! survives parse and canonical formatting unchanged, two different importer
//! names never share a namespace, and dedup splits the namespace at the right
//! `/` even when the id itself contains `/`.

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, Posting, Transaction};
use rustledger_ops::dedup::{
    FuzzyDedupConfig, WASM_ID_LINK_PREFIX, find_import_duplicates, wasm_id_link,
};

const BANK: &str = "Assets:Bank";

/// Names and ids over every kind of character the encoder treats
/// differently: kept ASCII, `_` (the escape byte itself), `/` (the namespace
/// separator), `.`, spaces, literal `_XX`-looking runs, and multi-byte
/// non-ASCII.
fn text() -> impl Strategy<Value = String> {
    prop::collection::vec(
        prop::sample::select(vec![
            "a",
            "Z",
            "0",
            "9",
            "-",
            ".",
            "_",
            "/",
            " ",
            ":",
            "^",
            "_20",
            "_5F",
            "_2F",
            "é",
            "€",
            "日本",
            "\u{1F600}",
            "\t",
            "%",
        ]),
        0..12,
    )
    .prop_map(|parts| parts.concat())
}

/// The importer name a link's namespace encodes, decoded (`_XX` is one
/// byte), or `None` when the link is not a well-formed wasm id link.
fn decode_name(link: &str) -> Option<Vec<u8>> {
    let rest = link.strip_prefix(WASM_ID_LINK_PREFIX)?;
    let encoded = &rest[..rest.find('/')?];
    let mut bytes = Vec::new();
    let mut chars = encoded.bytes();
    while let Some(b) = chars.next() {
        if b == b'_' {
            let hex = [chars.next()?, chars.next()?];
            bytes.push(u8::from_str_radix(std::str::from_utf8(&hex).ok()?, 16).ok()?);
        } else {
            bytes.push(b);
        }
    }
    Some(bytes)
}

fn txn(narration: &str, link: &str) -> Transaction {
    Transaction::new("2024-01-15".parse().unwrap(), narration)
        .with_synthesized_posting(Posting::new(
            BANK,
            Amount::new(Decimal::new(-250, 2), "EUR"),
        ))
        .with_synthesized_posting(Posting::auto("Expenses:Food"))
        .with_link(link)
}

fn duplicates(new: &Transaction, existing: &Transaction) -> usize {
    find_import_duplicates(
        &[new],
        &[existing],
        Some(BANK),
        &FuzzyDedupConfig::default(),
    )
    .len()
}

proptest! {
    /// Every emitted link uses only the link charset (beancount's and the
    /// lexer's `\^[a-zA-Z0-9-_/.]+`), encodes the importer name losslessly,
    /// and comes back unchanged through parse -> canonical format -> parse.
    #[test]
    fn every_link_is_valid_and_round_trips(name in text(), id in text()) {
        let Some(link) = wasm_id_link(&name, &id) else {
            // Only an empty name or an id with no letter or digit is refused.
            prop_assert!(name.is_empty() || !id.chars().any(|c| c.is_ascii_alphanumeric()));
            return Ok(());
        };
        prop_assert!(
            link.bytes().all(|b| b.is_ascii_alphanumeric() || b"-_/.".contains(&b)),
            "{link:?}"
        );
        prop_assert_eq!(decode_name(&link), Some(name.as_bytes().to_vec()), "{}", link);

        let source = format!(
            "2024-01-15 * \"x\" ^{link}\n  {BANK}  -2.50 EUR\n  Expenses:Food\n"
        );
        let parsed = rustledger_parser::parse(&source);
        prop_assert!(parsed.errors.is_empty(), "{:?} for {}", parsed.errors, source);
        let links = |directives: &[Directive]| -> Vec<String> {
            directives
                .iter()
                .filter_map(|d| match d {
                    Directive::Transaction(t) => Some(t.links.iter().map(ToString::to_string)),
                    _ => None,
                })
                .flatten()
                .collect()
        };
        let first: Vec<Directive> = parsed.directives.into_iter().map(|s| s.value).collect();
        prop_assert_eq!(links(&first), vec![link.clone()]);
        let formatted = rustledger_parser::format::canonicalize_directives(
            first.iter(),
            &rustledger_core::format::FormatConfig::default(),
        )
        .unwrap();
        let reparsed = rustledger_parser::parse(&formatted);
        prop_assert!(reparsed.errors.is_empty(), "{:?}", reparsed.errors);
        let second: Vec<Directive> = reparsed.directives.into_iter().map(|s| s.value).collect();
        prop_assert_eq!(links(&second), vec![link]);
    }

    /// Two different names never produce the same namespace, including a
    /// literal name that looks like an encoding (`My_20Bank` vs `My Bank`).
    #[test]
    fn different_names_never_share_a_namespace(a in text(), b in text()) {
        prop_assume!(a != b && !a.is_empty() && !b.is_empty());
        let (la, lb) = (wasm_id_link(&a, "1").unwrap(), wasm_id_link(&b, "1").unwrap());
        prop_assert_ne!(la, lb);
    }

    /// Dedup reads the namespace up to the first `/`, which the encoded name
    /// can never contain, so an id with `/` in it does not move the split:
    /// the same importer with different ids is two transactions; different
    /// importers' ids never contradict (text decides); the same id matches.
    #[test]
    fn dedup_splits_the_namespace_at_the_first_slash(
        a in text(), b in text(), id1 in text(), id2 in text(),
    ) {
        prop_assume!(!a.is_empty() && !b.is_empty() && a != b);
        let (Some(a1), Some(a2), Some(b2)) =
            (wasm_id_link(&a, &id1), wasm_id_link(&a, &id2), wasm_id_link(&b, &id2))
        else {
            return Ok(());
        };
        prop_assert_eq!(duplicates(&txn("Bakery", &a1), &txn("Rent", &a1)), 1);
        if a1 != a2 {
            prop_assert_eq!(duplicates(&txn("Bakery", &a2), &txn("Bakery", &a1)), 0);
        }
        prop_assert_eq!(duplicates(&txn("Bakery", &b2), &txn("Bakery", &a1)), 1);
    }
}

/// The literal-escape case, spelled out: `_` is always escaped, so a name
/// containing `_20` cannot collide with one containing a space.
#[test]
fn a_name_that_looks_encoded_is_escaped_again() {
    assert_eq!(
        wasm_id_link("My Bank", "1").as_deref(),
        Some("wasm-My_20Bank/1")
    );
    assert_eq!(
        wasm_id_link("My_20Bank", "1").as_deref(),
        Some("wasm-My_5F20Bank/1")
    );
    assert_eq!(wasm_id_link("a/b", "c").as_deref(), Some("wasm-a_2Fb/c"));
    assert_eq!(wasm_id_link("a", "b/c").as_deref(), Some("wasm-a/b/c"));
    let long = "x".repeat(10_000);
    assert_eq!(wasm_id_link(&long, "1").map(|l| l.len()), Some(10_000 + 7));
}
