//! Properties of the FFI directive-identity hash (#1902 Phase 1).
//!
//! `compute_directive_hash` is surfaced as `meta.hash` across the WIT boundary,
//! so rustfava and the desktop app treat it as a directive's identity. Two
//! distinct directives sharing a hash means those consumers conflate them.
//!
//! This crate had the highest defect density on #1902's table (13.1 fixes/kloc)
//! and fuzz as its only verification. The first property written found three
//! real collisions.

use rustledger_core::{Directive, Link, Metadata, Tag, naive_date};
use rustledger_ffi_wasi::compute_directive_hash as hash;

fn txn(payee: Option<&str>, narration: &str, tags: &[&str], links: &[&str]) -> Directive {
    Directive::Transaction(rustledger_core::directive::Transaction {
        date: naive_date(2024, 1, 1).unwrap(),
        flag: '*',
        payee: payee.map(std::convert::Into::into),
        narration: narration.into(),
        tags: tags.iter().copied().map(Tag::new).collect(),
        links: links.iter().copied().map(Link::new).collect(),
        meta: Metadata::default(),
        postings: Vec::new(),
        trailing_comments: Vec::new(),
    })
}

/// The same directive hashes the same every time.
///
/// Cheap, and it is the assumption every other property here rests on.
#[test]
fn hashing_is_deterministic() {
    let d = txn(Some("p"), "n", &["t"], &["l"]);
    let first = hash(&d);
    for _ in 0..8 {
        assert_eq!(hash(&d), first, "the same directive must hash the same");
    }
    // Length ALONE would also accept a 64-character non-hex encoding, which is
    // the plausible way this changes: a switch to base64 or to an uppercase
    // renderer would keep the count and break every consumer parsing the digest.
    assert_eq!(first.len(), 64, "a SHA256 hex digest is 64 characters");
    assert!(
        first
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
        "a SHA256 hex digest is lowercase hex; got {first}",
    );
}

/// Moving a character across a field boundary must change the hash.
///
/// `Sha256::update` concatenates, so before #1902's Phase 1 work this function
/// was ambiguous at every boundary and all three of these collided. The third
/// is the one that mattered most: a transaction WITH a payee hashed identically
/// to one WITHOUT.
#[test]
fn field_boundaries_are_unambiguous() {
    let cases: [(Directive, Directive, &str); 3] = [
        (
            txn(Some("ab"), "c", &[], &[]),
            txn(Some("a"), "bc", &[], &[]),
            "payee/narration boundary",
        ),
        (
            txn(None, "n", &["ab"], &[]),
            txn(None, "n", &["a"], &["b"]),
            "tag/link boundary",
        ),
        (
            txn(None, "ab", &[], &[]),
            txn(Some("a"), "b", &[], &[]),
            "absent payee vs present payee",
        ),
    ];
    for (a, b, what) in cases {
        assert_ne!(
            hash(&a),
            hash(&b),
            "{what}: distinct directives must not collide"
        );
    }
}

/// Every field the hash reads must be able to change the hash.
///
/// A field that is hashed but cannot move the digest would be dead weight; a
/// field that is NOT hashed shows up here as a collision, which is the useful
/// signal — it says the identity contract ignores something a consumer may
/// consider identifying.
#[test]
fn each_hashed_field_affects_the_digest() {
    let base = txn(Some("p"), "n", &["t"], &["l"]);
    let variants: [(Directive, &str); 4] = [
        (txn(Some("P"), "n", &["t"], &["l"]), "payee"),
        (txn(Some("p"), "N", &["t"], &["l"]), "narration"),
        (txn(Some("p"), "n", &["T"], &["l"]), "tag"),
        (txn(Some("p"), "n", &["t"], &["L"]), "link"),
    ];
    for (v, field) in variants {
        assert_ne!(
            hash(&base),
            hash(&v),
            "changing the {field} must change the hash"
        );
    }
}

/// Directive KIND is part of the identity.
///
/// Two different directive types on the same date with the same account must
/// not share a hash, or a close would be indistinguishable from an open in any
/// consumer keyed on the digest.
#[test]
fn directive_kind_is_part_of_the_identity() {
    let date = naive_date(2024, 1, 1).unwrap();
    let acct = rustledger_core::Account::new("Assets:A");
    let open = Directive::Open(rustledger_core::directive::Open {
        date,
        account: acct.clone(),
        currencies: Vec::new(),
        booking: None,
        meta: Metadata::default(),
    });
    let close = Directive::Close(rustledger_core::directive::Close {
        date,
        account: acct,
        meta: Metadata::default(),
    });
    assert_ne!(hash(&open), hash(&close), "open and close must not collide");
}
