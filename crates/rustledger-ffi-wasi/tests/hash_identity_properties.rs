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

/// A posting with an account, and optionally units.
fn txn_with_postings(
    narration: &str,
    links: &[&str],
    postings: &[(&str, Option<(&str, Option<&str>)>)],
) -> Directive {
    let postings: Vec<rustledger_core::Spanned<rustledger_core::directive::Posting>> = postings
        .iter()
        .map(|(account, units)| {
            let mut p = rustledger_core::directive::Posting::new(
                *account,
                rustledger_core::Amount::new(rustledger_core::Decimal::ZERO, "USD"),
            );
            p.units = units.map(|(number, currency)| {
                let n = number.parse().expect("a decimal");
                match currency {
                    Some(c) => rustledger_core::IncompleteAmount::complete(n, (*c).to_owned()),
                    None => rustledger_core::IncompleteAmount::number_only(n),
                }
            });
            rustledger_core::Spanned::new(p, rustledger_core::Span::new(0, 0))
        })
        .collect();
    let Directive::Transaction(mut t) = txn(None, narration, &[], links) else {
        unreachable!()
    };
    t.postings = postings;
    Directive::Transaction(t)
}

/// A field must not be able to MIGRATE across a collection boundary.
///
/// Length-prefixing each field is not sufficient on its own, which Copilot
/// caught on review. A stream of length-prefixed fields decodes to a unique
/// SEQUENCE of byte strings, but two different structures can produce the same
/// sequence whenever a variable-length collection abuts anything else — so
/// `tags ["a","b"], links []` and `tags ["a"], links ["b"]` both emit
/// `["a", "b"]` and collide.
///
/// This is the same defect class the length prefix fixed, one level up: the
/// element boundaries were unambiguous but the COLLECTION boundaries were not.
///
/// All three collide against the previous commit. They are not equally
/// load-bearing on one mechanism, which is why the failure lists every case
/// rather than stopping at the first: the tag/link case is caught only by the
/// collection counts, while the other two are caught independently by both the
/// counts and the presence tags.
#[test]
fn fields_cannot_migrate_across_collection_boundaries() {
    let cases: [(Directive, Directive, &str); 3] = [
        (
            txn(None, "n", &["a", "b"], &[]),
            txn(None, "n", &["a"], &["b"]),
            "tag/link boundary: a tag must not be able to become a link",
        ),
        (
            txn(None, "a", &["b"], &[]),
            txn(Some("a"), "b", &[], &[]),
            "payee/narration/tag boundary: an absent payee must not let the \
             narration and a tag shift up into its place",
        ),
        (
            txn_with_postings("n", &["a", "b"], &[]),
            txn_with_postings("n", &["a"], &[("b", None)]),
            "link/posting boundary: a link must not be able to become a posting \
             account",
        ),
    ];
    // Collect rather than stop at the first: an assert_ne in a loop hides
    // whether the remaining cases are load-bearing or riding on this one.
    let collisions: Vec<&str> = cases
        .iter()
        .filter(|(left, right, _)| hash(left) == hash(right))
        .map(|(_, _, what)| *what)
        .collect();
    assert!(
        collisions.is_empty(),
        "{} of {} boundary cases collided: {collisions:#?}",
        collisions.len(),
        cases.len(),
    );
}

/// Units contribute a VARIABLE number of fields, so the posting boundary needs
/// its own marker.
///
/// The collection counts alone do not cover this. Within the postings list a
/// posting emits its account and then zero, one, or two more fields depending
/// on whether its units carry a number, a currency, both, or are absent — so
/// two postings can be re-partitioned into two different postings emitting the
/// identical field sequence:
///
/// ```text
///   [Assets:A  1 USD] [Assets:B]        -> "Assets:A" "1" "USD" "Assets:B"
///   [Assets:A  1    ] [USD  Assets:B]   -> "Assets:A" "1" "USD" "Assets:B"
/// ```
///
/// Same count, same fields, different transactions. The presence tag on units
/// (and on the number and currency inside them) is what separates these; it is
/// the one case the counts cannot reach.
#[test]
fn units_presence_is_part_of_the_posting_boundary() {
    fn posting(
        account: &str,
        units: Option<rustledger_core::IncompleteAmount>,
    ) -> rustledger_core::Spanned<rustledger_core::directive::Posting> {
        let mut p = rustledger_core::directive::Posting::new(
            account,
            rustledger_core::Amount::new(rustledger_core::Decimal::ZERO, "USD"),
        );
        p.units = units;
        rustledger_core::Spanned::new(p, rustledger_core::Span::new(0, 0))
    }
    fn with(
        postings: Vec<rustledger_core::Spanned<rustledger_core::directive::Posting>>,
    ) -> Directive {
        let Directive::Transaction(mut t) = txn(None, "n", &[], &[]) else {
            unreachable!()
        };
        t.postings = postings;
        Directive::Transaction(t)
    }
    let one = rustledger_core::Decimal::ONE;
    let left = with(vec![
        posting(
            "Assets:A",
            Some(rustledger_core::IncompleteAmount::complete(
                one,
                "USD".to_owned(),
            )),
        ),
        posting("Assets:B", None),
    ]);
    let right = with(vec![
        posting(
            "Assets:A",
            Some(rustledger_core::IncompleteAmount::number_only(one)),
        ),
        posting(
            "USD",
            Some(rustledger_core::IncompleteAmount::currency_only(
                "Assets:B".to_owned(),
            )),
        ),
    ]);
    assert_ne!(
        hash(&left),
        hash(&right),
        "units re-partitioned across a posting boundary must not collide",
    );
}

/// A posting's cost, price and flag are part of its identity.
///
/// They were not hashed at all — a different defect from the boundary
/// ambiguity above: not two fields blurring together, but fields never
/// consulted. Caught by Copilot on review, and all of these collided before
/// the fix. The first is the one that matters: two purchases of the same stock
/// at different prices were the same object to every consumer of `meta.hash`.
#[test]
fn cost_price_and_flag_are_part_of_posting_identity() {
    use rustledger_core::{CostNumber, CostSpec, Decimal, IncompleteAmount, PriceKind};

    fn cost(number: Option<CostNumber>) -> CostSpec {
        CostSpec {
            number,
            currency: Some("USD".into()),
            ..CostSpec::empty()
        }
    }
    fn per_unit(v: i64) -> Option<CostNumber> {
        Some(CostNumber::PerUnit {
            value: Decimal::from(v),
        })
    }
    let build = |mutate: &dyn Fn(&mut rustledger_core::directive::Posting)| {
        let mut p = rustledger_core::directive::Posting::new(
            "Assets:A",
            rustledger_core::Amount::new(Decimal::ONE, "HOOL"),
        );
        mutate(&mut p);
        let Directive::Transaction(mut t) = txn(None, "n", &[], &[]) else {
            unreachable!()
        };
        t.postings = vec![rustledger_core::Spanned::new(
            p,
            rustledger_core::Span::new(0, 0),
        )];
        Directive::Transaction(t)
    };

    let plain = build(&|_| {});
    let cost_100 = build(&|p| p.cost = Some(cost(per_unit(100))));
    let cost_200 = build(&|p| p.cost = Some(cost(per_unit(200))));
    let cost_total = build(&|p| {
        p.cost = Some(cost(Some(CostNumber::Total {
            value: Decimal::from(100),
        })));
    });
    let cost_labelled = build(&|p| {
        let mut c = cost(per_unit(100));
        c.label = Some("lot-a".to_owned());
        p.cost = Some(c);
    });
    let flagged = build(&|p| p.flag = Some('!'));
    let priced = build(&|p| {
        p.price = Some(rustledger_core::PriceAnnotation {
            kind: PriceKind::Unit,
            amount: Some(IncompleteAmount::complete(
                Decimal::from(100),
                "USD".to_owned(),
            )),
        });
    });
    let priced_total = build(&|p| {
        p.price = Some(rustledger_core::PriceAnnotation {
            kind: PriceKind::Total,
            amount: Some(IncompleteAmount::complete(
                Decimal::from(100),
                "USD".to_owned(),
            )),
        });
    });

    let cases: [(&Directive, &Directive, &str); 7] = [
        (&cost_100, &cost_200, "a different cost number"),
        (&cost_100, &plain, "a cost vs no cost"),
        (
            &cost_100,
            &cost_total,
            "per-unit {100} vs total {{100}} — the accessors cannot tell these \
             apart from the booked and compound shapes, which is why the match \
             is written out",
        ),
        (&cost_100, &cost_labelled, "a lot label"),
        (&flagged, &plain, "a posting flag"),
        (&priced, &plain, "a price vs no price"),
        (&priced, &priced_total, "@ vs @@ at the same amount"),
    ];
    let collisions: Vec<&str> = cases
        .iter()
        .filter(|(left, right, _)| hash(left) == hash(right))
        .map(|(_, _, what)| *what)
        .collect();
    assert!(
        collisions.is_empty(),
        "{} of {} posting-identity cases collided: {collisions:#?}",
        collisions.len(),
        cases.len(),
    );
}
