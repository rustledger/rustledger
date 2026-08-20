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
    let cost_100 = build(&|p| p.cost = Some(Box::new(cost(per_unit(100)))));
    let cost_200 = build(&|p| p.cost = Some(Box::new(cost(per_unit(200)))));
    let cost_total = build(&|p| {
        p.cost = Some(Box::new(cost(Some(CostNumber::Total {
            value: Decimal::from(100),
        }))));
    });
    let cost_labelled = build(&|p| {
        let mut c = cost(per_unit(100));
        c.label = Some("lot-a".to_owned());
        p.cost = Some(Box::new(c));
    });
    let flagged = build(&|p| p.flag = Some('!'));
    let priced = build(&|p| {
        p.price = Some(Box::new(rustledger_core::PriceAnnotation {
            kind: PriceKind::Unit,
            amount: Some(IncompleteAmount::complete(
                Decimal::from(100),
                "USD".to_owned(),
            )),
        }));
    });
    let priced_total = build(&|p| {
        p.price = Some(Box::new(rustledger_core::PriceAnnotation {
            kind: PriceKind::Total,
            amount: Some(IncompleteAmount::complete(
                Decimal::from(100),
                "USD".to_owned(),
            )),
        }));
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

/// Build a metadata map from key/value pairs.
fn meta(pairs: &[(&str, rustledger_core::MetaValue)]) -> Metadata {
    pairs
        .iter()
        .map(|(k, v)| ((*k).to_owned(), v.clone()))
        .collect()
}

fn txn_with_meta(m: Metadata) -> Directive {
    let Directive::Transaction(mut t) = txn(None, "n", &[], &[]) else {
        unreachable!()
    };
    t.meta = m;
    Directive::Transaction(t)
}

/// User metadata is part of a directive's identity — the #1968 decision.
///
/// Two directives differing only by a metadata key were the same object to
/// every consumer of `meta.hash`, including rustfava's `insert_metadata`, which
/// resolves an entry BY hash and then writes to that entry's line without any
/// second factor. The endpoint whose whole job is creating metadata-only
/// differences was the one unguarded against them.
#[test]
fn metadata_is_part_of_the_identity() {
    use rustledger_core::MetaValue as V;

    let none = txn_with_meta(meta(&[]));
    let a = txn_with_meta(meta(&[("k", V::String("a".into()))]));
    let b = txn_with_meta(meta(&[("k", V::String("b".into()))]));
    let other_key = txn_with_meta(meta(&[("j", V::String("a".into()))]));
    let two = txn_with_meta(meta(&[
        ("k", V::String("a".into())),
        ("j", V::String("b".into())),
    ]));

    let cases: [(&Directive, &Directive, &str); 4] = [
        (&none, &a, "metadata present vs absent"),
        (&a, &b, "a different value under the same key"),
        (&a, &other_key, "the same value under a different key"),
        (&a, &two, "an additional key"),
    ];
    let collisions: Vec<&str> = cases
        .iter()
        .filter(|(left, right, _)| hash(left) == hash(right))
        .map(|(_, _, what)| *what)
        .collect();
    assert!(
        collisions.is_empty(),
        "{} of {} metadata cases collided: {collisions:#?}",
        collisions.len(),
        cases.len(),
    );
}

/// A metadata VALUE's type is part of its identity, not just its rendering.
///
/// `MetaValue`'s `Display` is lossy across variants: `Number(42)` and `Int(42)`
/// both render `42`. The parser goes to deliberate trouble (#1766) to keep
/// those distinct, so hashing the rendering would throw the distinction away
/// again one layer down. Hence the variant tag.
#[test]
fn metadata_value_types_do_not_collide() {
    use rustledger_core::MetaValue as V;

    let int = txn_with_meta(meta(&[("k", V::Int(42))]));
    let number = txn_with_meta(meta(&[("k", V::Number(42.into()))]));
    let string = txn_with_meta(meta(&[("k", V::String("42".into()))]));
    let null = txn_with_meta(meta(&[("k", V::None)]));
    let bool_true = txn_with_meta(meta(&[("k", V::Bool(true))]));
    let bool_false = txn_with_meta(meta(&[("k", V::Bool(false))]));

    let cases: [(&Directive, &Directive, &str); 4] = [
        (&int, &number, "Int(42) vs Number(42) — both render `42`"),
        (&int, &string, "Int(42) vs String(\"42\")"),
        (&null, &bool_false, "None vs Bool(false)"),
        (&bool_true, &bool_false, "Bool(true) vs Bool(false)"),
    ];
    let collisions: Vec<&str> = cases
        .iter()
        .filter(|(left, right, _)| hash(left) == hash(right))
        .map(|(_, _, what)| *what)
        .collect();
    assert!(
        collisions.is_empty(),
        "{} of {} meta-value cases collided: {collisions:#?}",
        collisions.len(),
        cases.len(),
    );
}

/// The same metadata hashes the same however the map was built.
///
/// `Metadata` is an `FxHashMap`, so iteration order is an implementation
/// detail. Hashing it as it iterates would make the digest depend on insertion
/// history — nondeterminism in the one field every consumer treats as stable.
/// Inserting the same pairs in the opposite order is the cheapest way to reach
/// a differently-ordered map.
#[test]
fn metadata_hashing_does_not_depend_on_map_order() {
    use rustledger_core::MetaValue as V;

    let pairs = [
        ("alpha", V::String("1".into())),
        ("beta", V::Int(2)),
        ("gamma", V::Bool(true)),
        ("delta", V::None),
    ];
    let mut forward = Metadata::default();
    for (k, v) in &pairs {
        forward.insert((*k).to_owned(), v.clone());
    }
    let mut backward = Metadata::default();
    for (k, v) in pairs.iter().rev() {
        backward.insert((*k).to_owned(), v.clone());
    }

    // Self-check FIRST. This test only exercises the sort if the two maps
    // actually iterate differently — and whether they do is a property of
    // these particular keys and `FxHashMap`'s bucket layout, not something
    // the test controls. If a hasher change or a different key set ever makes
    // both iterate identically, the assertion below would pass with the sort
    // deleted. Failing loudly here is the difference between a guard and a
    // decoration.
    let f: Vec<&String> = forward.keys().collect();
    let b: Vec<&String> = backward.keys().collect();
    assert_ne!(
        f, b,
        "these two maps iterate identically, so this test can no longer \
         distinguish a sorted digest from an unsorted one — pick keys that \
         do produce different orders"
    );

    assert_eq!(
        hash(&txn_with_meta(forward)),
        hash(&txn_with_meta(backward)),
        "insertion order must not reach the digest"
    );
}

/// Comments are deliberately NOT part of the identity — the other half of
/// #1968.
///
/// This asserts a deliberate collision, which is the only way to pin a decision
/// to EXCLUDE something: if a future change starts hashing comments, this test
/// fails and the decision gets re-made on purpose rather than by accident.
#[test]
fn comments_are_deliberately_not_part_of_the_identity() {
    let plain = txn(None, "n", &[], &[]);

    let Directive::Transaction(mut t) = txn(None, "n", &[], &[]) else {
        unreachable!()
    };
    t.trailing_comments = vec!["; a note to self".to_owned()];
    let commented = Directive::Transaction(t);

    assert_eq!(
        hash(&plain),
        hash(&commented),
        "a comment must not change a directive's identity (#1968)"
    );
}

/// Fields that reached NO digest at all, found by auditing every directive
/// struct's fields against the arms of `compute_directive_hash`.
///
/// Same defect class as the `cost`/`price`/`flag` omission #1961 fixed — not
/// two fields blurring together, but fields never consulted. These are not the
/// #1968 judgment call; each is unambiguously identity-bearing:
///
/// - `Open::booking` decides how every reduction against the account is booked.
/// - `Balance::tolerance` — `100 USD` and `100 USD ~ 0.05` are different
///   assertions, and one can pass where the other fails.
/// - `Document::tags`/`links` — a Document carries both, exactly as a
///   Transaction does.
/// - `Custom::values` — the values ARE the directive. Every `custom "budget"`
///   on a given date hashed identically.
#[test]
fn every_directive_field_reaches_the_digest() {
    use rustledger_core::MetaValue as V;
    use rustledger_core::directive::{Balance, Custom, Document, Open};

    let d = naive_date(2024, 1, 1).unwrap();
    let amount = rustledger_core::Amount::new(rustledger_core::Decimal::ONE, "USD");

    let mut open_fifo = Open::new(d, "Assets:A");
    open_fifo.booking = Some("FIFO".to_owned());
    let mut open_lifo = Open::new(d, "Assets:A");
    open_lifo.booking = Some("LIFO".to_owned());
    let open_none = Open::new(d, "Assets:A");

    let bal_plain = Balance::new(d, "Assets:A", amount.clone());
    let mut bal_tol = Balance::new(d, "Assets:A", amount.clone());
    bal_tol.tolerance = Some("0.05".parse().unwrap());
    let mut bal_tol2 = Balance::new(d, "Assets:A", amount);
    bal_tol2.tolerance = Some("0.50".parse().unwrap());

    let doc_plain = Document::new(d, "Assets:A", "/x.pdf");
    let mut doc_tagged = Document::new(d, "Assets:A", "/x.pdf");
    doc_tagged.tags = vec![Tag::new("t")];
    let mut doc_linked = Document::new(d, "Assets:A", "/x.pdf");
    doc_linked.links = vec![Link::new("t")];

    let mut custom_a = Custom::new(d, "budget");
    custom_a.values = vec![V::String("a".into())];
    let mut custom_b = Custom::new(d, "budget");
    custom_b.values = vec![V::String("b".into())];
    let custom_empty = Custom::new(d, "budget");

    let pairs: Vec<(Directive, Directive, &str)> = vec![
        (
            Directive::Open(open_fifo.clone()),
            Directive::Open(open_lifo),
            "Open: FIFO vs LIFO",
        ),
        (
            Directive::Open(open_fifo),
            Directive::Open(open_none),
            "Open: a booking method vs none",
        ),
        (
            Directive::Balance(bal_plain),
            Directive::Balance(bal_tol.clone()),
            "Balance: a tolerance vs none",
        ),
        (
            Directive::Balance(bal_tol),
            Directive::Balance(bal_tol2),
            "Balance: a different tolerance",
        ),
        (
            Directive::Document(doc_plain),
            Directive::Document(doc_tagged.clone()),
            "Document: a tag vs none",
        ),
        (
            Directive::Document(doc_tagged),
            Directive::Document(doc_linked),
            "Document: the same name as a tag vs as a link",
        ),
        (
            Directive::Custom(custom_a.clone()),
            Directive::Custom(custom_b),
            "Custom: a different value",
        ),
        (
            Directive::Custom(custom_a),
            Directive::Custom(custom_empty),
            "Custom: a value vs none",
        ),
    ];
    let collisions: Vec<&str> = pairs
        .iter()
        .filter(|(left, right, _)| hash(left) == hash(right))
        .map(|(_, _, what)| *what)
        .collect();
    assert!(
        collisions.is_empty(),
        "{} of {} never-hashed-field cases collided: {collisions:#?}",
        collisions.len(),
        pairs.len(),
    );
}
