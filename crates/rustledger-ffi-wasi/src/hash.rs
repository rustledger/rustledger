//! Directive hashing (core → hash, DTO-free).

use std::fmt::Write;

use sha2::{Digest, Sha256};

use rustledger_core::Directive;

/// Feed one field into the hash, length-prefixed.
///
/// Without this the hash is ambiguous at every field boundary, because
/// `Sha256::update` just concatenates. Real collisions this produced, all
/// verified before the fix:
///
/// ```text
///   payee "ab" + narration "c"   ==  payee "a"  + narration "bc"
///   tags ["ab"]                  ==  tags ["a"] + links ["b"]
///   no payee  + narration "ab"   ==  payee "a"  + narration "b"
/// ```
///
/// The third is the worst: a transaction WITH a payee hashed identically to one
/// WITHOUT. `compute_directive_hash` is the FFI identity contract - it is
/// surfaced as `meta.hash` across the WIT boundary - so a collision means two
/// distinct directives are the same object to rustfava and the desktop app.
///
/// Length-prefixing rather than a separator byte: fields are arbitrary UTF-8
/// and any sentinel could legitimately occur inside one. A `u64` length cannot.
fn field(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

/// Feed a collection's LENGTH into the hash before its elements.
///
/// Length-prefixing each element is not enough on its own, which Copilot caught
/// on review. A stream of length-prefixed fields decodes to a unique SEQUENCE
/// of byte strings, but two different structures can produce the SAME sequence
/// whenever a variable-length collection abuts anything else:
///
/// ```text
///   tags ["a","b"], links []   ==  tags ["a"], links ["b"]
/// ```
///
/// Both emit `["a", "b"]`. Counting the elements pins the partition, so a field
/// can no longer migrate across a collection boundary undetected.
///
/// This is the same defect the length prefix fixed, one level up: the element
/// boundaries were unambiguous, the COLLECTION boundaries were not.
fn count(hasher: &mut Sha256, n: usize) {
    hasher.update((n as u64).to_le_bytes());
}

/// Feed an OPTIONAL field into the hash, presence-tagged.
///
/// [`count`] does not subsume this. Within the postings list a posting emits
/// its account and then zero, one, or two further fields depending on whether
/// its units carry a number, a currency, both, or are absent - so even at a
/// fixed posting COUNT the fields can be re-partitioned:
///
/// ```text
///   [Assets:A  1 USD] [Assets:B]       ->  "Assets:A" "1" "USD" "Assets:B"
///   [Assets:A  1    ] [USD  Assets:B]  ->  "Assets:A" "1" "USD" "Assets:B"
/// ```
///
/// Same count, same fields, different transactions. That case is reachable only
/// through the presence tag; the payee tag is the same mechanism applied
/// uniformly, and is belt-and-braces rather than load-bearing (the fixed run of
/// three collection counts after the narration already separates a present
/// payee from an absent one).
///
/// The tag byte sits outside the field's own length prefix, so no field content
/// can forge it.
fn opt(hasher: &mut Sha256, bytes: Option<&[u8]>) {
    match bytes {
        Some(b) => {
            hasher.update([1u8]);
            field(hasher, b);
        }
        None => hasher.update([0u8]),
    }
}

/// Feed a `Decimal` in, as its canonical rendering.
fn decimal(hasher: &mut Sha256, d: rustledger_core::Decimal) {
    field(hasher, d.to_string().as_bytes());
}

/// Feed one metadata VALUE in, variant-tagged.
///
/// The tag is not decoration. `MetaValue`'s `Display` is lossy across variants -
/// `Number(42)` and `Int(42)` both render `42`, and `Account("Assets:A")`
/// renders the same as a `String` would if the quoting were dropped - so
/// hashing the rendering would collide `key: 42` with `key: 42.0` where the
/// parser went to deliberate trouble (#1766) to keep them distinct.
///
/// Written out variant by variant rather than through `Display` for the same
/// reason `CostNumber` is below: an exhaustive match means adding a variant is
/// a compile error here, which forces the identity question to be answered
/// rather than silently defaulted. `MetaValue::Int` was appended once already.
fn meta_value(hasher: &mut Sha256, v: &rustledger_core::MetaValue) {
    use rustledger_core::MetaValue as V;

    match v {
        V::String(s) => {
            hasher.update([1u8]);
            field(hasher, s.as_bytes());
        }
        V::Account(a) => {
            hasher.update([2u8]);
            field(hasher, a.as_bytes());
        }
        V::Currency(c) => {
            hasher.update([3u8]);
            field(hasher, c.as_bytes());
        }
        V::Tag(t) => {
            hasher.update([4u8]);
            field(hasher, t.as_bytes());
        }
        V::Link(l) => {
            hasher.update([5u8]);
            field(hasher, l.as_bytes());
        }
        V::Date(d) => {
            hasher.update([6u8]);
            field(hasher, d.to_string().as_bytes());
        }
        V::Number(n) => {
            hasher.update([7u8]);
            decimal(hasher, *n);
        }
        V::Bool(b) => {
            hasher.update([8u8]);
            hasher.update([u8::from(*b)]);
        }
        V::Amount(a) => {
            hasher.update([9u8]);
            decimal(hasher, a.number);
            field(hasher, a.currency.as_bytes());
        }
        V::None => hasher.update([10u8]),
        V::Int(i) => {
            hasher.update([11u8]);
            field(hasher, i.to_string().as_bytes());
        }
    }
}

/// Feed a directive's or posting's user metadata in, key-sorted.
///
/// `Metadata` is an `FxHashMap`, so its iteration order is not stable across
/// runs - hashing it as it iterates would make the digest nondeterministic,
/// which is the one thing every consumer relies on. Sorting by key also makes
/// this agree with `meta_entries_from_core` in the component's converter, which
/// sorts for the same reason before filling the WIT `user` list. The two now
/// order the same data the same way.
///
/// Metadata is IN the identity per #1968: it is structured user data with a
/// whole write API (`insert_metadata`) premised on it being meaningful, so two
/// postings differing only by a metadata key are not the same object.
///
/// Comments are OUT, per the same decision. They are presentation rather than
/// data, they do not reliably survive a parse/format round trip, and including
/// them would mean fixing a typo in a comment changes a directive's identity.
fn metadata(hasher: &mut Sha256, m: &rustledger_core::Metadata) {
    count(hasher, m.len());
    let mut keys: Vec<&String> = m.keys().collect();
    keys.sort_unstable();
    for k in keys {
        field(hasher, k.as_bytes());
        meta_value(hasher, &m[k]);
    }
}

/// Feed an optional amount in, presence-tagged, number then currency.
fn incomplete_amount(hasher: &mut Sha256, amount: Option<&rustledger_core::IncompleteAmount>) {
    match amount {
        Some(a) => {
            hasher.update([1u8]);
            let number = a.number().map(|n| n.to_string());
            opt(hasher, number.as_deref().map(str::as_bytes));
            opt(hasher, a.currency().map(str::as_bytes));
        }
        None => hasher.update([0u8]),
    }
}

/// Feed a posting's whole identity in - not just its account and units.
///
/// `cost`, `price` and `flag` were absent from the digest entirely, which
/// Copilot caught on review of #1961. That is a different defect from the
/// boundary ambiguity above: not two fields blurring together, but fields
/// never consulted at all. `2 HOOL {100.00 USD}` and `2 HOOL {200.00 USD}`
/// hashed identically - two economically different transactions that rustfava
/// and the desktop app could not tell apart.
///
/// The `CostNumber` match is written out variant by variant rather than
/// through the `per_unit()`/`total()` accessors on purpose. Those two cannot
/// distinguish `PerUnitFromTotal` from `Compound` (both set both), and an
/// exhaustive match means adding a variant is a compile error here - which
/// forces the identity question to be answered rather than silently defaulted.
///
/// Posting `meta` IS hashed and posting comments are not — the #1968 split.
/// Metadata is structured user data with a write API premised on it being
/// meaningful; comments are presentation, and do not reliably survive a
/// parse/format round trip. See [`metadata`].
fn posting_identity(hasher: &mut Sha256, p: &rustledger_core::directive::Posting) {
    use rustledger_core::CostNumber;

    field(hasher, p.account.as_bytes());
    incomplete_amount(hasher, p.units.as_ref());

    let flag = p.flag.map(|c| c.to_string());
    opt(hasher, flag.as_deref().map(str::as_bytes));

    match &p.cost {
        Some(c) => {
            hasher.update([1u8]);
            match &c.number {
                None => hasher.update([0u8]),
                Some(CostNumber::PerUnit { value }) => {
                    hasher.update([1u8]);
                    decimal(hasher, *value);
                }
                Some(CostNumber::Total { value }) => {
                    hasher.update([2u8]);
                    decimal(hasher, *value);
                }
                Some(CostNumber::PerUnitFromTotal(booked)) => {
                    hasher.update([3u8]);
                    decimal(hasher, booked.per_unit);
                    decimal(hasher, booked.total);
                }
                Some(CostNumber::Compound { per_unit, total }) => {
                    hasher.update([4u8]);
                    decimal(hasher, *per_unit);
                    decimal(hasher, *total);
                }
            }
            opt(hasher, c.currency.as_deref().map(str::as_bytes));
            let date = c.date.map(|d| d.to_string());
            opt(hasher, date.as_deref().map(str::as_bytes));
            opt(hasher, c.label.as_deref().map(str::as_bytes));
            hasher.update([u8::from(c.merge)]);
        }
        None => hasher.update([0u8]),
    }

    match &p.price {
        Some(price) => {
            hasher.update([1u8]);
            match price.kind {
                rustledger_core::PriceKind::Unit => hasher.update([1u8]),
                rustledger_core::PriceKind::Total => hasher.update([2u8]),
            }
            incomplete_amount(hasher, price.amount.as_ref());
        }
        None => hasher.update([0u8]),
    }

    metadata(hasher, &p.meta);
    // `comments` / `trailing_comments` are deliberately NOT hashed - #1968.
}

/// Compute a SHA256 hash of a directive for unique identification.
pub fn compute_directive_hash(directive: &Directive) -> String {
    let mut hasher = Sha256::new();

    // Hash the directive type and core content
    match directive {
        Directive::Transaction(t) => {
            field(&mut hasher, b"Transaction");
            field(&mut hasher, t.date.to_string().as_bytes());
            field(&mut hasher, t.flag.to_string().as_bytes());
            opt(&mut hasher, t.payee.as_deref().map(str::as_bytes));
            field(&mut hasher, t.narration.as_bytes());
            count(&mut hasher, t.tags.len());
            for tag in &t.tags {
                field(&mut hasher, tag.as_bytes());
            }
            count(&mut hasher, t.links.len());
            for link in &t.links {
                field(&mut hasher, link.as_bytes());
            }
            count(&mut hasher, t.postings.len());
            for posting in &t.postings {
                posting_identity(&mut hasher, posting);
            }
            metadata(&mut hasher, &t.meta);
            // `trailing_comments` deliberately NOT hashed - #1968.
        }
        Directive::Open(o) => {
            field(&mut hasher, b"Open");
            field(&mut hasher, o.date.to_string().as_bytes());
            field(&mut hasher, o.account.as_bytes());
            count(&mut hasher, o.currencies.len());
            for c in &o.currencies {
                field(&mut hasher, c.as_bytes());
            }
            // Never consulted before: two Opens differing only by booking
            // method hashed identically, and the method decides how every
            // reduction against the account is booked.
            opt(&mut hasher, o.booking.as_deref().map(str::as_bytes));
            metadata(&mut hasher, &o.meta);
        }
        Directive::Close(c) => {
            field(&mut hasher, b"Close");
            field(&mut hasher, c.date.to_string().as_bytes());
            field(&mut hasher, c.account.as_bytes());
            metadata(&mut hasher, &c.meta);
        }
        Directive::Balance(b) => {
            field(&mut hasher, b"Balance");
            field(&mut hasher, b.date.to_string().as_bytes());
            field(&mut hasher, b.account.as_bytes());
            field(&mut hasher, b.amount.number.to_string().as_bytes());
            field(&mut hasher, b.amount.currency.as_bytes());
            // Never consulted before: `100 USD` and `100 USD ~ 0.05` are
            // different assertions and hashed the same.
            let tolerance = b.tolerance.map(|t| t.to_string());
            opt(&mut hasher, tolerance.as_deref().map(str::as_bytes));
            metadata(&mut hasher, &b.meta);
        }
        Directive::Pad(p) => {
            field(&mut hasher, b"Pad");
            field(&mut hasher, p.date.to_string().as_bytes());
            field(&mut hasher, p.account.as_bytes());
            field(&mut hasher, p.source_account.as_bytes());
            metadata(&mut hasher, &p.meta);
        }
        Directive::Commodity(c) => {
            field(&mut hasher, b"Commodity");
            field(&mut hasher, c.date.to_string().as_bytes());
            field(&mut hasher, c.currency.as_bytes());
            metadata(&mut hasher, &c.meta);
        }
        Directive::Price(p) => {
            field(&mut hasher, b"Price");
            field(&mut hasher, p.date.to_string().as_bytes());
            field(&mut hasher, p.currency.as_bytes());
            field(&mut hasher, p.amount.number.to_string().as_bytes());
            field(&mut hasher, p.amount.currency.as_bytes());
            metadata(&mut hasher, &p.meta);
        }
        Directive::Event(e) => {
            field(&mut hasher, b"Event");
            field(&mut hasher, e.date.to_string().as_bytes());
            field(&mut hasher, e.event_type.as_bytes());
            field(&mut hasher, e.value.as_bytes());
            metadata(&mut hasher, &e.meta);
        }
        Directive::Note(n) => {
            field(&mut hasher, b"Note");
            field(&mut hasher, n.date.to_string().as_bytes());
            field(&mut hasher, n.account.as_bytes());
            field(&mut hasher, n.comment.as_bytes());
            metadata(&mut hasher, &n.meta);
        }
        Directive::Document(d) => {
            field(&mut hasher, b"Document");
            field(&mut hasher, d.date.to_string().as_bytes());
            field(&mut hasher, d.account.as_bytes());
            field(&mut hasher, d.path.as_bytes());
            // Never consulted before: a Document carries tags and links just
            // as a Transaction does, and neither reached the digest.
            count(&mut hasher, d.tags.len());
            for tag in &d.tags {
                field(&mut hasher, tag.as_bytes());
            }
            count(&mut hasher, d.links.len());
            for link in &d.links {
                field(&mut hasher, link.as_bytes());
            }
            metadata(&mut hasher, &d.meta);
        }
        Directive::Query(q) => {
            field(&mut hasher, b"Query");
            field(&mut hasher, q.date.to_string().as_bytes());
            field(&mut hasher, q.name.as_bytes());
            field(&mut hasher, q.query.as_bytes());
            metadata(&mut hasher, &q.meta);
        }
        Directive::Custom(c) => {
            field(&mut hasher, b"Custom");
            field(&mut hasher, c.date.to_string().as_bytes());
            field(&mut hasher, c.custom_type.as_bytes());
            // Never consulted before: the values ARE the directive. Every
            // `custom "budget"` on a given date hashed identically.
            count(&mut hasher, c.values.len());
            for v in &c.values {
                meta_value(&mut hasher, v);
            }
            metadata(&mut hasher, &c.meta);
        }
    }

    let result = hasher.finalize();
    result.iter().fold(String::new(), |mut s, b| {
        let _ = write!(s, "{b:02x}");
        s
    })
}
