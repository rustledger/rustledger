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
/// Posting `meta` and comments are deliberately NOT hashed; see #1968.
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
        }
        Directive::Open(o) => {
            field(&mut hasher, b"Open");
            field(&mut hasher, o.date.to_string().as_bytes());
            field(&mut hasher, o.account.as_bytes());
            count(&mut hasher, o.currencies.len());
            for c in &o.currencies {
                field(&mut hasher, c.as_bytes());
            }
        }
        Directive::Close(c) => {
            field(&mut hasher, b"Close");
            field(&mut hasher, c.date.to_string().as_bytes());
            field(&mut hasher, c.account.as_bytes());
        }
        Directive::Balance(b) => {
            field(&mut hasher, b"Balance");
            field(&mut hasher, b.date.to_string().as_bytes());
            field(&mut hasher, b.account.as_bytes());
            field(&mut hasher, b.amount.number.to_string().as_bytes());
            field(&mut hasher, b.amount.currency.as_bytes());
        }
        Directive::Pad(p) => {
            field(&mut hasher, b"Pad");
            field(&mut hasher, p.date.to_string().as_bytes());
            field(&mut hasher, p.account.as_bytes());
            field(&mut hasher, p.source_account.as_bytes());
        }
        Directive::Commodity(c) => {
            field(&mut hasher, b"Commodity");
            field(&mut hasher, c.date.to_string().as_bytes());
            field(&mut hasher, c.currency.as_bytes());
        }
        Directive::Price(p) => {
            field(&mut hasher, b"Price");
            field(&mut hasher, p.date.to_string().as_bytes());
            field(&mut hasher, p.currency.as_bytes());
            field(&mut hasher, p.amount.number.to_string().as_bytes());
            field(&mut hasher, p.amount.currency.as_bytes());
        }
        Directive::Event(e) => {
            field(&mut hasher, b"Event");
            field(&mut hasher, e.date.to_string().as_bytes());
            field(&mut hasher, e.event_type.as_bytes());
            field(&mut hasher, e.value.as_bytes());
        }
        Directive::Note(n) => {
            field(&mut hasher, b"Note");
            field(&mut hasher, n.date.to_string().as_bytes());
            field(&mut hasher, n.account.as_bytes());
            field(&mut hasher, n.comment.as_bytes());
        }
        Directive::Document(d) => {
            field(&mut hasher, b"Document");
            field(&mut hasher, d.date.to_string().as_bytes());
            field(&mut hasher, d.account.as_bytes());
            field(&mut hasher, d.path.as_bytes());
        }
        Directive::Query(q) => {
            field(&mut hasher, b"Query");
            field(&mut hasher, q.date.to_string().as_bytes());
            field(&mut hasher, q.name.as_bytes());
            field(&mut hasher, q.query.as_bytes());
        }
        Directive::Custom(c) => {
            field(&mut hasher, b"Custom");
            field(&mut hasher, c.date.to_string().as_bytes());
            field(&mut hasher, c.custom_type.as_bytes());
        }
    }

    let result = hasher.finalize();
    result.iter().fold(String::new(), |mut s, b| {
        let _ = write!(s, "{b:02x}");
        s
    })
}
