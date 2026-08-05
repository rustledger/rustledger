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
                field(&mut hasher, posting.account.as_bytes());
                match &posting.units {
                    Some(units) => {
                        hasher.update([1u8]);
                        let number = units.number().map(|n| n.to_string());
                        opt(&mut hasher, number.as_deref().map(str::as_bytes));
                        opt(&mut hasher, units.currency().map(str::as_bytes));
                    }
                    None => hasher.update([0u8]),
                }
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
