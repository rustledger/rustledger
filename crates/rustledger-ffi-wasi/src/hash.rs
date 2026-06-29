//! Directive hashing (core → hash, DTO-free).

use std::fmt::Write;

use sha2::{Digest, Sha256};

use rustledger_core::Directive;

/// Compute a SHA256 hash of a directive for unique identification.
pub fn compute_directive_hash(directive: &Directive) -> String {
    let mut hasher = Sha256::new();

    // Hash the directive type and core content
    match directive {
        Directive::Transaction(t) => {
            hasher.update(b"Transaction");
            hasher.update(t.date.to_string().as_bytes());
            hasher.update(t.flag.to_string().as_bytes());
            if let Some(ref payee) = t.payee {
                hasher.update(payee.as_bytes());
            }
            hasher.update(t.narration.as_bytes());
            for tag in &t.tags {
                hasher.update(tag.as_bytes());
            }
            for link in &t.links {
                hasher.update(link.as_bytes());
            }
            for posting in &t.postings {
                hasher.update(posting.account.as_bytes());
                if let Some(ref units) = posting.units {
                    if let Some(num) = units.number() {
                        hasher.update(num.to_string().as_bytes());
                    }
                    if let Some(cur) = units.currency() {
                        hasher.update(cur.as_bytes());
                    }
                }
            }
        }
        Directive::Open(o) => {
            hasher.update(b"Open");
            hasher.update(o.date.to_string().as_bytes());
            hasher.update(o.account.as_bytes());
            for c in &o.currencies {
                hasher.update(c.as_bytes());
            }
        }
        Directive::Close(c) => {
            hasher.update(b"Close");
            hasher.update(c.date.to_string().as_bytes());
            hasher.update(c.account.as_bytes());
        }
        Directive::Balance(b) => {
            hasher.update(b"Balance");
            hasher.update(b.date.to_string().as_bytes());
            hasher.update(b.account.as_bytes());
            hasher.update(b.amount.number.to_string().as_bytes());
            hasher.update(b.amount.currency.as_bytes());
        }
        Directive::Pad(p) => {
            hasher.update(b"Pad");
            hasher.update(p.date.to_string().as_bytes());
            hasher.update(p.account.as_bytes());
            hasher.update(p.source_account.as_bytes());
        }
        Directive::Commodity(c) => {
            hasher.update(b"Commodity");
            hasher.update(c.date.to_string().as_bytes());
            hasher.update(c.currency.as_bytes());
        }
        Directive::Price(p) => {
            hasher.update(b"Price");
            hasher.update(p.date.to_string().as_bytes());
            hasher.update(p.currency.as_bytes());
            hasher.update(p.amount.number.to_string().as_bytes());
            hasher.update(p.amount.currency.as_bytes());
        }
        Directive::Event(e) => {
            hasher.update(b"Event");
            hasher.update(e.date.to_string().as_bytes());
            hasher.update(e.event_type.as_bytes());
            hasher.update(e.value.as_bytes());
        }
        Directive::Note(n) => {
            hasher.update(b"Note");
            hasher.update(n.date.to_string().as_bytes());
            hasher.update(n.account.as_bytes());
            hasher.update(n.comment.as_bytes());
        }
        Directive::Document(d) => {
            hasher.update(b"Document");
            hasher.update(d.date.to_string().as_bytes());
            hasher.update(d.account.as_bytes());
            hasher.update(d.path.as_bytes());
        }
        Directive::Query(q) => {
            hasher.update(b"Query");
            hasher.update(q.date.to_string().as_bytes());
            hasher.update(q.name.as_bytes());
            hasher.update(q.query.as_bytes());
        }
        Directive::Custom(c) => {
            hasher.update(b"Custom");
            hasher.update(c.date.to_string().as_bytes());
            hasher.update(c.custom_type.as_bytes());
        }
    }

    let result = hasher.finalize();
    result.iter().fold(String::new(), |mut s, b| {
        let _ = write!(s, "{b:02x}");
        s
    })
}
