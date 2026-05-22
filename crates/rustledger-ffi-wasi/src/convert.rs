//! Conversion functions between core types and JSON.

use std::collections::HashMap;
use std::fmt::Write;

use sha2::{Digest, Sha256};

use rustledger_core::Directive;

use crate::types::{
    Amount, DirectiveJson, Meta, Posting, PostingCost, TypedValue, meta_value_to_json,
};

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

/// Convert core directive to JSON output format.
pub fn directive_to_json(directive: &Directive, line: u32, filename: &str) -> DirectiveJson {
    let hash = compute_directive_hash(directive);

    match directive {
        Directive::Transaction(t) => {
            let meta = Meta::new(filename, line, hash, &t.meta);
            DirectiveJson::Transaction {
                date: t.date.to_string(),
                flag: t.flag.to_string(),
                payee: t.payee.as_ref().map(std::string::ToString::to_string),
                narration: if t.narration.is_empty() {
                    None
                } else {
                    Some(t.narration.to_string())
                },
                tags: t
                    .tags
                    .iter()
                    .map(std::string::ToString::to_string)
                    .collect(),
                links: t
                    .links
                    .iter()
                    .map(std::string::ToString::to_string)
                    .collect(),
                postings: t
                    .postings
                    .iter()
                    .map(|p| {
                        // Extract amount from IncompleteAmount
                        let units = p.units.as_ref().and_then(|u| {
                            u.as_amount().map(|a| Amount {
                                number: a.number.to_string(),
                                currency: a.currency.to_string(),
                            })
                        });

                        // Extract cost. The wire `CostNumber` is a
                        // tagged enum that mirrors the host shape — JSON
                        // consumers branch on `kind` exactly like Rust
                        // pattern matching, with no risk of constructing
                        // the both-set invalid state.
                        let cost = p.cost.as_ref().map(|c| {
                            use crate::types::output::CostNumber as WireCN;
                            let number = c.number.map(|n| match n {
                                rustledger_core::CostNumber::PerUnit { value: d } => {
                                    WireCN::PerUnit {
                                        value: d.to_string(),
                                    }
                                }
                                rustledger_core::CostNumber::Total { value: d } => WireCN::Total {
                                    value: d.to_string(),
                                },
                                rustledger_core::CostNumber::PerUnitFromTotal(b) => {
                                    WireCN::PerUnitFromTotal {
                                        per_unit: b.per_unit.to_string(),
                                        total: b.total.to_string(),
                                    }
                                }
                            });
                            PostingCost {
                                number,
                                currency: c.currency.as_ref().map(std::string::ToString::to_string),
                                date: c.date.map(|d| d.to_string()),
                                label: c.label.clone(),
                            }
                        });

                        // Extract price from PriceAnnotation
                        let price = p.price.as_ref().and_then(|pr| {
                            pr.amount().map(|a| Amount {
                                number: a.number.to_string(),
                                currency: a.currency.to_string(),
                            })
                        });

                        // Posting metadata
                        let mut posting_meta = HashMap::new();
                        for (key, value) in &p.meta {
                            posting_meta.insert(key.clone(), meta_value_to_json(value));
                        }

                        Posting {
                            account: p.account.to_string(),
                            units,
                            cost,
                            price,
                            flag: p.flag.map(|c| c.to_string()),
                            meta: posting_meta,
                        }
                    })
                    .collect(),
                meta,
            }
        }
        Directive::Open(o) => {
            let meta = Meta::new(filename, line, hash, &o.meta);
            DirectiveJson::Open {
                date: o.date.to_string(),
                account: o.account.to_string(),
                currencies: o
                    .currencies
                    .iter()
                    .map(std::string::ToString::to_string)
                    .collect(),
                booking: o.booking.clone(),
                meta,
            }
        }
        Directive::Close(c) => {
            let meta = Meta::new(filename, line, hash, &c.meta);
            DirectiveJson::Close {
                date: c.date.to_string(),
                account: c.account.to_string(),
                meta,
            }
        }
        Directive::Balance(b) => {
            let meta = Meta::new(filename, line, hash, &b.meta);
            DirectiveJson::Balance {
                date: b.date.to_string(),
                account: b.account.to_string(),
                amount: Amount {
                    number: b.amount.number.to_string(),
                    currency: b.amount.currency.to_string(),
                },
                tolerance: b.tolerance.map(|t| t.to_string()),
                meta,
            }
        }
        Directive::Pad(p) => {
            let meta = Meta::new(filename, line, hash, &p.meta);
            DirectiveJson::Pad {
                date: p.date.to_string(),
                account: p.account.to_string(),
                source_account: p.source_account.to_string(),
                meta,
            }
        }
        Directive::Commodity(c) => {
            let meta = Meta::new(filename, line, hash, &c.meta);
            DirectiveJson::Commodity {
                date: c.date.to_string(),
                currency: c.currency.to_string(),
                meta,
            }
        }
        Directive::Price(p) => {
            let meta = Meta::new(filename, line, hash, &p.meta);
            DirectiveJson::Price {
                date: p.date.to_string(),
                currency: p.currency.to_string(),
                amount: Amount {
                    number: p.amount.number.to_string(),
                    currency: p.amount.currency.to_string(),
                },
                meta,
            }
        }
        Directive::Event(e) => {
            let meta = Meta::new(filename, line, hash, &e.meta);
            DirectiveJson::Event {
                date: e.date.to_string(),
                event_type: e.event_type.clone(),
                value: e.value.clone(),
                meta,
            }
        }
        Directive::Note(n) => {
            let meta = Meta::new(filename, line, hash, &n.meta);
            DirectiveJson::Note {
                date: n.date.to_string(),
                account: n.account.to_string(),
                comment: n.comment.clone(),
                meta,
            }
        }
        Directive::Document(d) => {
            let meta = Meta::new(filename, line, hash, &d.meta);
            DirectiveJson::Document {
                date: d.date.to_string(),
                account: d.account.to_string(),
                path: d.path.clone(),
                meta,
            }
        }
        Directive::Query(q) => {
            let meta = Meta::new(filename, line, hash, &q.meta);
            DirectiveJson::Query {
                date: q.date.to_string(),
                name: q.name.clone(),
                query_string: q.query.clone(),
                meta,
            }
        }
        Directive::Custom(c) => {
            let meta = Meta::new(filename, line, hash, &c.meta);
            DirectiveJson::Custom {
                date: c.date.to_string(),
                custom_type: c.custom_type.clone(),
                values: c.values.iter().map(TypedValue::from_meta_value).collect(),
                meta,
            }
        }
    }
}

/// Convert query Value to JSON.
pub fn value_to_json(value: &rustledger_query::Value) -> serde_json::Value {
    use rustledger_query::Value;
    match value {
        Value::Null => serde_json::Value::Null,
        Value::Boolean(b) => serde_json::Value::Bool(*b),
        Value::Integer(i) => serde_json::json!(i),
        Value::String(s) => serde_json::Value::String(s.clone()),
        Value::Date(d) => serde_json::Value::String(d.to_string()),
        Value::Number(d) => serde_json::json!({"number": d.to_string()}),
        Value::Amount(a) => serde_json::json!({
            "number": a.number.to_string(),
            "currency": a.currency
        }),
        Value::Position(p) => serde_json::json!({
            "units": {
                "number": p.units.number.to_string(),
                "currency": p.units.currency
            }
        }),
        Value::Inventory(inv) => {
            let positions: Vec<_> = inv
                .positions()
                .map(|p| {
                    serde_json::json!({
                        "units": {
                            "number": p.units.number.to_string(),
                            "currency": p.units.currency
                        }
                    })
                })
                .collect();
            serde_json::json!({ "positions": positions })
        }
        Value::StringSet(set) => {
            serde_json::json!(set)
        }
        Value::Object(obj) => {
            let mut map = serde_json::Map::new();
            for (k, v) in obj.as_ref() {
                map.insert(k.clone(), value_to_json(v));
            }
            serde_json::Value::Object(map)
        }
        Value::Metadata(meta) => {
            let obj: serde_json::Map<String, serde_json::Value> = meta
                .iter()
                .map(|(k, v)| (k.clone(), serde_json::json!(format!("{v:?}"))))
                .collect();
            serde_json::Value::Object(obj)
        }
        Value::Interval(interval) => serde_json::json!({
            "count": interval.count,
            "unit": match interval.unit {
                rustledger_query::IntervalUnit::Day => "day",
                rustledger_query::IntervalUnit::Week => "week",
                rustledger_query::IntervalUnit::Month => "month",
                rustledger_query::IntervalUnit::Quarter => "quarter",
                rustledger_query::IntervalUnit::Year => "year",
            },
        }),
        Value::Set(set) => {
            let items: Vec<_> = set.iter().map(value_to_json).collect();
            serde_json::Value::Array(items)
        }
    }
}

/// Get datatype string for a Value.
pub const fn value_datatype(value: &rustledger_query::Value) -> &'static str {
    use rustledger_query::Value;
    match value {
        Value::Null => "null",
        Value::Boolean(_) => "bool",
        Value::Integer(_) => "int",
        Value::String(_) => "str",
        Value::Date(_) => "date",
        Value::Number(_) => "Decimal",
        Value::Amount(_) => "Amount",
        Value::Position(_) => "Position",
        Value::Inventory(_) => "Inventory",
        Value::StringSet(_) => "set",
        Value::Object(_) => "object",
        Value::Metadata(_) => "Metadata",
        Value::Interval(_) => "Interval",
        Value::Set(_) => "set",
    }
}
