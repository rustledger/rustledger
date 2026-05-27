//! Conversion functions between Beancount types and JSON DTOs.

use std::collections::HashMap;

use rustledger_core::{Directive, MetaValue, Metadata};

use crate::types::{
    AmountValue, CellValue, CostNumberJson, CostValue, DirectiveJson, MetaValueJson, PositionValue,
    PostingCostJson, PostingJson,
};

/// Lower a host [`MetaValue`] to the wire [`MetaValueJson`].
///
/// Mirrors `rustledger-ffi-wasi::meta_value_to_json` so the two
/// bindings emit identical metadata across wire surfaces (issue
/// #1168). The host's strong newtypes — `Account`, `Currency`, `Tag`,
/// `Link`, `Date`, `Number` — all flatten to JSON strings; JS
/// consumers that need the strong type info should query a typed API
/// rather than rely on the wire shape.
fn meta_value_to_json(value: &MetaValue) -> MetaValueJson {
    match value {
        MetaValue::String(s) => MetaValueJson::String(s.clone()),
        MetaValue::Account(a) => MetaValueJson::String(a.to_string()),
        MetaValue::Currency(c) => MetaValueJson::String(c.to_string()),
        MetaValue::Tag(t) => MetaValueJson::String(t.to_string()),
        MetaValue::Link(l) => MetaValueJson::String(l.to_string()),
        MetaValue::Date(d) => MetaValueJson::String(d.to_string()),
        // Numbers go through `to_string` to preserve precision — JSON
        // numbers can't represent `rust_decimal::Decimal` losslessly,
        // and matching FFI-WASI's behavior keeps the wire shape
        // portable.
        MetaValue::Number(n) => MetaValueJson::String(n.to_string()),
        MetaValue::Bool(b) => MetaValueJson::Bool(*b),
        MetaValue::Amount(a) => MetaValueJson::Amount {
            number: a.number.to_string(),
            currency: a.currency.to_string(),
        },
        MetaValue::None => MetaValueJson::Null,
    }
}

/// Build the wire `meta` map from a host [`Metadata`].
fn metadata_to_json(meta: &Metadata) -> HashMap<String, MetaValueJson> {
    meta.iter()
        .map(|(k, v)| (k.clone(), meta_value_to_json(v)))
        .collect()
}

/// Convert a Directive to its JSON representation.
pub fn directive_to_json(directive: &Directive) -> DirectiveJson {
    use rustledger_core::PriceAnnotation;

    fn price_annotation_to_amount(pr: &PriceAnnotation) -> Option<AmountValue> {
        // JSON only emits the amount when it's complete; `kind` is
        // encoded separately by callers that care.
        pr.amount
            .as_ref()
            .and_then(rustledger_core::IncompleteAmount::as_amount)
            .map(|a| AmountValue {
                number: a.number.to_string(),
                currency: a.currency.to_string(),
            })
    }

    match directive {
        Directive::Transaction(txn) => DirectiveJson::Transaction {
            date: txn.date.to_string(),
            flag: txn.flag.to_string(),
            payee: txn.payee.as_ref().map(ToString::to_string),
            narration: Some(txn.narration.to_string()),
            tags: txn.tags.iter().map(ToString::to_string).collect(),
            links: txn.links.iter().map(ToString::to_string).collect(),
            postings: txn
                .postings
                .iter()
                .map(|p| PostingJson {
                    account: p.account.to_string(),
                    units: p.units.as_ref().map(|u| AmountValue {
                        number: u.number().map(|n| n.to_string()).unwrap_or_default(),
                        currency: u.currency().map(ToString::to_string).unwrap_or_default(),
                    }),
                    cost: p.cost.as_ref().map(|c| PostingCostJson {
                        // The wire `CostNumberJson` is a tagged enum
                        // mirroring `CostNumber`; JS branches on `kind`.
                        number: c.number.map(|n| match n {
                            rustledger_core::CostNumber::PerUnit { value: d } => {
                                CostNumberJson::PerUnit {
                                    value: d.to_string(),
                                }
                            }
                            rustledger_core::CostNumber::Total { value: d } => {
                                CostNumberJson::Total {
                                    value: d.to_string(),
                                }
                            }
                            rustledger_core::CostNumber::PerUnitFromTotal(b) => {
                                CostNumberJson::PerUnitFromTotal {
                                    per_unit: b.per_unit.to_string(),
                                    total: b.total.to_string(),
                                }
                            }
                        }),
                        currency: c.currency.as_ref().map(ToString::to_string),
                        date: c.date.map(|d| d.to_string()),
                        label: c.label.clone(),
                    }),
                    price: p.price.as_ref().and_then(price_annotation_to_amount),
                    flag: p.flag.map(|c| c.to_string()),
                    meta: metadata_to_json(&p.meta),
                })
                .collect(),
            meta: metadata_to_json(&txn.meta),
        },
        Directive::Balance(bal) => DirectiveJson::Balance {
            date: bal.date.to_string(),
            account: bal.account.to_string(),
            amount: AmountValue {
                number: bal.amount.number.to_string(),
                currency: bal.amount.currency.to_string(),
            },
            meta: metadata_to_json(&bal.meta),
        },
        Directive::Open(open) => DirectiveJson::Open {
            date: open.date.to_string(),
            account: open.account.to_string(),
            currencies: open.currencies.iter().map(ToString::to_string).collect(),
            // Pre-fix this Debug-formatted the inner String, which
            // adds quotes — JS consumers saw `booking: "\"STRICT\""`
            // instead of `"STRICT"`. Matches the FFI-WASI shape now
            // (no quote-wrapping). Issue #1200 audit caught it; the
            // glaring-bug-in-same-crate gets fixed alongside #1168.
            booking: open.booking.clone(),
            meta: metadata_to_json(&open.meta),
        },
        Directive::Close(close) => DirectiveJson::Close {
            date: close.date.to_string(),
            account: close.account.to_string(),
            meta: metadata_to_json(&close.meta),
        },
        Directive::Commodity(comm) => DirectiveJson::Commodity {
            date: comm.date.to_string(),
            currency: comm.currency.to_string(),
            meta: metadata_to_json(&comm.meta),
        },
        Directive::Pad(pad) => DirectiveJson::Pad {
            date: pad.date.to_string(),
            account: pad.account.to_string(),
            source_account: pad.source_account.to_string(),
            meta: metadata_to_json(&pad.meta),
        },
        Directive::Event(event) => DirectiveJson::Event {
            date: event.date.to_string(),
            event_type: event.event_type.clone(),
            value: event.value.clone(),
            meta: metadata_to_json(&event.meta),
        },
        Directive::Note(note) => DirectiveJson::Note {
            date: note.date.to_string(),
            account: note.account.to_string(),
            comment: note.comment.clone(),
            meta: metadata_to_json(&note.meta),
        },
        Directive::Document(doc) => DirectiveJson::Document {
            date: doc.date.to_string(),
            account: doc.account.to_string(),
            path: doc.path.clone(),
            meta: metadata_to_json(&doc.meta),
        },
        Directive::Price(price) => DirectiveJson::Price {
            date: price.date.to_string(),
            currency: price.currency.to_string(),
            amount: AmountValue {
                number: price.amount.number.to_string(),
                currency: price.amount.currency.to_string(),
            },
            meta: metadata_to_json(&price.meta),
        },
        Directive::Query(query) => DirectiveJson::Query {
            date: query.date.to_string(),
            name: query.name.clone(),
            query_string: query.query.clone(),
            meta: metadata_to_json(&query.meta),
        },
        Directive::Custom(custom) => DirectiveJson::Custom {
            date: custom.date.to_string(),
            custom_type: custom.custom_type.clone(),
            values: custom.values.iter().map(meta_value_to_json).collect(),
            meta: metadata_to_json(&custom.meta),
        },
    }
}

/// Convert a query Value to a `CellValue` for JSON serialization.
pub fn value_to_cell(value: &rustledger_query::Value) -> CellValue {
    use rustledger_query::Value;

    match value {
        Value::String(s) => CellValue::String(s.clone()),
        Value::Number(n) => CellValue::String(n.to_string()),
        Value::Integer(i) => CellValue::Integer(*i),
        Value::Date(d) => CellValue::String(d.to_string()),
        Value::Boolean(b) => CellValue::Boolean(*b),
        Value::Amount(a) => CellValue::Amount {
            number: a.number.to_string(),
            currency: a.currency.to_string(),
        },
        Value::Position(p) => CellValue::Position {
            units: AmountValue {
                number: p.units.number.to_string(),
                currency: p.units.currency.to_string(),
            },
            cost: p.cost.as_ref().map(|c| CostValue {
                number: c.number.to_string(),
                currency: c.currency.to_string(),
                date: c.date.map(|d| d.to_string()),
                label: c.label.clone(),
            }),
        },
        Value::Inventory(inv) => CellValue::Inventory {
            positions: inv
                .positions()
                .map(|p| PositionValue {
                    units: AmountValue {
                        number: p.units.number.to_string(),
                        currency: p.units.currency.to_string(),
                    },
                })
                .collect(),
        },
        Value::StringSet(set) => CellValue::StringSet(set.clone()),
        Value::Set(values) => {
            CellValue::Set(values.iter().map(|v| Box::new(value_to_cell(v))).collect())
        }
        Value::Metadata(meta) => {
            // Convert metadata to a string representation
            let repr = meta
                .iter()
                .map(|(k, v)| format!("{k}: {v:?}"))
                .collect::<Vec<_>>()
                .join(", ");
            CellValue::String(repr)
        }
        Value::Interval(interval) => {
            let unit_str = match interval.unit {
                rustledger_query::IntervalUnit::Day => "day",
                rustledger_query::IntervalUnit::Week => "week",
                rustledger_query::IntervalUnit::Month => "month",
                rustledger_query::IntervalUnit::Quarter => "quarter",
                rustledger_query::IntervalUnit::Year => "year",
            };
            let plural = if interval.count.abs() == 1 { "" } else { "s" };
            CellValue::String(format!("{} {}{}", interval.count, unit_str, plural))
        }
        Value::Object(map) => {
            let converted: std::collections::HashMap<String, Box<CellValue>> = map
                .iter()
                .map(|(k, v)| (k.clone(), Box::new(value_to_cell(v))))
                .collect();
            CellValue::Object(converted)
        }
        Value::Null => CellValue::Null,
    }
}

// The convert.rs test module runs on the host only: the new #1168
// tests use `serde_json`, which is gated as a host-only dev-dep to
// keep the wasm32 test build lean (see
// `crates/rustledger-wasm/Cargo.toml`). The shape under test is
// target-independent, so the host coverage is sufficient.
#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;
    use rustledger_parser::parse as parse_beancount;

    #[test]
    fn test_directive_to_json() {
        let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food:Coffee  5.00 USD
  Assets:Bank          -5.00 USD
2024-01-20 balance Assets:Bank 100.00 USD
"#;

        let result = parse_beancount(source);
        assert!(result.errors.is_empty());

        // Convert to JSON
        for spanned in &result.directives {
            let json = directive_to_json(&spanned.value);

            // Verify JSON structure
            match (&spanned.value, &json) {
                (Directive::Open(a), DirectiveJson::Open { date, account, .. }) => {
                    assert_eq!(&a.date.to_string(), date);
                    assert_eq!(&a.account.to_string(), account);
                }
                (
                    Directive::Transaction(a),
                    DirectiveJson::Transaction {
                        date, narration, ..
                    },
                ) => {
                    assert_eq!(&a.date.to_string(), date);
                    assert_eq!(&a.narration, narration.as_ref().unwrap_or(&String::new()));
                }
                (
                    Directive::Balance(a),
                    DirectiveJson::Balance {
                        date,
                        account,
                        amount,
                        ..
                    },
                ) => {
                    assert_eq!(&a.date.to_string(), date);
                    assert_eq!(&a.account.to_string(), account);
                    assert_eq!(&a.amount.number.to_string(), &amount.number);
                    assert_eq!(&a.amount.currency.to_string(), &amount.currency);
                }
                _ => panic!("directive type mismatch"),
            }
        }
    }

    /// Regression for #1168: metadata on every directive type must
    /// survive the conversion. Pre-fix all `meta` fields were dropped
    /// and JS consumers had no way to read user-defined key/value
    /// data.
    #[test]
    fn directive_to_json_preserves_metadata_1168() {
        let source = r#"
2024-01-01 open Assets:Bank USD
  description: "Main checking account"
  source: "Bank XYZ"
2024-01-01 commodity USD
  precision: 2
2024-01-15 * "Coffee Shop" "Morning coffee"
  trip: "vacation-2024"
  category: "food"
  Expenses:Food:Coffee  5.00 USD
    posting_note: "espresso"
  Assets:Bank          -5.00 USD
2024-01-20 balance Assets:Bank 100.00 USD
  reconciled: TRUE
"#;
        let result = parse_beancount(source);
        assert!(
            result.errors.is_empty(),
            "fixture must parse cleanly: {:?}",
            result.errors
        );

        for spanned in &result.directives {
            let json = directive_to_json(&spanned.value);
            let meta = json.meta();

            match &spanned.value {
                Directive::Open(_) => {
                    assert_eq!(
                        meta.get("description"),
                        Some(&MetaValueJson::String("Main checking account".into())),
                        "open metadata `description` missing — got {meta:?}",
                    );
                    assert_eq!(
                        meta.get("source"),
                        Some(&MetaValueJson::String("Bank XYZ".into())),
                    );
                }
                Directive::Commodity(_) => {
                    // Numbers stringify (matches FFI-WASI; JSON
                    // numbers can't represent Decimal losslessly).
                    assert_eq!(
                        meta.get("precision"),
                        Some(&MetaValueJson::String("2".into())),
                    );
                }
                Directive::Transaction(_) => {
                    assert_eq!(
                        meta.get("trip"),
                        Some(&MetaValueJson::String("vacation-2024".into())),
                    );
                    assert_eq!(
                        meta.get("category"),
                        Some(&MetaValueJson::String("food".into())),
                    );

                    // Posting-level metadata too.
                    let DirectiveJson::Transaction { postings, .. } = &json else {
                        unreachable!()
                    };
                    let coffee = postings
                        .iter()
                        .find(|p| p.account.contains("Coffee"))
                        .expect("Coffee posting present");
                    assert_eq!(
                        coffee.meta.get("posting_note"),
                        Some(&MetaValueJson::String("espresso".into())),
                    );
                }
                Directive::Balance(_) => {
                    assert_eq!(
                        meta.get("reconciled"),
                        Some(&MetaValueJson::Bool(true)),
                        "boolean metadata must serialize as Bool, not String",
                    );
                }
                _ => {}
            }
        }
    }

    #[test]
    fn directive_to_json_omits_meta_when_empty_1168() {
        // The wire shape skips `meta` when empty so existing
        // consumers don't see a new field on directives that didn't
        // have metadata. Pin via the serialized JSON to guard
        // against accidental `serialize_if_none` drift.
        let source = "2024-01-01 open Assets:Bank USD\n";
        let result = parse_beancount(source);
        assert!(result.errors.is_empty());

        let json = directive_to_json(&result.directives[0].value);
        let serialized = serde_json::to_string(&json).expect("serializes");
        assert!(
            !serialized.contains("\"meta\""),
            "empty meta must be omitted from JSON output; got: {serialized}",
        );
    }

    #[test]
    fn custom_directive_carries_values_1168() {
        // Pre-fix the Custom variant dropped both `values` AND `meta`.
        // Pin the `values` round-trip (and verify the value shape
        // matches `MetaValueJson`).
        let source = r#"2024-01-01 custom "budget" "monthly" 100.00 USD TRUE
"#;
        let result = parse_beancount(source);
        assert!(
            result.errors.is_empty(),
            "fixture must parse cleanly: {:?}",
            result.errors
        );

        let json = directive_to_json(&result.directives[0].value);
        let DirectiveJson::Custom { values, .. } = json else {
            panic!("expected Custom directive");
        };

        // The fixture has 4 positional values: "monthly", 100.00,
        // USD, TRUE — types preserved via MetaValueJson.
        assert!(!values.is_empty(), "Custom values must not be empty");
        assert!(
            values
                .iter()
                .any(|v| matches!(v, MetaValueJson::String(s) if s == "monthly")),
            "values should include `monthly` string: {values:?}",
        );
        assert!(
            values
                .iter()
                .any(|v| matches!(v, MetaValueJson::Bool(true))),
            "values should include `TRUE` bool: {values:?}",
        );
    }

    #[test]
    fn meta_value_to_json_covers_all_variants() {
        use rustledger_core::{Amount, Decimal};

        // Pin the wire mapping for every MetaValue variant. Without
        // this, a future variant added upstream (e.g. a new typed
        // metadata kind) silently maps via the `_` default and
        // confuses JS consumers. The match in `meta_value_to_json`
        // is exhaustive, so this is a behavioral spot-check —
        // adding a variant breaks compilation in both places.
        assert!(matches!(
            meta_value_to_json(&MetaValue::String("hi".into())),
            MetaValueJson::String(s) if s == "hi",
        ));
        assert!(matches!(
            meta_value_to_json(&MetaValue::Account("Assets:Bank".into())),
            MetaValueJson::String(s) if s == "Assets:Bank",
        ));
        assert!(matches!(
            meta_value_to_json(&MetaValue::Currency("USD".into())),
            MetaValueJson::String(s) if s == "USD",
        ));
        assert!(matches!(
            meta_value_to_json(&MetaValue::Tag("food".into())),
            MetaValueJson::String(s) if s == "food",
        ));
        assert!(matches!(
            meta_value_to_json(&MetaValue::Link("receipt-1".into())),
            MetaValueJson::String(s) if s == "receipt-1",
        ));
        // 4250 * 10^-2 = 42.50
        let forty_two_fifty = Decimal::new(4250, 2);
        assert!(matches!(
            meta_value_to_json(&MetaValue::Number(forty_two_fifty)),
            MetaValueJson::String(s) if s == "42.50",
        ));
        assert!(matches!(
            meta_value_to_json(&MetaValue::Bool(true)),
            MetaValueJson::Bool(true),
        ));
        let amount_value =
            meta_value_to_json(&MetaValue::Amount(Amount::new(Decimal::from(100), "USD")));
        match amount_value {
            MetaValueJson::Amount { number, currency } => {
                assert_eq!(number, "100");
                assert_eq!(currency, "USD");
            }
            other => panic!("Amount must map to Amount variant, got {other:?}"),
        }

        // Scale preservation: user-written `100.00 USD` (scale 2)
        // round-trips trailing zeros. `Decimal::Display` preserves
        // scale; `Decimal::from(100)` above is scale 0 (`"100"`).
        // Pin both so a future tweak to either side is caught.
        let scaled = meta_value_to_json(&MetaValue::Amount(Amount::new(
            Decimal::new(10000, 2), // 100.00
            "USD",
        )));
        match scaled {
            MetaValueJson::Amount { number, .. } => {
                assert_eq!(
                    number, "100.00",
                    "Decimal scale must survive the wire — trailing zeros lost: {number}",
                );
            }
            other => panic!("Amount must map to Amount variant, got {other:?}"),
        }

        assert!(matches!(
            meta_value_to_json(&MetaValue::None),
            MetaValueJson::Null,
        ));
    }

    /// The wire contract on `MetaValue::Number` is "stringify to
    /// preserve `Decimal` precision" — a JS client sending raw JSON
    /// `42` (number, not string) must NOT silently deserialize as
    /// some `MetaValueJson` variant. There's intentionally no numeric
    /// arm; the four variants (`String`/`Bool`/`Amount`/`Null`) only
    /// match string/bool/object/null JSON shapes. Pin the rejection
    /// so a future "helpful" addition of a numeric arm doesn't
    /// silently erode precision on the round-trip.
    #[test]
    fn meta_value_json_rejects_raw_json_number() {
        let err = serde_json::from_str::<MetaValueJson>("42");
        assert!(
            err.is_err(),
            "raw JSON number must fail deserialize (wire contract: numbers \
             are strings to preserve Decimal precision), got {err:?}",
        );

        // Negative + fractional just for thoroughness — same rule.
        assert!(serde_json::from_str::<MetaValueJson>("-1.5").is_err());
    }

    /// `Custom.values` is a positional list — a `MetaValue::None` in
    /// the middle of the list must keep its position so JS consumers
    /// see `[..., null, ...]` rather than the position silently
    /// collapsing. The plugin-types side of this is filed in #1200's
    /// audit; pin the WASM wire shape here independently.
    #[test]
    fn custom_values_preserve_null_position_1168() {
        use rustledger_core::{Custom, Decimal};

        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();
        let custom = Custom {
            date,
            custom_type: "budget".into(),
            values: vec![
                MetaValue::String("monthly".into()),
                MetaValue::None,
                MetaValue::Number(Decimal::new(10000, 2)),
            ],
            meta: Default::default(),
        };

        let json = directive_to_json(&Directive::Custom(custom));
        let DirectiveJson::Custom { values, .. } = json else {
            panic!("expected Custom directive");
        };

        assert_eq!(values.len(), 3, "all three values must survive: {values:?}");
        assert!(matches!(values[0], MetaValueJson::String(ref s) if s == "monthly"));
        assert!(
            matches!(values[1], MetaValueJson::Null),
            "middle Null must keep position {values:?}",
        );
        assert!(matches!(values[2], MetaValueJson::String(ref s) if s == "100.00"));
    }
}
