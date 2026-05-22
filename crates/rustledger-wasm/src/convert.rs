//! Conversion functions between Beancount types and JSON DTOs.

use rustledger_core::Directive;

use crate::types::{
    AmountValue, CellValue, CostNumberJson, CostValue, DirectiveJson, PositionValue,
    PostingCostJson, PostingJson,
};

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
                })
                .collect(),
        },
        Directive::Balance(bal) => DirectiveJson::Balance {
            date: bal.date.to_string(),
            account: bal.account.to_string(),
            amount: AmountValue {
                number: bal.amount.number.to_string(),
                currency: bal.amount.currency.to_string(),
            },
        },
        Directive::Open(open) => DirectiveJson::Open {
            date: open.date.to_string(),
            account: open.account.to_string(),
            currencies: open.currencies.iter().map(ToString::to_string).collect(),
            booking: open.booking.as_ref().map(|b| format!("{b:?}")),
        },
        Directive::Close(close) => DirectiveJson::Close {
            date: close.date.to_string(),
            account: close.account.to_string(),
        },
        Directive::Commodity(comm) => DirectiveJson::Commodity {
            date: comm.date.to_string(),
            currency: comm.currency.to_string(),
        },
        Directive::Pad(pad) => DirectiveJson::Pad {
            date: pad.date.to_string(),
            account: pad.account.to_string(),
            source_account: pad.source_account.to_string(),
        },
        Directive::Event(event) => DirectiveJson::Event {
            date: event.date.to_string(),
            event_type: event.event_type.clone(),
            value: event.value.clone(),
        },
        Directive::Note(note) => DirectiveJson::Note {
            date: note.date.to_string(),
            account: note.account.to_string(),
            comment: note.comment.clone(),
        },
        Directive::Document(doc) => DirectiveJson::Document {
            date: doc.date.to_string(),
            account: doc.account.to_string(),
            path: doc.path.clone(),
        },
        Directive::Price(price) => DirectiveJson::Price {
            date: price.date.to_string(),
            currency: price.currency.to_string(),
            amount: AmountValue {
                number: price.amount.number.to_string(),
                currency: price.amount.currency.to_string(),
            },
        },
        Directive::Query(query) => DirectiveJson::Query {
            date: query.date.to_string(),
            name: query.name.clone(),
            query_string: query.query.clone(),
        },
        Directive::Custom(custom) => DirectiveJson::Custom {
            date: custom.date.to_string(),
            custom_type: custom.custom_type.clone(),
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

#[cfg(test)]
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
}
