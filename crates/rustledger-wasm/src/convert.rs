//! Conversion functions between Beancount types and JSON DTOs.

use rustledger_core::{Amount, Directive};

use crate::types::{
    AmountValue, CellValue, CostValue, DirectiveJson, PositionValue, PostingCostJson, PostingJson,
};

/// Convert a Directive to its JSON representation.
pub fn directive_to_json(directive: &Directive) -> DirectiveJson {
    use rustledger_core::PriceAnnotation;

    fn price_annotation_to_amount(pr: &PriceAnnotation) -> Option<AmountValue> {
        match pr {
            PriceAnnotation::Unit(a) | PriceAnnotation::Total(a) => Some(AmountValue {
                number: a.number.to_string(),
                currency: a.currency.clone(),
            }),
            _ => None,
        }
    }

    match directive {
        Directive::Transaction(txn) => DirectiveJson::Transaction {
            date: txn.date.to_string(),
            flag: txn.flag.to_string(),
            payee: txn.payee.clone(),
            narration: Some(txn.narration.clone()),
            tags: txn.tags.clone(),
            links: txn.links.clone(),
            postings: txn
                .postings
                .iter()
                .map(|p| PostingJson {
                    account: p.account.clone(),
                    units: p.units.as_ref().map(|u| AmountValue {
                        number: u.number().map(|n| n.to_string()).unwrap_or_default(),
                        currency: u.currency().map(ToString::to_string).unwrap_or_default(),
                    }),
                    cost: p.cost.as_ref().map(|c| PostingCostJson {
                        number_per: c.number_per.map(|n| n.to_string()),
                        currency: c.currency.clone(),
                        date: c.date.map(|d| d.to_string()),
                        label: c.label.clone(),
                    }),
                    price: p.price.as_ref().and_then(price_annotation_to_amount),
                })
                .collect(),
        },
        Directive::Balance(bal) => DirectiveJson::Balance {
            date: bal.date.to_string(),
            account: bal.account.clone(),
            amount: AmountValue {
                number: bal.amount.number.to_string(),
                currency: bal.amount.currency.clone(),
            },
        },
        Directive::Open(open) => DirectiveJson::Open {
            date: open.date.to_string(),
            account: open.account.clone(),
            currencies: open.currencies.clone(),
            booking: open.booking.as_ref().map(|b| format!("{b:?}")),
        },
        Directive::Close(close) => DirectiveJson::Close {
            date: close.date.to_string(),
            account: close.account.clone(),
        },
        Directive::Commodity(comm) => DirectiveJson::Commodity {
            date: comm.date.to_string(),
            currency: comm.currency.clone(),
        },
        Directive::Pad(pad) => DirectiveJson::Pad {
            date: pad.date.to_string(),
            account: pad.account.clone(),
            source_account: pad.source_account.clone(),
        },
        Directive::Event(event) => DirectiveJson::Event {
            date: event.date.to_string(),
            event_type: event.event_type.clone(),
            value: event.value.clone(),
        },
        Directive::Note(note) => DirectiveJson::Note {
            date: note.date.to_string(),
            account: note.account.clone(),
            comment: note.comment.clone(),
        },
        Directive::Document(doc) => DirectiveJson::Document {
            date: doc.date.to_string(),
            account: doc.account.clone(),
            path: doc.path.clone(),
        },
        Directive::Price(price) => DirectiveJson::Price {
            date: price.date.to_string(),
            currency: price.currency.clone(),
            amount: AmountValue {
                number: price.amount.number.to_string(),
                currency: price.amount.currency.clone(),
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

/// Convert a JSON directive back to a Directive.
pub fn json_to_directive(json: &DirectiveJson) -> Result<Directive, String> {
    use rustledger_core::NaiveDate;
    use rustledger_core::{
        Balance, Close, Commodity, CostSpec, Custom, Decimal, Document, Event, IncompleteAmount,
        Note, Open, Pad, Posting, Price, Transaction,
    };

    fn parse_date(date_str: &str) -> Result<NaiveDate, String> {
        NaiveDate::parse_from_str(date_str, "%Y-%m-%d")
            .map_err(|e| format!("invalid date '{date_str}': {e}"))
    }

    fn amount_value_to_amount(av: &AmountValue) -> Result<Amount, String> {
        let decimal: Decimal = av
            .number
            .parse()
            .map_err(|e| format!("invalid number '{}': {e}", av.number))?;
        Ok(Amount::new(decimal, &av.currency))
    }

    match json {
        DirectiveJson::Transaction {
            date,
            flag,
            payee,
            narration,
            tags,
            links,
            postings,
        } => {
            let date = parse_date(date)?;
            let flag_char = flag.chars().next().unwrap_or('*');

            let mut parsed_postings = Vec::new();
            for p in postings {
                let units = if let Some(u) = &p.units {
                    if u.number.is_empty() && u.currency.is_empty() {
                        None
                    } else {
                        let number: Option<Decimal> = if u.number.is_empty() {
                            None
                        } else {
                            Some(
                                u.number
                                    .parse()
                                    .map_err(|e| format!("invalid number '{}': {e}", u.number))?,
                            )
                        };
                        let currency = if u.currency.is_empty() {
                            None
                        } else {
                            Some(u.currency.clone())
                        };
                        match (number, currency) {
                            (Some(n), Some(c)) => {
                                Some(IncompleteAmount::Complete(Amount::new(n, c)))
                            }
                            (Some(n), None) => Some(IncompleteAmount::NumberOnly(n)),
                            (None, Some(c)) => Some(IncompleteAmount::CurrencyOnly(c)),
                            (None, None) => None,
                        }
                    }
                } else {
                    None
                };

                let cost = if let Some(c) = &p.cost {
                    let number_per = c
                        .number_per
                        .as_ref()
                        .and_then(|s| s.parse::<Decimal>().ok());
                    let cost_date = c
                        .date
                        .as_ref()
                        .and_then(|s| NaiveDate::parse_from_str(s, "%Y-%m-%d").ok());
                    Some(CostSpec {
                        number_per,
                        number_total: None,
                        currency: c.currency.clone(),
                        date: cost_date,
                        label: c.label.clone(),
                        merge: false,
                    })
                } else {
                    None
                };

                let price = if let Some(pr) = &p.price {
                    use rustledger_core::PriceAnnotation;
                    let amount = amount_value_to_amount(pr)?;
                    Some(PriceAnnotation::Unit(amount))
                } else {
                    None
                };

                parsed_postings.push(Posting {
                    account: p.account.clone(),
                    units,
                    cost,
                    price,
                    flag: None,
                    meta: std::collections::HashMap::new(),
                });
            }

            let mut txn = Transaction::new(date, narration.as_deref().unwrap_or(""));
            txn.flag = flag_char;
            txn.payee.clone_from(payee);
            txn.tags.clone_from(tags);
            txn.links.clone_from(links);
            txn.postings = parsed_postings;
            Ok(Directive::Transaction(txn))
        }
        DirectiveJson::Balance {
            date,
            account,
            amount,
        } => {
            let date = parse_date(date)?;
            let amount = amount_value_to_amount(amount)?;
            Ok(Directive::Balance(Balance {
                date,
                account: account.clone(),
                amount,
                tolerance: None,
                meta: std::collections::HashMap::new(),
            }))
        }
        DirectiveJson::Open {
            date,
            account,
            currencies,
            booking,
        } => {
            let date = parse_date(date)?;
            Ok(Directive::Open(Open {
                date,
                account: account.clone(),
                currencies: currencies.clone(),
                booking: booking.clone(),
                meta: std::collections::HashMap::new(),
            }))
        }
        DirectiveJson::Close { date, account } => {
            let date = parse_date(date)?;
            Ok(Directive::Close(Close {
                date,
                account: account.clone(),
                meta: std::collections::HashMap::new(),
            }))
        }
        DirectiveJson::Commodity { date, currency } => {
            let date = parse_date(date)?;
            Ok(Directive::Commodity(Commodity {
                date,
                currency: currency.clone(),
                meta: std::collections::HashMap::new(),
            }))
        }
        DirectiveJson::Pad {
            date,
            account,
            source_account,
        } => {
            let date = parse_date(date)?;
            Ok(Directive::Pad(Pad {
                date,
                account: account.clone(),
                source_account: source_account.clone(),
                meta: std::collections::HashMap::new(),
            }))
        }
        DirectiveJson::Event {
            date,
            event_type,
            value,
        } => {
            let date = parse_date(date)?;
            Ok(Directive::Event(Event {
                date,
                event_type: event_type.clone(),
                value: value.clone(),
                meta: std::collections::HashMap::new(),
            }))
        }
        DirectiveJson::Note {
            date,
            account,
            comment,
        } => {
            let date = parse_date(date)?;
            Ok(Directive::Note(Note {
                date,
                account: account.clone(),
                comment: comment.clone(),
                meta: std::collections::HashMap::new(),
            }))
        }
        DirectiveJson::Document {
            date,
            account,
            path,
        } => {
            let date = parse_date(date)?;
            Ok(Directive::Document(Document {
                date,
                account: account.clone(),
                path: path.clone(),
                tags: Vec::new(),
                links: Vec::new(),
                meta: std::collections::HashMap::new(),
            }))
        }
        DirectiveJson::Price {
            date,
            currency,
            amount,
        } => {
            let date = parse_date(date)?;
            let amount = amount_value_to_amount(amount)?;
            Ok(Directive::Price(Price {
                date,
                currency: currency.clone(),
                amount,
                meta: std::collections::HashMap::new(),
            }))
        }
        DirectiveJson::Query {
            date,
            name,
            query_string,
        } => {
            let date = parse_date(date)?;
            Ok(Directive::Query(rustledger_core::Query {
                date,
                name: name.clone(),
                query: query_string.clone(),
                meta: std::collections::HashMap::new(),
            }))
        }
        DirectiveJson::Custom { date, custom_type } => {
            let date = parse_date(date)?;
            Ok(Directive::Custom(Custom {
                date,
                custom_type: custom_type.clone(),
                values: Vec::new(),
                meta: std::collections::HashMap::new(),
            }))
        }
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
            currency: a.currency.clone(),
        },
        Value::Position(p) => CellValue::Position {
            units: AmountValue {
                number: p.units.number.to_string(),
                currency: p.units.currency.clone(),
            },
            cost: p.cost.as_ref().map(|c| CostValue {
                number: c.number.to_string(),
                currency: c.currency.clone(),
                date: c.date.map(|d| d.to_string()),
                label: c.label.clone(),
            }),
        },
        Value::Inventory(inv) => {
            let positions = inv.positions();
            CellValue::Inventory {
                positions: positions
                    .iter()
                    .map(|p| PositionValue {
                        units: AmountValue {
                            number: p.units.number.to_string(),
                            currency: p.units.currency.clone(),
                        },
                    })
                    .collect(),
            }
        }
        Value::StringSet(set) => CellValue::StringSet(set.clone()),
        Value::Null => CellValue::Null,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse as parse_beancount;

    #[test]
    fn test_json_to_directive_roundtrip() {
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

            // Convert back from JSON
            let reconstructed = json_to_directive(&json).expect("should reconstruct directive");

            // Verify directive types match
            match (&spanned.value, &reconstructed) {
                (Directive::Open(a), Directive::Open(b)) => {
                    assert_eq!(a.date, b.date);
                    assert_eq!(a.account, b.account);
                    assert_eq!(a.currencies, b.currencies);
                }
                (Directive::Transaction(a), Directive::Transaction(b)) => {
                    assert_eq!(a.date, b.date);
                    assert_eq!(a.narration, b.narration);
                    assert_eq!(a.postings.len(), b.postings.len());
                }
                (Directive::Balance(a), Directive::Balance(b)) => {
                    assert_eq!(a.date, b.date);
                    assert_eq!(a.account, b.account);
                    assert_eq!(a.amount.number, b.amount.number);
                    assert_eq!(a.amount.currency, b.amount.currency);
                }
                _ => panic!("directive type mismatch"),
            }
        }
    }

    #[test]
    fn test_all_directive_types_reconstruction() {
        use crate::types::AmountValue;

        // Test reconstruction of all directive types
        let test_cases: Vec<DirectiveJson> = vec![
            DirectiveJson::Open {
                date: "2024-01-01".to_string(),
                account: "Assets:Bank".to_string(),
                currencies: vec!["USD".to_string()],
                booking: None,
            },
            DirectiveJson::Close {
                date: "2024-12-31".to_string(),
                account: "Assets:Bank".to_string(),
            },
            DirectiveJson::Commodity {
                date: "2024-01-01".to_string(),
                currency: "USD".to_string(),
            },
            DirectiveJson::Balance {
                date: "2024-01-15".to_string(),
                account: "Assets:Bank".to_string(),
                amount: AmountValue {
                    number: "100.00".to_string(),
                    currency: "USD".to_string(),
                },
            },
            DirectiveJson::Pad {
                date: "2024-01-01".to_string(),
                account: "Assets:Bank".to_string(),
                source_account: "Equity:Opening".to_string(),
            },
            DirectiveJson::Event {
                date: "2024-01-01".to_string(),
                event_type: "location".to_string(),
                value: "NYC".to_string(),
            },
            DirectiveJson::Note {
                date: "2024-01-01".to_string(),
                account: "Assets:Bank".to_string(),
                comment: "Test note".to_string(),
            },
            DirectiveJson::Document {
                date: "2024-01-01".to_string(),
                account: "Assets:Bank".to_string(),
                path: "/path/to/doc.pdf".to_string(),
            },
            DirectiveJson::Price {
                date: "2024-01-01".to_string(),
                currency: "AAPL".to_string(),
                amount: AmountValue {
                    number: "150.00".to_string(),
                    currency: "USD".to_string(),
                },
            },
            DirectiveJson::Query {
                date: "2024-01-01".to_string(),
                name: "test_query".to_string(),
                query_string: "SELECT account".to_string(),
            },
            DirectiveJson::Custom {
                date: "2024-01-01".to_string(),
                custom_type: "budget".to_string(),
            },
        ];

        for json in &test_cases {
            let result = json_to_directive(json);
            assert!(result.is_ok(), "failed to reconstruct: {:?}", result.err());
        }
    }
}
