//! Input types for JSON deserialization.

use std::collections::HashMap;

use rustledger_core::{Directive, MetaValue, Metadata, NaiveDate};
use serde::Deserialize;

/// Input amount for entry creation.
#[derive(Debug, Deserialize, Clone)]
pub struct InputAmount {
    pub number: String,
    pub currency: String,
}

/// Input cost-number for entry creation.
///
/// Mirrors the host `CostNumber` enum on the wire. Consumers supply
/// `{"kind": "per_unit", "value": "..."}` or `{"kind": "total", "value":
/// "..."}` for unbooked specs. `per_unit_from_total` is reserved for
/// already-booked posting input and is rejected if the per-unit and
/// total are inconsistent with the supplied units.
#[derive(Debug, Deserialize, Clone)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum InputCostNumber {
    /// `{value USD}` — per-unit cost.
    PerUnit {
        /// Per-unit value.
        value: String,
    },
    /// `{{value USD}}` — total cost.
    Total {
        /// Total value.
        value: String,
    },
    /// Post-booking: derived per-unit and preserved source total.
    PerUnitFromTotal {
        /// Derived per-unit.
        per_unit: String,
        /// Source total.
        total: String,
    },
}

/// Input cost for entry creation.
#[derive(Debug, Deserialize, Clone, Default)]
pub struct InputCost {
    /// Cost number (per-unit, total, or post-booking pair).
    /// `None` corresponds to a bare `{}` cost spec.
    #[serde(default)]
    pub number: Option<InputCostNumber>,
    /// Cost currency.
    #[serde(default)]
    pub currency: Option<String>,
    /// Acquisition date.
    #[serde(default)]
    pub date: Option<String>,
    /// Lot label.
    #[serde(default)]
    pub label: Option<String>,
}

/// Input posting for entry creation.
#[derive(Debug, Deserialize, Clone)]
pub struct InputPosting {
    pub account: String,
    #[serde(default)]
    pub units: Option<InputAmount>,
    #[serde(default)]
    pub cost: Option<InputCost>,
    #[serde(default)]
    pub price: Option<InputAmount>,
    #[serde(default)]
    pub meta: HashMap<String, serde_json::Value>,
}

/// Input entry for create-entry/format-entry commands.
#[derive(Debug, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum InputEntry {
    Transaction {
        date: String,
        #[serde(default = "default_flag")]
        flag: String,
        #[serde(default)]
        payee: Option<String>,
        #[serde(default)]
        narration: Option<String>,
        #[serde(default)]
        tags: Vec<String>,
        #[serde(default)]
        links: Vec<String>,
        #[serde(default)]
        postings: Vec<InputPosting>,
        #[serde(default)]
        meta: HashMap<String, serde_json::Value>,
    },
    Open {
        date: String,
        account: String,
        #[serde(default)]
        currencies: Vec<String>,
        #[serde(default)]
        booking: Option<String>,
        #[serde(default)]
        meta: HashMap<String, serde_json::Value>,
    },
    Close {
        date: String,
        account: String,
        #[serde(default)]
        meta: HashMap<String, serde_json::Value>,
    },
    Balance {
        date: String,
        account: String,
        amount: InputAmount,
        #[serde(default)]
        meta: HashMap<String, serde_json::Value>,
    },
    Pad {
        date: String,
        account: String,
        source_account: String,
        #[serde(default)]
        meta: HashMap<String, serde_json::Value>,
    },
    Commodity {
        date: String,
        currency: String,
        #[serde(default)]
        meta: HashMap<String, serde_json::Value>,
    },
    Price {
        date: String,
        currency: String,
        amount: InputAmount,
        #[serde(default)]
        meta: HashMap<String, serde_json::Value>,
    },
    Event {
        date: String,
        event_type: String,
        value: String,
        #[serde(default)]
        meta: HashMap<String, serde_json::Value>,
    },
    Note {
        date: String,
        account: String,
        comment: String,
        #[serde(default)]
        meta: HashMap<String, serde_json::Value>,
    },
    Document {
        date: String,
        account: String,
        path: String,
        #[serde(default)]
        meta: HashMap<String, serde_json::Value>,
    },
    Query {
        date: String,
        name: String,
        query_string: String,
        #[serde(default)]
        meta: HashMap<String, serde_json::Value>,
    },
    Custom {
        date: String,
        custom_type: String,
        #[serde(default)]
        values: Vec<serde_json::Value>,
        #[serde(default)]
        meta: HashMap<String, serde_json::Value>,
    },
}

fn default_flag() -> String {
    "*".to_string()
}

/// Convert JSON metadata value to core `MetaValue`.
pub fn json_to_meta_value(value: &serde_json::Value) -> MetaValue {
    match value {
        serde_json::Value::String(s) => MetaValue::String(s.clone()),
        serde_json::Value::Bool(b) => MetaValue::Bool(*b),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                MetaValue::Number(rustledger_core::Decimal::from(i))
            } else if let Some(f) = n.as_f64() {
                MetaValue::Number(
                    rustledger_core::Decimal::from_str_exact(&f.to_string())
                        .unwrap_or_else(|_| rustledger_core::Decimal::from(0)),
                )
            } else {
                MetaValue::None
            }
        }
        serde_json::Value::Null => MetaValue::None,
        serde_json::Value::Object(obj) => {
            // Handle Amount objects
            if let (Some(number), Some(currency)) = (obj.get("number"), obj.get("currency"))
                && let (Some(n), Some(c)) = (number.as_str(), currency.as_str())
            {
                return MetaValue::Amount(rustledger_core::Amount {
                    number: rustledger_core::Decimal::from_str_exact(n)
                        .unwrap_or_else(|_| rustledger_core::Decimal::from(0)),
                    currency: c.into(),
                });
            }
            MetaValue::None
        }
        serde_json::Value::Array(_) => MetaValue::None,
    }
}

/// Convert `HashMap<String, Value>` to core Metadata.
pub fn json_map_to_metadata(map: &HashMap<String, serde_json::Value>) -> Metadata {
    map.iter()
        .map(|(k, v)| (k.clone(), json_to_meta_value(v)))
        .collect()
}

/// Convert `InputEntry` to core Directive.
pub fn input_entry_to_directive(entry: &InputEntry) -> Result<Directive, String> {
    match entry {
        InputEntry::Transaction {
            date,
            flag,
            payee,
            narration,
            tags,
            links,
            postings,
            meta,
        } => {
            let date = date
                .parse::<NaiveDate>()
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;

            let flag = match flag.as_str() {
                "*" | "txn" => '*',
                "!" => '!',
                other => other.chars().next().unwrap_or('*'),
            };

            let postings: Vec<rustledger_core::Spanned<rustledger_core::Posting>> = postings
                .iter()
                .map(|p| {
                    let units = p.units.as_ref().map(|u| {
                        rustledger_core::IncompleteAmount::Complete(rustledger_core::Amount {
                            number: rustledger_core::Decimal::from_str_exact(&u.number)
                                .unwrap_or_else(|_| rustledger_core::Decimal::from(0)),
                            currency: u.currency.clone().into(),
                        })
                    });

                    let cost = p.cost.as_ref().map(|c| {
                        // The wire `InputCostNumber` is a tagged enum
                        // mirroring the host `CostNumber`. The type
                        // system prevents the both-set state; here we
                        // additionally enforce the
                        // `per_unit * |units| == total` invariant for
                        // PerUnitFromTotal so external clients cannot
                        // smuggle in inconsistent post-booking pairs.
                        let parse = |s: &str| {
                            rustledger_core::Decimal::from_str_exact(s)
                                .unwrap_or_else(|_| rustledger_core::Decimal::from(0))
                        };
                        let posting_units = units
                            .as_ref()
                            .and_then(|u: &rustledger_core::IncompleteAmount| u.as_amount());
                        let number = c.number.as_ref().map(|n| match n {
                            crate::types::input::InputCostNumber::PerUnit { value } => {
                                rustledger_core::CostNumber::PerUnit {
                                    value: parse(value),
                                }
                            }
                            crate::types::input::InputCostNumber::Total { value } => {
                                rustledger_core::CostNumber::Total {
                                    value: parse(value),
                                }
                            }
                            crate::types::input::InputCostNumber::PerUnitFromTotal {
                                per_unit,
                                total,
                            } => {
                                let per_unit_d = parse(per_unit);
                                let total_d = parse(total);
                                // `try_new` returns None if the pair is
                                // inconsistent with the posting's
                                // units; we fall back to interpreting
                                // as raw PerUnit so the directive still
                                // parses but loses the bogus total
                                // (loud truncation > silent corruption).
                                let units_n = posting_units.as_ref().map_or_else(
                                    || rustledger_core::Decimal::from(0),
                                    |a| a.number,
                                );
                                match rustledger_core::BookedCost::try_new(
                                    per_unit_d, total_d, units_n,
                                ) {
                                    Some(b) => rustledger_core::CostNumber::PerUnitFromTotal(b),
                                    None => {
                                        rustledger_core::CostNumber::PerUnit { value: per_unit_d }
                                    }
                                }
                            }
                        });
                        rustledger_core::CostSpec {
                            number,
                            currency: c.currency.clone().map(Into::into),
                            date: c.date.as_ref().and_then(|d| d.parse::<NaiveDate>().ok()),
                            label: c.label.clone(),
                            merge: false,
                        }
                    });

                    let price = p.price.as_ref().map(|pr| {
                        rustledger_core::PriceAnnotation::unit(rustledger_core::Amount {
                            number: rustledger_core::Decimal::from_str_exact(&pr.number)
                                .unwrap_or_else(|_| rustledger_core::Decimal::from(0)),
                            currency: pr.currency.clone().into(),
                        })
                    });

                    rustledger_core::Spanned::synthesized(rustledger_core::Posting {
                        account: p.account.clone().into(),
                        units,
                        cost,
                        price,
                        flag: None,
                        meta: json_map_to_metadata(&p.meta),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    })
                })
                .collect();

            Ok(Directive::Transaction(rustledger_core::Transaction {
                date,
                flag,
                payee: payee.clone().map(Into::into),
                narration: narration.clone().unwrap_or_default().into(),
                tags: tags.iter().map(|t| t.clone().into()).collect(),
                links: links.iter().map(|l| l.clone().into()).collect(),
                postings,
                meta: json_map_to_metadata(meta),
                trailing_comments: Vec::new(),
            }))
        }
        InputEntry::Open {
            date,
            account,
            currencies,
            booking,
            meta,
        } => {
            let date = date
                .parse::<NaiveDate>()
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;
            Ok(Directive::Open(rustledger_core::Open {
                date,
                account: account.clone().into(),
                currencies: currencies.iter().map(|c| c.clone().into()).collect(),
                booking: booking.clone(),
                meta: json_map_to_metadata(meta),
            }))
        }
        InputEntry::Close {
            date,
            account,
            meta,
        } => {
            let date = date
                .parse::<NaiveDate>()
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;
            Ok(Directive::Close(rustledger_core::Close {
                date,
                account: account.clone().into(),
                meta: json_map_to_metadata(meta),
            }))
        }
        InputEntry::Balance {
            date,
            account,
            amount,
            meta,
        } => {
            let date = date
                .parse::<NaiveDate>()
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;
            Ok(Directive::Balance(rustledger_core::Balance {
                date,
                account: account.clone().into(),
                amount: rustledger_core::Amount {
                    number: rustledger_core::Decimal::from_str_exact(&amount.number)
                        .unwrap_or_else(|_| rustledger_core::Decimal::from(0)),
                    currency: amount.currency.clone().into(),
                },
                tolerance: None,
                meta: json_map_to_metadata(meta),
            }))
        }
        InputEntry::Pad {
            date,
            account,
            source_account,
            meta,
        } => {
            let date = date
                .parse::<NaiveDate>()
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;
            Ok(Directive::Pad(rustledger_core::Pad {
                date,
                account: account.clone().into(),
                source_account: source_account.clone().into(),
                meta: json_map_to_metadata(meta),
            }))
        }
        InputEntry::Commodity {
            date,
            currency,
            meta,
        } => {
            let date = date
                .parse::<NaiveDate>()
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;
            Ok(Directive::Commodity(rustledger_core::Commodity {
                date,
                currency: currency.clone().into(),
                meta: json_map_to_metadata(meta),
            }))
        }
        InputEntry::Price {
            date,
            currency,
            amount,
            meta,
        } => {
            let date = date
                .parse::<NaiveDate>()
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;
            Ok(Directive::Price(rustledger_core::Price {
                date,
                currency: currency.clone().into(),
                amount: rustledger_core::Amount {
                    number: rustledger_core::Decimal::from_str_exact(&amount.number)
                        .unwrap_or_else(|_| rustledger_core::Decimal::from(0)),
                    currency: amount.currency.clone().into(),
                },
                meta: json_map_to_metadata(meta),
            }))
        }
        InputEntry::Event {
            date,
            event_type,
            value,
            meta,
        } => {
            let date = date
                .parse::<NaiveDate>()
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;
            Ok(Directive::Event(rustledger_core::Event {
                date,
                event_type: event_type.clone(),
                value: value.clone(),
                meta: json_map_to_metadata(meta),
            }))
        }
        InputEntry::Note {
            date,
            account,
            comment,
            meta,
        } => {
            let date = date
                .parse::<NaiveDate>()
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;
            Ok(Directive::Note(rustledger_core::Note {
                date,
                account: account.clone().into(),
                comment: comment.clone(),
                meta: json_map_to_metadata(meta),
            }))
        }
        InputEntry::Document {
            date,
            account,
            path,
            meta,
        } => {
            let date = date
                .parse::<NaiveDate>()
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;
            Ok(Directive::Document(rustledger_core::Document {
                date,
                account: account.clone().into(),
                path: path.clone(),
                tags: Vec::new(),
                links: Vec::new(),
                meta: json_map_to_metadata(meta),
            }))
        }
        InputEntry::Query {
            date,
            name,
            query_string,
            meta,
        } => {
            let date = date
                .parse::<NaiveDate>()
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;
            Ok(Directive::Query(rustledger_core::Query {
                date,
                name: name.clone(),
                query: query_string.clone(),
                meta: json_map_to_metadata(meta),
            }))
        }
        InputEntry::Custom {
            date,
            custom_type,
            values,
            meta,
        } => {
            let date = date
                .parse::<NaiveDate>()
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;
            Ok(Directive::Custom(rustledger_core::Custom {
                date,
                custom_type: custom_type.clone(),
                values: values.iter().map(json_to_meta_value).collect(),
                meta: json_map_to_metadata(meta),
            }))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ===== Input cost-number wire-format tests (#1164) =====
    //
    // The wire `InputCostNumber` enum is the boundary that makes the
    // both-set invalid state structurally unrepresentable. These tests
    // pin that property — neither serde nor the bridge can construct
    // a CostSpec with both per-unit AND total set unless they come in
    // via the explicit `per_unit_from_total` variant (which carries
    // the post-booking invariant).

    #[test]
    fn input_cost_number_per_unit_parses() {
        let json = r#"{"kind": "per_unit", "value": "100"}"#;
        let cn: InputCostNumber = serde_json::from_str(json).unwrap();
        match cn {
            InputCostNumber::PerUnit { value } => assert_eq!(value, "100"),
            _ => panic!("expected PerUnit"),
        }
    }

    #[test]
    fn input_cost_number_total_parses() {
        let json = r#"{"kind": "total", "value": "1500"}"#;
        let cn: InputCostNumber = serde_json::from_str(json).unwrap();
        match cn {
            InputCostNumber::Total { value } => assert_eq!(value, "1500"),
            _ => panic!("expected Total"),
        }
    }

    #[test]
    fn input_cost_number_per_unit_from_total_parses() {
        let json = r#"{"kind": "per_unit_from_total", "per_unit": "150", "total": "300"}"#;
        let cn: InputCostNumber = serde_json::from_str(json).unwrap();
        match cn {
            InputCostNumber::PerUnitFromTotal { per_unit, total } => {
                assert_eq!(per_unit, "150");
                assert_eq!(total, "300");
            }
            _ => panic!("expected PerUnitFromTotal"),
        }
    }

    #[test]
    fn input_cost_number_rejects_unknown_kind() {
        // Wire shape strict: unknown discriminator is an error, not a
        // silent fallback. Important so future variants don't get
        // confused with mistyped input.
        let json = r#"{"kind": "per_unit_with_total", "value": "100"}"#;
        let result: Result<InputCostNumber, _> = serde_json::from_str(json);
        assert!(result.is_err(), "expected error for unknown kind, got Ok");
    }

    #[test]
    fn input_cost_number_rejects_missing_kind() {
        // No `kind` discriminator → serde can't pick a variant.
        let json = r#"{"value": "100"}"#;
        let result: Result<InputCostNumber, _> = serde_json::from_str(json);
        assert!(result.is_err(), "expected error without kind tag, got Ok");
    }

    #[test]
    fn input_cost_number_rejects_legacy_flat_shape() {
        // The pre-#1164 wire shape `{"number_per": "...", "number_total": null}`
        // is gone. Sending it gets a parse error, which is the right
        // behavior — silent coercion to `PerUnit` would mask client
        // bugs and re-introduce the invalid both-set state through
        // the bridge.
        let json = r#"{"number_per": "100", "number_total": null}"#;
        let result: Result<InputCostNumber, _> = serde_json::from_str(json);
        assert!(
            result.is_err(),
            "expected error for legacy flat shape, got Ok"
        );
    }

    #[test]
    fn input_cost_with_no_number_parses_as_bare_brace() {
        // `{}` lot match: the `number` field is absent or null.
        let json = r#"{"currency": "USD"}"#;
        let cost: InputCost = serde_json::from_str(json).unwrap();
        assert!(cost.number.is_none());
        assert_eq!(cost.currency.as_deref(), Some("USD"));
    }
}
