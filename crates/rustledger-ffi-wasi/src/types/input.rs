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

/// Input cost for entry creation.
#[derive(Debug, Deserialize, Clone, Default)]
pub struct InputCost {
    #[serde(default)]
    pub number: Option<String>,
    #[serde(default)]
    pub number_total: Option<String>,
    #[serde(default)]
    pub currency: Option<String>,
    #[serde(default)]
    pub date: Option<String>,
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
            let date = NaiveDate::parse_from_str(date, "%Y-%m-%d")
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;

            let flag = match flag.as_str() {
                "*" | "txn" => '*',
                "!" => '!',
                other => other.chars().next().unwrap_or('*'),
            };

            let postings: Vec<rustledger_core::Posting> = postings
                .iter()
                .map(|p| {
                    let units = p.units.as_ref().map(|u| {
                        rustledger_core::IncompleteAmount::Complete(rustledger_core::Amount {
                            number: rustledger_core::Decimal::from_str_exact(&u.number)
                                .unwrap_or_else(|_| rustledger_core::Decimal::from(0)),
                            currency: u.currency.clone().into(),
                        })
                    });

                    let cost = p.cost.as_ref().map(|c| rustledger_core::CostSpec {
                        number_per: c
                            .number
                            .as_ref()
                            .and_then(|n| rustledger_core::Decimal::from_str_exact(n).ok()),
                        number_total: c
                            .number_total
                            .as_ref()
                            .and_then(|n| rustledger_core::Decimal::from_str_exact(n).ok()),
                        currency: c.currency.clone().map(Into::into),
                        date: c
                            .date
                            .as_ref()
                            .and_then(|d| NaiveDate::parse_from_str(d, "%Y-%m-%d").ok()),
                        label: c.label.clone(),
                        merge: false,
                    });

                    let price = p.price.as_ref().map(|pr| {
                        rustledger_core::PriceAnnotation::Unit(rustledger_core::Amount {
                            number: rustledger_core::Decimal::from_str_exact(&pr.number)
                                .unwrap_or_else(|_| rustledger_core::Decimal::from(0)),
                            currency: pr.currency.clone().into(),
                        })
                    });

                    rustledger_core::Posting {
                        account: p.account.clone().into(),
                        units,
                        cost,
                        price,
                        flag: None,
                        meta: json_map_to_metadata(&p.meta),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    }
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
            let date = NaiveDate::parse_from_str(date, "%Y-%m-%d")
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
            let date = NaiveDate::parse_from_str(date, "%Y-%m-%d")
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
            let date = NaiveDate::parse_from_str(date, "%Y-%m-%d")
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
            let date = NaiveDate::parse_from_str(date, "%Y-%m-%d")
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
            let date = NaiveDate::parse_from_str(date, "%Y-%m-%d")
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
            let date = NaiveDate::parse_from_str(date, "%Y-%m-%d")
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
            let date = NaiveDate::parse_from_str(date, "%Y-%m-%d")
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
            let date = NaiveDate::parse_from_str(date, "%Y-%m-%d")
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
            let date = NaiveDate::parse_from_str(date, "%Y-%m-%d")
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
            let date = NaiveDate::parse_from_str(date, "%Y-%m-%d")
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
            let date = NaiveDate::parse_from_str(date, "%Y-%m-%d")
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
