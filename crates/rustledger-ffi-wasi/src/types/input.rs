//! Input types for JSON deserialization.

use std::collections::HashMap;

use rustledger_core::{Directive, MetaValue, Metadata, NaiveDate};
use serde::Deserialize;

/// Parse an `InputAmount` to a host `Amount`, propagating decimal parse
/// errors instead of silently coercing them to zero.
///
/// Pre-fix every amount-bearing field on the wire used
/// `unwrap_or_else(|_| Decimal::from(0))`, which meant a balance
/// assertion like `{"amount": {"number": "garbage", "currency":
/// "USD"}}` was accepted as `0 USD` — silently defeating balance
/// checks (review B-4.1). All callers now propagate the parse error
/// to the wire client.
fn parse_input_amount(
    field: &str,
    amount: &InputAmount,
) -> Result<rustledger_core::Amount, String> {
    let number = rustledger_core::Decimal::from_str_exact(&amount.number)
        .map_err(|e| format!("invalid {field} number {:?}: {e}", amount.number))?;
    Ok(rustledger_core::Amount {
        number,
        currency: amount.currency.clone().into(),
    })
}

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
///
/// `Option` fields follow serde's standard convention: an omitted JSON
/// field is treated as `None` (this can't be tightened without a
/// custom `Deserialize` impl — serde's `Option` deserializer is
/// inherently lenient). `#[serde(deny_unknown_fields)]` catches the
/// other half of the client-bug risk: a misspelled field name will
/// fail to parse instead of silently being dropped (review A-3.8).
#[derive(Debug, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
pub struct InputCost {
    /// Cost number (per-unit, total, or post-booking pair).
    /// `None` / absent corresponds to a bare `{}` cost spec.
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
    /// Merge-into-existing-lot flag (the `*` marker on a cost spec —
    /// triggers average-cost booking for the position). Pre-A-4.6 the
    /// FFI bridge hard-coded `false`, which silently diverged from the
    /// plugin egress (`from_wrapper.rs`) that does accept the field.
    /// Both ingress surfaces now consume `merge` uniformly.
    #[serde(default)]
    pub merge: bool,
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
        /// Tags attached to the document directive (issue #1144 added
        /// these to core `Document`; plumbed through to the RPC input
        /// in #1213).
        #[serde(default)]
        tags: Vec<String>,
        /// Links attached to the document directive (issue #1144).
        #[serde(default)]
        links: Vec<String>,
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
///
/// Unparsable numeric values become `MetaValue::None` (review B-4.1)
/// rather than silently coercing to zero. Metadata is informational
/// so a typed `MetaValue::None` is the right "I saw something but
/// couldn't interpret it as a number" signal — preferable to either
/// silently substituting zero (loses the original value) or panicking
/// (heavyweight for a metadata field).
pub fn json_to_meta_value(value: &serde_json::Value) -> MetaValue {
    match value {
        serde_json::Value::String(s) => MetaValue::String(s.clone()),
        serde_json::Value::Bool(b) => MetaValue::Bool(*b),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                MetaValue::Number(rustledger_core::Decimal::from(i))
            } else if let Some(f) = n.as_f64() {
                match rustledger_core::Decimal::from_str_exact(&f.to_string()) {
                    Ok(d) => MetaValue::Number(d),
                    Err(_) => MetaValue::None,
                }
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
                return match rustledger_core::Decimal::from_str_exact(n) {
                    Ok(number) => MetaValue::Amount(rustledger_core::Amount {
                        number,
                        currency: c.into(),
                    }),
                    Err(_) => MetaValue::None,
                };
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
                    let units = p
                        .units
                        .as_ref()
                        .map(|u| parse_input_amount("posting units", u))
                        .transpose()?
                        .map(rustledger_core::IncompleteAmount::Complete);

                    let cost = p
                        .cost
                        .as_ref()
                        .map(|c| {
                            // The wire `InputCostNumber` is a tagged enum
                            // mirroring the host `CostNumber`. The type
                            // system prevents the both-set state; we
                            // additionally enforce the
                            // `per_unit * |units| == total` invariant for
                            // PerUnitFromTotal so external clients cannot
                            // smuggle in inconsistent post-booking pairs.
                            // Inconsistent pairs become a parse error
                            // (review B-3.1) — silently falling back to
                            // PerUnit and dropping the supplied total
                            // would itself be a corruption pattern.
                            let parse = |s: &str| {
                                rustledger_core::Decimal::from_str_exact(s).map_err(|e| {
                                    format!("invalid cost number {s:?}: {e}")
                                })
                            };
                            let posting_units = units
                                .as_ref()
                                .and_then(|u: &rustledger_core::IncompleteAmount| u.as_amount());
                            let number = match c.number.as_ref() {
                                None => None,
                                Some(crate::types::input::InputCostNumber::PerUnit { value }) => {
                                    Some(rustledger_core::CostNumber::PerUnit { value: parse(value)? })
                                }
                                Some(crate::types::input::InputCostNumber::Total { value }) => {
                                    Some(rustledger_core::CostNumber::Total { value: parse(value)? })
                                }
                                Some(crate::types::input::InputCostNumber::PerUnitFromTotal {
                                    per_unit,
                                    total,
                                }) => {
                                    let per_unit_d = parse(per_unit)?;
                                    let total_d = parse(total)?;
                                    // PerUnitFromTotal is the post-booking
                                    // shape — the wire client MUST supply
                                    // units. Missing units → reject (not
                                    // "fall back to PerUnit", which would
                                    // silently drop the supplied total).
                                    let units_n = posting_units.as_ref().map(|a| a.number).ok_or_else(|| {
                                        "PerUnitFromTotal cost requires units on the posting — \
                                         this is the post-booking shape and is meaningless without units. \
                                         Send `{kind:\"per_unit\", value:...}` or `{kind:\"total\", value:...}` for unbooked specs.".to_string()
                                    })?;
                                    let booked = rustledger_core::BookedCost::try_new(
                                        per_unit_d, total_d, units_n,
                                    )
                                    .map_err(|e| format!("{e}"))?;
                                    Some(rustledger_core::CostNumber::PerUnitFromTotal(booked))
                                }
                            };
                            Ok::<_, String>(rustledger_core::CostSpec {
                                number,
                                currency: c.currency.clone().map(Into::into),
                                date: c.date.as_ref().and_then(|d| d.parse::<NaiveDate>().ok()),
                                label: c.label.clone(),
                                merge: c.merge,
                            })
                        })
                        .transpose()?;

                    let price = p
                        .price
                        .as_ref()
                        .map(|pr| parse_input_amount("posting price", pr))
                        .transpose()?
                        .map(rustledger_core::PriceAnnotation::unit);

                    Ok::<_, String>(rustledger_core::Spanned::synthesized(rustledger_core::Posting {
                        account: p.account.clone().into(),
                        units,
                        cost,
                        price,
                        flag: None,
                        meta: json_map_to_metadata(&p.meta),
                        comments: Vec::new(),
                        trailing_comments: Vec::new(),
                    }))
                })
                .collect::<Result<_, String>>()?;

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
                amount: parse_input_amount("balance amount", amount)?,
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
                amount: parse_input_amount("price amount", amount)?,
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
            tags,
            links,
            meta,
        } => {
            let date = date
                .parse::<NaiveDate>()
                .map_err(|e| format!("Invalid date '{date}': {e}"))?;
            Ok(Directive::Document(rustledger_core::Document {
                date,
                account: account.clone().into(),
                path: path.clone(),
                tags: tags.iter().map(|t| t.clone().into()).collect(),
                links: links.iter().map(|l| l.clone().into()).collect(),
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
        // `{}` lot match: number absent → bare cost spec. Serde's
        // Option deserializer treats missing fields as `None` by
        // convention; we lean on `deny_unknown_fields` for the other
        // client-bug case (misspelled field).
        let json = r#"{"currency": "USD"}"#;
        let cost: InputCost = serde_json::from_str(json).unwrap();
        assert!(cost.number.is_none());
        assert_eq!(cost.currency.as_deref(), Some("USD"));
    }

    #[test]
    fn input_cost_rejects_unknown_field() {
        // `deny_unknown_fields` catches misspelled fields that would
        // otherwise be silently dropped (review A-3.8). A client
        // sending an unrecognized key (e.g. `cost_number` instead of
        // `number`) gets a parse error instead of an unexpectedly
        // bare cost spec on the directive.
        let json = r#"{"cost_number": {"kind": "per_unit", "value": "100"}, "currency": "USD"}"#;
        let result: Result<InputCost, _> = serde_json::from_str(json);
        assert!(
            result.is_err(),
            "expected parse error for unknown field, got Ok"
        );
    }

    #[test]
    fn input_cost_per_unit_from_total_rejected_when_inconsistent() {
        // Bridge-level test through the actual conversion path:
        // PerUnitFromTotal with mismatched per_unit/total/units must
        // produce a typed error string, not silently coerce to
        // PerUnit. Pre-fix this fell back to `PerUnit { value:
        // per_unit_d }`, dropping the supplied total.
        let entry_json = r#"{
            "type": "transaction",
            "date": "2024-01-15",
            "flag": "*",
            "payee": null,
            "narration": "Buy stock",
            "tags": [],
            "links": [],
            "meta": {},
            "postings": [
                {
                    "account": "Assets:Stock",
                    "units": {"number": "10", "currency": "STK"},
                    "cost": {
                        "number": {"kind": "per_unit_from_total", "per_unit": "999999", "total": "0.01"},
                        "currency": "USD",
                        "date": null,
                        "label": null
                    },
                    "price": null,
                    "meta": {}
                }
            ]
        }"#;
        let entry: InputEntry = serde_json::from_str(entry_json).unwrap();
        let result = input_entry_to_directive(&entry);
        assert!(
            result.is_err(),
            "inconsistent PerUnitFromTotal must reject at the bridge"
        );
        let err = result.unwrap_err();
        // Diagnostic mentions the invariant so plugin authors can fix
        // their wire client.
        assert!(
            err.contains("invariant") || err.contains("per_unit") || err.contains("total"),
            "error message must describe the invariant violation, got: {err}"
        );
    }

    #[test]
    fn balance_with_malformed_amount_is_rejected() {
        // The load-bearing B-4.1 regression guard: a balance
        // assertion with a non-numeric amount field used to be
        // silently accepted as `0 USD`, defeating balance checks.
        // The wire bridge now propagates the parse error so the
        // client knows their payload was malformed.
        let entry_json = r#"{
            "type": "balance",
            "date": "2024-01-15",
            "account": "Assets:Bank",
            "amount": {"number": "garbage", "currency": "USD"},
            "meta": {}
        }"#;
        let entry: InputEntry = serde_json::from_str(entry_json).unwrap();
        let result = input_entry_to_directive(&entry);
        assert!(
            result.is_err(),
            "malformed balance amount must surface a parse error, not silently coerce to 0"
        );
        let err = result.unwrap_err();
        assert!(
            err.contains("balance amount") && err.contains("garbage"),
            "error must name both the field and the offending value, got: {err}"
        );
    }

    #[test]
    fn price_with_malformed_amount_is_rejected() {
        let entry_json = r#"{
            "type": "price",
            "date": "2024-01-15",
            "currency": "AAPL",
            "amount": {"number": "abc", "currency": "USD"},
            "meta": {}
        }"#;
        let entry: InputEntry = serde_json::from_str(entry_json).unwrap();
        let result = input_entry_to_directive(&entry);
        assert!(
            result.is_err(),
            "malformed price amount must surface a parse error"
        );
        assert!(result.unwrap_err().contains("price amount"));
    }

    #[test]
    fn posting_with_malformed_units_is_rejected() {
        let entry_json = r#"{
            "type": "transaction",
            "date": "2024-01-15",
            "flag": "*",
            "payee": null,
            "narration": "Buy",
            "tags": [], "links": [],
            "meta": {},
            "postings": [
                {
                    "account": "Assets:Stock",
                    "units": {"number": "not-a-number", "currency": "STK"},
                    "cost": null,
                    "price": null,
                    "meta": {}
                }
            ]
        }"#;
        let entry: InputEntry = serde_json::from_str(entry_json).unwrap();
        let result = input_entry_to_directive(&entry);
        assert!(
            result.is_err(),
            "malformed posting units must surface a parse error"
        );
        assert!(result.unwrap_err().contains("posting units"));
    }

    /// Regression for #1213: `Document` directives constructed via
    /// the RPC input side must carry `tags` and `links` through to
    /// the resulting core `Document`. Pre-#1213 the bridge hardcoded
    /// empty `Vec::new()` even when the caller supplied the fields.
    #[test]
    fn document_tags_and_links_round_trip_1213() {
        let entry_json = r#"{
            "type": "document",
            "date": "2024-01-15",
            "account": "Assets:Bank",
            "path": "statements/2024-01.pdf",
            "tags": ["statement", "bank"],
            "links": ["inv-2024-01"],
            "meta": {}
        }"#;
        let entry: InputEntry = serde_json::from_str(entry_json).unwrap();
        let directive = input_entry_to_directive(&entry).expect("valid document must convert");
        let Directive::Document(doc) = directive else {
            panic!("expected Document directive");
        };
        assert_eq!(doc.tags.len(), 2);
        assert_eq!(doc.tags[0].to_string(), "statement");
        assert_eq!(doc.tags[1].to_string(), "bank");
        assert_eq!(doc.links.len(), 1);
        assert_eq!(doc.links[0].to_string(), "inv-2024-01");
    }

    /// Backward-compat: a Document payload without `tags`/`links`
    /// fields (the pre-#1213 RPC clients still in the wild) must
    /// continue to deserialize as empty vectors via `serde(default)`.
    #[test]
    fn document_tags_and_links_default_to_empty_1213() {
        let entry_json = r#"{
            "type": "document",
            "date": "2024-01-15",
            "account": "Assets:Bank",
            "path": "statements/2024-01.pdf",
            "meta": {}
        }"#;
        let entry: InputEntry = serde_json::from_str(entry_json).unwrap();
        let directive = input_entry_to_directive(&entry).expect("legacy payload must convert");
        let Directive::Document(doc) = directive else {
            panic!("expected Document directive");
        };
        assert!(doc.tags.is_empty());
        assert!(doc.links.is_empty());
    }

    #[test]
    fn input_cost_per_unit_from_total_rejected_when_units_missing() {
        // PerUnitFromTotal is post-booking; a plugin sending it
        // without units is malformed (review B-3.1). The bridge must
        // reject rather than default units to 0 (which the
        // pre-fix `invariant_holds` short-circuit accepted).
        let entry_json = r#"{
            "type": "transaction",
            "date": "2024-01-15",
            "flag": "*",
            "payee": null,
            "narration": "Buy stock",
            "tags": [],
            "links": [],
            "meta": {},
            "postings": [
                {
                    "account": "Assets:Stock",
                    "units": null,
                    "cost": {
                        "number": {"kind": "per_unit_from_total", "per_unit": "999999", "total": "0.01"},
                        "currency": "USD",
                        "date": null,
                        "label": null
                    },
                    "price": null,
                    "meta": {}
                }
            ]
        }"#;
        let entry: InputEntry = serde_json::from_str(entry_json).unwrap();
        let result = input_entry_to_directive(&entry);
        assert!(
            result.is_err(),
            "PerUnitFromTotal without units must reject (post-booking shape requires units)"
        );
    }
}
