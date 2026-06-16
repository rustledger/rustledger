//! Conversion from the reused `rustledger-ffi-wasi` DTOs into the generated
//! WIT types.
//!
//! The loader orchestration (`load_source`) and the core→DTO conversion
//! (`directive_to_json`) are reused wholesale; this module is the mechanical
//! DTO→WIT shuffle, since the WIT types were authored 1:1 with the DTOs.
//!
//! Known fidelity gap: directive/posting metadata is reused from the DTO, which
//! flattens `MetaValue` to JSON and stringifies numbers — so a numeric metadata
//! value currently surfaces as `meta-value::text`. Faithful typing requires
//! reading the core `MetaValue` directly; tracked as a follow-up. (Custom
//! directive values keep their type via `TypedValue`, so they are unaffected.)

use rustledger_ffi_wasi as ffi;
use serde_json::Value as Json;

use crate::exports::rustledger::ledger::ledger as out;
use crate::rustledger::ledger::types as wit;

fn amount(a: ffi::Amount) -> wit::Amount {
    wit::Amount {
        number: a.number,
        currency: a.currency,
    }
}

fn cost_number(n: ffi::CostNumber) -> wit::CostNumber {
    match n {
        ffi::CostNumber::PerUnit { value } => wit::CostNumber::PerUnit(value),
        ffi::CostNumber::Total { value } => wit::CostNumber::Total(value),
        ffi::CostNumber::PerUnitFromTotal { per_unit, total } => {
            wit::CostNumber::PerUnitFromTotal((per_unit, total))
        }
    }
}

fn cost(c: ffi::PostingCost) -> wit::Cost {
    wit::Cost {
        number: c.number.map(cost_number),
        currency: c.currency,
        date: c.date,
        label: c.label,
    }
}

/// JSON metadata value → WIT `meta-value`. See the module-level fidelity note.
fn meta_value(v: Json) -> wit::MetaValue {
    match v {
        Json::Null => wit::MetaValue::Null,
        Json::Bool(b) => wit::MetaValue::Boolean(b),
        Json::Number(n) => wit::MetaValue::Number(n.to_string()),
        Json::Object(map) => {
            match (map.get("number"), map.get("currency")) {
                (Some(Json::String(n)), Some(Json::String(c))) => {
                    wit::MetaValue::Amount(wit::Amount {
                        number: n.clone(),
                        currency: c.clone(),
                    })
                }
                // Not an amount object — preserve a best-effort textual form.
                _ => wit::MetaValue::Text(Json::Object(map).to_string()),
            }
        }
        Json::String(s) => wit::MetaValue::Text(s),
        other => wit::MetaValue::Text(other.to_string()),
    }
}

fn meta_entries(user: std::collections::HashMap<String, Json>) -> Vec<(String, wit::MetaValue)> {
    let mut entries: Vec<(String, wit::MetaValue)> =
        user.into_iter().map(|(k, v)| (k, meta_value(v))).collect();
    // Deterministic order (HashMap iteration is not).
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    entries
}

fn meta(m: ffi::Meta) -> wit::Meta {
    wit::Meta {
        filename: m.filename,
        lineno: m.lineno,
        hash: m.hash,
        user: meta_entries(m.user),
    }
}

fn posting(p: ffi::Posting) -> wit::Posting {
    wit::Posting {
        account: p.account,
        units: p.units.map(amount),
        cost: p.cost.map(cost),
        price: p.price.map(amount),
        flag: p.flag,
        meta: meta_entries(p.meta),
    }
}

fn directive(d: ffi::DirectiveJson) -> wit::Directive {
    use ffi::DirectiveJson as D;
    match d {
        D::Transaction {
            date,
            flag,
            payee,
            narration,
            tags,
            links,
            postings,
            meta: m,
        } => wit::Directive::Transaction(wit::Transaction {
            date,
            flag,
            payee,
            narration,
            tags,
            links,
            postings: postings.into_iter().map(posting).collect(),
            meta: meta(m),
        }),
        D::Open {
            date,
            account,
            currencies,
            booking,
            meta: m,
        } => wit::Directive::Open(wit::OpenDir {
            date,
            account,
            currencies,
            booking,
            meta: meta(m),
        }),
        D::Close {
            date,
            account,
            meta: m,
        } => wit::Directive::Close(wit::CloseDir {
            date,
            account,
            meta: meta(m),
        }),
        D::Balance {
            date,
            account,
            amount: amt,
            tolerance,
            meta: m,
        } => wit::Directive::Balance(wit::BalanceDir {
            date,
            account,
            amount: amount(amt),
            tolerance,
            meta: meta(m),
        }),
        D::Pad {
            date,
            account,
            source_account,
            meta: m,
        } => wit::Directive::Pad(wit::PadDir {
            date,
            account,
            source_account,
            meta: meta(m),
        }),
        D::Commodity {
            date,
            currency,
            meta: m,
        } => wit::Directive::Commodity(wit::CommodityDir {
            date,
            currency,
            meta: meta(m),
        }),
        D::Price {
            date,
            currency,
            amount: amt,
            meta: m,
        } => wit::Directive::Price(wit::PriceDir {
            date,
            currency,
            amount: amount(amt),
            meta: meta(m),
        }),
        D::Event {
            date,
            event_type,
            value,
            meta: m,
        } => wit::Directive::Event(wit::EventDir {
            date,
            event_type,
            value,
            meta: meta(m),
        }),
        D::Note {
            date,
            account,
            comment,
            meta: m,
        } => wit::Directive::Note(wit::NoteDir {
            date,
            account,
            comment,
            meta: meta(m),
        }),
        D::Document {
            date,
            account,
            path,
            tags,
            links,
            meta: m,
        } => wit::Directive::Document(wit::DocumentDir {
            date,
            account,
            path,
            tags,
            links,
            meta: meta(m),
        }),
        D::Query {
            date,
            name,
            query_string,
            meta: m,
        } => wit::Directive::Query(wit::QueryDir {
            date,
            name,
            query_string,
            meta: meta(m),
        }),
        D::Custom {
            date,
            custom_type,
            values,
            meta: m,
        } => wit::Directive::Custom(wit::CustomDir {
            date,
            custom_type,
            values: values.into_iter().map(|tv| meta_value(tv.value)).collect(),
            meta: meta(m),
        }),
    }
}

fn error(e: ffi::Error) -> wit::Error {
    wit::Error {
        message: e.message,
        line: e.line,
        column: e.column,
        field: e.field,
        // DTO uses usize; WIT uses u32.
        entry_index: e.entry_index.map(|i| i as u32),
        severity: e.severity,
        phase: e.phase,
    }
}

fn pairs_u32(m: std::collections::HashMap<String, u32>) -> Vec<(String, u32)> {
    let mut v: Vec<_> = m.into_iter().collect();
    v.sort_by(|a, b| a.0.cmp(&b.0));
    v
}

fn pairs_str(m: std::collections::HashMap<String, String>) -> Vec<(String, String)> {
    let mut v: Vec<_> = m.into_iter().collect();
    v.sort_by(|a, b| a.0.cmp(&b.0));
    v
}

fn options(o: ffi::LedgerOptions) -> wit::LedgerOptions {
    wit::LedgerOptions {
        title: o.title,
        operating_currency: o.operating_currency,
        name_assets: o.name_assets,
        name_liabilities: o.name_liabilities,
        name_equity: o.name_equity,
        name_income: o.name_income,
        name_expenses: o.name_expenses,
        documents: o.documents,
        commodities: o.commodities,
        booking_method: o.booking_method,
        display_precision: pairs_u32(o.display_precision),
        render_commas: o.render_commas,
        inferred_tolerance_default: pairs_str(o.inferred_tolerance_default),
        inferred_tolerance_multiplier: o.inferred_tolerance_multiplier,
        infer_tolerance_from_cost: o.infer_tolerance_from_cost,
        account_rounding: o.account_rounding,
        account_previous_balances: o.account_previous_balances,
        account_previous_earnings: o.account_previous_earnings,
        account_previous_conversions: o.account_previous_conversions,
        account_current_earnings: o.account_current_earnings,
        account_current_conversions: o.account_current_conversions,
        account_unrealized_gains: o.account_unrealized_gains,
        conversion_currency: o.conversion_currency,
    }
}

/// `ledger.load` — parse + book `source`, returning a typed load result.
pub fn load(source: &str, filename: &str) -> out::LoadResult {
    let loaded = ffi::helpers::load_source(source);
    let entries = loaded
        .directives
        .iter()
        .zip(loaded.directive_lines.iter())
        .map(|(d, &line)| directive(ffi::convert::directive_to_json(d, line, filename)))
        .collect();
    out::LoadResult {
        entries,
        errors: loaded.errors.into_iter().map(error).collect(),
        options: options(loaded.options),
        plugins: loaded
            .plugins
            .into_iter()
            .map(|p| wit::Plugin {
                name: p.name,
                config: p.config,
            })
            .collect(),
        includes: loaded
            .includes
            .into_iter()
            .map(|i| wit::SourceInclude {
                path: i.path,
                lineno: i.lineno,
            })
            .collect(),
    }
}
