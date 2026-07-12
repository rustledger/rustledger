//! Conversion from `rustledger-core` types into the generated WIT types.
//!
//! The loader orchestration (`load_source`) is reused from `rustledger-ffi-wasi`,
//! but each core [`rustledger_core::Directive`] is mapped **directly** to its WIT
//! shape here (no JSON DTO middle layer). Mirrors the field mapping the former
//! JSON DTO conversion performed, emitting WIT types instead.
//!
//! Doing the conversion against core gives metadata full fidelity: a numeric
//! metadata value surfaces as the typed `meta-value::number` (the DTO path
//! stringified it to JSON, collapsing it to `meta-value::text`). The string-like
//! `MetaValue` variants (string/account/currency/tag/link/date/int) still lower
//! to `text`, matching the JSON surface; `bool`/`amount`/`none` keep their typed
//! cases. (Custom-directive arguments additionally carry their `value-type` tag
//! via the WIT `typed-value` record.)

use rustledger_core::{Directive, MetaValue, Metadata, NaiveDate};
use rustledger_ffi_wasi as ffi;
use rustledger_query::{Executor, IntervalUnit, Value, parse as parse_query};
use serde_json::Value as Json;

use crate::exports::rustledger::ledger::ledger as out;
use crate::rustledger::ledger::types as wit;

/// Core `Amount` → WIT `amount` (decimal preserved as text).
fn amount_from_core(a: &rustledger_core::Amount) -> wit::Amount {
    wit::Amount {
        number: a.number.to_string(),
        currency: a.currency.to_string(),
    }
}

/// Core `CostNumber` → WIT `cost-number` (mirrors the DTO's tagged mapping).
fn cost_number_from_core(n: rustledger_core::CostNumber) -> wit::CostNumber {
    match n {
        rustledger_core::CostNumber::PerUnit { value } => {
            wit::CostNumber::PerUnit(value.to_string())
        }
        rustledger_core::CostNumber::Total { value } => wit::CostNumber::Total(value.to_string()),
        rustledger_core::CostNumber::PerUnitFromTotal(b) => {
            wit::CostNumber::PerUnitFromTotal((b.per_unit.to_string(), b.total.to_string()))
        }
        rustledger_core::CostNumber::Compound { per_unit, total } => {
            wit::CostNumber::Compound((per_unit.to_string(), total.to_string()))
        }
    }
}

/// Core posting `CostSpec` → WIT `cost`. Every field optional (a bare `{USD}`
/// lot match carries no `number`), matching the lean `PostingCost` shape.
fn cost_from_core(c: &rustledger_core::CostSpec) -> wit::Cost {
    wit::Cost {
        number: c.number.map(cost_number_from_core),
        currency: c.currency.as_ref().map(std::string::ToString::to_string),
        date: c.date.map(|d| d.to_string()),
        label: c.label.clone(),
    }
}

/// Core `MetaValue` → WIT `meta-value`, fully typed.
///
/// `Number` becomes the typed `meta-value::number` (the fidelity fix vs the old
/// JSON DTO path, which stringified it to `text`); `bool`/`amount`/`none` keep
/// their typed cases. The string-like variants (`String`/`Account`/`Currency`/
/// `Tag`/`Link`/`Date`/`Int`) lower to `text`, matching the JSON surface
/// (`Int` is stringified, like the DTO did).
fn meta_value_from_core(v: &MetaValue) -> wit::MetaValue {
    match v {
        MetaValue::String(s) => wit::MetaValue::Text(s.clone()),
        MetaValue::Account(a) => wit::MetaValue::Text(a.to_string()),
        MetaValue::Currency(c) => wit::MetaValue::Text(c.to_string()),
        MetaValue::Tag(t) => wit::MetaValue::Text(t.to_string()),
        MetaValue::Link(l) => wit::MetaValue::Text(l.to_string()),
        MetaValue::Date(d) => wit::MetaValue::Text(d.to_string()),
        // `number`, not `text`: the return path (`json_from_meta_value` →
        // `json_to_meta_value`) restores an integral number as
        // `MetaValue::Int`, so an integer round-trips the session/builder
        // boundary intact. As `text` it came back as a STRING — a session
        // round-trip turned `precision: 4` into `precision: "4"`, quoting
        // every integer metadata value in re-rendered ledger text and
        // breaking commodity-precision handling in `session.format` (#1766).
        MetaValue::Int(i) => wit::MetaValue::Number(i.to_string()),
        MetaValue::Number(n) => wit::MetaValue::Number(n.to_string()),
        MetaValue::Bool(b) => wit::MetaValue::Boolean(*b),
        MetaValue::Amount(a) => wit::MetaValue::Amount(amount_from_core(a)),
        MetaValue::None => wit::MetaValue::Null,
    }
}

/// Core metadata map → WIT `meta-entry` list, key-sorted (the source map has no
/// stable order; WIT has no map type so it is modeled as an ordered pair list).
fn meta_entries_from_core(m: &Metadata) -> Vec<(String, wit::MetaValue)> {
    let mut entries: Vec<(String, wit::MetaValue)> = m
        .iter()
        .map(|(k, v)| (k.clone(), meta_value_from_core(v)))
        .collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    entries
}

/// Build the WIT `meta` record (source location + typed user key/values).
fn meta_from_core(m: &Metadata, line: u32, filename: &str, hash: String) -> wit::Meta {
    wit::Meta {
        filename: filename.to_string(),
        lineno: line,
        hash,
        user: meta_entries_from_core(m),
    }
}

/// Core `Posting` → WIT `posting` (mirrors `directive_to_json`'s posting arm:
/// units from the complete amount, optional cost/price, flag, posting meta).
fn posting_from_core(p: &rustledger_core::Posting) -> wit::Posting {
    wit::Posting {
        account: p.account.to_string(),
        units: p
            .units
            .as_ref()
            .and_then(|u| u.as_amount())
            .map(amount_from_core),
        cost: p.cost.as_ref().map(cost_from_core),
        price: p
            .price
            .as_ref()
            .and_then(|pr| pr.amount())
            .map(amount_from_core),
        flag: p.flag.map(|c| c.to_string()),
        meta: meta_entries_from_core(&p.meta),
    }
}

/// Map a core [`Directive`] directly to its WIT shape, deriving `meta.hash` the
/// same way the DTO path did (`compute_directive_hash`). Field-for-field mirror
/// of the former JSON DTO conversion, emitting WIT types and fully-typed
/// metadata.
fn directive_from_core(d: &Directive, line: u32, filename: &str) -> wit::Directive {
    let hash = ffi::compute_directive_hash(d);
    let meta = |m: &Metadata| meta_from_core(m, line, filename, hash.clone());
    match d {
        Directive::Transaction(t) => wit::Directive::Transaction(wit::Transaction {
            date: t.date.to_string(),
            flag: t.flag.to_string(),
            payee: t.payee.as_ref().map(std::string::ToString::to_string),
            // Empty narration is omitted (the DTO maps "" → None).
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
            postings: t.postings.iter().map(|p| posting_from_core(p)).collect(),
            meta: meta(&t.meta),
        }),
        Directive::Open(o) => wit::Directive::Open(wit::OpenDir {
            date: o.date.to_string(),
            account: o.account.to_string(),
            currencies: o
                .currencies
                .iter()
                .map(std::string::ToString::to_string)
                .collect(),
            booking: o.booking.clone(),
            meta: meta(&o.meta),
        }),
        Directive::Close(c) => wit::Directive::Close(wit::CloseDir {
            date: c.date.to_string(),
            account: c.account.to_string(),
            meta: meta(&c.meta),
        }),
        Directive::Balance(b) => wit::Directive::Balance(wit::BalanceDir {
            date: b.date.to_string(),
            account: b.account.to_string(),
            amount: amount_from_core(&b.amount),
            tolerance: b.tolerance.map(|t| t.to_string()),
            // Filled in by `attach_balance_diffs` after validation runs (#1663);
            // `directive_from_core` has no ledger-wide context on its own.
            diff: None,
            meta: meta(&b.meta),
        }),
        Directive::Pad(p) => wit::Directive::Pad(wit::PadDir {
            date: p.date.to_string(),
            account: p.account.to_string(),
            source_account: p.source_account.to_string(),
            meta: meta(&p.meta),
        }),
        Directive::Commodity(c) => wit::Directive::Commodity(wit::CommodityDir {
            date: c.date.to_string(),
            currency: c.currency.to_string(),
            meta: meta(&c.meta),
        }),
        Directive::Price(p) => wit::Directive::Price(wit::PriceDir {
            date: p.date.to_string(),
            currency: p.currency.to_string(),
            amount: amount_from_core(&p.amount),
            meta: meta(&p.meta),
        }),
        Directive::Event(e) => wit::Directive::Event(wit::EventDir {
            date: e.date.to_string(),
            event_type: e.event_type.clone(),
            value: e.value.clone(),
            meta: meta(&e.meta),
        }),
        Directive::Note(n) => wit::Directive::Note(wit::NoteDir {
            date: n.date.to_string(),
            account: n.account.to_string(),
            comment: n.comment.clone(),
            meta: meta(&n.meta),
        }),
        Directive::Document(doc) => wit::Directive::Document(wit::DocumentDir {
            date: doc.date.to_string(),
            account: doc.account.to_string(),
            path: doc.path.clone(),
            tags: doc
                .tags
                .iter()
                .map(std::string::ToString::to_string)
                .collect(),
            links: doc
                .links
                .iter()
                .map(std::string::ToString::to_string)
                .collect(),
            meta: meta(&doc.meta),
        }),
        Directive::Query(q) => wit::Directive::Query(wit::QueryDir {
            date: q.date.to_string(),
            name: q.name.clone(),
            query_string: q.query.clone(),
            meta: meta(&q.meta),
        }),
        Directive::Custom(c) => wit::Directive::Custom(wit::CustomDir {
            date: c.date.to_string(),
            custom_type: c.custom_type.clone(),
            // Carry the `value-type` tag (account/currency/tag/…) alongside the
            // value, which `meta-value` alone would flatten to `text`.
            values: c
                .values
                .iter()
                .map(|v| wit::TypedValue {
                    value_type: rustledger_core::meta_value_type_tag(v).to_string(),
                    value: meta_value_from_core(v),
                })
                .collect(),
            meta: meta(&c.meta),
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

/// Flatten a map into a key-sorted `list<tuple>` (WIT has no map type, so the
/// surface models maps as deterministically-ordered pair lists).
fn pairs<V>(m: std::collections::HashMap<String, V>) -> Vec<(String, V)> {
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
        display_precision: pairs(o.display_precision),
        render_commas: o.render_commas,
        inferred_tolerance_default: pairs(o.inferred_tolerance_default),
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
/// `expand_pads` materializes `pad` directives into synthesized `Padding`
/// transactions (balance consumers opt in); default-off is source-faithful (#1628).
pub fn load(source: &str, filename: &str, expand_pads: bool) -> out::LoadResult {
    load_result(ffi::helpers::load_source(source), filename, expand_pads)
}

/// Run the semantic validation session over a loaded result and return its
/// validation-phase errors. Empty when the input has parse errors (validation
/// only runs on syntactically-valid input, matching `validate`).
///
/// Shared by `validate` and the `load`/`load_file` path so the primary load
/// surface reports balance-assertion failures (and the other Late checks) like
/// beancount's `loader.load_file` — not only `validate`. Embedders that load via
/// `load` (rustfava) would otherwise see a failing `balance` as `errors: []`
/// (#1663).
fn semantic_validation_errors(
    loaded: &ffi::helpers::LoadResult,
) -> (Vec<ffi::Error>, Vec<rustledger_validate::BalanceActual>) {
    if loaded.errors.iter().any(|e| e.phase == "parse") {
        return (Vec::new(), Vec::new());
    }
    let today = jiff::Zoned::now().date();
    let session = rustledger_validate::ValidationSession::new(
        rustledger_validate::ValidationOptions::default(),
    );
    let (session, mut verrs) = session.run_early_spanned(&loaded.spanned_directives, today);
    let (session, late) = session.run_late_spanned(&loaded.spanned_directives, today);
    verrs.extend(late);
    // Capture the per-balance computed results (#1663) before `finalize` consumes
    // the session.
    let actuals = session.balance_actuals().to_vec();
    verrs.extend(session.finalize());
    // `load_source` already ran booking, which reports reduction failures
    // (insufficient units / no-matching-lot / ambiguous match) WITH transaction
    // context. The validation session re-derives the same failures context-free
    // (its reduce-check is a standalone-validation safety net), so a fresh error
    // here would duplicate the one already in `loaded.errors` — once with
    // context, once without (#1668). Drop a session error when a load error is
    // identical or is that message followed by booking's ` (date, "narration")`
    // suffix.
    let load_msgs: Vec<&str> = loaded.errors.iter().map(|e| e.message.as_str()).collect();
    let is_dup_of_booking = |msg: &str| {
        let with_ctx = format!("{msg} (");
        load_msgs
            .iter()
            .any(|lm| *lm == msg || lm.starts_with(&with_ctx))
    };
    let errors = verrs
        .into_iter()
        .filter(|err| !is_dup_of_booking(&err.message))
        .map(|err| {
            let mut e = ffi::Error::new(&err.message).validate_phase();
            // Preserve severity, like the loader path already does. Every
            // validation finding was crossing as `severity: "error"` because
            // that is `Error::new`'s default, so a WARNING flipped
            // `validate-result.valid` to false. Harmless while every validation
            // code was an error; E11001 is a warning that fires on ordinary
            // Fava-budgeted ledgers, so a host gating on `valid` would call a
            // perfectly loadable ledger broken over an extension-point
            // directive Fava itself ignores.
            if err.code.severity() == rustledger_validate::Severity::Warning {
                e.severity = "warning".to_string();
            }
            if let Some(span) = err.span {
                e = e.with_line(loaded.line_lookup.byte_to_line(span.start));
            }
            e
        })
        .collect();
    (errors, actuals)
}

/// Attach the computed `diff` (`computed − asserted`) to each `balance` directive
/// entry from the validator's recorded results (#1663), keyed by
/// `(date, account, currency)`.
fn attach_balance_diffs(
    entries: &mut [wit::Directive],
    actuals: &[rustledger_validate::BalanceActual],
) {
    if actuals.is_empty() {
        return;
    }
    let map: std::collections::HashMap<(String, String, String), rustledger_core::Decimal> =
        actuals
            .iter()
            .map(|a| {
                (
                    (
                        a.date.to_string(),
                        a.account.to_string(),
                        a.currency.to_string(),
                    ),
                    a.diff,
                )
            })
            .collect();
    for entry in entries.iter_mut() {
        if let wit::Directive::Balance(b) = entry {
            let key = (b.date.clone(), b.account.clone(), b.amount.currency.clone());
            if let Some(diff) = map.get(&key) {
                b.diff = Some(wit::Amount {
                    number: diff.to_string(),
                    currency: b.amount.currency.clone(),
                });
            }
        }
    }
}

/// Build a WIT load-result from a consumed `ffi-wasi` load result (shared by
/// `load` and `batch`). `batch` always passes `expand_pads = false` — its load
/// section is source-faithful and its queries pad-expand separately.
fn load_result(
    loaded: ffi::helpers::LoadResult,
    filename: &str,
    expand_pads: bool,
) -> out::LoadResult {
    // #1663: run semantic validation (balance assertions and the other Late
    // checks) so `load`/`load_file` report them like beancount's
    // `loader.load_file` — not only `validate`. Computed before `loaded` is
    // consumed below.
    let (validation_errs, balance_actuals) = semantic_validation_errors(&loaded);

    // Synthesized pad transactions have no source line (tagged 0).
    let (directives, directive_lines) = if expand_pads {
        ffi::helpers::expand_pads(loaded.directives, loaded.directive_lines, &0u32)
    } else {
        (loaded.directives, loaded.directive_lines)
    };
    let mut entries: Vec<wit::Directive> = directives
        .iter()
        .zip(directive_lines.iter())
        .map(|(d, &line)| directive_from_core(d, line, filename))
        .collect();
    // #1663 (Part 2): stamp each `balance` directive with `computed − asserted`.
    attach_balance_diffs(&mut entries, &balance_actuals);
    let mut errors = loaded.errors;
    errors.extend(validation_errs);
    out::LoadResult {
        entries,
        errors: errors.into_iter().map(error).collect(),
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

// ---- query + validate ----

fn realized_cost(c: &rustledger_core::Cost) -> wit::Cost {
    // A booked position carries a concrete per-unit cost (mirrors #1399).
    wit::Cost {
        number: Some(wit::CostNumber::PerUnit(c.number.to_string())),
        currency: Some(c.currency.to_string()),
        date: c.date.map(|d| d.to_string()),
        label: c.label.clone(),
    }
}

fn position(p: &rustledger_core::Position) -> wit::Position {
    wit::Position {
        units: wit::Amount {
            number: p.units.number.to_string(),
            currency: p.units.currency.to_string(),
        },
        cost: p.cost.as_ref().map(realized_cost),
    }
}

/// `rustledger_query::Value` → WIT `query-value` (mirrors `value_to_json`,
/// but typed). `object`/`set` are self-referential — WIT can't type them, so
/// they fall to the `json` escape hatch via the reused `value_to_json`.
fn query_value(v: &Value) -> wit::QueryValue {
    use wit::QueryValue as Q;
    match v {
        Value::Null => Q::Null,
        Value::Boolean(b) => Q::Boolean(*b),
        Value::Integer(i) => Q::Integer(*i),
        Value::String(s) => Q::Text(s.clone()),
        Value::Date(d) => Q::Date(d.to_string()),
        Value::Number(n) => Q::Number(n.to_string()),
        Value::Amount(a) => Q::Amount(wit::Amount {
            number: a.number.to_string(),
            currency: a.currency.to_string(),
        }),
        Value::Position(p) => Q::Position(position(p)),
        Value::Inventory(inv) => Q::Inventory(inv.positions().map(position).collect()),
        Value::StringSet(set) => Q::StringSet(set.clone()),
        Value::Metadata(m) => Q::Metadata(
            // `Display`, matching the canonical CLI, not `Debug` (which leaked
            // the Rust wrapper, e.g. `String("foo")`).
            m.iter()
                .map(|(k, val)| (k.clone(), format!("{val}")))
                .collect(),
        ),
        Value::Interval(iv) => Q::Interval(wit::Interval {
            count: iv.count,
            unit: match iv.unit {
                IntervalUnit::Day => wit::IntervalUnit::Day,
                IntervalUnit::Week => wit::IntervalUnit::Week,
                IntervalUnit::Month => wit::IntervalUnit::Month,
                IntervalUnit::Quarter => wit::IntervalUnit::Quarter,
                IntervalUnit::Year => wit::IntervalUnit::Year,
            },
        }),
        Value::Object(_) | Value::Set(_) => Q::Json(value_to_json(v).to_string()),
    }
}

/// `rustledger_query::Value` → `serde_json` form, for the `object`/`set` cases
/// that WIT can't type (they are self-referential). Self-contained equivalent of
/// the former JSON DTO query-value conversion — recursion has to handle every
/// nested variant even though only `object`/`set` reach it here.
fn value_to_json(value: &Value) -> Json {
    match value {
        Value::Null => Json::Null,
        Value::Boolean(b) => Json::Bool(*b),
        Value::Integer(i) => serde_json::json!(i),
        Value::String(s) => Json::String(s.clone()),
        Value::Date(d) => Json::String(d.to_string()),
        Value::Number(d) => serde_json::json!({ "number": d.to_string() }),
        Value::Amount(a) => serde_json::json!({
            "number": a.number.to_string(),
            "currency": a.currency.to_string(),
        }),
        Value::Position(p) => position_to_json(p),
        Value::Inventory(inv) => {
            let positions: Vec<Json> = inv.positions().map(position_to_json).collect();
            serde_json::json!({ "positions": positions })
        }
        Value::StringSet(set) => serde_json::json!(set),
        Value::Object(obj) => {
            let mut map = serde_json::Map::new();
            for (k, v) in obj.as_ref() {
                map.insert(k.clone(), value_to_json(v));
            }
            Json::Object(map)
        }
        Value::Metadata(m) => {
            // `Display`, matching the canonical CLI, not `Debug`.
            let obj: serde_json::Map<String, Json> = m
                .iter()
                .map(|(k, v)| (k.clone(), serde_json::json!(format!("{v}"))))
                .collect();
            Json::Object(obj)
        }
        Value::Interval(iv) => serde_json::json!({
            "count": iv.count,
            "unit": match iv.unit {
                IntervalUnit::Day => "day",
                IntervalUnit::Week => "week",
                IntervalUnit::Month => "month",
                IntervalUnit::Quarter => "quarter",
                IntervalUnit::Year => "year",
            },
        }),
        Value::Set(set) => Json::Array(set.iter().map(value_to_json).collect()),
    }
}

/// A position's units (+ realized per-unit cost, when held at cost) as JSON.
/// Mirrors the former JSON DTO position conversion.
fn position_to_json(p: &rustledger_core::Position) -> Json {
    let mut obj = serde_json::json!({
        "units": {
            "number": p.units.number.to_string(),
            "currency": p.units.currency.to_string(),
        }
    });
    if let Some(cost) = &p.cost {
        let mut cost_obj = serde_json::json!({
            "number": { "kind": "per_unit", "value": cost.number.to_string() },
            "currency": cost.currency.to_string(),
        });
        if let Some(date) = cost.date {
            cost_obj["date"] = Json::String(date.to_string());
        }
        if let Some(label) = &cost.label {
            cost_obj["label"] = Json::String(label.clone());
        }
        obj["cost"] = cost_obj;
    }
    obj
}

/// Datatype string for a query `Value` (column-type inference). Self-contained
/// equivalent of the former JSON DTO datatype helper.
const fn value_datatype(value: &Value) -> &'static str {
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
        Value::StringSet(_) | Value::Set(_) => "set",
        Value::Object(_) => "object",
        Value::Metadata(_) => "Metadata",
        Value::Interval(_) => "Interval",
    }
}

fn simple_error(message: String) -> wit::Error {
    error(ffi::Error::new(message))
}

/// `ledger.validate` — parse + semantic validation. Mirrors the JSON-RPC
/// `handle_validate` orchestration (`load_source` + `ValidationSession`).
pub fn validate(source: &str) -> out::ValidateResult {
    let load = ffi::helpers::load_source(source);
    let parse_error_count = load.errors.iter().filter(|e| e.phase == "parse").count();
    let (validation_errs, _actuals) = semantic_validation_errors(&load);
    let mut errors = load.errors;
    errors.extend(validation_errs);

    let validate_error_count = errors.iter().filter(|e| e.phase == "validate").count();
    out::ValidateResult {
        valid: errors.is_empty(),
        errors: errors.into_iter().map(error).collect(),
        parse_error_count: parse_error_count as u32,
        validate_error_count: validate_error_count as u32,
    }
}

/// `query.execute` — run a BQL query against `source`.
pub fn query(source: &str, query_str: &str) -> out::QueryResult {
    query_loaded(&ffi::helpers::load_source(source), query_str)
}

/// Short-circuit on load (parse/booking) errors, then run one query over the
/// pad-expanded directives — matching `handle_query` (FFI's `load_source` does
/// not pad-expand, so balance-computing consumers must opt in explicitly).
fn query_loaded(loaded: &ffi::helpers::LoadResult, query_str: &str) -> out::QueryResult {
    if !loaded.errors.is_empty() {
        return out::QueryResult {
            columns: Vec::new(),
            rows: Vec::new(),
            errors: loaded.errors.iter().cloned().map(error).collect(),
        };
    }
    let directives = rustledger_booking::merge_with_padding(&loaded.directives);
    run_query(&directives, query_str, account_types_from(&loaded.options))
}

/// Run one query against already-loaded, pad-expanded directives.
/// Build the config-aware account-type classifier from loaded ledger
/// options, so BQL `POSSIGN`/`ACCOUNT_SORTKEY` honor `name_*` renames the
/// way beanquery does (L5).
fn account_types_from(
    options: &rustledger_ffi_wasi::LedgerOptions,
) -> rustledger_core::AccountTypes {
    rustledger_core::AccountTypes {
        assets: options.name_assets.clone(),
        liabilities: options.name_liabilities.clone(),
        equity: options.name_equity.clone(),
        income: options.name_income.clone(),
        expenses: options.name_expenses.clone(),
    }
}

pub fn run_query(
    directives: &[rustledger_core::Directive],
    query_str: &str,
    account_types: rustledger_core::AccountTypes,
) -> out::QueryResult {
    let parsed = match parse_query(query_str) {
        Ok(q) => q,
        Err(e) => {
            return out::QueryResult {
                columns: vec![],
                rows: vec![],
                errors: vec![simple_error(e.to_string())],
            };
        }
    };
    let mut executor = Executor::new(directives);
    executor.set_account_types(account_types);
    match executor.execute(&parsed) {
        Ok(result) => {
            // Infer each column's datatype from its first NON-NULL value.
            // First-row-only inference declared "null" for columns whose
            // first row happened to be NULL, and baked in whichever shape row
            // one carried for expressions that were type-unstable across rows
            // (#1701) — the host trusts this declaration when deserializing
            // every row.
            let columns = if result.rows.is_empty() {
                result
                    .columns
                    .iter()
                    .map(|name| wit::ColumnInfo {
                        name: name.clone(),
                        datatype: "str".to_string(),
                    })
                    .collect()
            } else {
                result
                    .columns
                    .iter()
                    .enumerate()
                    .map(|(i, name)| {
                        let datatype = result
                            .rows
                            .iter()
                            .map(|row| &row[i])
                            .find(|v| !matches!(v, Value::Null))
                            .map_or("null", value_datatype);
                        wit::ColumnInfo {
                            name: name.clone(),
                            datatype: datatype.to_string(),
                        }
                    })
                    .collect()
            };
            let rows = result
                .rows
                .iter()
                .map(|row| row.iter().map(query_value).collect())
                .collect();
            out::QueryResult {
                columns,
                rows,
                errors: vec![],
            }
        }
        Err(e) => out::QueryResult {
            columns: vec![],
            rows: vec![],
            errors: vec![simple_error(format!("Query error: {e}"))],
        },
    }
}

/// `query.batch` — load `source` once, then run several queries against it.
/// On parse errors, every query returns the canonical short-circuit error
/// (matching `handle_batch`); otherwise pads are expanded once for all queries.
pub fn batch(source: &str, queries: &[String]) -> out::BatchResult {
    let loaded = ffi::helpers::load_source(source);
    let query_results: Vec<out::QueryResult> = if loaded.errors.is_empty() {
        let directives = rustledger_booking::merge_with_padding(&loaded.directives);
        queries
            .iter()
            .map(|q| run_query(&directives, q, account_types_from(&loaded.options)))
            .collect()
    } else {
        queries
            .iter()
            .map(|_| out::QueryResult {
                columns: Vec::new(),
                rows: Vec::new(),
                errors: vec![simple_error(
                    "Cannot execute query: parse errors exist".to_string(),
                )],
            })
            .collect()
    };
    out::BatchResult {
        load: load_result(loaded, "<stdin>", false),
        queries: query_results,
    }
}

// ---- file variants ----

fn read_file(path: &str) -> Result<String, String> {
    std::fs::read_to_string(path).map_err(|e| format!("Failed to read file '{path}': {e}"))
}

/// `ledger.loadFile` — load from a path, resolving `include` directives, with
/// a post-booking plugin pass.
///
/// Includes are confined to the entry file's directory tree by default;
/// `allow_unrestricted_includes == true` lifts that path-traversal protection
/// (so the safe state is the `false`/zero default). The flag is negated into
/// the loader's `path_security` at the boundary.
/// A filesystem that reads from the WASI-preopened disk but delegates GPG
/// decryption to the **host** via the `host.decrypt` import.
///
/// A WASI guest can neither spawn `gpg` nor reach the user's keyring, so
/// `.gpg`/`.asc` inputs can't be decrypted in the sandbox. The embedder (which
/// runs natively and holds that authority) satisfies the import — the
/// capability-passing pattern the WASI/component model is built around (#1667).
#[derive(Debug)]
struct HostDecryptFs(rustledger_loader::DiskFileSystem);

impl rustledger_loader::FileSystem for HostDecryptFs {
    fn read(
        &self,
        path: &std::path::Path,
    ) -> Result<std::sync::Arc<str>, rustledger_loader::LoadError> {
        self.0.read(path)
    }

    fn exists(&self, path: &std::path::Path) -> bool {
        self.0.exists(path)
    }

    fn is_encrypted(&self, path: &std::path::Path) -> bool {
        self.0.is_encrypted(path)
    }

    fn normalize(&self, path: &std::path::Path) -> std::path::PathBuf {
        self.0.normalize(path)
    }

    fn supports_parallel_read(&self) -> bool {
        self.0.supports_parallel_read()
    }

    fn glob(&self, pattern: &str) -> Result<Vec<std::path::PathBuf>, String> {
        self.0.glob(pattern)
    }

    fn decrypt(
        &self,
        path: &std::path::Path,
    ) -> Result<std::sync::Arc<str>, rustledger_loader::LoadError> {
        // Read the ciphertext from the sandbox, then hand it to the host to
        // decrypt with its keyring (the guest cannot) — #1667.
        let ciphertext =
            std::fs::read(path).map_err(|e| rustledger_loader::LoadError::Decryption {
                path: path.to_path_buf(),
                message: format!("failed to read encrypted file: {e}"),
            })?;
        let plaintext =
            crate::rustledger::ledger::host::decrypt(&ciphertext).map_err(|message| {
                rustledger_loader::LoadError::Decryption {
                    path: path.to_path_buf(),
                    message,
                }
            })?;
        Ok(std::sync::Arc::from(plaintext))
    }
}

pub fn load_file(
    path: &str,
    allow_unrestricted_includes: bool,
    plugins: &[String],
    expand_pads: bool,
) -> out::LoadResult {
    // The loader takes `path_security` (true = confine includes); the WIT flag
    // is inverted so the safe state is the `false`/zero default.
    let path_security = !allow_unrestricted_includes;
    // Inject a filesystem that routes GPG decryption to the `host.decrypt`
    // import — the sandbox can't run gpg or read the keyring (#1667).
    let fs = Box::new(HostDecryptFs(rustledger_loader::DiskFileSystem));
    match ffi::helpers::load_file_with_fs(std::path::Path::new(path), path_security, Some(fs)) {
        Ok(fl) => {
            let mut errors = fl.errors;
            let opts = fl.options;
            let plugin_dtos = fl.plugins;
            let loaded_files = fl.loaded_files;
            // Run requested plugins via the same helper the JSON-RPC handler uses.
            let plugin_names: Vec<&str> = plugins.iter().map(String::as_str).collect();
            let (directives, directive_lines, directive_files) = ffi::helpers::apply_plugins(
                &plugin_names,
                fl.directives,
                fl.directive_lines,
                fl.directive_files,
                &mut errors,
                &opts,
            );
            // Opt-in pad expansion for balance consumers (#1628); synthesized
            // transactions have no source location.
            let (directives, directive_lines, directive_files) = if expand_pads {
                let tags: Vec<(u32, String)> =
                    directive_lines.into_iter().zip(directive_files).collect();
                let (directives, tags) = ffi::helpers::expand_pads(
                    directives,
                    tags,
                    &(0u32, "<synthesized>".to_string()),
                );
                let (lines, files): (Vec<u32>, Vec<String>) = tags.into_iter().unzip();
                (directives, lines, files)
            } else {
                (directives, directive_lines, directive_files)
            };
            let entries = directives
                .iter()
                .enumerate()
                .map(|(i, d)| {
                    let line = directive_lines.get(i).copied().unwrap_or(0);
                    let file = directive_files.get(i).map_or("<unknown>", String::as_str);
                    directive_from_core(d, line, file)
                })
                .collect();
            out::LoadResult {
                entries,
                errors: errors.into_iter().map(error).collect(),
                options: options(opts),
                plugins: plugin_dtos
                    .into_iter()
                    .map(|p| wit::Plugin {
                        name: p.name,
                        config: p.config,
                    })
                    .collect(),
                // File load reports the resolved file set (no per-include line),
                // carried in `includes` with lineno 0.
                includes: loaded_files
                    .into_iter()
                    .map(|p| wit::SourceInclude { path: p, lineno: 0 })
                    .collect(),
            }
        }
        Err(e) => out::LoadResult {
            entries: vec![],
            errors: vec![simple_error(e)],
            options: options(ffi::LedgerOptions::default()),
            plugins: vec![],
            includes: vec![],
        },
    }
}

// validate/query/batch over a file match the JSON-RPC handlers: read the file
// and run the single-source path (these do not resolve includes).

/// Validate the ledger at `path`. Reads the file and runs the single-source
/// [`validate`] path (no include resolution); a read failure becomes an
/// invalid result carrying the I/O error.
pub fn validate_file(path: &str) -> out::ValidateResult {
    match read_file(path) {
        Ok(src) => validate(&src),
        Err(e) => out::ValidateResult {
            valid: false,
            errors: vec![simple_error(e)],
            parse_error_count: 0,
            validate_error_count: 0,
        },
    }
}

/// Run a single BQL query against the ledger at `path`. Reads the file and
/// runs the single-source [`query`] path (no include resolution); a read
/// failure becomes an errored result carrying the I/O error.
pub fn query_file(path: &str, query_str: &str) -> out::QueryResult {
    match read_file(path) {
        Ok(src) => query(&src, query_str),
        Err(e) => out::QueryResult {
            columns: vec![],
            rows: vec![],
            errors: vec![simple_error(e)],
        },
    }
}

/// Run several BQL queries against the ledger at `path`, loading it once.
/// Reads the file and runs the single-source [`batch`] path (no include
/// resolution); a read failure becomes an errored result carrying the I/O
/// error.
pub fn batch_file(path: &str, queries: &[String]) -> out::BatchResult {
    match read_file(path) {
        Ok(src) => batch(&src, queries),
        Err(e) => out::BatchResult {
            load: out::LoadResult {
                entries: vec![],
                errors: vec![simple_error(e)],
                options: options(ffi::LedgerOptions::default()),
                plugins: vec![],
                includes: vec![],
            },
            queries: vec![],
        },
    }
}

// ---- builder: WIT input -> core directive (reverse of the output path) ----

fn json_from_meta_value(v: &wit::MetaValue) -> Json {
    match v {
        wit::MetaValue::Text(s) => Json::String(s.clone()),
        // A numeric string round-trips to MetaValue::Number via json_to_meta_value.
        wit::MetaValue::Number(s) => {
            serde_json::from_str(s).unwrap_or_else(|_| Json::String(s.clone()))
        }
        wit::MetaValue::Boolean(b) => Json::Bool(*b),
        wit::MetaValue::Amount(a) => {
            serde_json::json!({"number": a.number, "currency": a.currency})
        }
        wit::MetaValue::Null => Json::Null,
    }
}

fn input_meta(entries: &[(String, wit::MetaValue)]) -> std::collections::HashMap<String, Json> {
    entries
        .iter()
        .map(|(k, v)| (k.clone(), json_from_meta_value(v)))
        .collect()
}

fn input_amount(a: &wit::Amount) -> ffi::InputAmount {
    ffi::InputAmount {
        number: a.number.clone(),
        currency: a.currency.clone(),
    }
}

fn input_cost_number(n: &wit::CostNumber) -> ffi::InputCostNumber {
    match n {
        wit::CostNumber::PerUnit(v) => ffi::InputCostNumber::PerUnit { value: v.clone() },
        wit::CostNumber::Total(v) => ffi::InputCostNumber::Total { value: v.clone() },
        wit::CostNumber::PerUnitFromTotal((per_unit, total)) => {
            ffi::InputCostNumber::PerUnitFromTotal {
                per_unit: per_unit.clone(),
                total: total.clone(),
            }
        }
        wit::CostNumber::Compound((per_unit, total)) => ffi::InputCostNumber::Compound {
            per_unit: per_unit.clone(),
            total: total.clone(),
        },
    }
}

fn input_cost(c: &wit::InputCost) -> ffi::InputCost {
    ffi::InputCost {
        number: c.number.as_ref().map(input_cost_number),
        currency: c.currency.clone(),
        date: c.date.clone(),
        label: c.label.clone(),
        merge: c.merge,
    }
}

fn input_posting(p: &wit::InputPosting) -> ffi::InputPosting {
    ffi::InputPosting {
        account: p.account.clone(),
        units: p.units.as_ref().map(input_amount),
        cost: p.cost.as_ref().map(input_cost),
        price: p.price.as_ref().map(input_amount),
        meta: input_meta(&p.meta),
    }
}

fn input_entry(d: &wit::InputDirective) -> ffi::InputEntry {
    use ffi::InputEntry as E;
    use wit::InputDirective as I;
    match d {
        I::Transaction(t) => E::Transaction {
            date: t.date.clone(),
            flag: t.flag.clone(),
            payee: t.payee.clone(),
            narration: t.narration.clone(),
            tags: t.tags.clone(),
            links: t.links.clone(),
            postings: t.postings.iter().map(input_posting).collect(),
            meta: input_meta(&t.meta),
        },
        I::Open(o) => E::Open {
            date: o.date.clone(),
            account: o.account.clone(),
            currencies: o.currencies.clone(),
            booking: o.booking.clone(),
            meta: input_meta(&o.meta),
        },
        I::Close(c) => E::Close {
            date: c.date.clone(),
            account: c.account.clone(),
            meta: input_meta(&c.meta),
        },
        I::Balance(b) => E::Balance {
            date: b.date.clone(),
            account: b.account.clone(),
            amount: input_amount(&b.amount),
            meta: input_meta(&b.meta),
        },
        I::Pad(p) => E::Pad {
            date: p.date.clone(),
            account: p.account.clone(),
            source_account: p.source_account.clone(),
            meta: input_meta(&p.meta),
        },
        I::Commodity(c) => E::Commodity {
            date: c.date.clone(),
            currency: c.currency.clone(),
            meta: input_meta(&c.meta),
        },
        I::Price(p) => E::Price {
            date: p.date.clone(),
            currency: p.currency.clone(),
            amount: input_amount(&p.amount),
            meta: input_meta(&p.meta),
        },
        I::Event(e) => E::Event {
            date: e.date.clone(),
            event_type: e.event_type.clone(),
            value: e.value.clone(),
            meta: input_meta(&e.meta),
        },
        I::Note(n) => E::Note {
            date: n.date.clone(),
            account: n.account.clone(),
            comment: n.comment.clone(),
            meta: input_meta(&n.meta),
        },
        I::Document(doc) => E::Document {
            date: doc.date.clone(),
            account: doc.account.clone(),
            path: doc.path.clone(),
            tags: doc.tags.clone(),
            links: doc.links.clone(),
            meta: input_meta(&doc.meta),
        },
        I::Query(q) => E::Query {
            date: q.date.clone(),
            name: q.name.clone(),
            query_string: q.query_string.clone(),
            meta: input_meta(&q.meta),
        },
        I::Custom(c) => E::Custom {
            date: c.date.clone(),
            custom_type: c.custom_type.clone(),
            values: c.values.iter().map(json_from_meta_value).collect(),
            meta: input_meta(&c.meta),
        },
    }
}

/// `entry.create` — build one directive from typed input.
pub fn create(entry: &wit::InputDirective) -> Result<wit::Directive, String> {
    let core = ffi::input_entry_to_directive(&input_entry(entry))?;
    Ok(directive_from_core(&core, 0, "<created>"))
}

/// `entry.createBatch` — all-or-nothing (first failure fails the call).
pub fn create_batch(entries: &[wit::InputDirective]) -> Result<Vec<wit::Directive>, String> {
    entries.iter().map(create).collect()
}

fn directive_date(d: &wit::Directive) -> &str {
    use wit::Directive as D;
    match d {
        D::Transaction(t) => &t.date,
        D::Open(o) => &o.date,
        D::Close(c) => &c.date,
        D::Balance(b) => &b.date,
        D::Pad(p) => &p.date,
        D::Commodity(c) => &c.date,
        D::Price(p) => &p.date,
        D::Event(e) => &e.date,
        D::Note(n) => &n.date,
        D::Document(doc) => &doc.date,
        D::Query(q) => &q.date,
        D::Custom(c) => &c.date,
    }
}

/// `entry.filter` — filter directives by date range, matching the JSON-RPC
/// `filter_entries`: `commodity` is always dropped, `open` is kept while still
/// active (`date < end`), `close` is kept from `begin` on (`date >= begin`),
/// and everything else is kept within `[begin, end)`. Entries with an absent or
/// unparsable date are dropped. Unparsable bounds return the input unchanged
/// (the WIT signature has no error channel).
pub fn filter(entries: Vec<wit::Directive>, begin: &str, end: &str) -> Vec<wit::Directive> {
    let (Ok(begin), Ok(end)) = (
        begin.parse::<rustledger_core::NaiveDate>(),
        end.parse::<rustledger_core::NaiveDate>(),
    ) else {
        return entries;
    };
    entries
        .into_iter()
        .filter(|d| {
            let Ok(date) = directive_date(d).parse::<rustledger_core::NaiveDate>() else {
                return false;
            };
            match d {
                wit::Directive::Commodity(_) => false,
                wit::Directive::Open(_) => date < end,
                wit::Directive::Close(_) => date >= begin,
                _ => date >= begin && date < end,
            }
        })
        .collect()
}

// ---- util ----

use crate::exports::rustledger::ledger::util as out_util;

/// `util.types` — static type metadata about this build.
pub fn types_info() -> out_util::TypesInfo {
    let strs = |xs: &[&str]| xs.iter().map(|s| (*s).to_string()).collect();
    out_util::TypesInfo {
        all_directives: strs(&[
            "transaction",
            "balance",
            "open",
            "close",
            "commodity",
            "pad",
            "event",
            "note",
            "document",
            "price",
            "query",
            "custom",
        ]),
        booking_methods: strs(&[
            "STRICT",
            "STRICT_WITH_SIZE",
            "NONE",
            "AVERAGE",
            "FIFO",
            "LIFO",
            "HIFO",
        ]),
        missing: out_util::MissingSentinel {
            description: "Represents a missing/interpolated amount in a posting".to_string(),
            json_representation: "null or {currency_only: string}".to_string(),
        },
        account_types: strs(&ffi::helpers::ACCOUNT_TYPES),
    }
}

/// `util.isEncrypted` — true for `.gpg` / `.asc` files (by extension).
#[must_use]
pub fn is_encrypted(path: &str) -> bool {
    std::path::Path::new(path)
        .extension()
        .is_some_and(|ext| ext.eq_ignore_ascii_case("gpg") || ext.eq_ignore_ascii_case("asc"))
}

/// `util.getAccountType` — the (lowercased) type root of an account name.
#[must_use]
pub fn get_account_type(account: &str) -> String {
    ffi::helpers::account_type(account).to_string()
}

// ---- format ----

/// `format.source` — canonically reformat beancount source (best-effort; parse
/// errors don't abort, since the WIT signature has no error channel).
#[must_use]
pub fn format_source(source: &str) -> String {
    let parsed = rustledger_parser::parse(source);
    rustledger_parser::format::format_source_with_parsed(&parsed, source)
}

/// `format.file` — reformat the file at `path`. On read error the message is
/// returned as the body (the WIT signature has no error channel).
#[must_use]
pub fn format_file(path: &str) -> String {
    match read_file(path) {
        Ok(src) => format_source(&src),
        Err(e) => e,
    }
}

fn format_directives(dirs: &[rustledger_core::Directive]) -> Result<String, String> {
    let config = rustledger_core::format::FormatConfig::default();
    rustledger_parser::format::canonicalize_directives(dirs.iter(), &config)
        .map_err(|e| e.to_string())
}

/// `format.entry` — render one constructed directive to canonical text.
pub fn format_entry(entry: &wit::InputDirective) -> Result<String, String> {
    let dir = ffi::input_entry_to_directive(&input_entry(entry))?;
    format_directives(std::slice::from_ref(&dir))
}

/// `format.entries` — render constructed directives to canonical text.
pub fn format_entries(entries: &[wit::InputDirective]) -> Result<String, String> {
    let mut dirs = Vec::with_capacity(entries.len());
    for e in entries {
        dirs.push(ffi::input_entry_to_directive(&input_entry(e))?);
    }
    format_directives(&dirs)
}

/// Render LOADED directives to canonical beancount text (3.6.0). The
/// loaded->input down-conversion is the same one `session.from-entries` and
/// `builder.query-entries` use, so an entry that round-trips there renders
/// here.
pub fn format_loaded(entries: &[wit::Directive]) -> Result<String, String> {
    let mut dirs = Vec::with_capacity(entries.len());
    for e in entries {
        dirs.push(ffi::input_entry_to_directive(&loaded_directive_to_input(
            e,
        ))?);
    }
    format_directives(&dirs)
}

// ---- builder: clamp (WIT loaded directives -> core -> ops::clamp -> WIT) ----

fn loaded_meta(m: &wit::Meta) -> std::collections::HashMap<String, Json> {
    // Drop source location (filename/lineno/hash); keep user key/values. The
    // user pairs have the same shape as an input entry's meta.
    input_meta(&m.user)
}

fn loaded_cost_to_input(c: &wit::Cost) -> ffi::InputCost {
    ffi::InputCost {
        number: c.number.as_ref().map(input_cost_number),
        currency: c.currency.clone(),
        date: c.date.clone(),
        label: c.label.clone(),
        merge: false,
    }
}

fn loaded_posting_to_input(p: &wit::Posting) -> ffi::InputPosting {
    ffi::InputPosting {
        account: p.account.clone(),
        units: p.units.as_ref().map(input_amount),
        cost: p.cost.as_ref().map(loaded_cost_to_input),
        price: p.price.as_ref().map(input_amount),
        meta: input_meta(&p.meta),
    }
}

/// A loaded WIT `directive` -> `InputEntry`, so it can be reconstructed into a
/// core `Directive` via `input_entry_to_directive` (dropping the source-location
/// metadata, which is re-derived on output).
fn loaded_directive_to_input(d: &wit::Directive) -> ffi::InputEntry {
    use ffi::InputEntry as E;
    use wit::Directive as D;
    match d {
        D::Transaction(t) => E::Transaction {
            date: t.date.clone(),
            flag: t.flag.clone(),
            payee: t.payee.clone(),
            narration: t.narration.clone(),
            tags: t.tags.clone(),
            links: t.links.clone(),
            postings: t.postings.iter().map(loaded_posting_to_input).collect(),
            meta: loaded_meta(&t.meta),
        },
        D::Open(o) => E::Open {
            date: o.date.clone(),
            account: o.account.clone(),
            currencies: o.currencies.clone(),
            booking: o.booking.clone(),
            meta: loaded_meta(&o.meta),
        },
        D::Close(c) => E::Close {
            date: c.date.clone(),
            account: c.account.clone(),
            meta: loaded_meta(&c.meta),
        },
        D::Balance(b) => E::Balance {
            date: b.date.clone(),
            account: b.account.clone(),
            amount: input_amount(&b.amount),
            meta: loaded_meta(&b.meta),
        },
        D::Pad(p) => E::Pad {
            date: p.date.clone(),
            account: p.account.clone(),
            source_account: p.source_account.clone(),
            meta: loaded_meta(&p.meta),
        },
        D::Commodity(c) => E::Commodity {
            date: c.date.clone(),
            currency: c.currency.clone(),
            meta: loaded_meta(&c.meta),
        },
        D::Price(p) => E::Price {
            date: p.date.clone(),
            currency: p.currency.clone(),
            amount: input_amount(&p.amount),
            meta: loaded_meta(&p.meta),
        },
        D::Event(e) => E::Event {
            date: e.date.clone(),
            event_type: e.event_type.clone(),
            value: e.value.clone(),
            meta: loaded_meta(&e.meta),
        },
        D::Note(n) => E::Note {
            date: n.date.clone(),
            account: n.account.clone(),
            comment: n.comment.clone(),
            meta: loaded_meta(&n.meta),
        },
        D::Document(doc) => E::Document {
            date: doc.date.clone(),
            account: doc.account.clone(),
            path: doc.path.clone(),
            tags: doc.tags.clone(),
            links: doc.links.clone(),
            meta: loaded_meta(&doc.meta),
        },
        D::Query(q) => E::Query {
            date: q.date.clone(),
            name: q.name.clone(),
            query_string: q.query_string.clone(),
            meta: loaded_meta(&q.meta),
        },
        D::Custom(c) => E::Custom {
            date: c.date.clone(),
            custom_type: c.custom_type.clone(),
            // `values` are now `typed-value`; the input DTO re-derives the type
            // from the value, so unwrap to the inner `meta-value`.
            values: c
                .values
                .iter()
                .map(|tv| json_from_meta_value(&tv.value))
                .collect(),
            meta: loaded_meta(&c.meta),
        },
    }
}

/// `entry.clamp` — clamp loaded directives to `[begin, end)` via the typed
/// [`rustledger_ops::clamp::clamp_indexed`].
///
/// In-window entries and carried-forward prices are handed back as their
/// **original** WIT directive (full fidelity + provenance) via the source index;
/// only the synthesized opening-balance / earnings summaries are built fresh
/// (with the `<clamped>` sentinel). This matches `SessionState::clamp` so the
/// stateless and session clamp paths produce the same result — the divergence
/// that the JSON `clamp_entries` workaround left open (#1425).
pub fn clamp(entries: Vec<wit::Directive>, begin: &str, end: &str) -> Vec<wit::Directive> {
    let (Ok(begin_date), Ok(end_date)) = (
        begin.parse::<rustledger_core::NaiveDate>(),
        end.parse::<rustledger_core::NaiveDate>(),
    ) else {
        // Unparsable bounds: return the input unchanged (no error channel).
        return entries;
    };

    // Convert inputs to core directives, remembering each one's position in
    // `entries` so a `clamp_indexed` source index can map an output back to the
    // exact original WIT directive. These are already-loaded WIT directives, so
    // conversion normally succeeds — with one known exception since the
    // account-name ingress gate: a held directive whose account is not a
    // lexable account name (possible via plugin-synthesized or
    // embedder-constructed directives; parser-produced accounts always
    // re-lex) now FAILS conversion and is dropped from the result. This
    // surface returns `Vec<wit::Directive>` with no error channel (matching
    // the unparsable-bounds early return above), so the drop is silent —
    // acceptable because such a directive could never round-trip through
    // text anyway; if that trade stops being acceptable, add a warnings
    // channel to the WIT signature. `orig_index` keeps the surviving cores
    // aligned to their WIT source.
    let mut core: Vec<rustledger_core::Directive> = Vec::with_capacity(entries.len());
    let mut orig_index: Vec<usize> = Vec::with_capacity(entries.len());
    for (i, d) in entries.iter().enumerate() {
        if let Ok(c) = ffi::input_entry_to_directive(&loaded_directive_to_input(d)) {
            core.push(c);
            orig_index.push(i);
        }
    }

    // A bare directive list carries no ledger options, so classification and
    // the synthesized-summary account names fall back to beancount defaults
    // (#1806). The session's `clamp` uses the held options instead.
    // On overflow the opening-balance summary cannot be computed. The WIT
    // signature has no error channel (`rustledger:ledger@3.0.0` returns a bare
    // list), so we hand back the input UNCLAMPED rather than emit a summary
    // built from a clamped total — the caller then sees real directives, never
    // a fabricated opening balance (#1863). Surfacing this as a typed error
    // needs a WIT contract change; tracked as follow-up.
    let Ok(clamped) = rustledger_ops::clamp::clamp_indexed(
        &core,
        begin_date,
        end_date,
        &rustledger_ops::clamp::ClampAccounts::default(),
    ) else {
        return entries;
    };
    clamped
        .into_iter()
        .map(|(d, src)| match src.and_then(|j| orig_index.get(j)) {
            // Pass-through: hand back the original WIT directive untouched.
            Some(&i) => entries[i].clone(),
            // Synthesized summary: build from core with the `<clamped>` source.
            None => directive_from_core(&d, 0, "<clamped>"),
        })
        .collect()
}

/// Run a BQL query against an already-loaded directive set (#1423).
/// The typed counterpart to `filter`/`clamp`: converts the WIT directives to
/// core, expands pads (as the source-based query does), then runs the query —
/// so the embedder queries the directives it holds with no re-parse/re-render.
///
/// Like `clamp`, a held directive that fails conversion is silently dropped
/// (`filter_map(..ok())`) — since the account-name ingress gate this includes
/// directives with un-lexable account names; see the note in [`clamp`].
pub fn query_entries(entries: &[wit::Directive], query_str: &str) -> out::QueryResult {
    let core: Vec<rustledger_core::Directive> = entries
        .iter()
        .filter_map(|d| ffi::input_entry_to_directive(&loaded_directive_to_input(d)).ok())
        .collect();
    let directives = rustledger_booking::merge_with_padding(&core);
    // The `query-entries` WIT contract carries no ledger options, so the
    // classifier defaults to the standard five roots. Renamed-root ledgers
    // queried via host-provided entries won't POSSIGN-flip custom names —
    // `session.from-entries-with-options` (3.7.0, #1766) is the
    // options-carrying path; this free function is doc-soft-deprecated
    // in its favor.
    run_query(
        &directives,
        query_str,
        rustledger_core::AccountTypes::default(),
    )
}

// ---- stateful ledger handle (`resource session`, #1421) -------------------
//
// Normalizes the source and file load paths into one held state so the
// `query`/`filter`/`clamp` methods don't care which produced it. The win over
// the free functions: these run against the held *core* directives, so they
// never re-parse source nor round-trip a directive list through the host.

/// Replace empty `name-*` roots in host-supplied options with their
/// defaults: an empty root can never classify an account, so a
/// zero-initialized record from a guest language would silently break
/// every `POSSIGN`/`ACCOUNT_SORTKEY` result with no diagnostic (deep
/// review of #1805). Non-empty values pass through verbatim — including
/// duplicates, which are the host's to avoid.
fn sanitize_options(mut provided: wit::LedgerOptions) -> wit::LedgerOptions {
    let defaults = options(ffi::LedgerOptions::default());
    let fix = |field: &mut String, default: String| {
        if field.is_empty() {
            *field = default;
        }
    };
    fix(&mut provided.name_assets, defaults.name_assets);
    fix(&mut provided.name_liabilities, defaults.name_liabilities);
    fix(&mut provided.name_equity, defaults.name_equity);
    fix(&mut provided.name_income, defaults.name_income);
    fix(&mut provided.name_expenses, defaults.name_expenses);
    provided
}

/// Held state behind a `session` resource: the booked core directives + their
/// per-directive provenance, plus the load metadata, normalized across the
/// source and file load paths. Errors are pre-converted to WIT form (the file
/// path's failure case has only a message, not a rich `ffi::Error`).
pub struct SessionState {
    directives: Vec<rustledger_core::Directive>,
    lines: Vec<u32>,
    files: Vec<String>,
    errors: Vec<wit::Error>,
    options: wit::LedgerOptions,
    plugins: Vec<ffi::Plugin>,
    includes: Vec<(String, u32)>,
    /// Pad-expanded directives for querying, computed once on first `query`.
    padded: std::cell::OnceCell<Vec<rustledger_core::Directive>>,
}

impl SessionState {
    /// Parse + book from source text (single synthetic `<stdin>` filename).
    pub fn from_source(source: &str) -> Self {
        let loaded = ffi::helpers::load_source(source);
        let files = vec!["<stdin>".to_string(); loaded.directives.len()];
        Self {
            directives: loaded.directives,
            lines: loaded.directive_lines,
            files,
            errors: loaded.errors.into_iter().map(error).collect(),
            options: options(loaded.options),
            plugins: loaded.plugins,
            includes: loaded
                .includes
                .into_iter()
                .map(|i| (i.path, i.lineno))
                .collect(),
            padded: std::cell::OnceCell::new(),
        }
    }

    /// Hold an already-loaded directive set (WIT 3.4.0, `from-entries`).
    /// The typed counterpart to `builder.query-entries`'s conversion step:
    /// wire directives convert to core ONCE here, and every subsequent
    /// method call runs against the held core list with no re-marshaling.
    /// Conversion failures (e.g. un-lexable accounts, see the note on
    /// `clamp`) drop the directive, mirroring `query-entries`.
    pub fn from_entries(entries: &[wit::Directive]) -> Self {
        // Held entries carry no ledger options (they were stripped at
        // the original load); defaults here match what a stand-alone
        // directive set implies. Embedders holding the original load's
        // options should use `from_entries_with_options` (#1766).
        Self::from_entries_with_options(entries, options(ffi::LedgerOptions::default()))
    }

    /// `from_entries` with the ledger's options attached (WIT 3.7.0,
    /// #1766). What the held options DO today: `query` builds its
    /// account classifier from the `name-*` roots (BQL
    /// `POSSIGN`/`ACCOUNT_SORTKEY` on renamed-root ledgers),
    /// `info()` echoes the full record, and `format` (3.8.0) renders
    /// with the held `display_precision`. Booked-time options
    /// (booking-method, tolerances) cannot re-apply — the entries are
    /// already booked — and clamp does not consume options yet (its
    /// hardcoded summary accounts are #1806).
    ///
    /// Empty `name-*` fields are replaced with their defaults (an
    /// empty root can never classify — a zero-initialized record from
    /// a guest language would silently break every classification);
    /// duplicated roots are the host's to avoid: classification
    /// matches roots exactly, first match wins.
    pub fn from_entries_with_options(
        entries: &[wit::Directive],
        options: wit::LedgerOptions,
    ) -> Self {
        let options = sanitize_options(options);
        // The one-time conversion is this API's whole reason to exist —
        // reserve up front so a large ledger doesn't reallocate through
        // the collect (review catch; drops are rare, over-reserving by
        // the dropped count is fine).
        let mut directives: Vec<rustledger_core::Directive> = Vec::with_capacity(entries.len());
        directives.extend(
            entries
                .iter()
                .filter_map(|d| ffi::input_entry_to_directive(&loaded_directive_to_input(d)).ok()),
        );
        let n = directives.len();
        Self {
            directives,
            lines: vec![0; n],
            files: vec!["<entries>".to_string(); n],
            errors: vec![],
            options,
            plugins: vec![],
            includes: vec![],
            padded: std::cell::OnceCell::new(),
        }
    }

    /// Parse + book from a file path. Mirrors the free `load_file`'s handling
    /// (path-security flag inversion, requested-plugin pass, per-directive
    /// file provenance); a load failure becomes an empty ledger whose single
    /// error carries the message.
    pub fn from_file(path: &str, allow_unrestricted_includes: bool, plugins: &[String]) -> Self {
        let path_security = !allow_unrestricted_includes;
        match ffi::helpers::load_file(std::path::Path::new(path), path_security) {
            Ok(fl) => {
                let mut errors = fl.errors;
                let opts = fl.options;
                let plugin_dtos = fl.plugins;
                let loaded_files = fl.loaded_files;
                let plugin_names: Vec<&str> = plugins.iter().map(String::as_str).collect();
                let (directives, lines, files) = ffi::helpers::apply_plugins(
                    &plugin_names,
                    fl.directives,
                    fl.directive_lines,
                    fl.directive_files,
                    &mut errors,
                    &opts,
                );
                Self {
                    directives,
                    lines,
                    files,
                    errors: errors.into_iter().map(error).collect(),
                    options: options(opts),
                    plugins: plugin_dtos,
                    includes: loaded_files.into_iter().map(|p| (p, 0)).collect(),
                    padded: std::cell::OnceCell::new(),
                }
            }
            Err(e) => Self {
                directives: vec![],
                lines: vec![],
                files: vec![],
                errors: vec![simple_error(e)],
                options: options(ffi::LedgerOptions::default()),
                plugins: vec![],
                includes: vec![],
                padded: std::cell::OnceCell::new(),
            },
        }
    }

    /// The held directives as WIT, carrying their real line/file provenance.
    fn entries(&self) -> Vec<wit::Directive> {
        self.directives
            .iter()
            .enumerate()
            .map(|(i, d)| {
                let line = self.lines.get(i).copied().unwrap_or(0);
                let file = self.files.get(i).map_or("<unknown>", String::as_str);
                directive_from_core(d, line, file)
            })
            .collect()
    }

    /// The load result the host materializes once (entries/errors/options/...).
    pub fn info(&self) -> out::LoadResult {
        out::LoadResult {
            entries: self.entries(),
            errors: self.errors.clone(),
            options: self.options.clone(),
            plugins: self
                .plugins
                .iter()
                .map(|p| wit::Plugin {
                    name: p.name.clone(),
                    config: p.config.clone(),
                })
                .collect(),
            includes: self
                .includes
                .iter()
                .map(|(path, lineno)| wit::SourceInclude {
                    path: path.clone(),
                    lineno: *lineno,
                })
                .collect(),
        }
    }

    /// Run a BQL query against the held ledger (no re-parse).
    pub fn query(&self, query_str: &str) -> out::QueryResult {
        if !self.errors.is_empty() {
            return out::QueryResult {
                columns: vec![],
                rows: vec![],
                errors: self.errors.clone(),
            };
        }
        let directives = self
            .padded
            .get_or_init(|| rustledger_booking::merge_with_padding(&self.directives));
        run_query(directives, query_str, self.account_types())
    }

    /// The held options' account-root classifier — the single place the
    /// session turns its `name-*` roots into an [`AccountTypes`], shared by
    /// `query` (BQL classification), `clamp` (summary classification) and
    /// `budget` (income-vs-expense sign normalization and total bucketing).
    fn account_types(&self) -> rustledger_core::AccountTypes {
        rustledger_core::AccountTypes {
            assets: self.options.name_assets.clone(),
            liabilities: self.options.name_liabilities.clone(),
            equity: self.options.name_equity.clone(),
            income: self.options.name_income.clone(),
            expenses: self.options.name_expenses.clone(),
        }
    }

    /// The held options' clamp configuration (#1806): the account-root
    /// classifier plus the `account_previous_balances` / `_earnings`
    /// summary account names. So `session.clamp` synthesizes opening
    /// balances into the ledger's OWN accounts, where the options-less
    /// builder free `clamp` falls back to beancount defaults.
    fn clamp_accounts(&self) -> rustledger_ops::clamp::ClampAccounts {
        rustledger_ops::clamp::ClampAccounts {
            types: self.account_types(),
            previous_balances: self.options.account_previous_balances.clone(),
            previous_earnings: self.options.account_previous_earnings.clone(),
        }
    }

    /// Keep only directives within `[begin, end)`. Reuses the free `filter`'s
    /// date predicate over the held directives (filter is lossless).
    pub fn filter(&self, begin: &str, end: &str) -> Vec<wit::Directive> {
        filter(self.entries(), begin, end)
    }

    /// Clamp to `[begin, end)`, running `rustledger_ops::clamp` **directly on
    /// the held core directives** — no WIT -> core -> WIT round-trip, the value
    /// the resource exists to deliver (#1421).
    /// Flag duplicate candidates against the HELD directives using the
    /// batch canonical (`rustledger_ops::dedup::find_fuzzy_duplicates`),
    /// which precomputes each held transaction's comparison key once —
    /// per-candidate matching would rebuild every key for every candidate.
    /// Same matcher as `rledger extract --existing`: same date, same
    /// first-posting amount, similar payee/narration text. One bool per
    /// candidate, in input order; a candidate that fails conversion (or
    /// isn't a transaction) is never flagged, mirroring the documented
    /// `from-entries` drop policy for the held side.
    pub fn dedup(&self, candidates: &[wit::Directive]) -> Vec<bool> {
        // Convert per-candidate so one unconvertible candidate can't shift
        // flags out of alignment with the input order. `None` marks it.
        let cores: Vec<Option<rustledger_core::Directive>> = candidates
            .iter()
            .map(|d| ffi::input_entry_to_directive(&loaded_directive_to_input(d)).ok())
            .collect();
        let convertible: Vec<rustledger_core::Directive> =
            cores.iter().flatten().cloned().collect();
        let matches = rustledger_ops::dedup::find_fuzzy_duplicates(
            &convertible,
            &self.directives,
            &rustledger_ops::dedup::FuzzyDedupConfig::default(),
        );
        let dup_in_convertible: std::collections::HashSet<usize> =
            matches.iter().map(|m| m.new_index).collect();
        // Map convertible-space indices back to candidate-space.
        let mut flags = vec![false; candidates.len()];
        let mut j = 0;
        for (i, core) in cores.iter().enumerate() {
            if core.is_some() {
                flags[i] = dup_in_convertible.contains(&j);
                j += 1;
            }
        }
        flags
    }

    /// Render the held directives to canonical text honoring the ledger's
    /// display precision (WIT 3.8.0, #1766) — the options-aware rendering
    /// `format.format-loaded` can't do (a bare directive list carries no
    /// options). Builds the `DisplayContext` with the canonical
    /// [`rustledger_core::DisplayContext::from_directives`] (the exact
    /// builder the CLI's loader uses: amount-scan inference, then the held
    /// options' `display_precision` overrides, then per-commodity
    /// `precision:` metadata) and renders through the same
    /// `canonicalize_directives` path as the free `format` interface —
    /// only the config differs. `render_commas` IS honored here: this path
    /// holds the ledger's options, and a grouped numeral is something every
    /// conforming reader must accept (the grammar admits it), so the parser —
    /// not the file — is the machine boundary. `rledger format` groups only
    /// when given `--ledger <root>`, which is how it brings a ledger's options
    /// into scope; bare `rledger format <file>` has none and emits ungrouped
    /// text.
    pub fn format(&self) -> Result<String, String> {
        // The session holds the ledger's options, so this path can honor
        // `render_commas` on disk — the boundary a machine consumer crosses is
        // the PARSER, and the grammar admits grouped numerals. (Contrast the
        // csv/json surfaces, whose consumers have no grammar; those stay
        // separator-free unconditionally.) `rledger format` still passes
        // `false` because it is a per-file text transform with no options in
        // scope; giving it a context is a separate decision about whether
        // `format` becomes a ledger operation.
        let ctx = rustledger_core::DisplayContext::from_directives(
            self.directives.iter(),
            self.options
                .display_precision
                .iter()
                .map(|(c, p)| (c.as_str(), *p)),
            self.options.render_commas,
        );
        let config = rustledger_core::format::FormatConfig {
            number_display: Some(ctx),
            ..Default::default()
        };
        rustledger_parser::format::canonicalize_directives(self.directives.iter(), &config)
            .map_err(|e| e.to_string())
    }

    /// The account-type root for `account`, honoring this ledger's
    /// `name_assets` … `name_expenses` renames (WIT 3.11.0, #1964).
    ///
    /// The free `util.get-account-type` classifies with hardcoded English
    /// roots, so on a ledger that renames Expenses it answers "unknown" while
    /// `report balsheet` — which classifies through
    /// [`rustledger_core::AccountTypes`], the canonical CLAUDE.md names —
    /// gets it right. Same ledger, different answers depending on the surface
    /// asked. That utility cannot fix it: its interface holds no ledger. A
    /// session does, so this one goes through the canonical.
    ///
    /// Returns the canonical lowercase kind — `assets`, `liabilities`,
    /// `equity`, `income`, `expenses`, or `unknown` — exactly the vocabulary
    /// `util.get-account-type` already returns, so a caller can swap one for
    /// the other without re-reading the strings. `AccountTypes::root_name` is
    /// the inverse when the ledger's own display name is wanted.
    pub fn account_type(&self, account: &str) -> String {
        let types = rustledger_core::AccountTypes {
            assets: self.options.name_assets.clone(),
            liabilities: self.options.name_liabilities.clone(),
            equity: self.options.name_equity.clone(),
            income: self.options.name_income.clone(),
            expenses: self.options.name_expenses.clone(),
        };
        types
            .kind(account)
            .map_or_else(|| "unknown".to_string(), |k| k.as_str().to_string())
    }

    /// Investment returns over the held ledger (WIT 3.9.0, #1847): the
    /// `rledger report returns` engine over the boundary, so a host charts
    /// returns without re-deriving the cash-flow extraction or the XIRR/TWR
    /// math. Delegates to [`rustledger_query::scope_returns`] — the *same*
    /// composition the CLI's `report returns` calls — over the same interpolated,
    /// pad-expanded stream `query` builds (reused via the `padded` cell; booking is
    /// not required — net units are valued at market), so the two surfaces cannot
    /// compute different figures for one ledger.
    ///
    /// A parse-recovered load error does not block it — it computes over the held
    /// directives just as the CLI's `report returns` renders over them (errors
    /// surface separately, here via `info().errors`). It values **net units at
    /// market**, so a cost-basis / lot error (an over-sell, an empty-cost `{}` sale
    /// with no matching lot — the common state of imported brokerage data) does NOT
    /// block the report: the units net (possibly negative) and value at market,
    /// like beancount + beangrow. `rledger check` remains the validator. The only
    /// genuinely-unvaluable inputs error (see below). The CLI and this op agree on
    /// every ledger.
    ///
    /// `investments`/`income` are the scope's account-name prefixes; `currency`
    /// is the single reporting currency (empty → the ledger's first
    /// `operating_currency`); `end` is the horizon + terminal-valuation date.
    ///
    /// # Errors
    /// `Err(message)` when `end` is empty/unparseable, no reporting currency
    /// resolves (empty `currency` and no `operating_currency`), a boundary or
    /// terminal flow cannot be priced, or an elided/uninterpolated posting leaves a
    /// scope-relevant quantity unknown — an in-scope holding, or an external
    /// boundary leg whose cash flow is unknown (the one shape net-units cannot
    /// value). A cost-basis/lot error is NOT an error here.
    pub fn returns(
        &self,
        investments: &[String],
        income: &[String],
        currency: &str,
        end: &str,
    ) -> Result<out::ReturnsResult, String> {
        let end_date: NaiveDate = end
            .parse()
            .map_err(|_| format!("invalid end-date {end:?} (expected YYYY-MM-DD)"))?;
        // Reporting currency: the caller's, else the ledger's first operating
        // currency, else an actionable error (returns are single-currency).
        let reporting_currency = if currency.is_empty() {
            self.options
                .operating_currency
                .first()
                .cloned()
                .ok_or_else(|| {
                    "no reporting currency: pass a currency or set `option \"operating_currency\"`"
                        .to_string()
                })?
        } else {
            currency.to_string()
        };
        let directives = self
            .padded
            .get_or_init(|| rustledger_booking::merge_with_padding(&self.directives));
        let scope = rustledger_returns::Scope::new(investments.to_vec(), income.to_vec());
        let returns =
            rustledger_query::scope_returns(directives, &scope, &reporting_currency, end_date)
                .map_err(|e| e.to_string())?;
        Ok(out::ReturnsResult {
            // usize -> u32: a cash-flow count is one per boundary-crossing
            // posting, so it cannot approach u32::MAX in any real ledger; the
            // saturating clamp is unreachable defensive code, not a lossy path.
            cash_flows: u32::try_from(returns.cash_flows).unwrap_or(u32::MAX),
            invested: returns.invested.to_string(),
            distributions: returns.distributions.to_string(),
            current_value: returns.current_value.to_string(),
            money_weighted: returns.money_weighted,
            time_weighted: returns.time_weighted,
        })
    }

    /// `session.budget` — budgeted vs actual over the held ledger (WIT 3.10.0).
    ///
    /// The engine is [`rustledger_budget`], the same crate the CLI report and
    /// `rledger check`'s E11001 use, so a host cannot get a different answer
    /// from the one `rledger report budget` prints on the same ledger. Nothing
    /// about supersession, calendar anchoring or the pro-rata accrual is
    /// re-derived here; this function only converts.
    ///
    /// Amounts are raw decimal strings, matching `returns` — the boundary does
    /// not display-format, because the host owns locale and precision.
    pub fn budget(
        &self,
        from: &str,
        to: &str,
        children: bool,
        account_filter: &str,
    ) -> Result<out::BudgetResult, String> {
        let parse = |s: &str, what: &str| -> Result<NaiveDate, String> {
            s.parse::<NaiveDate>()
                .map_err(|_| format!("invalid {what} {s:?} (expected YYYY-MM-DD)"))
        };
        let from_date = parse(from, "from-date")?;
        let to_date = parse(to, "to-date")?;
        if to_date <= from_date {
            return Err(format!(
                "empty window: to ({to}) must be after from ({from}); the window is \
                 half-open [from, to)"
            ));
        }
        // Padded, like every other balance-computing consumer: pad-synthesized
        // postings are spending as much as any other, and reading the
        // source-faithful stream made the CLI report disagree with `balances`
        // on the very same ledger.
        let directives = self
            .padded
            .get_or_init(|| rustledger_booking::merge_with_padding(&self.directives));
        let types = self.account_types();
        let budgets = rustledger_budget::Budgets::from_directives(directives);
        let filter = (!account_filter.is_empty()).then_some(account_filter);
        // Rows, totals AND warnings from one call. Assembling the warning list
        // here is what let this surface disagree with the CLI about which
        // budgets deserved a complaint, and in what order.
        let cmp = budgets.compare(directives, &types, from_date, to_date, children, filter);

        let amount = |v: Option<rust_decimal::Decimal>| v.map(|d| d.to_string());
        Ok(out::BudgetResult {
            rows: cmp
                .rows
                .iter()
                .map(|r| out::BudgetRow {
                    account: r.account.as_str().to_string(),
                    currency: r.currency.as_str().to_string(),
                    budgeted: amount(r.budgeted),
                    actual: amount(r.actual),
                    remaining: amount(r.remaining()),
                    used: r.used_fraction(),
                })
                .collect(),
            totals: cmp
                .totals
                .iter()
                .map(|t| out::BudgetTotal {
                    // The account TYPE, not the ledger's configured root name:
                    // a host switching on this must not have to know whether
                    // the ledger said `option "name_expenses"`.
                    //
                    // Through `AccountTypeKind::as_str`, the same table
                    // `util.get-account-type` answers from — `format!("{k:?}")`
                    // agreed by coincidence and would have changed the wire the
                    // day someone renamed a variant. A root outside the five is
                    // lowercased too, so two totals can never differ only in
                    // case.
                    // `kind` is a CLOSED vocabulary — the five types plus
                    // "other" — and `root` carries the ledger's own spelling.
                    // Lowercasing an unrecognized root into the same space as
                    // the five made two distinct totals collide on the only key
                    // this record offers.
                    kind: match &t.bucket {
                        rustledger_budget::Bucket::Typed(k) => k.as_str().to_string(),
                        rustledger_budget::Bucket::Other(_) => "other".to_string(),
                    },
                    root: match &t.bucket {
                        rustledger_budget::Bucket::Typed(k) => types.root_name(*k).to_string(),
                        rustledger_budget::Bucket::Other(root) => root.as_str().to_string(),
                    },
                    currency: t.currency.as_str().to_string(),
                    budgeted: amount(t.budgeted),
                    actual: amount(t.actual),
                    remaining: amount(t.remaining()),
                    used: t.used_fraction(),
                })
                .collect(),
            // Unreadable budget directives are reported, not fatal: one typo
            // must not cost the host every other budget in the ledger.
            // The same diagnosis the CLI prints, as a stable tag. A host with
            // rows and totals but no explanation for a blank panel is exactly
            // the ambiguity `Empty` exists to remove.
            empty: cmp.empty.map(|e| e.code().to_string()),
            errors: cmp
                .errors
                .into_iter()
                .map(|e| wit::Error {
                    message: format!("{}: {}", e.date, e.reason),
                    line: None,
                    column: None,
                    field: e.account.map(|a| a.as_str().to_string()),
                    entry_index: None,
                    severity: "warning".to_string(),
                    phase: "budget".to_string(),
                })
                .collect(),
        })
    }

    pub fn clamp(&self, begin: &str, end: &str) -> Vec<wit::Directive> {
        let (Ok(begin_date), Ok(end_date)) = (
            begin.parse::<rustledger_core::NaiveDate>(),
            end.parse::<rustledger_core::NaiveDate>(),
        ) else {
            return self.entries();
        };
        // Pass-through entries (in-window directives, carried-forward prices)
        // keep their original filename/lineno via the source index; only the
        // synthesized opening-balance / earnings summaries fall back to the
        // `<clamped>` sentinel. (#1425 — restores provenance that the old
        // `clamp` -> `directive_to_json(d, 0, "<clamped>")` mapping dropped.)
        // The held options drive classification + summary account names
        // (#1806), so a renamed-root ledger clamps into its own accounts.
        // See the note in the free-function `clamp` above: no WIT error
        // channel, so an out-of-range opening balance degrades to unclamped
        // output rather than a fabricated summary (#1863).
        let Ok(clamped) = rustledger_ops::clamp::clamp_indexed(
            &self.directives,
            begin_date,
            end_date,
            &self.clamp_accounts(),
        ) else {
            // Same fallback as an unparsable date above: hand back every
            // entry unclamped. Returning an empty list would silently drop the
            // whole ledger, which is worse than not clamping.
            return self.entries();
        };
        clamped
            .into_iter()
            .map(|(d, src)| {
                let (line, file) = src
                    .and_then(|i| self.lines.get(i).copied().zip(self.files.get(i)))
                    .map_or((0, "<clamped>"), |(line, file)| (line, file.as_str()));
                directive_from_core(&d, line, file)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    //! Field-level correctness of the direct core→WIT conversion
    //! (`directive_from_core`). The cross-binding parity crate
    //! (`rustledger-ffi-component-tests`) only checks entry *counts*; this pins
    //! the actual mapped fields for a comprehensive ledger, and in particular
    //! the metadata-fidelity fix: numeric metadata now surfaces as the typed
    //! `meta-value::number` (the old JSON-DTO path stringified it to
    //! `meta-value::text`).

    use super::{cost_number_from_core, directive_from_core, ffi, input_cost_number, wit};
    use rustledger_core::Directive;

    // Covers most directive types, a posting carrying BOTH cost and price, and
    // transaction metadata with a NUMERIC value (`num`) and a STRING value
    // (`note`) — the two whose typing the fix distinguishes.
    const LEDGER: &str = r#"
2024-01-01 open Assets:Stock
2024-01-01 open Assets:Cash
2024-01-01 commodity AAPL
  name: "Apple Inc"
2024-01-15 * "Broker" "Buy shares" #trip ^inv-1
  num: 42.50
  note: "hello"
  Assets:Stock  10 AAPL {150.00 USD} @ 155.00 USD
  Assets:Cash  -1500.00 USD
2024-02-01 balance Assets:Cash  -1500.00 USD
2024-03-01 price AAPL  160.00 USD
2024-03-04 document Assets:Cash "/docs/x.pdf" #dtag ^dlink
2024-03-05 query "recent" "SELECT date, account"
2024-03-06 custom "budget" "groceries" 500.00
2024-12-31 close Assets:Cash
"#;

    fn dir_meta(d: &wit::Directive) -> &wit::Meta {
        use wit::Directive as D;
        match d {
            D::Transaction(t) => &t.meta,
            D::Open(o) => &o.meta,
            D::Close(c) => &c.meta,
            D::Balance(b) => &b.meta,
            D::Pad(p) => &p.meta,
            D::Commodity(c) => &c.meta,
            D::Price(p) => &p.meta,
            D::Event(e) => &e.meta,
            D::Note(n) => &n.meta,
            D::Document(doc) => &doc.meta,
            D::Query(q) => &q.meta,
            D::Custom(c) => &c.meta,
        }
    }

    fn user_get<'a>(m: &'a wit::Meta, key: &str) -> &'a wit::MetaValue {
        m.user
            .iter()
            .find(|(k, _)| k == key)
            .map_or_else(|| panic!("missing meta key {key}"), |(_, v)| v)
    }

    fn load() -> (Vec<Directive>, Vec<u32>) {
        let loaded = ffi::helpers::load_source(LEDGER);
        let msgs: Vec<String> = loaded.errors.iter().map(|e| e.message.clone()).collect();
        assert!(loaded.errors.is_empty(), "unexpected load errors: {msgs:?}");
        (loaded.directives, loaded.directive_lines)
    }

    /// Every directive's `meta` carries the source location we passed in, and a
    /// non-empty hash matching `compute_directive_hash` (proves the meta record
    /// is wired through `directive_from_core`/`meta_from_core`).
    #[test]
    fn meta_source_location_and_hash_wired() {
        let (dirs, lines) = load();
        assert!(!dirs.is_empty());
        for (d, &line) in dirs.iter().zip(&lines) {
            let w = directive_from_core(d, line, "<test>");
            let m = dir_meta(&w);
            assert_eq!(m.filename, "<test>");
            assert_eq!(m.lineno, line);
            assert_eq!(m.hash, ffi::compute_directive_hash(d));
            assert!(!m.hash.is_empty());
            // User entries are key-sorted (deterministic, unlike the source map).
            let keys: Vec<&String> = m.user.iter().map(|(k, _)| k).collect();
            let mut sorted = keys.clone();
            sorted.sort();
            assert_eq!(keys, sorted, "meta user entries must be key-sorted");
        }
    }

    /// THE FIDELITY FIX: a numeric metadatum is now `meta-value::number` (typed),
    /// while a string metadatum stays `meta-value::text`. The old
    /// `directive(directive_to_json(..))` path gave `text` for BOTH.
    #[test]
    fn numeric_metadata_is_typed_number_string_is_text() {
        let (dirs, lines) = load();
        let txn = dirs
            .iter()
            .zip(&lines)
            .find_map(|(d, &l)| match directive_from_core(d, l, "<test>") {
                wit::Directive::Transaction(t) => Some(t),
                _ => None,
            })
            .expect("transaction present");

        match user_get(&txn.meta, "num") {
            wit::MetaValue::Number(s) => assert_eq!(s, "42.50"),
            _ => panic!(
                "numeric metadata must be typed meta-value::number (the old DTO \
                 path collapsed it to text)"
            ),
        }
        match user_get(&txn.meta, "note") {
            wit::MetaValue::Text(s) => assert_eq!(s, "hello"),
            _ => panic!("string metadata must be meta-value::text"),
        }
    }

    /// Full field check of the transaction + its cost/price posting.
    #[test]
    fn transaction_fields_and_posting_cost_price() {
        let (dirs, lines) = load();
        let txn = dirs
            .iter()
            .zip(&lines)
            .find_map(|(d, &l)| match directive_from_core(d, l, "<test>") {
                wit::Directive::Transaction(t) => Some(t),
                _ => None,
            })
            .expect("transaction present");

        assert_eq!(txn.date, "2024-01-15");
        assert_eq!(txn.flag, "*");
        assert_eq!(txn.payee.as_deref(), Some("Broker"));
        assert_eq!(txn.narration.as_deref(), Some("Buy shares"));
        assert_eq!(txn.tags, vec!["trip".to_string()]);
        assert_eq!(txn.links, vec!["inv-1".to_string()]);
        assert_eq!(txn.postings.len(), 2);

        let stock = &txn.postings[0];
        assert_eq!(stock.account, "Assets:Stock");
        let units = stock.units.as_ref().expect("units");
        assert_eq!(units.number, "10");
        assert_eq!(units.currency, "AAPL");
        let cost = stock.cost.as_ref().expect("cost");
        match &cost.number {
            Some(wit::CostNumber::PerUnit(v)) => assert_eq!(v, "150.00"),
            _ => panic!("expected per-unit cost number"),
        }
        assert_eq!(cost.currency.as_deref(), Some("USD"));
        let price = stock.price.as_ref().expect("price");
        assert_eq!(price.number, "155.00");
        assert_eq!(price.currency, "USD");

        let cash = &txn.postings[1];
        assert_eq!(cash.account, "Assets:Cash");
        let cu = cash.units.as_ref().expect("units");
        assert_eq!(cu.number, "-1500.00");
        assert_eq!(cu.currency, "USD");
        assert!(cash.cost.is_none());
        assert!(cash.price.is_none());
    }

    /// Spot-check the remaining directive shapes (balance/price/commodity/
    /// document/custom/close), including typed `custom` arguments.
    #[test]
    fn other_directive_shapes() {
        let (dirs, lines) = load();
        let wits: Vec<wit::Directive> = dirs
            .iter()
            .zip(&lines)
            .map(|(d, &l)| directive_from_core(d, l, "<test>"))
            .collect();

        // balance: amount + tolerance None (none was written).
        let bal = wits
            .iter()
            .find_map(|w| match w {
                wit::Directive::Balance(b) => Some(b),
                _ => None,
            })
            .expect("balance");
        assert_eq!(bal.account, "Assets:Cash");
        assert_eq!(bal.amount.number, "-1500.00");
        assert_eq!(bal.amount.currency, "USD");
        assert!(bal.tolerance.is_none());

        // price.
        let price = wits
            .iter()
            .find_map(|w| match w {
                wit::Directive::Price(p) => Some(p),
                _ => None,
            })
            .expect("price");
        assert_eq!(price.currency, "AAPL");
        assert_eq!(price.amount.number, "160.00");
        assert_eq!(price.amount.currency, "USD");

        // commodity: string meta stays text.
        let com = wits
            .iter()
            .find_map(|w| match w {
                wit::Directive::Commodity(c) => Some(c),
                _ => None,
            })
            .expect("commodity");
        assert_eq!(com.currency, "AAPL");
        match user_get(&com.meta, "name") {
            wit::MetaValue::Text(s) => assert_eq!(s, "Apple Inc"),
            _ => panic!("commodity name meta must be text"),
        }

        // document: tags + links carried.
        let doc = wits
            .iter()
            .find_map(|w| match w {
                wit::Directive::Document(d) => Some(d),
                _ => None,
            })
            .expect("document");
        assert_eq!(doc.path, "/docs/x.pdf");
        assert_eq!(doc.tags, vec!["dtag".to_string()]);
        assert_eq!(doc.links, vec!["dlink".to_string()]);

        // custom: typed values carry their value-type tag; numeric arg is number.
        let custom = wits
            .iter()
            .find_map(|w| match w {
                wit::Directive::Custom(c) => Some(c),
                _ => None,
            })
            .expect("custom");
        assert_eq!(custom.custom_type, "budget");
        assert_eq!(custom.values.len(), 2);
        assert_eq!(custom.values[0].value_type, "string");
        match &custom.values[0].value {
            wit::MetaValue::Text(s) => assert_eq!(s, "groceries"),
            _ => panic!("custom string arg must be text"),
        }
        assert_eq!(custom.values[1].value_type, "number");
        match &custom.values[1].value {
            wit::MetaValue::Number(s) => assert_eq!(s, "500.00"),
            _ => panic!("custom numeric arg must be number"),
        }

        // close.
        let close = wits
            .iter()
            .find_map(|w| match w {
                wit::Directive::Close(c) => Some(c),
                _ => None,
            })
            .expect("close");
        assert_eq!(close.account, "Assets:Cash");
    }

    /// WIT `cost-number` mapping, both directions — the fifth `CostNumber`
    /// wire mirror. The four JSON mirrors are held to one canonical shape
    /// by `rustledger-wasm/tests/cost_number_wire_parity.rs` (W1); the WIT
    /// variant is positional rather than `kind`-tagged, so what parity
    /// means HERE is: every core variant lowers to the same-named WIT arm
    /// with the same string payloads (scale preserved), and every WIT arm
    /// raises into the matching `InputCostNumber` variant. A new
    /// `CostNumber` variant makes both matches non-exhaustive, forcing an
    /// update at exactly these two sites.
    #[test]
    fn cost_number_lowers_to_matching_wit_arms() {
        let d = |s: &str| rustledger_core::Decimal::from_str_exact(s).unwrap();
        match cost_number_from_core(rustledger_core::CostNumber::PerUnit { value: d("100") }) {
            wit::CostNumber::PerUnit(v) => assert_eq!(v, "100"),
            other => panic!("PerUnit lowered to wrong arm: {other:?}"),
        }
        match cost_number_from_core(rustledger_core::CostNumber::Total { value: d("1500") }) {
            wit::CostNumber::Total(v) => assert_eq!(v, "1500"),
            other => panic!("Total lowered to wrong arm: {other:?}"),
        }
        match cost_number_from_core(rustledger_core::CostNumber::Compound {
            per_unit: d("5.00"),
            total: d("10.00"),
        }) {
            wit::CostNumber::Compound((per_unit, total)) => {
                assert_eq!(per_unit, "5.00", "scale must be preserved");
                assert_eq!(total, "10.00");
            }
            other => panic!("Compound lowered to wrong arm: {other:?}"),
        }
        match cost_number_from_core(rustledger_core::CostNumber::PerUnitFromTotal(
            rustledger_core::BookedCost {
                per_unit: d("150"),
                total: d("300"),
            },
        )) {
            wit::CostNumber::PerUnitFromTotal((per_unit, total)) => {
                assert_eq!(per_unit, "150");
                assert_eq!(total, "300");
            }
            other => panic!("PerUnitFromTotal lowered to wrong arm: {other:?}"),
        }
    }

    #[test]
    fn wit_cost_number_raises_to_matching_input_variants() {
        let cases = [
            wit::CostNumber::PerUnit("100".to_string()),
            wit::CostNumber::Total("1500".to_string()),
            wit::CostNumber::Compound(("5.00".to_string(), "10.00".to_string())),
            wit::CostNumber::PerUnitFromTotal(("150".to_string(), "300".to_string())),
        ];
        for case in &cases {
            match (case, input_cost_number(case)) {
                (wit::CostNumber::PerUnit(v), ffi::InputCostNumber::PerUnit { value }) => {
                    assert_eq!(&value, v);
                }
                (wit::CostNumber::Total(v), ffi::InputCostNumber::Total { value }) => {
                    assert_eq!(&value, v);
                }
                (
                    wit::CostNumber::Compound((p, t)),
                    ffi::InputCostNumber::Compound { per_unit, total },
                ) => {
                    assert_eq!(&per_unit, p);
                    assert_eq!(&total, t);
                }
                (
                    wit::CostNumber::PerUnitFromTotal((p, t)),
                    ffi::InputCostNumber::PerUnitFromTotal { per_unit, total },
                ) => {
                    assert_eq!(&per_unit, p);
                    assert_eq!(&total, t);
                }
                (case, got) => panic!("WIT {case:?} raised to wrong variant: {got:?}"),
            }
        }
    }

    /// WIT 3.4.0 `session.from-entries`: a held directive set answers
    /// queries with no per-call marshaling, and conversion-failing
    /// directives (un-lexable accounts) are dropped like
    /// `builder.query-entries` — observable via `info()`.
    #[test]
    fn session_from_entries_holds_and_queries() {
        use super::SessionState;
        // Round-trip the comprehensive LEDGER through the real load path
        // (parse + book) into WIT directives, then hold them in a session
        // built from that WIT list.
        let loaded = ffi::helpers::load_source(LEDGER);
        let wit_dirs: Vec<wit::Directive> = loaded
            .directives
            .iter()
            .map(|d| directive_from_core(d, 0, "<test>"))
            .collect();
        let n = wit_dirs.len();
        let session = SessionState::from_entries(&wit_dirs);
        assert_eq!(
            session.info().entries.len(),
            n,
            "all well-formed directives must survive the hold"
        );
        let result = session.query("SELECT account, sum(position) GROUP BY account");
        assert!(result.errors.is_empty(), "{:?}", result.errors);
        assert!(!result.rows.is_empty());

        // An un-lexable account drops its directive (mirrors query-entries).
        let bad = directive_from_core(
            &rustledger_core::Directive::Open(rustledger_core::Open::new(
                rustledger_core::naive_date(2024, 1, 1).unwrap(),
                "bad account name",
            )),
            0,
            "<test>",
        );
        let session = SessionState::from_entries(&[bad]);
        assert_eq!(session.info().entries.len(), 0);
    }
}

// ---- importer interface (3.5.0) ------------------------------------------
//
// The `rledger extract` engine over the component boundary (roadmap "import
// over the component boundary"). Content arrives as bytes from the host —
// there is no file to read — so extraction goes through the importer crate's
// content-based entry points (`CsvImporter::extract_string`,
// `OfxImporter::extract_from_string`). The declarative config is ONE
// `importers.toml` entry parsed by the canonical
// `rustledger_importer::toml_entry` schema module shared with the CLI.

use crate::exports::rustledger::ledger::importer as imp;
use rustledger_importer::csv_importer::CsvImporter;
use rustledger_importer::{DetectedFormat, OfxImporter, detect_format, toml_entry};

/// Names of built-in importers that recognize the file. Delegates to the
/// canonical `rustledger_importer::detect_format` — the extension is
/// authoritative when recognized; the content sniff only decides for
/// absent/unrecognized extensions (misnamed downloads).
pub fn import_identify(filename: &str, content: &[u8]) -> Vec<String> {
    match detect_format(filename, content) {
        Some(DetectedFormat::Ofx) => vec!["OFX/QFX".to_string()],
        Some(DetectedFormat::Csv) => vec!["CSV".to_string()],
        None => Vec::new(),
    }
}

/// Infer a CSV mapping; returns an `importers.toml` entry (bare TOML table)
/// that round-trips into [`import_extract`].
pub fn import_infer(_filename: &str, content: &[u8]) -> Result<String, String> {
    let text = std::str::from_utf8(content).map_err(|_| "content is not UTF-8".to_string())?;
    let inferred = rustledger_importer::csv_inference::infer_csv_config(text)
        .ok_or_else(|| "content does not look like parseable CSV".to_string())?;
    toml_entry::entry_toml_from_inferred("inferred", &inferred).map_err(|e| e.to_string())
}

/// Extract directives from statement bytes using a declarative config entry.
///
/// Mirrors the CLI's semantics: `currency` defaults to USD when the entry
/// omits it (the schema's documented default — the CLI injects it via the
/// `--currency` flag default), and non-UTF-8 content is decoded lossily so
/// a Latin-1 OFX 1.x download degrades to replacement characters in text
/// fields instead of dead-ending a file `identify` just recognized.
pub fn import_extract(
    filename: &str,
    content: &[u8],
    config: &str,
) -> Result<imp::ExtractResult, String> {
    let mut entry = toml_entry::ImporterEntry::from_toml_str(config).map_err(|e| e.to_string())?;
    if entry.preprocess.is_some() {
        return Err(
            "`preprocess` is not available over the component boundary (a WASI \
             component cannot exec): run the preprocessor on the host and pass \
             its output as `content`"
                .to_string(),
        );
    }
    if entry.currency.is_none() {
        entry.currency = Some("USD".to_string());
    }
    let text = String::from_utf8_lossy(content);

    let result = if detect_format(filename, content) == Some(DetectedFormat::Ofx) {
        // OFX needs only account/currency; column mappings don't apply.
        // `account` is required HERE (not defaulted): the builder would
        // otherwise silently target Expenses:Unknown, which is wrong for
        // the asset/liability account a statement belongs to.
        let Some(ref account) = entry.account else {
            return Err("OFX extraction requires `account` in the config entry".to_string());
        };
        let mut builder = rustledger_importer::ImporterConfig::csv().account(account);
        if let Some(ref currency) = entry.currency {
            builder = builder.currency(currency);
        }
        let cfg = builder.build().map_err(|e| e.to_string())?;
        OfxImporter
            .extract_from_string(&text, &cfg)
            .map_err(|e| e.to_string())?
    } else {
        let cfg = toml_entry::build_config_from_entry(&entry).map_err(|e| e.to_string())?;
        CsvImporter
            .extract_string(&text, &cfg)
            .map_err(|e| e.to_string())?
    };

    Ok(imp::ExtractResult {
        entries: result
            .directives
            .iter()
            .map(|d| directive_from_core(d, 0, filename))
            .collect(),
        warnings: result.warnings.into_iter().map(extract_warning).collect(),
    })
}

/// An import warning as the structured `error` record (severity `warning`,
/// phase `extract`) — same diagnostic shape as every other surface, and
/// line/field attribution can be added later without a record-shape break.
fn extract_warning(message: String) -> wit::Error {
    wit::Error {
        message,
        line: None,
        column: None,
        field: None,
        entry_index: None,
        severity: "warning".to_string(),
        phase: "extract".to_string(),
    }
}

#[cfg(test)]
mod session_options_tests {
    //! The `from-entries-with-options` carrier (WIT 3.7.0, #1766): a
    //! session rebuilt from another session's `info()` must classify
    //! accounts with the LEDGER's roots, where the options-less
    //! `from_entries` falls back to the defaults. POSSIGN is the exact
    //! observable the L5 note recorded as broken.

    use super::SessionState;

    const RENAMED: &str = "\
option \"name_income\" \"Einnahmen\"
2024-01-01 open Einnahmen:Salary
2024-01-01 open Assets:Bank

2024-01-02 * \"pay\"
  Assets:Bank  100.00 USD
  Einnahmen:Salary
";

    /// The first cell of the first row as the typed numeric value —
    /// exact-variant matching, not a debug-substring proxy (Copilot
    /// review: `contains("-100")` also matches "-1000").
    fn first_number(result: &super::out::QueryResult) -> String {
        match result
            .rows
            .first()
            .and_then(|r| r.first())
            .expect("query returns at least one row")
        {
            super::wit::QueryValue::Number(n) => n.clone(),
            other => panic!("POSSIGN must return query-value::number, got {other:?}"),
        }
    }

    #[test]
    fn with_options_honors_renamed_roots_where_from_entries_defaults() {
        let loaded = SessionState::from_source(RENAMED);
        let info = loaded.info();
        assert!(
            info.errors.is_empty(),
            "fixture must load: {:?}",
            info.errors
        );

        // POSSIGN negates income-rooted accounts; "Einnahmen" is income
        // only when the ledger's renamed roots are carried.
        let query = "SELECT possign(100, 'Einnahmen:Salary')";

        let with_options =
            SessionState::from_entries_with_options(&info.entries, info.options.clone());
        assert_eq!(
            first_number(&with_options.query(query)),
            "-100",
            "renamed income root must POSSIGN-negate"
        );

        let without_options = SessionState::from_entries(&info.entries);
        assert_eq!(
            first_number(&without_options.query(query)),
            "100",
            "options-less entries default the classifier (documented, #1766)"
        );
    }

    /// Empty `name-*` roots are replaced with defaults — a
    /// zero-initialized options record must not silently break every
    /// classification (deep review of #1805).
    #[test]
    fn empty_roots_fall_back_to_defaults() {
        let loaded = SessionState::from_source(RENAMED);
        let info = loaded.info();
        let mut options = info.options.clone();
        options.name_assets = String::new();
        let session = SessionState::from_entries_with_options(&info.entries, options);
        let echoed = session.info().options;
        assert_eq!(echoed.name_assets, "Assets", "empty root falls back");
        assert_eq!(
            echoed.name_income, "Einnahmen",
            "provided roots pass through"
        );
    }

    /// `info()` echoes the provided options — the session is the
    /// canonical carrier, so a host can round-trip them.
    #[test]
    fn info_echoes_provided_options() {
        let loaded = SessionState::from_source(RENAMED);
        let info = loaded.info();
        let session = SessionState::from_entries_with_options(&info.entries, info.options.clone());
        assert_eq!(session.info().options.name_income, "Einnahmen");
        // And the options-less constructor documents its default.
        assert_eq!(
            SessionState::from_entries(&info.entries)
                .info()
                .options
                .name_income,
            "Income"
        );
    }

    /// #1806: `session.clamp` drives classification and the synthesized
    /// summary account names from the HELD options. A ledger renaming its
    /// income root and its `account_previous_earnings` must roll pre-window
    /// income into the configured account — where the options-less
    /// `from_entries` path falls back to beancount defaults.
    #[test]
    fn clamp_honors_held_options_for_classification_and_summaries() {
        const RENAMED_EARNINGS: &str = "\
option \"name_income\" \"Einnahmen\"
option \"account_previous_earnings\" \"Eigenkapital:Gewinn\"
option \"account_previous_balances\" \"Eigenkapital:Anfang\"
2023-01-01 open Assets:Bank
2023-01-01 open Einnahmen:Lohn

2023-06-01 * \"pre-window pay\"
  Assets:Bank  100.00 EUR
  Einnahmen:Lohn  -100.00 EUR
";
        let loaded = SessionState::from_source(RENAMED_EARNINGS);
        let info = loaded.info();
        assert!(
            info.errors.is_empty(),
            "fixture must load: {:?}",
            info.errors
        );

        let mentions = |dirs: &[super::wit::Directive], account: &str| {
            dirs.iter().any(|d| {
                matches!(d, super::wit::Directive::Transaction(t)
                    if t.postings.iter().any(|p| p.account == account))
            })
        };

        // Held options: pre-window income (a RENAMED root) rolls up, and
        // the summary legs use the configured equity accounts.
        let held = SessionState::from_entries_with_options(&info.entries, info.options.clone());
        let clamped = held.clamp("2024-01-01", "2024-12-31");
        assert!(
            mentions(&clamped, "Eigenkapital:Gewinn"),
            "renamed income must roll into the configured earnings account"
        );
        assert!(
            mentions(&clamped, "Eigenkapital:Anfang"),
            "opening balance must use the configured contra account"
        );
        assert!(
            !mentions(&clamped, "Equity:Opening-Balances")
                && !mentions(&clamped, "Equity:Earnings:Previous"),
            "no hardcoded default summary accounts on a renamed ledger"
        );

        // Options-less path: same entries, but classification falls back to
        // defaults, so the renamed `Einnahmen` root is NOT income and no
        // earnings rollup is synthesized.
        let defaulted = SessionState::from_entries(&info.entries);
        let clamped = defaulted.clamp("2024-01-01", "2024-12-31");
        assert!(
            !mentions(&clamped, "Eigenkapital:Gewinn")
                && !mentions(&clamped, "Equity:Earnings:Previous"),
            "default classifier does not treat Einnahmen as income, so no earnings summary"
        );
    }
}

#[cfg(test)]
mod session_format_tests {
    //! `session.format` (WIT 3.8.0, #1766): render the held entries
    //! honoring the ledger's display precision. The distinguishing
    //! observable: an option precision WIDER than every written amount —
    //! inference alone can never produce it, so padding to it proves the
    //! held options reached the renderer.

    use super::SessionState;

    /// `USD:0.001` (3dp) is wider than the written 2dp, so the padded
    /// third decimal can only come from the option.
    const PRECISION_LEDGER: &str = "\
option \"display_precision\" \"USD:0.001\"
2024-01-01 open Assets:Bank
2024-01-15 balance Assets:Bank  100.50 USD
";

    #[test]
    fn format_pads_to_display_precision_option() {
        let session = SessionState::from_source(PRECISION_LEDGER);
        let info = session.info();
        assert!(
            info.errors.is_empty(),
            "fixture must load: {:?}",
            info.errors
        );
        let text = session.format().expect("held entries render");
        assert!(
            text.contains("2024-01-15 balance Assets:Bank 100.500 USD\n"),
            "option 3dp must pad the written 2dp amount, got:\n{text}"
        );
    }

    /// The round-trip that motivated the whole options carrier: a session
    /// rebuilt from another session's `info()` formats identically WITH
    /// the options, and falls back to entry-inferred precision without.
    #[test]
    fn from_entries_with_options_carries_display_precision() {
        let loaded = SessionState::from_source(PRECISION_LEDGER);
        let info = loaded.info();
        assert!(
            info.options
                .display_precision
                .contains(&("USD".to_string(), 3)),
            "loader must derive 3 digits from USD:0.001, got {:?}",
            info.options.display_precision
        );

        let with_options =
            SessionState::from_entries_with_options(&info.entries, info.options.clone());
        let text = with_options.format().expect("held entries render");
        assert!(
            text.contains("2024-01-15 balance Assets:Bank 100.500 USD\n"),
            "held options must pad to 3dp, got:\n{text}"
        );

        let without_options = SessionState::from_entries(&info.entries);
        let text = without_options.format().expect("held entries render");
        assert!(
            text.contains("2024-01-15 balance Assets:Bank 100.50 USD\n"),
            "options-less entries keep the entry-inferred 2dp, got:\n{text}"
        );
    }

    /// Commodity `precision:` metadata travels IN the held entries (it is
    /// a directive, not an option), so even the options-less path honors
    /// it — and it wins over the option, same precedence as the loader
    /// (pinned currency-by-currency in
    /// `rustledger_core::display_context`'s precedence test).
    #[test]
    fn commodity_precision_metadata_survives_the_entries_round_trip() {
        const LEDGER: &str = "\
option \"display_precision\" \"USD:0.1\"
2024-01-01 commodity USD
  precision: 4
2024-01-01 open Assets:Bank
2024-01-15 balance Assets:Bank  100.50 USD
";
        let loaded = SessionState::from_source(LEDGER);
        let info = loaded.info();
        assert!(
            info.errors.is_empty(),
            "fixture must load: {:?}",
            info.errors
        );
        for session in [
            &loaded,
            &SessionState::from_entries_with_options(&info.entries, info.options.clone()),
            &SessionState::from_entries(&info.entries),
        ] {
            let text = session.format().expect("held entries render");
            assert!(
                text.contains("2024-01-15 balance Assets:Bank 100.5000 USD\n"),
                "commodity metadata 4dp must win everywhere, got:\n{text}"
            );
        }
    }
}

#[cfg(test)]
mod importer_tests {
    use super::*;

    const CSV: &str =
        "Date,Description,Amount\n2026-07-01,Coffee Shop,-4.50\n2026-07-02,Salary,2500.00\n";
    const OFX: &str = "OFXHEADER:100\nDATA:OFXSGML\n\n<OFX><BANKMSGSRSV1><STMTTRNRS><STMTRS>\n<CURDEF>USD\n<BANKTRANLIST>\n<STMTTRN><TRNTYPE>DEBIT<DTPOSTED>20260701<TRNAMT>-4.50<FITID>1<NAME>Coffee</STMTTRN>\n</BANKTRANLIST></STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>\n";

    #[test]
    fn identify_by_extension_and_sniff() {
        assert_eq!(import_identify("bank.csv", CSV.as_bytes()), vec!["CSV"]);
        assert_eq!(import_identify("bank.qfx", OFX.as_bytes()), vec!["OFX/QFX"]);
        // Misnamed OFX download: content sniff catches it.
        assert_eq!(
            import_identify("statement.txt", OFX.as_bytes()),
            vec!["OFX/QFX"]
        );
        // Headerless junk matches nothing.
        assert!(import_identify("blob.bin", &[0u8, 159, 146, 150]).is_empty());
    }

    /// The extract -> dedup -> format-loaded loop a host review UI runs.
    #[test]
    fn dedup_flags_and_format_loaded_close_the_loop() {
        let config = "name = \"x\"\naccount = \"Assets:Bank\"\ndate_column = \"Date\"\nnarration_column = \"Description\"\namount_column = \"Amount\"\n";
        let first = import_extract("bank.csv", CSV.as_bytes(), config).expect("extracts");
        assert_eq!(first.entries.len(), 2);

        // Re-importing the same statement into a session holding it:
        // every entry is a duplicate; an empty session flags nothing.
        let held = SessionState::from_entries(&first.entries);
        assert_eq!(held.dedup(&first.entries), vec![true, true]);
        let empty = SessionState::from_entries(&[]);
        assert_eq!(empty.dedup(&first.entries), vec![false, false]);

        // A fuzzy near-miss agrees with the canonical matcher: same
        // date/amount, lightly-reworded narration is still a duplicate.
        let mut reworded = first.entries.clone();
        if let wit::Directive::Transaction(t) = &mut reworded[0] {
            t.narration = Some("Coffee Shop purchase".to_string());
        }
        assert_eq!(held.dedup(&reworded), vec![true, true]);

        // The extracted entries render to canonical text a host can write
        // into the ledger file.
        let text = format_loaded(&first.entries).expect("renders");
        assert!(text.contains("Assets:Bank"), "{text}");
        assert!(text.contains("2026-07-01"), "{text}");
    }

    /// The extension is authoritative: a CSV whose narration mentions
    /// "<OFX" must stay on the CSV path (review finding — the sniff must
    /// not override an explicit extension).
    #[test]
    fn csv_extension_beats_ofx_looking_content() {
        let csv = "Date,Description,Amount\n2026-07-01,REFUND <OFX PORTAL>,-4.50\n";
        assert_eq!(import_identify("bank.csv", csv.as_bytes()), vec!["CSV"]);
        let config = "name = \"x\"\naccount = \"Assets:Bank\"\ndate_column = \"Date\"\nnarration_column = \"Description\"\namount_column = \"Amount\"\n";
        let result = import_extract("bank.csv", csv.as_bytes(), config).expect("CSV path");
        assert_eq!(result.entries.len(), 1);
    }

    /// Currency defaults to USD (the schema's documented default), so an
    /// entry with only account works over the component exactly like the
    /// CLI, where the --currency flag default supplies it.
    #[test]
    fn currency_defaults_to_usd() {
        let config = "name = \"ofx\"\naccount = \"Assets:Checking\"\n";
        let result = import_extract("bank.ofx", OFX.as_bytes(), config).expect("extracts");
        assert_eq!(result.entries.len(), 1);
    }

    /// Latin-1 OFX (CHARSET:1252, the OFX 1.x default many banks emit) is
    /// decoded lossily instead of dead-ending a file identify recognized.
    #[test]
    fn latin1_ofx_extracts_lossily() {
        let mut bytes = OFX.replace("Coffee", "Entr~e").into_bytes();
        let idx = bytes.iter().position(|&b| b == b'~').expect("marker");
        bytes[idx] = 0xE9; // \u{e9} in Latin-1 (Entree with an accent) — invalid UTF-8
        assert_eq!(import_identify("bank.ofx", &bytes), vec!["OFX/QFX"]);
        let config = "name = \"ofx\"\naccount = \"Assets:Checking\"\ncurrency = \"USD\"\n";
        let result = import_extract("bank.ofx", &bytes, config).expect("lossy decode extracts");
        assert_eq!(result.entries.len(), 1);
    }

    /// The infer -> extract loop a GUI host runs: infer a mapping, append
    /// account/currency, extract with it.
    #[test]
    fn infer_round_trips_into_extract() {
        let config = import_infer("bank.csv", CSV.as_bytes()).expect("inferable");
        let config = format!("{config}account = \"Assets:Bank\"\ncurrency = \"USD\"\n");
        let result = import_extract("bank.csv", CSV.as_bytes(), &config).expect("extracts");
        assert_eq!(result.entries.len(), 2);
        let wit::Directive::Transaction(txn) = &result.entries[0] else {
            panic!("expected a transaction");
        };
        assert!(txn.postings.iter().any(|p| p.account == "Assets:Bank"));
        // Extracted entries carry the statement filename as provenance.
        assert_eq!(txn.meta.filename, "bank.csv");
    }

    #[test]
    fn extract_ofx_needs_only_account_and_currency() {
        let config = "name = \"ofx\"\naccount = \"Assets:Checking\"\ncurrency = \"USD\"\n";
        let result = import_extract("bank.ofx", OFX.as_bytes(), config).expect("extracts");
        assert_eq!(result.entries.len(), 1);
    }

    /// OFX without `account` is an error, not a silent import into the
    /// builder's Expenses:Unknown default (review comment).
    #[test]
    fn extract_ofx_without_account_is_rejected() {
        let err =
            import_extract("bank.ofx", OFX.as_bytes(), "name = \"ofx\"").expect_err("rejects");
        assert!(err.contains("account"), "{err}");
    }

    /// `preprocess` cannot exec inside a component — reject with guidance.
    #[test]
    fn extract_rejects_preprocess_entries() {
        let config = "name = \"pdf\"\naccount = \"Assets:Bank\"\npreprocess = [\"pdftotext\"]";
        let err = import_extract("x.csv", CSV.as_bytes(), config).expect_err("rejects");
        assert!(err.contains("host"), "{err}");
    }

    #[test]
    fn extract_rejects_malformed_config() {
        assert!(import_extract("bank.csv", CSV.as_bytes(), "not = [valid").is_err());
        // Missing `name` is a schema violation, same as the CLI.
        assert!(import_extract("bank.csv", CSV.as_bytes(), "account = \"Assets:Bank\"").is_err());
    }
}

/// `session.returns` (WIT 3.9.0, #1847): the returns engine over the boundary.
#[cfg(test)]
mod returns_tests {
    use super::SessionState;

    const LEDGER: &str = "\
option \"operating_currency\" \"USD\"
2020-01-01 open Assets:Invest:Broker
2020-01-01 open Assets:Cash
2020-01-01 open Income:Dividends

2020-01-01 * \"Buy 10 ACME\"
  Assets:Invest:Broker  10 ACME {100 USD}
  Assets:Cash

2020-07-01 * \"Dividend\"
  Assets:Cash  20 USD
  Income:Dividends

2021-01-01 price ACME  120 USD
";

    fn scope_args() -> (Vec<String>, Vec<String>) {
        (
            vec!["Assets:Invest".to_string()],
            vec!["Income".to_string()],
        )
    }

    /// Drift guard (canonical-function discipline): `session.returns` must equal
    /// [`rustledger_query::scope_returns`] over the same interpolated, pad-expanded
    /// stream. That helper is the SAME composition the CLI's `report returns`
    /// calls, so equality here pins the component against the CLI's returns path
    /// — not merely against a private copy of the engine wiring.
    #[test]
    fn returns_matches_shared_helper() {
        let state = SessionState::from_source(LEDGER);
        assert!(
            state.info().errors.is_empty(),
            "fixture must load: {:?}",
            state.info().errors
        );
        let (inv, inc) = scope_args();

        let via = state
            .returns(&inv, &inc, "USD", "2021-01-01")
            .expect("returns computes");

        // The shared helper both surfaces route through (CLI report_returns and
        // session.returns), so agreement here == CLI parity, not a self-check.
        let padded = rustledger_booking::merge_with_padding(&state.directives);
        let scope = rustledger_returns::Scope::new(inv, inc);
        let end = "2021-01-01".parse().expect("date");
        let shared = rustledger_query::scope_returns(&padded, &scope, "USD", end)
            .expect("shared helper computes");

        // Decimal fields (rust_decimal → deterministic) are exact strings.
        assert_eq!(via.cash_flows, u32::try_from(shared.cash_flows).unwrap());
        assert_eq!(via.invested, shared.invested.to_string());
        assert_eq!(via.distributions, shared.distributions.to_string());
        assert_eq!(via.current_value, shared.current_value.to_string());
        // Rates are the same in-process computation, so identical; compare with
        // a tolerance anyway (clippy forbids exact float `==`).
        let same_rate = |a: Option<f64>, b: Option<f64>| match (a, b) {
            (Some(x), Some(y)) => (x - y).abs() < 1e-12,
            (None, None) => true,
            _ => false,
        };
        assert!(same_rate(via.money_weighted, shared.money_weighted));
        assert!(same_rate(via.time_weighted, shared.time_weighted));

        // Value anchors (numeric parse tolerates 1000 vs 1000.00 formatting).
        assert!((via.invested.parse::<f64>().unwrap() - 1000.0).abs() < 1e-9);
        assert!((via.current_value.parse::<f64>().unwrap() - 1200.0).abs() < 1e-9);
        assert!(
            via.money_weighted.is_some_and(|r| r > 0.0),
            "a held gain must yield a positive money-weighted return, got {:?}",
            via.money_weighted
        );
    }

    /// Empty `currency` falls back to the ledger's first `operating_currency`,
    /// matching the CLI's `--currency`-optional behavior.
    #[test]
    fn returns_currency_falls_back_to_operating() {
        let state = SessionState::from_source(LEDGER);
        let (inv, inc) = scope_args();
        let explicit = state.returns(&inv, &inc, "USD", "2021-01-01").unwrap();
        let fallback = state.returns(&inv, &inc, "", "2021-01-01").unwrap();
        assert_eq!(explicit.invested, fallback.invested);
        assert_eq!(explicit.current_value, fallback.current_value);
        // Same computation, so the money-weighted rate matches (tolerance
        // comparison — clippy forbids exact float `==`).
        match (explicit.money_weighted, fallback.money_weighted) {
            (Some(a), Some(b)) => assert!((a - b).abs() < 1e-12),
            (None, None) => {}
            other => panic!("currency fallback changed the rate: {other:?}"),
        }
    }

    #[test]
    fn returns_rejects_bad_end_date() {
        let state = SessionState::from_source(LEDGER);
        let (inv, inc) = scope_args();
        assert!(state.returns(&inv, &inc, "USD", "").is_err());
        assert!(state.returns(&inv, &inc, "USD", "not-a-date").is_err());
    }

    #[test]
    fn returns_errors_without_reporting_currency() {
        // No `operating_currency` and an empty `currency` arg → actionable error
        // rather than a return silently reported in the wrong currency.
        const NO_CCY: &str = "\
2020-01-01 open Assets:Invest:Broker
2020-01-01 open Assets:Cash
2020-01-01 * \"Buy\"
  Assets:Invest:Broker  10 ACME {100 USD}
  Assets:Cash
2021-01-01 price ACME  120 USD
";
        let state = SessionState::from_source(NO_CCY);
        let (inv, inc) = scope_args();
        let err = state.returns(&inv, &inc, "", "2021-01-01").unwrap_err();
        assert!(err.contains("reporting currency"), "got: {err}");
    }

    #[test]
    fn returns_proceeds_over_recovered_load_error() {
        // Like the CLI report (beancount/fava model), returns does NOT refuse on
        // a recovered load error — it computes over the held directives, and the
        // error surfaces separately via info().errors. Here a garbage line is a
        // recovered parse error with no investment activity, so returns is a clean
        // (empty) result, not an Err.
        const PARSE_ERR: &str = "\
option \"operating_currency\" \"USD\"
2020-01-01 open Assets:Invest:Broker
this line is not a valid directive @#$
";
        let state = SessionState::from_source(PARSE_ERR);
        assert!(!state.info().errors.is_empty(), "fixture must load-error");
        let (inv, inc) = scope_args();
        assert!(
            state.returns(&inv, &inc, "USD", "2021-01-01").is_ok(),
            "a recovered parse error must not block the report (errors are in info())"
        );
    }

    #[test]
    fn returns_tolerates_in_scope_booking_error() {
        // A booking-FAILED transaction (selling 10 units when only 5 were bought,
        // empty cost forcing a lot match) is re-merged into the held directives
        // UN-booked — the common state of imported brokerage data. Returns value
        // NET UNITS at market (never cost-basis lots), so this must NOT trap and
        // must NOT refuse the report: the over-sell nets to −5 ACME, valued at the
        // terminal price (−5 × 120 = −600). The booking error still surfaces via
        // info().errors; `rledger check` remains the validator (see #1850). Without
        // the net-units rewrite this native test would ABORT in the lot-matching
        // booking engine.
        const OVERSELL: &str = "\
option \"operating_currency\" \"USD\"
2020-01-01 open Assets:Invest:Broker
2020-01-01 open Assets:Cash
2020-01-01 * \"Buy 5 ACME\"
  Assets:Invest:Broker  5 ACME {100 USD}
  Assets:Cash
2020-06-01 * \"Sell 10 — more than held\"
  Assets:Invest:Broker  -10 ACME {}
  Assets:Cash  1000 USD
2021-01-01 price ACME  120 USD
";
        let state = SessionState::from_source(OVERSELL);
        assert!(
            !state.info().errors.is_empty(),
            "over-sell must surface as a booking load error"
        );
        let (inv, inc) = scope_args();
        let r = state
            .returns(&inv, &inc, "USD", "2021-01-01")
            .expect("net-units returns tolerate an in-scope over-sell");
        assert_eq!(r.current_value, "-600", "net −5 ACME × 120");
    }

    #[test]
    fn returns_from_entries_oversell_tolerated_not_traps() {
        // A `from_entries` session holds directives UN-booked with `errors:
        // vec![]`, so no load-error guard is involved at all. Returns value net
        // units at market, so an over-sell (reduce 10 of an empty-cost lot only 5
        // were bought into) nets to −5 ACME and is valued at the terminal price
        // (−5 × 120 = −600) — compute_returns, hence returns(), yields a clean Ok,
        // never a trap or refusal. This native test would abort without the
        // net-units rewrite (see #1850).
        use rustledger_core::{Amount, CostNumber, CostSpec, Decimal, Posting, Price, Transaction};
        let dt = |m, day| rustledger_core::naive_date(2020, m, day).unwrap();
        let buy = Transaction::new(dt(1, 1), "buy")
            .with_synthesized_posting(
                Posting::new(
                    "Assets:Invest:Broker",
                    Amount::new(Decimal::from(5), "ACME"),
                )
                .with_cost(
                    CostSpec::empty()
                        .with_number(CostNumber::PerUnit {
                            value: Decimal::from(100),
                        })
                        .with_currency("USD"),
                ),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(Decimal::from(-500), "USD"),
            ));
        let sell = Transaction::new(dt(6, 1), "oversell")
            .with_synthesized_posting(
                Posting::new(
                    "Assets:Invest:Broker",
                    Amount::new(Decimal::from(-10), "ACME"),
                )
                .with_cost(CostSpec::empty()),
            )
            .with_synthesized_posting(Posting::new(
                "Assets:Cash",
                Amount::new(Decimal::from(1000), "USD"),
            ));
        let price = Price::new(dt(12, 31), "ACME", Amount::new(Decimal::from(120), "USD"));
        let core = [
            rustledger_core::Directive::Transaction(buy),
            rustledger_core::Directive::Transaction(sell),
            rustledger_core::Directive::Price(price),
        ];
        let wit: Vec<_> = core
            .iter()
            .map(|d| super::directive_from_core(d, 0, "<test>"))
            .collect();
        let state = SessionState::from_entries(&wit);
        // from_entries carries no load errors; net-units tolerance is what matters.
        assert!(state.info().errors.is_empty());
        let (inv, inc) = scope_args();
        let r = state
            .returns(&inv, &inc, "USD", "2020-12-31")
            .expect("net-units returns tolerate an un-booked from_entries over-sell");
        assert_eq!(r.current_value, "-600", "net −5 ACME × 120");
    }
}

#[cfg(test)]
mod format_policy_tests {
    use super::SessionState;

    /// Both grouping tiers, over the FFI `session.format` surface.
    ///
    /// This surface honors `render_commas` and per-commodity `render_commas:`
    /// declarations — deliberately, per the doc on `SessionState::format`: the
    /// session holds the ledger's options, and the boundary a machine consumer
    /// crosses here is the PARSER, whose grammar admits grouped numerals.
    ///
    /// Nothing verified it. Deleting the flag from this path used to pass the
    /// entire workspace suite, because the construction was a second private
    /// copy of the loader's `build_display_context` and no test rendered
    /// through it. `DisplayContext::from_directives` now takes the flag as a
    /// parameter, so dropping it is a compile error rather than a silent
    /// downgrade — and this pins the behavior itself.
    const LEDGER: &str = "\
option \"render_commas\" \"TRUE\"

2024-01-01 commodity USD
2024-01-01 commodity JPY
  render_commas: FALSE

2024-01-01 open Assets:Bank
2024-01-01 open Assets:Yen
2024-01-01 open Equity:Open

2024-02-01 * \"big usd\"
  Assets:Bank    1234567.89 USD
  Equity:Open   -1234567.89 USD

2024-02-02 * \"big jpy\"
  Assets:Yen     9876543 JPY
  Equity:Open   -9876543 JPY
";

    #[test]
    fn format_honors_both_grouping_tiers() {
        let out = SessionState::from_source(LEDGER)
            .format()
            .expect("format succeeds");

        assert!(
            out.contains("1,234,567.89"),
            "the ledger-wide render_commas must group USD; got:\n{out}",
        );
        // The per-commodity opt-OUT is the half a global-only implementation
        // passes anyway, so it is the one that matters here.
        assert!(
            out.contains("9876543 JPY"),
            "JPY declares render_commas: FALSE and must stay ungrouped; got:\n{out}",
        );
        assert!(
            !out.contains("9,876,543"),
            "JPY was grouped despite its own declaration; got:\n{out}",
        );
    }

    /// Without `render_commas`, nothing groups — so the assertions above pin
    /// the OPTION rather than "this surface always groups".
    #[test]
    fn format_leaves_an_undeclared_ledger_ungrouped() {
        let plain = LEDGER.replace("option \"render_commas\" \"TRUE\"\n", "");
        let out = SessionState::from_source(&plain)
            .format()
            .expect("format succeeds");
        assert!(
            out.contains("1234567.89") && !out.contains("1,234,567.89"),
            "an undeclared ledger must not group; got:\n{out}",
        );
    }
}

#[cfg(test)]
mod account_type_tests {
    use super::SessionState;

    /// A renamed root classifies through the ledger's own names (#1964).
    ///
    /// `util.get-account-type` hardcodes the English roots, so it answers
    /// `unknown` for `Depenses:Food` while `report balsheet` — going through
    /// `AccountTypes`, the canonical — classifies it as Expenses. Two answers
    /// for one ledger depending on which surface is asked. This pins that the
    /// session agrees with the reports.
    const RENAMED: &str = "\
option \"name_expenses\" \"Depenses\"

2024-01-01 open Assets:Bank
2024-01-01 open Depenses:Food

2024-02-01 * \"lunch\"
  Depenses:Food   10.00 USD
  Assets:Bank    -10.00 USD
";

    #[test]
    fn account_type_honors_a_renamed_root() {
        let session = SessionState::from_source(RENAMED);
        assert_eq!(
            session.account_type("Depenses:Food"),
            "expenses",
            "the configured root must classify as Expenses",
        );

        // Non-vacuity, and the actual bug: the ledger-free utility cannot see
        // the rename, so it disagrees. If this ever starts returning
        // "Expenses" the utility gained ledger awareness and the two surfaces
        // no longer need separating.
        assert_eq!(
            super::get_account_type("Depenses:Food"),
            "unknown",
            "util.get-account-type is ledger-free and cannot see the rename",
        );
    }

    #[test]
    fn account_type_still_answers_for_default_roots() {
        let session = SessionState::from_source(RENAMED);
        assert_eq!(session.account_type("Assets:Bank"), "assets");
        // `Expenses:` is NOT a root on this ledger — it was renamed away, so
        // the canonical rejects it. Pins that the method reads the config
        // rather than accepting both spellings.
        assert_eq!(
            session.account_type("Expenses:Food"),
            "unknown",
            "the English root is not configured on this ledger",
        );
    }

    #[test]
    fn account_type_rejects_an_unknown_root() {
        let session = SessionState::from_source(RENAMED);
        assert_eq!(session.account_type("Nonsense:Thing"), "unknown");
    }
}
