//! Conversion from the reused `rustledger-ffi-wasi` DTOs into the generated
//! WIT types.
//!
//! The loader orchestration (`load_source`) and the core→DTO conversion
//! (`directive_to_json`) are reused wholesale; this module is the mechanical
//! DTO→WIT shuffle, since the WIT types were authored 1:1 with the DTOs.
//!
//! Known fidelity gap: directive/posting *metadata* (`meta.user`) is reused from
//! the DTO, which flattens `MetaValue` to JSON and stringifies numbers — so a
//! numeric metadata value currently surfaces as `meta-value::text`. Faithful
//! typing requires reading the core `MetaValue` directly; tracked as a
//! follow-up. (Custom-directive arguments are *not* affected: they carry their
//! `value-type` tag via the WIT `typed-value` record, so account/currency/tag/…
//! stay distinguishable.)

use rustledger_ffi_wasi as ffi;
use rustledger_query::{Executor, IntervalUnit, Value, parse as parse_query};
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
        arr @ Json::Array(_) => wit::MetaValue::Text(arr.to_string()),
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
            // Carry the `value-type` tag (account/currency/tag/…) alongside the
            // value, which `meta-value` alone would flatten to `text`.
            values: values
                .into_iter()
                .map(|tv| wit::TypedValue {
                    value_type: tv.value_type.to_string(),
                    value: meta_value(tv.value),
                })
                .collect(),
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
pub fn load(source: &str, filename: &str) -> out::LoadResult {
    load_result(ffi::helpers::load_source(source), filename)
}

/// Build a WIT load-result from a consumed `ffi-wasi` load result (shared by
/// `load` and `batch`).
fn load_result(loaded: ffi::helpers::LoadResult, filename: &str) -> out::LoadResult {
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
            m.iter()
                .map(|(k, val)| (k.clone(), format!("{val:?}")))
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
        Value::Object(_) | Value::Set(_) => Q::Json(ffi::convert::value_to_json(v).to_string()),
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
    let mut errors = load.errors;

    // Only run semantic validation when there are no syntactic errors.
    if parse_error_count == 0 {
        let today = jiff::Zoned::now().date();
        let session = rustledger_validate::ValidationSession::new(
            rustledger_validate::ValidationOptions::default(),
        );
        let (session, mut verrs) = session.run_early_spanned(&load.spanned_directives, today);
        let (session, late) = session.run_late_spanned(&load.spanned_directives, today);
        verrs.extend(late);
        verrs.extend(session.finalize());
        for err in verrs {
            let mut e = ffi::Error::new(&err.message).validate_phase();
            if let Some(span) = err.span {
                e = e.with_line(load.line_lookup.byte_to_line(span.start));
            }
            errors.push(e);
        }
    }

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
    run_query(&directives, query_str)
}

/// Run one query against already-loaded, pad-expanded directives.
pub fn run_query(directives: &[rustledger_core::Directive], query_str: &str) -> out::QueryResult {
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
    match executor.execute(&parsed) {
        Ok(result) => {
            // Infer column datatypes from the first row (reusing value_datatype).
            let columns = if let Some(first) = result.rows.first() {
                result
                    .columns
                    .iter()
                    .zip(first.iter())
                    .map(|(name, value)| wit::ColumnInfo {
                        name: name.clone(),
                        datatype: ffi::convert::value_datatype(value).to_string(),
                    })
                    .collect()
            } else {
                result
                    .columns
                    .iter()
                    .map(|name| wit::ColumnInfo {
                        name: name.clone(),
                        datatype: "str".to_string(),
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
        queries.iter().map(|q| run_query(&directives, q)).collect()
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
        load: load_result(loaded, "<stdin>"),
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
pub fn load_file(
    path: &str,
    allow_unrestricted_includes: bool,
    plugins: &[String],
) -> out::LoadResult {
    // The loader takes `path_security` (true = confine includes); the WIT flag
    // is inverted so the safe state is the `false`/zero default.
    let path_security = !allow_unrestricted_includes;
    match ffi::helpers::load_file(std::path::Path::new(path), path_security) {
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
            let entries = directives
                .iter()
                .enumerate()
                .map(|(i, d)| {
                    let line = directive_lines.get(i).copied().unwrap_or(0);
                    let file = directive_files.get(i).map_or("<unknown>", String::as_str);
                    directive(ffi::convert::directive_to_json(d, line, file))
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
    Ok(directive(ffi::convert::directive_to_json(
        &core,
        0,
        "<created>",
    )))
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
/// `rustledger_ops::clamp`. Round-trips WIT -> core -> ops -> WIT.
pub fn clamp(entries: Vec<wit::Directive>, begin: &str, end: &str) -> Vec<wit::Directive> {
    let (Ok(begin_date), Ok(end_date)) = (
        begin.parse::<rustledger_core::NaiveDate>(),
        end.parse::<rustledger_core::NaiveDate>(),
    ) else {
        // Unparsable bounds: return the input unchanged (no error channel).
        return entries;
    };
    let core: Vec<rustledger_core::Directive> = entries
        .iter()
        .filter_map(|d| ffi::input_entry_to_directive(&loaded_directive_to_input(d)).ok())
        .collect();
    rustledger_ops::clamp::clamp(&core, begin_date, end_date)
        .iter()
        .map(|d| directive(ffi::convert::directive_to_json(d, 0, "<clamped>")))
        .collect()
}

/// Run a BQL query against an already-loaded directive set (rustfava#173).
/// The typed counterpart to `filter`/`clamp`: converts the WIT directives to
/// core, expands pads (as the source-based query does), then runs the query —
/// so the embedder queries the directives it holds with no re-parse/re-render.
pub fn query_entries(entries: &[wit::Directive], query_str: &str) -> out::QueryResult {
    let core: Vec<rustledger_core::Directive> = entries
        .iter()
        .filter_map(|d| ffi::input_entry_to_directive(&loaded_directive_to_input(d)).ok())
        .collect();
    let directives = rustledger_booking::merge_with_padding(&core);
    run_query(&directives, query_str)
}

// ---- stateful ledger handle (`resource session`, rustfava#173) -------------------
//
// Normalizes the source and file load paths into one held state so the
// `query`/`filter`/`clamp` methods don't care which produced it. The win over
// the free functions: these run against the held *core* directives, so they
// never re-parse source nor round-trip a directive list through the host.

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
                directive(ffi::convert::directive_to_json(d, line, file))
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
        run_query(directives, query_str)
    }

    /// Keep only directives within `[begin, end)`. Reuses the free `filter`'s
    /// date predicate over the held directives (filter is lossless).
    pub fn filter(&self, begin: &str, end: &str) -> Vec<wit::Directive> {
        filter(self.entries(), begin, end)
    }

    /// Clamp to `[begin, end)`, running `rustledger_ops::clamp` **directly on
    /// the held core directives** — no WIT -> core -> WIT round-trip, the value
    /// the resource exists to deliver (rustfava#173).
    pub fn clamp(&self, begin: &str, end: &str) -> Vec<wit::Directive> {
        let (Ok(begin_date), Ok(end_date)) = (
            begin.parse::<rustledger_core::NaiveDate>(),
            end.parse::<rustledger_core::NaiveDate>(),
        ) else {
            return self.entries();
        };
        rustledger_ops::clamp::clamp(&self.directives, begin_date, end_date)
            .iter()
            .map(|d| directive(ffi::convert::directive_to_json(d, 0, "<clamped>")))
            .collect()
    }
}
