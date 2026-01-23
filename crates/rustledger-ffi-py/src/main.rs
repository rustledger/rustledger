//! Rustledger FFI for Python via WASI/wasmtime (Fava integration).
//!
//! This is a simple CLI that can be run via wasmtime:
//!
//! ```bash
//! # Load (full directive output with metadata)
//! cat ledger.beancount | wasmtime rustledger-ffi-py.wasm load
//!
//! # Validate
//! cat ledger.beancount | wasmtime rustledger-ffi-py.wasm validate
//!
//! # Query
//! cat ledger.beancount | wasmtime rustledger-ffi-py.wasm query "SELECT account, sum(position) GROUP BY 1"
//! ```
//!
//! All output is JSON to stdout.

use std::collections::{HashMap, HashSet};
use std::io::{self, Read};

use rustledger_booking::interpolate;
use rustledger_core::{Directive, MetaValue, Metadata};
use rustledger_parser::{Spanned, parse as parse_beancount};
use rustledger_query::{Executor, parse as parse_query};
use rustledger_validate::{ValidationOptions, validate_spanned_with_options};
use serde::Serialize;

// =============================================================================
// Output Types (JSON-serializable)
// =============================================================================

/// Metadata includes filename, lineno, plus any user-defined key-value pairs.
#[derive(Serialize, Default)]
struct Meta {
    filename: String,
    lineno: u32,
    #[serde(flatten)]
    user: HashMap<String, serde_json::Value>,
}

impl Meta {
    fn new(filename: &str, lineno: u32, directive_meta: &Metadata) -> Self {
        let mut user = HashMap::new();
        for (key, value) in directive_meta {
            user.insert(key.clone(), meta_value_to_json(value));
        }
        Self {
            filename: filename.to_string(),
            lineno,
            user,
        }
    }
}

/// Convert `MetaValue` to JSON, extracting raw values without extra formatting.
fn meta_value_to_json(value: &MetaValue) -> serde_json::Value {
    match value {
        MetaValue::String(s) => serde_json::Value::String(s.clone()),
        MetaValue::Account(a) => serde_json::Value::String(a.clone()),
        MetaValue::Currency(c) => serde_json::Value::String(c.clone()),
        MetaValue::Tag(t) => serde_json::Value::String(t.clone()),
        MetaValue::Link(l) => serde_json::Value::String(l.clone()),
        MetaValue::Date(d) => serde_json::Value::String(d.to_string()),
        MetaValue::Number(n) => serde_json::json!(n.to_string()),
        MetaValue::Bool(b) => serde_json::Value::Bool(*b),
        MetaValue::Amount(a) => serde_json::json!({
            "number": a.number.to_string(),
            "currency": a.currency.to_string()
        }),
        MetaValue::None => serde_json::Value::Null,
    }
}

#[derive(Serialize, Clone)]
struct Error {
    message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    line: Option<u32>,
    severity: String,
}

#[derive(Serialize)]
struct Amount {
    number: String,
    currency: String,
}

#[derive(Serialize)]
struct PostingCost {
    /// Per-unit cost (e.g., {100 USD})
    #[serde(skip_serializing_if = "Option::is_none")]
    number: Option<String>,
    /// Total cost (e.g., {{1000 USD}})
    #[serde(skip_serializing_if = "Option::is_none")]
    number_total: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    currency: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    date: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    label: Option<String>,
}

/// A typed value preserving the original type from the beancount source.
#[derive(Serialize)]
#[serde(rename_all = "lowercase")]
struct TypedValue {
    #[serde(rename = "type")]
    value_type: &'static str,
    value: serde_json::Value,
}

impl TypedValue {
    fn from_meta_value(mv: &MetaValue) -> Self {
        match mv {
            MetaValue::String(s) => Self {
                value_type: "string",
                value: serde_json::Value::String(s.clone()),
            },
            MetaValue::Account(a) => Self {
                value_type: "account",
                value: serde_json::Value::String(a.clone()),
            },
            MetaValue::Currency(c) => Self {
                value_type: "currency",
                value: serde_json::Value::String(c.clone()),
            },
            MetaValue::Tag(t) => Self {
                value_type: "tag",
                value: serde_json::Value::String(t.clone()),
            },
            MetaValue::Link(l) => Self {
                value_type: "link",
                value: serde_json::Value::String(l.clone()),
            },
            MetaValue::Date(d) => Self {
                value_type: "date",
                value: serde_json::Value::String(d.to_string()),
            },
            MetaValue::Number(n) => Self {
                value_type: "number",
                value: serde_json::Value::String(n.to_string()),
            },
            MetaValue::Bool(b) => Self {
                value_type: "bool",
                value: serde_json::Value::Bool(*b),
            },
            MetaValue::Amount(a) => Self {
                value_type: "amount",
                value: serde_json::json!({
                    "number": a.number.to_string(),
                    "currency": a.currency.to_string()
                }),
            },
            MetaValue::None => Self {
                value_type: "null",
                value: serde_json::Value::Null,
            },
        }
    }
}

#[derive(Serialize)]
struct Posting {
    account: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    units: Option<Amount>,
    #[serde(skip_serializing_if = "Option::is_none")]
    cost: Option<PostingCost>,
    #[serde(skip_serializing_if = "Option::is_none")]
    price: Option<Amount>,
    #[serde(skip_serializing_if = "HashMap::is_empty")]
    meta: HashMap<String, serde_json::Value>,
}

#[derive(Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
enum DirectiveJson {
    Transaction {
        date: String,
        flag: String,
        #[serde(skip_serializing_if = "Option::is_none")]
        payee: Option<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        narration: Option<String>,
        tags: Vec<String>,
        links: Vec<String>,
        postings: Vec<Posting>,
        meta: Meta,
    },
    Open {
        date: String,
        account: String,
        currencies: Vec<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        booking: Option<String>,
        meta: Meta,
    },
    Close {
        date: String,
        account: String,
        meta: Meta,
    },
    Balance {
        date: String,
        account: String,
        amount: Amount,
        meta: Meta,
    },
    Pad {
        date: String,
        account: String,
        source_account: String,
        meta: Meta,
    },
    Commodity {
        date: String,
        currency: String,
        meta: Meta,
    },
    Price {
        date: String,
        currency: String,
        amount: Amount,
        meta: Meta,
    },
    Event {
        date: String,
        event_type: String,
        value: String,
        meta: Meta,
    },
    Note {
        date: String,
        account: String,
        comment: String,
        meta: Meta,
    },
    Document {
        date: String,
        account: String,
        path: String,
        meta: Meta,
    },
    Query {
        date: String,
        name: String,
        query_string: String,
        meta: Meta,
    },
    Custom {
        date: String,
        custom_type: String,
        values: Vec<TypedValue>,
        meta: Meta,
    },
}

#[derive(Serialize)]
struct LedgerOptions {
    #[serde(skip_serializing_if = "Option::is_none")]
    title: Option<String>,
    operating_currency: Vec<String>,
    name_assets: String,
    name_liabilities: String,
    name_equity: String,
    name_income: String,
    name_expenses: String,
    documents: Vec<String>,
    commodities: Vec<String>,
    booking_method: String,
    display_precision: HashMap<String, u32>,
}

impl Default for LedgerOptions {
    fn default() -> Self {
        Self {
            title: None,
            operating_currency: Vec::new(),
            name_assets: "Assets".to_string(),
            name_liabilities: "Liabilities".to_string(),
            name_equity: "Equity".to_string(),
            name_income: "Income".to_string(),
            name_expenses: "Expenses".to_string(),
            documents: Vec::new(),
            commodities: Vec::new(),
            booking_method: "STRICT".to_string(),
            display_precision: HashMap::new(),
        }
    }
}

/// A plugin directive from the source file.
#[derive(Serialize)]
struct Plugin {
    name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    config: Option<String>,
}

/// An include directive from the source file.
#[derive(Serialize)]
struct Include {
    path: String,
    lineno: u32,
}

#[derive(Serialize)]
struct LoadOutput {
    entries: Vec<DirectiveJson>,
    errors: Vec<Error>,
    options: LedgerOptions,
    plugins: Vec<Plugin>,
    includes: Vec<Include>,
}

#[derive(Serialize)]
struct ValidateOutput {
    valid: bool,
    errors: Vec<Error>,
}

#[derive(Serialize)]
struct ColumnInfo {
    name: String,
    datatype: String,
}

#[derive(Serialize)]
struct QueryOutput {
    columns: Vec<ColumnInfo>,
    rows: Vec<Vec<serde_json::Value>>,
    errors: Vec<Error>,
}

#[derive(Serialize)]
struct VersionOutput {
    version: String,
}

/// Output for batch command: load + multiple queries in one parse.
#[derive(Serialize)]
struct BatchOutput {
    load: LoadOutput,
    queries: Vec<QueryOutput>,
}

// =============================================================================
// Helpers
// =============================================================================

/// Simple line lookup for byte offset to line number conversion.
struct LineLookup {
    line_starts: Vec<usize>,
}

impl LineLookup {
    fn new(source: &str) -> Self {
        let mut line_starts = vec![0];
        for (i, c) in source.char_indices() {
            if c == '\n' {
                line_starts.push(i + 1);
            }
        }
        Self { line_starts }
    }

    fn byte_to_line(&self, byte_offset: usize) -> u32 {
        match self.line_starts.binary_search(&byte_offset) {
            Ok(line) => line as u32 + 1,
            Err(line) => line as u32,
        }
    }
}

/// Track precision per currency: maps currency -> (`precision_counts` map)
struct PrecisionTracker {
    counts: HashMap<String, HashMap<u32, u32>>,
}

impl PrecisionTracker {
    fn new() -> Self {
        Self {
            counts: HashMap::new(),
        }
    }

    fn observe(&mut self, currency: &str, number: rustledger_core::Decimal) {
        let precision = number.scale();
        let currency_counts = self.counts.entry(currency.to_string()).or_default();
        *currency_counts.entry(precision).or_insert(0) += 1;
    }

    fn most_common_precision(&self) -> HashMap<String, u32> {
        self.counts
            .iter()
            .map(|(currency, counts)| {
                let precision = counts
                    .iter()
                    .max_by_key(|(_, count)| *count)
                    .map_or(2, |(prec, _)| *prec);
                (currency.clone(), precision)
            })
            .collect()
    }
}

/// Internal load result with all parsed data.
struct LoadResult {
    directives: Vec<Directive>,
    spanned_directives: Vec<Spanned<Directive>>,
    directive_lines: Vec<u32>,
    line_lookup: LineLookup,
    errors: Vec<Error>,
    options: LedgerOptions,
    plugins: Vec<Plugin>,
    includes: Vec<Include>,
}

/// Parse and interpolate source, returning directives with line numbers.
fn load_source(source: &str) -> LoadResult {
    let parse_result = parse_beancount(source);
    let lookup = LineLookup::new(source);

    let mut errors: Vec<Error> = parse_result
        .errors
        .iter()
        .map(|e| Error {
            message: e.to_string(),
            line: Some(lookup.byte_to_line(e.span().0)),
            severity: "error".to_string(),
        })
        .collect();

    // Extract options
    let mut options = LedgerOptions::default();
    for (key, value, _span) in &parse_result.options {
        match key.as_str() {
            "title" => options.title = Some(value.clone()),
            "operating_currency" => options.operating_currency.push(value.clone()),
            "name_assets" => options.name_assets.clone_from(value),
            "name_liabilities" => options.name_liabilities.clone_from(value),
            "name_equity" => options.name_equity.clone_from(value),
            "name_income" => options.name_income.clone_from(value),
            "name_expenses" => options.name_expenses.clone_from(value),
            "documents" => options.documents.push(value.clone()),
            "booking_method" => options.booking_method.clone_from(value),
            _ => {}
        }
    }

    // Collect directive line numbers, commodities, and precision
    let mut directive_lines: Vec<u32> = Vec::new();
    let mut commodities: HashSet<String> = HashSet::new();
    let mut precision_tracker = PrecisionTracker::new();

    let mut directives: Vec<Directive> = Vec::new();
    for spanned in &parse_result.directives {
        let line = lookup.byte_to_line(spanned.span.start);
        directive_lines.push(line);

        // Collect commodities and track precision
        match &spanned.value {
            Directive::Open(o) => {
                for c in &o.currencies {
                    commodities.insert(c.to_string());
                }
            }
            Directive::Commodity(c) => {
                commodities.insert(c.currency.to_string());
            }
            Directive::Transaction(t) => {
                for p in &t.postings {
                    if let Some(units) = &p.units {
                        if let Some(amt) = units.as_amount() {
                            commodities.insert(amt.currency.to_string());
                            precision_tracker.observe(amt.currency.as_ref(), amt.number);
                        }
                    }
                    if let Some(price) = &p.price {
                        if let Some(amt) = price.amount() {
                            commodities.insert(amt.currency.to_string());
                            precision_tracker.observe(amt.currency.as_ref(), amt.number);
                        }
                    }
                }
            }
            Directive::Balance(b) => {
                commodities.insert(b.amount.currency.to_string());
                precision_tracker.observe(b.amount.currency.as_ref(), b.amount.number);
            }
            Directive::Price(p) => {
                commodities.insert(p.currency.to_string());
                commodities.insert(p.amount.currency.to_string());
                precision_tracker.observe(p.amount.currency.as_ref(), p.amount.number);
            }
            _ => {}
        }

        directives.push(spanned.value.clone());
    }

    // Interpolate transactions
    if errors.is_empty() {
        for (i, directive) in directives.iter_mut().enumerate() {
            if let Directive::Transaction(txn) = directive {
                match interpolate(txn) {
                    Ok(result) => {
                        *txn = result.transaction;
                    }
                    Err(e) => {
                        errors.push(Error {
                            message: e.to_string(),
                            line: Some(directive_lines[i]),
                            severity: "error".to_string(),
                        });
                    }
                }
            }
        }
    }

    let mut commodity_list: Vec<_> = commodities.into_iter().collect();
    commodity_list.sort();
    options.commodities = commodity_list;
    options.display_precision = precision_tracker.most_common_precision();

    // Extract plugins
    let plugins: Vec<Plugin> = parse_result
        .plugins
        .iter()
        .map(|(name, config, _span)| Plugin {
            name: name.clone(),
            config: config.clone(),
        })
        .collect();

    // Extract includes
    let includes: Vec<Include> = parse_result
        .includes
        .iter()
        .map(|(path, span)| Include {
            path: path.clone(),
            lineno: lookup.byte_to_line(span.start),
        })
        .collect();

    // Clone spanned directives for validation
    let spanned_directives: Vec<Spanned<Directive>> = parse_result.directives.to_vec();

    LoadResult {
        directives,
        spanned_directives,
        directive_lines,
        line_lookup: lookup,
        errors,
        options,
        plugins,
        includes,
    }
}

/// Convert core directive to JSON output format.
fn directive_to_json(directive: &Directive, line: u32, filename: &str) -> DirectiveJson {
    match directive {
        Directive::Transaction(t) => {
            let meta = Meta::new(filename, line, &t.meta);
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

                        // Extract cost
                        let cost = p.cost.as_ref().map(|c| PostingCost {
                            number: c.number_per.as_ref().map(std::string::ToString::to_string),
                            number_total: c
                                .number_total
                                .as_ref()
                                .map(std::string::ToString::to_string),
                            currency: c.currency.as_ref().map(std::string::ToString::to_string),
                            date: c.date.map(|d| d.to_string()),
                            label: c.label.clone(),
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
                            meta: posting_meta,
                        }
                    })
                    .collect(),
                meta,
            }
        }
        Directive::Open(o) => {
            let meta = Meta::new(filename, line, &o.meta);
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
            let meta = Meta::new(filename, line, &c.meta);
            DirectiveJson::Close {
                date: c.date.to_string(),
                account: c.account.to_string(),
                meta,
            }
        }
        Directive::Balance(b) => {
            let meta = Meta::new(filename, line, &b.meta);
            DirectiveJson::Balance {
                date: b.date.to_string(),
                account: b.account.to_string(),
                amount: Amount {
                    number: b.amount.number.to_string(),
                    currency: b.amount.currency.to_string(),
                },
                meta,
            }
        }
        Directive::Pad(p) => {
            let meta = Meta::new(filename, line, &p.meta);
            DirectiveJson::Pad {
                date: p.date.to_string(),
                account: p.account.to_string(),
                source_account: p.source_account.to_string(),
                meta,
            }
        }
        Directive::Commodity(c) => {
            let meta = Meta::new(filename, line, &c.meta);
            DirectiveJson::Commodity {
                date: c.date.to_string(),
                currency: c.currency.to_string(),
                meta,
            }
        }
        Directive::Price(p) => {
            let meta = Meta::new(filename, line, &p.meta);
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
            let meta = Meta::new(filename, line, &e.meta);
            DirectiveJson::Event {
                date: e.date.to_string(),
                event_type: e.event_type.clone(),
                value: e.value.clone(),
                meta,
            }
        }
        Directive::Note(n) => {
            let meta = Meta::new(filename, line, &n.meta);
            DirectiveJson::Note {
                date: n.date.to_string(),
                account: n.account.to_string(),
                comment: n.comment.clone(),
                meta,
            }
        }
        Directive::Document(d) => {
            let meta = Meta::new(filename, line, &d.meta);
            DirectiveJson::Document {
                date: d.date.to_string(),
                account: d.account.to_string(),
                path: d.path.clone(),
                meta,
            }
        }
        Directive::Query(q) => {
            let meta = Meta::new(filename, line, &q.meta);
            DirectiveJson::Query {
                date: q.date.to_string(),
                name: q.name.clone(),
                query_string: q.query.clone(),
                meta,
            }
        }
        Directive::Custom(c) => {
            let meta = Meta::new(filename, line, &c.meta);
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
fn value_to_json(value: &rustledger_query::Value) -> serde_json::Value {
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
                .iter()
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
    }
}

/// Get datatype string for a Value.
const fn value_datatype(value: &rustledger_query::Value) -> &'static str {
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
    }
}

// =============================================================================
// Commands
// =============================================================================

fn cmd_load(source: &str, filename: &str) {
    let load = load_source(source);

    let entries: Vec<DirectiveJson> = load
        .directives
        .iter()
        .zip(load.directive_lines.iter())
        .map(|(d, &line)| directive_to_json(d, line, filename))
        .collect();

    let output = LoadOutput {
        entries,
        errors: load.errors,
        options: load.options,
        plugins: load.plugins,
        includes: load.includes,
    };
    println!("{}", serde_json::to_string(&output).unwrap());
}

fn cmd_validate(source: &str) {
    let load = load_source(source);
    let mut errors = load.errors;

    // Run validation if parsing succeeded
    if errors.is_empty() {
        let validation_errors =
            validate_spanned_with_options(&load.spanned_directives, ValidationOptions::default());
        for err in validation_errors {
            // Convert span to line number if available
            let line = err.span.map(|s| load.line_lookup.byte_to_line(s.start));
            errors.push(Error {
                message: err.message,
                line,
                severity: "error".to_string(),
            });
        }
    }

    let output = ValidateOutput {
        valid: errors.is_empty(),
        errors,
    };
    println!("{}", serde_json::to_string(&output).unwrap());
}

/// Execute a single query on directives, returning `QueryOutput`.
fn execute_query(directives: &[Directive], query_str: &str) -> QueryOutput {
    // Parse query
    let query = match parse_query(query_str) {
        Ok(q) => q,
        Err(e) => {
            return QueryOutput {
                columns: vec![],
                rows: vec![],
                errors: vec![Error {
                    message: format!("Query parse error: {e}"),
                    line: None,
                    severity: "error".to_string(),
                }],
            };
        }
    };

    // Execute
    let mut executor = Executor::new(directives);
    match executor.execute(&query) {
        Ok(result) => {
            // Infer column types from first row
            let columns: Vec<ColumnInfo> = if result.rows.is_empty() {
                result
                    .columns
                    .iter()
                    .map(|name| ColumnInfo {
                        name: name.clone(),
                        datatype: "str".to_string(), // Default if no rows
                    })
                    .collect()
            } else {
                result
                    .columns
                    .iter()
                    .zip(result.rows[0].iter())
                    .map(|(name, value)| ColumnInfo {
                        name: name.clone(),
                        datatype: value_datatype(value).to_string(),
                    })
                    .collect()
            };

            let rows: Vec<Vec<_>> = result
                .rows
                .iter()
                .map(|row| row.iter().map(value_to_json).collect())
                .collect();

            QueryOutput {
                columns,
                rows,
                errors: vec![],
            }
        }
        Err(e) => QueryOutput {
            columns: vec![],
            rows: vec![],
            errors: vec![Error {
                message: format!("Query error: {e}"),
                line: None,
                severity: "error".to_string(),
            }],
        },
    }
}

fn cmd_query(source: &str, query_str: &str) {
    let load = load_source(source);

    if !load.errors.is_empty() {
        let output = QueryOutput {
            columns: vec![],
            rows: vec![],
            errors: load.errors,
        };
        println!("{}", serde_json::to_string(&output).unwrap());
        return;
    }

    let output = execute_query(&load.directives, query_str);
    println!("{}", serde_json::to_string(&output).unwrap());
}

/// Batch command: load + multiple queries in one parse.
/// Usage: batch [filename] query1 query2 ...
fn cmd_batch(source: &str, filename: &str, queries: &[String]) {
    let load = load_source(source);

    // Build load output
    let entries: Vec<DirectiveJson> = load
        .directives
        .iter()
        .zip(load.directive_lines.iter())
        .map(|(d, &line)| directive_to_json(d, line, filename))
        .collect();

    let load_output = LoadOutput {
        entries,
        errors: load.errors.clone(),
        options: load.options,
        plugins: load.plugins,
        includes: load.includes,
    };

    // Execute queries (only if no parse errors)
    let query_outputs: Vec<QueryOutput> = if load.errors.is_empty() {
        queries
            .iter()
            .map(|q| execute_query(&load.directives, q))
            .collect()
    } else {
        // Return error for each query
        queries
            .iter()
            .map(|_| QueryOutput {
                columns: vec![],
                rows: vec![],
                errors: vec![Error {
                    message: "Cannot execute query: parse errors exist".to_string(),
                    line: None,
                    severity: "error".to_string(),
                }],
            })
            .collect()
    };

    let output = BatchOutput {
        load: load_output,
        queries: query_outputs,
    };
    println!("{}", serde_json::to_string(&output).unwrap());
}

fn cmd_version() {
    let output = VersionOutput {
        version: env!("CARGO_PKG_VERSION").to_string(),
    };
    println!("{}", serde_json::to_string(&output).unwrap());
}

fn cmd_help() {
    eprintln!("rustledger-ffi-py - Beancount FFI for Python/Fava via WASI");
    eprintln!();
    eprintln!("Usage: rustledger-ffi-py <command> [args...]");
    eprintln!();
    eprintln!("Commands:");
    eprintln!("  load [filename]      Load source from stdin, output entries + options + errors");
    eprintln!("  validate             Validate source from stdin");
    eprintln!("  query <bql>          Run BQL query on source from stdin");
    eprintln!("  batch [file] <bql>.. Load + run multiple queries in one parse (efficient)");
    eprintln!("  version              Show version");
    eprintln!("  help                 Show this help");
    eprintln!();
    eprintln!("All output is JSON to stdout.");
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  cat ledger.beancount | wasmtime rustledger-ffi-py.wasm load ledger.beancount");
    eprintln!("  cat ledger.beancount | wasmtime rustledger-ffi-py.wasm query \"BALANCES\"");
    eprintln!(
        "  cat ledger.beancount | wasmtime rustledger-ffi-py.wasm batch file.bc \"BALANCES\" \"SELECT account\""
    );
}

// =============================================================================
// Main
// =============================================================================

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        cmd_help();
        std::process::exit(1);
    }

    let command = &args[1];

    match command.as_str() {
        "version" => cmd_version(),
        "help" | "--help" | "-h" => cmd_help(),
        "load" | "validate" | "query" | "batch" => {
            // Read source from stdin
            let mut source = String::new();
            if let Err(e) = io::stdin().read_to_string(&mut source) {
                eprintln!("Error reading stdin: {e}");
                std::process::exit(1);
            }

            match command.as_str() {
                "load" => {
                    let filename = args.get(2).map_or("<stdin>", std::string::String::as_str);
                    cmd_load(&source, filename);
                }
                "validate" => cmd_validate(&source),
                "query" => {
                    if args.len() < 3 {
                        eprintln!("Error: query command requires BQL argument");
                        std::process::exit(1);
                    }
                    cmd_query(&source, &args[2]);
                }
                "batch" => {
                    let filename = args.get(2).map_or("<stdin>", std::string::String::as_str);
                    let queries: Vec<String> = args.iter().skip(3).cloned().collect();
                    cmd_batch(&source, filename, &queries);
                }
                _ => unreachable!(),
            }
        }
        _ => {
            eprintln!("Unknown command: {command}");
            cmd_help();
            std::process::exit(1);
        }
    }
}
