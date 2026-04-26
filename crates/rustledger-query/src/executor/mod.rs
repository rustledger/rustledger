//! BQL Query Executor.
//!
//! Executes parsed BQL queries against a set of Beancount directives.

mod functions;
mod types;

use types::AccountInfo;
pub use types::{
    Interval, IntervalUnit, PostingContext, QueryResult, Row, SourceLocation, Table, Value,
    WindowContext,
};

use std::sync::RwLock;

use rustc_hash::FxHashMap;

use regex::{Regex, RegexBuilder};
use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, InternedStr, Inventory, Metadata, NaiveDate, Position};
#[cfg(test)]
use rustledger_core::{MetaValue, Transaction};
use rustledger_loader::SourceMap;
use rustledger_parser::Spanned;

use crate::ast::{Expr, FromClause, FunctionCall, Query, Target};
use crate::error::QueryError;

/// Query executor.
pub struct Executor<'a> {
    /// All directives to query over.
    directives: &'a [Directive],
    /// Spanned directives (optional, for source location support).
    spanned_directives: Option<&'a [Spanned<Directive>]>,
    /// Account balances (built up during query).
    balances: FxHashMap<InternedStr, Inventory>,
    /// Price database for `VALUE()` conversions.
    price_db: crate::price::PriceDatabase,
    /// Target currency for `VALUE()` conversions.
    target_currency: Option<String>,
    /// Query date for price lookups (defaults to today).
    query_date: rustledger_core::NaiveDate,
    /// Cache for compiled regex patterns (`RwLock` for thread-safe parallel execution).
    regex_cache: RwLock<FxHashMap<String, Option<Regex>>>,
    /// Account info cache from Open/Close directives.
    account_info: FxHashMap<String, AccountInfo>,
    /// Source locations for directives (indexed by directive index).
    source_locations: Option<Vec<SourceLocation>>,
    /// In-memory tables created by CREATE TABLE.
    tables: FxHashMap<String, Table>,
}

// Sub-modules for focused functionality
mod aggregation;
mod evaluation;
mod execution;
mod operators;
mod sort;
mod window;

/// Default column names for `SELECT *` wildcard expansion.
/// This must match the order of values pushed in `evaluate_row()`.
pub const WILDCARD_COLUMNS: &[&str] =
    &["date", "flag", "payee", "narration", "account", "position"];

impl<'a> Executor<'a> {
    /// Create a new executor with the given directives.
    pub fn new(directives: &'a [Directive]) -> Self {
        let price_db = crate::price::PriceDatabase::from_directives(directives);

        // Build account info cache from Open/Close directives
        let mut account_info: FxHashMap<String, AccountInfo> = FxHashMap::default();
        for directive in directives {
            match directive {
                Directive::Open(open) => {
                    let account = open.account.to_string();
                    let info = account_info.entry(account).or_insert_with(|| AccountInfo {
                        open_date: None,
                        close_date: None,
                        open_meta: Metadata::default(),
                    });
                    info.open_date = Some(open.date);
                    info.open_meta.clone_from(&open.meta);
                }
                Directive::Close(close) => {
                    let account = close.account.to_string();
                    let info = account_info.entry(account).or_insert_with(|| AccountInfo {
                        open_date: None,
                        close_date: None,
                        open_meta: Metadata::default(),
                    });
                    info.close_date = Some(close.date);
                }
                _ => {}
            }
        }

        Self {
            directives,
            spanned_directives: None,
            balances: FxHashMap::default(),
            price_db,
            target_currency: None,
            query_date: jiff::Zoned::now().date(),
            regex_cache: RwLock::new(FxHashMap::default()),
            account_info,
            source_locations: None,
            tables: FxHashMap::default(),
        }
    }

    /// Create a new executor with source location support.
    ///
    /// This constructor accepts spanned directives and a source map, enabling
    /// the `filename`, `lineno`, and `location` columns in queries.
    pub fn new_with_sources(
        spanned_directives: &'a [Spanned<Directive>],
        source_map: &SourceMap,
    ) -> Self {
        // Build price database from spanned directives
        // Include both explicit prices and implicit prices from transactions
        let mut price_db = crate::price::PriceDatabase::new();
        for spanned in spanned_directives {
            match &spanned.value {
                Directive::Price(p) => {
                    price_db.add_price(p);
                }
                Directive::Transaction(txn) => {
                    price_db.add_implicit_prices_from_transaction(txn);
                }
                _ => {}
            }
        }
        price_db.sort_prices();

        // Build source locations
        let source_locations: Vec<SourceLocation> = spanned_directives
            .iter()
            .map(|spanned| {
                let file = source_map.get(spanned.file_id as usize);
                let (line, _col) = file.map_or((0, 0), |f| f.line_col(spanned.span.start));
                SourceLocation {
                    filename: file.map_or_else(String::new, |f| f.path.display().to_string()),
                    lineno: line,
                }
            })
            .collect();

        // Build account info cache from Open/Close directives
        let mut account_info: FxHashMap<String, AccountInfo> = FxHashMap::default();
        for spanned in spanned_directives {
            match &spanned.value {
                Directive::Open(open) => {
                    let account = open.account.to_string();
                    let info = account_info.entry(account).or_insert_with(|| AccountInfo {
                        open_date: None,
                        close_date: None,
                        open_meta: Metadata::default(),
                    });
                    info.open_date = Some(open.date);
                    info.open_meta.clone_from(&open.meta);
                }
                Directive::Close(close) => {
                    let account = close.account.to_string();
                    let info = account_info.entry(account).or_insert_with(|| AccountInfo {
                        open_date: None,
                        close_date: None,
                        open_meta: Metadata::default(),
                    });
                    info.close_date = Some(close.date);
                }
                _ => {}
            }
        }

        Self {
            directives: &[], // Empty - we use spanned_directives instead
            spanned_directives: Some(spanned_directives),
            balances: FxHashMap::default(),
            price_db,
            target_currency: None,
            query_date: jiff::Zoned::now().date(),
            regex_cache: RwLock::new(FxHashMap::default()),
            account_info,
            source_locations: Some(source_locations),
            tables: FxHashMap::default(),
        }
    }

    /// Get the source location for a directive by index.
    fn get_source_location(&self, directive_index: usize) -> Option<&SourceLocation> {
        self.source_locations
            .as_ref()
            .and_then(|locs| locs.get(directive_index))
    }

    /// Get or compile a regex pattern from the cache.
    ///
    /// Returns `Some(Regex)` if the pattern is valid, `None` if it's invalid.
    /// Invalid patterns are cached as `None` to avoid repeated compilation attempts.
    fn get_or_compile_regex(&self, pattern: &str) -> Option<Regex> {
        // Fast path: check read lock first
        {
            // Handle lock poisoning gracefully - if another thread panicked while holding
            // the lock, we can still recover the cached data via into_inner()
            let cache = match self.regex_cache.read() {
                Ok(guard) => guard,
                Err(poisoned) => poisoned.into_inner(),
            };
            if let Some(cached) = cache.get(pattern) {
                return cached.clone();
            }
        }
        // Slow path: compile and insert with write lock
        // Use case-insensitive matching to match Python beancount behavior
        let compiled = RegexBuilder::new(pattern)
            .case_insensitive(true)
            .build()
            .ok();
        let mut cache = match self.regex_cache.write() {
            Ok(guard) => guard,
            Err(poisoned) => poisoned.into_inner(),
        };
        // Double-check in case another thread inserted while we waited
        if let Some(cached) = cache.get(pattern) {
            return cached.clone();
        }
        cache.insert(pattern.to_string(), compiled.clone());
        compiled
    }

    /// Get or compile a regex pattern, returning an error if invalid.
    fn require_regex(&self, pattern: &str) -> Result<Regex, QueryError> {
        self.get_or_compile_regex(pattern)
            .ok_or_else(|| QueryError::Type(format!("invalid regex: {pattern}")))
    }

    /// Set the target currency for `VALUE()` conversions.
    pub fn set_target_currency(&mut self, currency: impl Into<String>) {
        self.target_currency = Some(currency.into());
    }

    /// Execute a query and return the results.
    ///
    /// # Errors
    ///
    /// Returns [`QueryError`] in the following cases:
    ///
    /// - [`QueryError::UnknownColumn`] - A referenced column name doesn't exist
    /// - [`QueryError::UnknownFunction`] - An unknown function is called
    /// - [`QueryError::InvalidArguments`] - Function called with wrong arguments
    /// - [`QueryError::Type`] - Type mismatch in expression (e.g., comparing string to number)
    /// - [`QueryError::Aggregation`] - Error in aggregate function (SUM, COUNT, etc.)
    /// - [`QueryError::Evaluation`] - General expression evaluation error
    pub fn execute(&mut self, query: &Query) -> Result<QueryResult, QueryError> {
        match query {
            Query::Select(select) => self.execute_select(select),
            Query::Journal(journal) => self.execute_journal(journal),
            Query::Balances(balances) => self.execute_balances(balances),
            Query::Print(print) => self.execute_print(print),
            Query::CreateTable(create) => self.execute_create_table(create),
            Query::Insert(insert) => self.execute_insert(insert),
        }
    }

    /// Execute a SELECT query.
    fn build_balances_with_filter(&mut self, from: Option<&FromClause>) -> Result<(), QueryError> {
        for directive in self.directives {
            if let Directive::Transaction(txn) = directive {
                // Apply FROM filter if present
                if let Some(from_clause) = from
                    && let Some(filter) = &from_clause.filter
                    && !self.evaluate_from_filter(filter, txn)?
                {
                    continue;
                }

                for posting in &txn.postings {
                    if let Some(units) = posting.amount() {
                        let balance = self.balances.entry(posting.account.clone()).or_default();

                        let pos = if let Some(cost_spec) = &posting.cost {
                            if let Some(cost) = cost_spec.resolve(units.number, txn.date) {
                                Position::with_cost(units.clone(), cost)
                            } else {
                                Position::simple(units.clone())
                            }
                        } else {
                            Position::simple(units.clone())
                        };
                        balance.add(pos);
                    }
                }
            }
        }
        Ok(())
    }

    /// Collect postings matching the FROM and WHERE clauses.
    fn collect_postings(
        &self,
        from: Option<&FromClause>,
        where_clause: Option<&Expr>,
    ) -> Result<Vec<PostingContext<'a>>, QueryError> {
        let mut postings = Vec::new();
        // Track running balance per account
        let mut running_balances: FxHashMap<InternedStr, Inventory> = FxHashMap::default();

        // Create an iterator over (directive_index, directive) pairs
        // Handle both spanned and unspanned directives
        let directive_iter: Vec<(usize, &Directive)> =
            if let Some(spanned) = self.spanned_directives {
                spanned
                    .iter()
                    .enumerate()
                    .map(|(i, s)| (i, &s.value))
                    .collect()
            } else {
                self.directives.iter().enumerate().collect()
            };

        for (directive_index, directive) in directive_iter {
            if let Directive::Transaction(txn) = directive {
                // Check FROM clause (transaction-level filter)
                if let Some(from) = from {
                    // Apply date filters
                    if let Some(open_date) = from.open_on
                        && txn.date < open_date
                    {
                        // Update balances but don't include in results
                        for posting in &txn.postings {
                            if let Some(units) = posting.amount() {
                                let balance =
                                    running_balances.entry(posting.account.clone()).or_default();
                                balance.add(Position::simple(units.clone()));
                            }
                        }
                        continue;
                    }
                    if let Some(close_date) = from.close_on
                        && txn.date > close_date
                    {
                        continue;
                    }
                    // Apply filter expression
                    if let Some(filter) = &from.filter
                        && !self.evaluate_from_filter(filter, txn)?
                    {
                        continue;
                    }
                }

                // Add postings with running balance
                for (i, posting) in txn.postings.iter().enumerate() {
                    // Update running balance for this account
                    if let Some(units) = posting.amount() {
                        let balance = running_balances.entry(posting.account.clone()).or_default();
                        balance.add(Position::simple(units.clone()));
                    }

                    let ctx = PostingContext {
                        transaction: txn,
                        posting_index: i,
                        balance: running_balances.get(&posting.account).cloned(),
                        directive_index: Some(directive_index),
                    };

                    // Check WHERE clause (posting-level filter)
                    if let Some(where_expr) = where_clause {
                        if self.evaluate_predicate(where_expr, &ctx)? {
                            postings.push(ctx);
                        }
                    } else {
                        postings.push(ctx);
                    }
                }
            }
        }

        Ok(postings)
    }
    fn evaluate_function(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        let name = func.name.to_uppercase();
        match name.as_str() {
            // Date functions
            "YEAR" | "MONTH" | "DAY" | "WEEKDAY" | "QUARTER" | "YMONTH" | "TODAY" => {
                self.eval_date_function(&name, func, ctx)
            }
            // Extended date functions
            "DATE" | "DATE_DIFF" | "DATE_ADD" | "DATE_TRUNC" | "DATE_PART" | "PARSE_DATE"
            | "DATE_BIN" | "INTERVAL" => self.eval_extended_date_function(&name, func, ctx),
            // String functions
            "LENGTH" | "UPPER" | "LOWER" | "SUBSTR" | "SUBSTRING" | "TRIM" | "STARTSWITH"
            | "ENDSWITH" | "GREP" | "GREPN" | "SUBST" | "SPLITCOMP" | "JOINSTR" | "MAXWIDTH" => {
                self.eval_string_function(&name, func, ctx)
            }
            // Account functions
            "PARENT" | "LEAF" | "ROOT" | "ACCOUNT_DEPTH" | "ACCOUNT_SORTKEY" => {
                self.eval_account_function(&name, func, ctx)
            }
            // Account metadata functions
            "OPEN_DATE" | "CLOSE_DATE" | "OPEN_META" => {
                self.eval_account_meta_function(&name, func, ctx)
            }
            // Math functions
            "ABS" | "NEG" | "ROUND" | "SAFEDIV" => self.eval_math_function(&name, func, ctx),
            // Amount/Position functions
            "NUMBER" | "CURRENCY" | "GETITEM" | "GET" | "UNITS" | "COST" | "WEIGHT" | "VALUE" => {
                self.eval_position_function(&name, func, ctx)
            }
            // Inventory functions
            "EMPTY" | "FILTER_CURRENCY" | "POSSIGN" => {
                self.eval_inventory_function(&name, func, ctx)
            }
            // Price functions
            "GETPRICE" => self.eval_getprice(func, ctx),
            // Utility functions
            "COALESCE" => self.eval_coalesce(func, ctx),
            "ONLY" => self.eval_only(func, ctx),
            // Metadata functions
            "META" | "ENTRY_META" | "ANY_META" | "POSTING_META" => {
                self.eval_meta_function(&name, func, ctx)
            }
            // Currency conversion
            "CONVERT" => self.eval_convert(func, ctx),
            // Type casting functions
            "INT" => self.eval_int(func, ctx),
            "DECIMAL" => self.eval_decimal(func, ctx),
            "STR" => self.eval_str(func, ctx),
            "BOOL" => self.eval_bool(func, ctx),
            // Aggregate functions return Null when evaluated on a single row
            // They're handled specially in aggregate evaluation
            "SUM" | "COUNT" | "MIN" | "MAX" | "FIRST" | "LAST" | "AVG" => Ok(Value::Null),
            _ => Err(QueryError::UnknownFunction(func.name.clone())),
        }
    }

    /// Evaluate a function with pre-evaluated arguments (for subquery context).
    fn evaluate_function_on_values(&self, name: &str, args: &[Value]) -> Result<Value, QueryError> {
        let name_upper = name.to_uppercase();
        match name_upper.as_str() {
            // Date functions
            "TODAY" => Ok(Value::Date(jiff::Zoned::now().date())),
            "YEAR" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Date(d) => Ok(Value::Integer(d.year().into())),
                    _ => Err(QueryError::Type("YEAR expects a date".to_string())),
                }
            }
            "MONTH" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Date(d) => Ok(Value::Integer(d.month().into())),
                    _ => Err(QueryError::Type("MONTH expects a date".to_string())),
                }
            }
            "DAY" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Date(d) => Ok(Value::Integer(d.day().into())),
                    _ => Err(QueryError::Type("DAY expects a date".to_string())),
                }
            }
            // String functions
            "LENGTH" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => Ok(Value::Integer(s.len() as i64)),
                    _ => Err(QueryError::Type("LENGTH expects a string".to_string())),
                }
            }
            "UPPER" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => Ok(Value::String(s.to_uppercase())),
                    _ => Err(QueryError::Type("UPPER expects a string".to_string())),
                }
            }
            "LOWER" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => Ok(Value::String(s.to_lowercase())),
                    _ => Err(QueryError::Type("LOWER expects a string".to_string())),
                }
            }
            "TRIM" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => Ok(Value::String(s.trim().to_string())),
                    _ => Err(QueryError::Type("TRIM expects a string".to_string())),
                }
            }
            // Math functions
            "ABS" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Number(n) => Ok(Value::Number(n.abs())),
                    Value::Integer(i) => Ok(Value::Integer(i.abs())),
                    _ => Err(QueryError::Type("ABS expects a number".to_string())),
                }
            }
            "ROUND" => {
                if args.is_empty() || args.len() > 2 {
                    return Err(QueryError::InvalidArguments(
                        "ROUND".to_string(),
                        "expected 1 or 2 arguments".to_string(),
                    ));
                }
                match &args[0] {
                    Value::Number(n) => {
                        let scale = if args.len() == 2 {
                            match &args[1] {
                                Value::Integer(i) => *i as u32,
                                _ => 0,
                            }
                        } else {
                            0
                        };
                        Ok(Value::Number(n.round_dp(scale)))
                    }
                    Value::Integer(i) => Ok(Value::Integer(*i)),
                    _ => Err(QueryError::Type("ROUND expects a number".to_string())),
                }
            }
            // Utility functions
            "COALESCE" => {
                for arg in args {
                    if !matches!(arg, Value::Null) {
                        return Ok(arg.clone());
                    }
                }
                Ok(Value::Null)
            }
            // Position/Amount functions
            "NUMBER" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Amount(a) => Ok(Value::Number(a.number)),
                    Value::Position(p) => Ok(Value::Number(p.units.number)),
                    Value::Number(n) => Ok(Value::Number(*n)),
                    Value::Integer(i) => Ok(Value::Number(Decimal::from(*i))),
                    Value::Inventory(inv) => {
                        // For inventory, only return a number if all positions share the same
                        // currency. Summing across different currencies is not meaningful.
                        let positions = inv.positions();
                        if positions.is_empty() {
                            return Ok(Value::Number(Decimal::ZERO));
                        }
                        let first_currency = &positions[0].units.currency;
                        let all_same_currency = positions
                            .iter()
                            .all(|p| &p.units.currency == first_currency);
                        if all_same_currency {
                            let total: Decimal = positions.iter().map(|p| p.units.number).sum();
                            Ok(Value::Number(total))
                        } else {
                            // Multiple currencies - return NULL rather than a meaningless sum
                            Ok(Value::Null)
                        }
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "NUMBER expects an amount, position, or inventory".to_string(),
                    )),
                }
            }
            "CURRENCY" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Amount(a) => Ok(Value::String(a.currency.to_string())),
                    Value::Position(p) => Ok(Value::String(p.units.currency.to_string())),
                    Value::Inventory(inv) => {
                        // Return the currency of the first position, or Null if empty
                        if let Some(pos) = inv.positions().first() {
                            Ok(Value::String(pos.units.currency.to_string()))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "CURRENCY expects an amount or position".to_string(),
                    )),
                }
            }
            "UNITS" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Position(p) => Ok(Value::Amount(p.units.clone())),
                    Value::Amount(a) => Ok(Value::Amount(a.clone())),
                    Value::Inventory(inv) => {
                        // Return inventory with just units (no cost info)
                        let mut units_inv = Inventory::new();
                        for pos in inv.positions() {
                            units_inv.add(Position::simple(pos.units.clone()));
                        }
                        Ok(Value::Inventory(Box::new(units_inv)))
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "UNITS expects a position or inventory".to_string(),
                    )),
                }
            }
            "COST" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Position(p) => {
                        if let Some(cost) = &p.cost {
                            // Preserve sign: buys give positive cost, sells give negative
                            let total = p.units.number * cost.number;
                            Ok(Value::Amount(Amount::new(total, cost.currency.clone())))
                        } else {
                            Ok(Value::Amount(p.units.clone()))
                        }
                    }
                    Value::Amount(a) => Ok(Value::Amount(a.clone())),
                    Value::Inventory(inv) => {
                        let mut total = Decimal::ZERO;
                        let mut currency: Option<InternedStr> = None;
                        for pos in inv.positions() {
                            if let Some(cost) = &pos.cost {
                                total += pos.units.number * cost.number;
                                if currency.is_none() {
                                    currency = Some(cost.currency.clone());
                                }
                            } else {
                                total += pos.units.number;
                                if currency.is_none() {
                                    currency = Some(pos.units.currency.clone());
                                }
                            }
                        }
                        if let Some(curr) = currency {
                            Ok(Value::Amount(Amount::new(total, curr)))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "COST expects a position or inventory".to_string(),
                    )),
                }
            }
            "VALUE" => {
                // Use shared VALUE implementation for consistent behavior.
                // See `eval_value` on PositionFunctions for the full signature
                // contract (DATE vs. currency-string dispatch).
                if args.is_empty() || args.len() > 2 {
                    return Err(QueryError::InvalidArguments(
                        "VALUE".to_string(),
                        "expected 1-2 arguments".to_string(),
                    ));
                }
                let (explicit_currency, at_date) = if args.len() == 2 {
                    match &args[1] {
                        Value::Date(d) => (None, Some(*d)),
                        Value::String(s) => (Some(s.as_str()), None),
                        Value::Null => {
                            return Err(QueryError::Type(
                                concat!(
                                    "VALUE: second argument evaluated to NULL; ",
                                    "expected a date or currency string ",
                                    "(this often means an aggregate expression couldn't ",
                                    "evaluate against an empty group — see issue #902)",
                                )
                                .to_string(),
                            ));
                        }
                        _ => {
                            return Err(QueryError::Type(
                                "VALUE second argument must be a date or currency string"
                                    .to_string(),
                            ));
                        }
                    }
                } else {
                    (None, None)
                };
                self.convert_to_market_value(&args[0], explicit_currency, at_date)
            }
            // Math functions
            "SAFEDIV" => {
                Self::require_args_count(&name_upper, args, 2)?;
                let (dividend, divisor) = (&args[0], &args[1]);
                match (dividend, divisor) {
                    (Value::Number(a), Value::Number(b)) => {
                        if b.is_zero() {
                            Ok(Value::Null)
                        } else {
                            Ok(Value::Number(a / b))
                        }
                    }
                    (Value::Integer(a), Value::Integer(b)) => {
                        if *b == 0 {
                            Ok(Value::Null)
                        } else {
                            Ok(Value::Number(Decimal::from(*a) / Decimal::from(*b)))
                        }
                    }
                    (Value::Number(a), Value::Integer(b)) => {
                        if *b == 0 {
                            Ok(Value::Null)
                        } else {
                            Ok(Value::Number(a / Decimal::from(*b)))
                        }
                    }
                    (Value::Integer(a), Value::Number(b)) => {
                        if b.is_zero() {
                            Ok(Value::Null)
                        } else {
                            Ok(Value::Number(Decimal::from(*a) / b))
                        }
                    }
                    (Value::Null, _) | (_, Value::Null) => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "SAFEDIV expects numeric arguments".to_string(),
                    )),
                }
            }
            "NEG" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Number(n) => Ok(Value::Number(-n)),
                    Value::Integer(i) => Ok(Value::Integer(-i)),
                    Value::Amount(a) => {
                        Ok(Value::Amount(Amount::new(-a.number, a.currency.clone())))
                    }
                    _ => Err(QueryError::Type(
                        "NEG expects a number or amount".to_string(),
                    )),
                }
            }
            // Account functions
            "ACCOUNT_SORTKEY" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => {
                        let type_index = Self::account_type_index(s);
                        Ok(Value::String(format!("{type_index}-{s}")))
                    }
                    _ => Err(QueryError::Type(
                        "ACCOUNT_SORTKEY expects an account string".to_string(),
                    )),
                }
            }
            "PARENT" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => {
                        if let Some(idx) = s.rfind(':') {
                            Ok(Value::String(s[..idx].to_string()))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    _ => Err(QueryError::Type(
                        "PARENT expects an account string".to_string(),
                    )),
                }
            }
            "LEAF" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => {
                        if let Some(idx) = s.rfind(':') {
                            Ok(Value::String(s[idx + 1..].to_string()))
                        } else {
                            Ok(Value::String(s.clone()))
                        }
                    }
                    _ => Err(QueryError::Type(
                        "LEAF expects an account string".to_string(),
                    )),
                }
            }
            "ROOT" => {
                if args.is_empty() || args.len() > 2 {
                    return Err(QueryError::InvalidArguments(
                        "ROOT".to_string(),
                        "expected 1 or 2 arguments".to_string(),
                    ));
                }
                let n = if args.len() == 2 {
                    match &args[1] {
                        Value::Integer(i) => *i as usize,
                        _ => 1,
                    }
                } else {
                    1
                };
                match &args[0] {
                    Value::String(s) => {
                        let parts: Vec<&str> = s.split(':').collect();
                        if n >= parts.len() {
                            Ok(Value::String(s.clone()))
                        } else {
                            Ok(Value::String(parts[..n].join(":")))
                        }
                    }
                    _ => Err(QueryError::Type(
                        "ROOT expects an account string".to_string(),
                    )),
                }
            }
            // ONLY function: extract single-currency amount from inventory
            "ONLY" => {
                Self::require_args_count(&name_upper, args, 2)?;
                let currency = match &args[0] {
                    Value::String(s) => s.clone(),
                    _ => {
                        return Err(QueryError::Type(
                            "ONLY: first argument must be a currency string".to_string(),
                        ));
                    }
                };
                match &args[1] {
                    Value::Inventory(inv) => {
                        let total = inv.units(&currency);
                        if total.is_zero() {
                            Ok(Value::Null)
                        } else {
                            Ok(Value::Amount(Amount::new(total, &currency)))
                        }
                    }
                    Value::Position(p) => {
                        if p.units.currency.as_str() == currency {
                            Ok(Value::Amount(p.units.clone()))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    Value::Amount(a) => {
                        if a.currency.as_str() == currency {
                            Ok(Value::Amount(a.clone()))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "ONLY: second argument must be an inventory, position, or amount"
                            .to_string(),
                    )),
                }
            }
            // GETPRICE function - needs price database
            "GETPRICE" => {
                if args.len() < 2 || args.len() > 3 {
                    return Err(QueryError::InvalidArguments(
                        "GETPRICE".to_string(),
                        "expected 2 or 3 arguments".to_string(),
                    ));
                }
                // Handle NULL arguments gracefully
                let base = match &args[0] {
                    Value::String(s) => s.clone(),
                    Value::Null => return Ok(Value::Null),
                    _ => {
                        return Err(QueryError::Type(
                            "GETPRICE: first argument must be a currency string".to_string(),
                        ));
                    }
                };
                let quote = match &args[1] {
                    Value::String(s) => s.clone(),
                    Value::Null => return Ok(Value::Null),
                    _ => {
                        return Err(QueryError::Type(
                            "GETPRICE: second argument must be a currency string".to_string(),
                        ));
                    }
                };
                let date = if args.len() == 3 {
                    match &args[2] {
                        Value::Date(d) => *d,
                        Value::Null => self.query_date,
                        _ => self.query_date,
                    }
                } else {
                    self.query_date
                };
                match self.price_db.get_price(&base, &quote, date) {
                    Some(price) => Ok(Value::Number(price)),
                    None => Ok(Value::Null),
                }
            }
            // Inventory functions
            "EMPTY" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Inventory(inv) => Ok(Value::Boolean(inv.is_empty())),
                    Value::Null => Ok(Value::Boolean(true)),
                    _ => Err(QueryError::Type("EMPTY expects an inventory".to_string())),
                }
            }
            "FILTER_CURRENCY" => {
                Self::require_args_count(&name_upper, args, 2)?;
                let currency = match &args[1] {
                    Value::String(s) => s.clone(),
                    _ => {
                        return Err(QueryError::Type(
                            "FILTER_CURRENCY expects (inventory, string)".to_string(),
                        ));
                    }
                };
                match &args[0] {
                    Value::Inventory(inv) => {
                        let filtered: Vec<Position> = inv
                            .positions()
                            .iter()
                            .filter(|p| p.units.currency.as_str() == currency)
                            .cloned()
                            .collect();
                        let mut new_inv = Inventory::new();
                        for pos in filtered {
                            new_inv.add(pos);
                        }
                        Ok(Value::Inventory(Box::new(new_inv)))
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "FILTER_CURRENCY expects (inventory, string)".to_string(),
                    )),
                }
            }
            "POSSIGN" => {
                Self::require_args_count(&name_upper, args, 2)?;
                let account_str = match &args[1] {
                    Value::String(s) => s.clone(),
                    _ => {
                        return Err(QueryError::Type(
                            "POSSIGN expects (amount, account_string)".to_string(),
                        ));
                    }
                };
                let first_component = account_str.split(':').next().unwrap_or("");
                let is_credit_normal =
                    matches!(first_component, "Liabilities" | "Equity" | "Income");
                match &args[0] {
                    Value::Amount(a) => {
                        let mut amt = a.clone();
                        if is_credit_normal {
                            amt.number = -amt.number;
                        }
                        Ok(Value::Amount(amt))
                    }
                    Value::Number(n) => {
                        let adjusted = if is_credit_normal { -n } else { *n };
                        Ok(Value::Number(adjusted))
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "POSSIGN expects (amount, account_string)".to_string(),
                    )),
                }
            }
            // CONVERT function - convert amounts/positions/inventories to target currency
            "CONVERT" => {
                if args.len() < 2 || args.len() > 3 {
                    return Err(QueryError::InvalidArguments(
                        "CONVERT".to_string(),
                        "expected 2 or 3 arguments: (value, currency[, date])".to_string(),
                    ));
                }

                let target_currency = match &args[1] {
                    Value::String(s) => s.clone(),
                    Value::Null => {
                        return Err(QueryError::Type(
                            concat!(
                                "CONVERT: second argument evaluated to NULL; ",
                                "expected a currency string ",
                                "(this often means an aggregate expression couldn't ",
                                "evaluate against an empty group — see issue #902)",
                            )
                            .to_string(),
                        ));
                    }
                    _ => {
                        return Err(QueryError::Type(
                            "CONVERT: second argument must be a currency string".to_string(),
                        ));
                    }
                };

                // Optional date argument
                let date: Option<rustledger_core::NaiveDate> = if args.len() == 3 {
                    match &args[2] {
                        Value::Date(d) => Some(*d),
                        Value::Null => None, // NULL date uses latest price
                        _ => {
                            return Err(QueryError::Type(
                                "CONVERT: third argument must be a date".to_string(),
                            ));
                        }
                    }
                } else {
                    None
                };

                // Helper closure to convert an amount
                let convert_amount = |amt: &Amount| -> Option<Amount> {
                    if let Some(d) = date {
                        self.price_db.convert(amt, &target_currency, d)
                    } else {
                        self.price_db.convert_latest(amt, &target_currency)
                    }
                };

                match &args[0] {
                    Value::Position(p) => {
                        if p.units.currency == target_currency {
                            Ok(Value::Amount(p.units.clone()))
                        } else if let Some(converted) = convert_amount(&p.units) {
                            Ok(Value::Amount(converted))
                        } else {
                            Ok(Value::Amount(p.units.clone()))
                        }
                    }
                    Value::Amount(a) => {
                        if a.currency == target_currency {
                            Ok(Value::Amount(a.clone()))
                        } else if let Some(converted) = convert_amount(a) {
                            Ok(Value::Amount(converted))
                        } else {
                            Ok(Value::Amount(a.clone()))
                        }
                    }
                    Value::Inventory(inv) => {
                        // Convert each position, keeping originals when no conversion available
                        // (matches Python beancount behavior)
                        let mut result = Inventory::default();
                        for pos in inv.positions() {
                            if pos.units.currency == target_currency {
                                result.add(Position::simple(pos.units.clone()));
                            } else if let Some(converted) = convert_amount(&pos.units) {
                                result.add(Position::simple(converted));
                            } else {
                                // No conversion available - keep original (Python beancount behavior)
                                result.add(Position::simple(pos.units.clone()));
                            }
                        }
                        // If result has single currency matching target, return as Amount
                        // If result is empty, return zero in target currency (issue #586)
                        let positions = result.positions();
                        if positions.is_empty() {
                            Ok(Value::Amount(Amount::new(Decimal::ZERO, &target_currency)))
                        } else if positions.len() == 1
                            && positions[0].units.currency == target_currency
                        {
                            Ok(Value::Amount(positions[0].units.clone()))
                        } else {
                            Ok(Value::Inventory(Box::new(result)))
                        }
                    }
                    Value::Number(n) => Ok(Value::Amount(Amount::new(*n, &target_currency))),
                    Value::Null => {
                        // For null values (e.g., empty sum), return zero in target currency
                        // This matches Python beancount behavior for empty balances (issue #586)
                        Ok(Value::Amount(Amount::new(Decimal::ZERO, &target_currency)))
                    }
                    _ => Err(QueryError::Type(
                        "CONVERT expects a position, amount, inventory, or number".to_string(),
                    )),
                }
            }
            // Type casting functions - use shared helpers
            "STR" => {
                Self::require_args_count(&name_upper, args, 1)?;
                Self::value_to_str(&args[0])
            }
            "INT" => {
                Self::require_args_count(&name_upper, args, 1)?;
                Self::value_to_int(&args[0])
            }
            "DECIMAL" => {
                Self::require_args_count(&name_upper, args, 1)?;
                Self::value_to_decimal(&args[0])
            }
            "BOOL" => {
                Self::require_args_count(&name_upper, args, 1)?;
                Self::value_to_bool(&args[0])
            }
            // Date functions for wrapping aggregates: QUARTER(MAX(date))
            "QUARTER" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Date(d) => Ok(Value::Integer(((d.month() - 1) / 3 + 1).into())),
                    _ => Err(QueryError::Type("QUARTER expects a date".to_string())),
                }
            }
            "WEEKDAY" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Date(d) => Ok(Value::Integer(
                        (d.weekday().to_monday_zero_offset() as u32).into(),
                    )),
                    _ => Err(QueryError::Type("WEEKDAY expects a date".to_string())),
                }
            }
            "YMONTH" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Date(d) => {
                        Ok(Value::String(format!("{:04}-{:02}", d.year(), d.month())))
                    }
                    _ => Err(QueryError::Type("YMONTH expects a date".to_string())),
                }
            }
            // String functions for wrapping aggregates
            "SUBSTR" | "SUBSTRING" => {
                if args.len() < 2 || args.len() > 3 {
                    return Err(QueryError::InvalidArguments(
                        name_upper,
                        "expected 2 or 3 arguments".to_string(),
                    ));
                }
                match (&args[0], &args[1], args.get(2)) {
                    (Value::String(s), Value::Integer(start), None) => {
                        let start = (*start).max(0) as usize;
                        let result: String = s.chars().skip(start).collect();
                        Ok(Value::String(result))
                    }
                    (Value::String(s), Value::Integer(start), Some(Value::Integer(len))) => {
                        let start = (*start).max(0) as usize;
                        let len = (*len).max(0) as usize;
                        let result: String = s.chars().skip(start).take(len).collect();
                        Ok(Value::String(result))
                    }
                    _ => Err(QueryError::Type(
                        "SUBSTR expects (string, int, [int])".to_string(),
                    )),
                }
            }
            "STARTSWITH" => {
                Self::require_args_count(&name_upper, args, 2)?;
                match (&args[0], &args[1]) {
                    (Value::String(s), Value::String(prefix)) => {
                        Ok(Value::Boolean(s.starts_with(prefix.as_str())))
                    }
                    _ => Err(QueryError::Type(
                        "STARTSWITH expects two strings".to_string(),
                    )),
                }
            }
            "ENDSWITH" => {
                Self::require_args_count(&name_upper, args, 2)?;
                match (&args[0], &args[1]) {
                    (Value::String(s), Value::String(suffix)) => {
                        Ok(Value::Boolean(s.ends_with(suffix.as_str())))
                    }
                    _ => Err(QueryError::Type("ENDSWITH expects two strings".to_string())),
                }
            }
            "MAXWIDTH" => {
                Self::require_args_count(&name_upper, args, 2)?;
                match (&args[0], &args[1]) {
                    (Value::String(s), Value::Integer(max)) => {
                        let n = *max as usize;
                        if s.chars().count() <= n {
                            Ok(Value::String(s.clone()))
                        } else if n <= 3 {
                            Ok(Value::String(s.chars().take(n).collect()))
                        } else {
                            let truncated: String = s.chars().take(n - 3).collect();
                            Ok(Value::String(format!("{truncated}...")))
                        }
                    }
                    _ => Err(QueryError::Type(
                        "MAXWIDTH expects (string, integer)".to_string(),
                    )),
                }
            }
            // Account function used in GROUP BY
            "ACCOUNT_DEPTH" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(s) => Ok(Value::Integer(s.matches(':').count() as i64 + 1)),
                    _ => Err(QueryError::Type(
                        "ACCOUNT_DEPTH expects an account string".to_string(),
                    )),
                }
            }
            // Position/amount getters
            "GETITEM" | "GET" => {
                Self::require_args_count(&name_upper, args, 2)?;
                match (&args[0], &args[1]) {
                    (Value::Inventory(inv), Value::String(currency)) => {
                        let amount = inv.units(currency);
                        if amount.is_zero() {
                            Ok(Value::Null)
                        } else {
                            Ok(Value::Amount(Amount::new(amount, currency.as_str())))
                        }
                    }
                    (Value::Null, _) => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "GETITEM expects (inventory, string)".to_string(),
                    )),
                }
            }
            "WEIGHT" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::Position(p) => {
                        if let Some(cost) = &p.cost {
                            let total = p.units.number * cost.number;
                            Ok(Value::Amount(Amount::new(total, cost.currency.clone())))
                        } else {
                            Ok(Value::Amount(p.units.clone()))
                        }
                    }
                    Value::Amount(a) => Ok(Value::Amount(a.clone())),
                    Value::Inventory(inv) => {
                        let mut result = Inventory::new();
                        for pos in inv.positions() {
                            if let Some(cost) = &pos.cost {
                                let total = pos.units.number * cost.number;
                                result.add(Position::simple(Amount::new(
                                    total,
                                    cost.currency.clone(),
                                )));
                            } else {
                                result.add(Position::simple(pos.units.clone()));
                            }
                        }
                        Ok(Value::Inventory(Box::new(result)))
                    }
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "WEIGHT expects a position, amount, or inventory".to_string(),
                    )),
                }
            }
            // Date: DATE_DIFF for wrapping aggregates like DATE_DIFF(MAX(date), MIN(date))
            "DATE_DIFF" => {
                Self::require_args_count(&name_upper, args, 2)?;
                match (&args[0], &args[1]) {
                    (Value::Date(d1), Value::Date(d2)) => Ok(Value::Integer(i64::from(
                        d1.since(*d2).unwrap_or_default().get_days(),
                    ))),
                    _ => Err(QueryError::Type("DATE_DIFF expects two dates".to_string())),
                }
            }
            // String: regex functions for wrapping aggregates
            "GREP" => {
                Self::require_args_count(&name_upper, args, 2)?;
                match (&args[0], &args[1]) {
                    (Value::String(pattern), Value::String(s)) => {
                        let re = regex::Regex::new(pattern).map_err(|e| {
                            QueryError::Type(format!("GREP: invalid regex '{pattern}': {e}"))
                        })?;
                        match re.find(s) {
                            Some(m) => Ok(Value::String(m.as_str().to_string())),
                            None => Ok(Value::Null),
                        }
                    }
                    // Null args → Null (e.g., narration is Null for non-transaction entries)
                    (Value::Null, _) | (_, Value::Null) => Ok(Value::Null),
                    _ => Err(QueryError::Type("GREP expects two strings".to_string())),
                }
            }
            "GREPN" => {
                Self::require_args_count(&name_upper, args, 3)?;
                let n = match &args[2] {
                    Value::Integer(i) => (*i).max(0) as usize,
                    Value::Number(n) => {
                        use rust_decimal::prelude::ToPrimitive;
                        n.to_usize().unwrap_or(0)
                    }
                    _ => {
                        return Err(QueryError::Type(
                            "GREPN: third argument must be an integer".to_string(),
                        ));
                    }
                };
                match (&args[0], &args[1]) {
                    (Value::String(pattern), Value::String(s)) => {
                        let re = regex::Regex::new(pattern).map_err(|e| {
                            QueryError::Type(format!("GREPN: invalid regex '{pattern}': {e}"))
                        })?;
                        match re.captures(s) {
                            Some(caps) => match caps.get(n) {
                                Some(m) => Ok(Value::String(m.as_str().to_string())),
                                None => Ok(Value::Null),
                            },
                            None => Ok(Value::Null),
                        }
                    }
                    (Value::Null, _) | (_, Value::Null) => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "GREPN expects (pattern, string, int)".to_string(),
                    )),
                }
            }
            "SUBST" => {
                Self::require_args_count(&name_upper, args, 3)?;
                match (&args[0], &args[1], &args[2]) {
                    (Value::String(pattern), Value::String(replacement), Value::String(s)) => {
                        let re = regex::Regex::new(pattern).map_err(|e| {
                            QueryError::Type(format!("SUBST: invalid regex '{pattern}': {e}"))
                        })?;
                        Ok(Value::String(
                            re.replace_all(s, replacement.as_str()).to_string(),
                        ))
                    }
                    _ => Err(QueryError::Type(
                        "SUBST expects (pattern, replacement, string)".to_string(),
                    )),
                }
            }
            "SPLITCOMP" => {
                Self::require_args_count(&name_upper, args, 3)?;
                let n = match &args[2] {
                    Value::Integer(i) => (*i).max(0) as usize,
                    Value::Number(n) => {
                        use rust_decimal::prelude::ToPrimitive;
                        n.to_usize().unwrap_or(0)
                    }
                    _ => {
                        return Err(QueryError::Type(
                            "SPLITCOMP: third argument must be an integer".to_string(),
                        ));
                    }
                };
                match (&args[0], &args[1]) {
                    (Value::String(s), Value::String(delim)) => {
                        let parts: Vec<&str> = s.split(delim.as_str()).collect();
                        match parts.get(n) {
                            Some(part) => Ok(Value::String((*part).to_string())),
                            None => Ok(Value::Null),
                        }
                    }
                    _ => Err(QueryError::Type(
                        "SPLITCOMP expects (string, delimiter, int)".to_string(),
                    )),
                }
            }
            "JOINSTR" => {
                let mut parts = Vec::new();
                for v in args {
                    match v {
                        Value::String(s) => parts.push(s.clone()),
                        Value::StringSet(ss) => parts.extend(ss.iter().cloned()),
                        Value::Integer(i) => parts.push(i.to_string()),
                        Value::Number(n) => parts.push(n.to_string()),
                        Value::Null => {}
                        _ => {}
                    }
                }
                Ok(Value::String(parts.join(",")))
            }
            // Account metadata functions — look up open/close info
            "OPEN_DATE" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(account) => Ok(self
                        .account_info
                        .get(account.as_str())
                        .and_then(|info| info.open_date)
                        .map_or(Value::Null, Value::Date)),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "OPEN_DATE expects an account string".to_string(),
                    )),
                }
            }
            "CLOSE_DATE" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(account) => Ok(self
                        .account_info
                        .get(account.as_str())
                        .and_then(|info| info.close_date)
                        .map_or(Value::Null, Value::Date)),
                    Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "CLOSE_DATE expects an account string".to_string(),
                    )),
                }
            }
            "OPEN_META" => {
                Self::require_args_count(&name_upper, args, 2)?;
                match (&args[0], &args[1]) {
                    (Value::String(account), Value::String(key)) => Ok(self
                        .account_info
                        .get(account.as_str())
                        .and_then(|info| info.open_meta.get(key))
                        .map_or(Value::Null, |mv| Self::meta_value_to_value(Some(mv)))),
                    (Value::Null, _) | (_, Value::Null) => Ok(Value::Null),
                    _ => Err(QueryError::Type(
                        "OPEN_META expects (account_string, key_string)".to_string(),
                    )),
                }
            }
            // Metadata access — returns Null in evaluate_function_on_values
            // because metadata is accessed via row context in eval_meta_on_table_row.
            // This branch handles edge cases where META is called outside table context.
            "META" | "ENTRY_META" | "ANY_META" | "POSTING_META" => {
                Self::require_args_count(&name_upper, args, 1)?;
                match &args[0] {
                    Value::String(_) | Value::Null => Ok(Value::Null),
                    _ => Err(QueryError::Type(format!(
                        "{name_upper}: argument must be a string key"
                    ))),
                }
            }
            // Aggregate functions return Null when evaluated on a single row
            "SUM" | "COUNT" | "MIN" | "MAX" | "FIRST" | "LAST" | "AVG" => Ok(Value::Null),
            _ => Err(QueryError::UnknownFunction(name.to_string())),
        }
    }

    /// Convert a `Metadata` map to a `Value::Object` for table storage.
    fn metadata_to_value(meta: &rustledger_core::Metadata) -> Value {
        if meta.is_empty() {
            return Value::Null;
        }
        let map: std::collections::BTreeMap<String, Value> = meta
            .iter()
            .map(|(k, v)| (k.clone(), Self::meta_value_to_value(Some(v))))
            .collect();
        Value::Object(Box::new(map))
    }

    /// Helper to require a specific number of arguments (for pre-evaluated args).
    fn require_args_count(name: &str, args: &[Value], expected: usize) -> Result<(), QueryError> {
        if args.len() != expected {
            return Err(QueryError::InvalidArguments(
                name.to_string(),
                format!("expected {} argument(s), got {}", expected, args.len()),
            ));
        }
        Ok(())
    }

    /// Helper to require a specific number of arguments.
    fn require_args(name: &str, func: &FunctionCall, expected: usize) -> Result<(), QueryError> {
        if func.args.len() != expected {
            return Err(QueryError::InvalidArguments(
                name.to_string(),
                format!("expected {expected} argument(s)"),
            ));
        }
        Ok(())
    }

    /// Convert a value to its market value.
    ///
    /// Shared `VALUE()` implementation used by both expression evaluation and
    /// the aggregate/subquery path in `evaluate_function_on_values`.
    ///
    /// # Arguments
    /// * `val` - The value to convert (`Position`, `Amount`, `Inventory`, or `Null`).
    /// * `explicit_currency` - Optional explicit target currency. When `None`,
    ///   the currency is inferred from the position's cost basis (Python
    ///   beancount compatibility) or falls back to the executor's
    ///   `target_currency` setting.
    /// * `at_date` - Optional valuation date. When `Some`, prices are looked up
    ///   with "on or before" semantics via [`price::PriceDatabase::convert`];
    ///   when `None`, the latest available price is used via
    ///   [`price::PriceDatabase::convert_latest`] (matches Python's
    ///   `value(position)` with `date=None`, which may use a future-dated price).
    ///
    /// # Returns
    /// - `Value::Amount` when conversion succeeds, or when the input is a
    ///   single `Position`/`Amount` that can't be priced (raw units returned).
    /// - `Value::Inventory` when no target currency can be determined and the
    ///   input is an `Inventory`.
    /// - `Value::Null` when the input is null.
    ///
    /// # Inventory caveat
    ///
    /// For `Value::Inventory` inputs with a determined target currency, this
    /// function returns a single `Value::Amount` summed in the target currency.
    /// Positions within the inventory that cannot be priced at `at_date` (or
    /// have no latest price) are silently dropped from the sum. This differs
    /// from Python beancount's `inventory.reduce(get_value, ...)`, which
    /// preserves unpriced positions as raw units in the resulting inventory.
    /// Reconciling this is tracked as a separate follow-up and is out of scope
    /// for #892.
    pub(crate) fn convert_to_market_value(
        &self,
        val: &Value,
        explicit_currency: Option<&str>,
        at_date: Option<NaiveDate>,
    ) -> Result<Value, QueryError> {
        // Determine target currency:
        // 1. Explicit argument takes precedence
        // 2. Infer from position's cost currency (beancount compatibility)
        // 3. Fall back to executor's target_currency setting
        let target_currency = if let Some(currency) = explicit_currency {
            currency.to_string()
        } else {
            // Try to infer from cost currency
            let inferred = match val {
                Value::Position(p) => p.cost.as_ref().map(|c| c.currency.to_string()),
                Value::Inventory(inv) => inv
                    .positions()
                    .iter()
                    .find_map(|p| p.cost.as_ref().map(|c| c.currency.to_string())),
                _ => None,
            };

            match inferred.or_else(|| self.target_currency.clone()) {
                Some(c) => c,
                None => {
                    // No currency can be determined — return value as-is
                    // (matches Python beancount behavior for positions without cost).
                    // Note: `at_date` is ignored here because there is nothing to
                    // convert without a target currency.
                    return match val {
                        Value::Position(p) => Ok(Value::Amount(p.units.clone())),
                        Value::Amount(a) => Ok(Value::Amount(a.clone())),
                        Value::Inventory(inv) => Ok(Value::Inventory(inv.clone())),
                        Value::Null => Ok(Value::Null),
                        _ => Err(QueryError::Type(
                            "VALUE expects a position, amount, or inventory".to_string(),
                        )),
                    };
                }
            }
        };

        // Price lookup matches Python beancount's semantics:
        // - When `at_date` is None, use the latest price (which may be future-dated).
        // - When `at_date` is Some, use the most recent price on or before that date;
        //   if no such price exists, the conversion silently returns the raw units.
        let convert_one = |amount: &Amount| -> Option<Amount> {
            match at_date {
                Some(d) => self.price_db.convert(amount, &target_currency, d),
                None => self.price_db.convert_latest(amount, &target_currency),
            }
        };

        match val {
            Value::Position(p) => {
                if p.units.currency == target_currency {
                    Ok(Value::Amount(p.units.clone()))
                } else if let Some(converted) = convert_one(&p.units) {
                    Ok(Value::Amount(converted))
                } else {
                    Ok(Value::Amount(p.units.clone()))
                }
            }
            Value::Amount(a) => {
                if a.currency == target_currency {
                    Ok(Value::Amount(a.clone()))
                } else if let Some(converted) = convert_one(a) {
                    Ok(Value::Amount(converted))
                } else {
                    Ok(Value::Amount(a.clone()))
                }
            }
            Value::Inventory(inv) => {
                let mut total = Decimal::ZERO;
                for pos in inv.positions() {
                    if pos.units.currency == target_currency {
                        total += pos.units.number;
                    } else if let Some(converted) = convert_one(&pos.units) {
                        total += converted.number;
                    }
                }
                Ok(Value::Amount(Amount::new(total, &target_currency)))
            }
            Value::Null => Ok(Value::Null),
            _ => Err(QueryError::Type(
                "VALUE expects a position, amount, or inventory".to_string(),
            )),
        }
    }

    /// Check if an expression is a window function.
    pub(super) const fn is_window_expr(expr: &Expr) -> bool {
        matches!(expr, Expr::Window(_))
    }

    /// Resolve column names from targets.
    fn resolve_column_names(&self, targets: &[Target]) -> Result<Vec<String>, QueryError> {
        let mut names = Vec::new();
        for (i, target) in targets.iter().enumerate() {
            if matches!(target.expr, Expr::Wildcard) {
                // Check wildcard BEFORE alias to catch `SELECT * AS alias` edge case
                if target.alias.is_some() {
                    return Err(QueryError::Evaluation(
                        "Cannot alias wildcard (*) - it expands to multiple columns".to_string(),
                    ));
                }
                // Expand wildcard using shared constant (must match evaluate_row expansion)
                names.extend(WILDCARD_COLUMNS.iter().map(|s| (*s).to_string()));
            } else if let Some(alias) = &target.alias {
                names.push(alias.clone());
            } else {
                names.push(self.expr_to_name(&target.expr, i));
            }
        }
        Ok(names)
    }

    /// Convert an expression to a column name.
    fn expr_to_name(&self, expr: &Expr, index: usize) -> String {
        match expr {
            Expr::Wildcard => "*".to_string(),
            Expr::Column(name) => name.clone(),
            Expr::Function(func) => func.name.clone(),
            Expr::Window(wf) => wf.name.clone(),
            _ => format!("col{index}"),
        }
    }

    /// Get a built-in system table by name.
    ///
    /// Built-in tables are virtual tables that provide access to ledger data:
    /// - `#prices` / `prices`: Price directives from the ledger
    /// - `#balances` / `balances`: Balance assertion directives from the ledger
    /// - `#commodities` / `commodities`: Commodity directives from the ledger
    /// - `#events` / `events`: Event directives from the ledger
    /// - `#notes` / `notes`: Note directives from the ledger
    /// - `#documents` / `documents`: Document directives from the ledger
    /// - `#accounts` / `accounts`: Open/Close directives paired by account
    /// - `#transactions` / `transactions`: Transaction directives from the ledger
    /// - `#entries` / `entries`: All directives with source location info
    /// - `#postings` / `postings`: All postings from transactions
    ///
    /// Both `#`-prefixed and non-prefixed names are supported for Python beancount
    /// compatibility (issue #632).
    ///
    /// Returns `None` if the table name is not a recognized built-in table.
    pub(super) fn get_builtin_table(&self, table_name: &str) -> Option<Table> {
        // Normalize table name: strip # prefix if present for Python beancount compatibility.
        // Both "#transactions" (rustledger) and "transactions" (beancount) work.
        // Using strip_prefix avoids allocation in the common case.
        let upper = table_name.to_uppercase();
        let normalized = upper.strip_prefix('#').unwrap_or(&upper);

        match normalized {
            "PRICES" => Some(self.build_prices_table()),
            "BALANCES" => Some(self.build_balances_table()),
            "COMMODITIES" => Some(self.build_commodities_table()),
            "EVENTS" => Some(self.build_events_table()),
            "NOTES" => Some(self.build_notes_table()),
            "DOCUMENTS" => Some(self.build_documents_table()),
            "ACCOUNTS" => Some(self.build_accounts_table()),
            "TRANSACTIONS" => Some(self.build_transactions_table()),
            "ENTRIES" => Some(self.build_entries_table()),
            "POSTINGS" => Some(self.build_postings_table()),
            _ => None,
        }
    }

    /// Build the #prices table from price directives.
    ///
    /// The table has columns: date, currency, amount
    /// - date: The date of the price directive
    /// - currency: The base currency being priced
    /// - amount: The price as an Amount (number + quote currency)
    fn build_prices_table(&self) -> Table {
        let columns = vec![
            "date".to_string(),
            "currency".to_string(),
            "amount".to_string(),
        ];
        let mut table = Table::new(columns);

        // Collect all price entries from the price database
        let mut entries: Vec<_> = self.price_db.iter_entries().collect();
        // Sort by (date, base_currency) for consistent, deterministic output
        entries.sort_by(|(currency_a, date_a, _, _), (currency_b, date_b, _, _)| {
            date_a.cmp(date_b).then_with(|| currency_a.cmp(currency_b))
        });

        for (base_currency, date, price_number, quote_currency) in entries {
            let row = vec![
                Value::Date(date),
                Value::String(base_currency.to_string()),
                Value::Amount(Amount::new(price_number, quote_currency)),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #balances table from balance assertion directives.
    ///
    /// The table has columns: date, account, amount
    /// - date: The date of the balance assertion
    /// - account: The account being balanced
    /// - amount: The expected balance amount
    fn build_balances_table(&self) -> Table {
        let columns = vec![
            "date".to_string(),
            "account".to_string(),
            "amount".to_string(),
        ];
        let mut table = Table::new(columns);

        // Collect balance directives from either spanned or unspanned directives
        let mut balances: Vec<_> = if let Some(spanned) = self.spanned_directives {
            spanned
                .iter()
                .filter_map(|s| {
                    if let Directive::Balance(b) = &s.value {
                        Some((b.date, b.account.as_ref(), b.amount.clone()))
                    } else {
                        None
                    }
                })
                .collect()
        } else {
            self.directives
                .iter()
                .filter_map(|d| {
                    if let Directive::Balance(b) = d {
                        Some((b.date, b.account.as_ref(), b.amount.clone()))
                    } else {
                        None
                    }
                })
                .collect()
        };

        // Sort by (date, account) for consistent, deterministic output
        balances.sort_by(|(date_a, account_a, _), (date_b, account_b, _)| {
            date_a.cmp(date_b).then_with(|| account_a.cmp(account_b))
        });

        for (date, account, amount) in balances {
            let row = vec![
                Value::Date(date),
                Value::String(account.to_string()),
                Value::Amount(amount),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #commodities table from commodity directives.
    ///
    /// The table has columns: date, name
    /// - date: The date of the commodity declaration
    /// - name: The currency/commodity code
    fn build_commodities_table(&self) -> Table {
        let columns = vec!["date".to_string(), "name".to_string()];
        let mut table = Table::new(columns);

        // Collect commodity directives from either spanned or unspanned directives
        let mut commodities: Vec<_> = if let Some(spanned) = self.spanned_directives {
            spanned
                .iter()
                .filter_map(|s| {
                    if let Directive::Commodity(c) = &s.value {
                        Some((c.date, c.currency.as_ref()))
                    } else {
                        None
                    }
                })
                .collect()
        } else {
            self.directives
                .iter()
                .filter_map(|d| {
                    if let Directive::Commodity(c) = d {
                        Some((c.date, c.currency.as_ref()))
                    } else {
                        None
                    }
                })
                .collect()
        };

        // Sort by (date, name) for consistent output
        commodities.sort_by(|(date_a, name_a), (date_b, name_b)| {
            date_a.cmp(date_b).then_with(|| name_a.cmp(name_b))
        });

        for (date, name) in commodities {
            let row = vec![Value::Date(date), Value::String(name.to_string())];
            table.add_row(row);
        }

        table
    }

    /// Build the #events table from event directives.
    ///
    /// The table has columns: date, type, description
    /// - date: The date of the event
    /// - type: The event type
    /// - description: The event value/description
    fn build_events_table(&self) -> Table {
        let columns = vec![
            "date".to_string(),
            "type".to_string(),
            "description".to_string(),
        ];
        let mut table = Table::new(columns);

        // Collect event directives
        let mut events: Vec<_> = if let Some(spanned) = self.spanned_directives {
            spanned
                .iter()
                .filter_map(|s| {
                    if let Directive::Event(e) = &s.value {
                        Some((e.date, e.event_type.as_str(), e.value.as_str()))
                    } else {
                        None
                    }
                })
                .collect()
        } else {
            self.directives
                .iter()
                .filter_map(|d| {
                    if let Directive::Event(e) = d {
                        Some((e.date, e.event_type.as_str(), e.value.as_str()))
                    } else {
                        None
                    }
                })
                .collect()
        };

        // Sort by (date, type) for consistent output
        events.sort_by(|(date_a, type_a, _), (date_b, type_b, _)| {
            date_a.cmp(date_b).then_with(|| type_a.cmp(type_b))
        });

        for (date, event_type, description) in events {
            let row = vec![
                Value::Date(date),
                Value::String(event_type.to_string()),
                Value::String(description.to_string()),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #notes table from note directives.
    ///
    /// The table has columns: date, account, comment
    /// - date: The date of the note
    /// - account: The account the note is attached to
    /// - comment: The note text
    fn build_notes_table(&self) -> Table {
        let columns = vec![
            "date".to_string(),
            "account".to_string(),
            "comment".to_string(),
        ];
        let mut table = Table::new(columns);

        // Collect note directives
        let mut notes: Vec<_> = if let Some(spanned) = self.spanned_directives {
            spanned
                .iter()
                .filter_map(|s| {
                    if let Directive::Note(n) = &s.value {
                        Some((n.date, n.account.as_ref(), n.comment.as_str()))
                    } else {
                        None
                    }
                })
                .collect()
        } else {
            self.directives
                .iter()
                .filter_map(|d| {
                    if let Directive::Note(n) = d {
                        Some((n.date, n.account.as_ref(), n.comment.as_str()))
                    } else {
                        None
                    }
                })
                .collect()
        };

        // Sort by (date, account) for consistent output
        notes.sort_by(|(date_a, account_a, _), (date_b, account_b, _)| {
            date_a.cmp(date_b).then_with(|| account_a.cmp(account_b))
        });

        for (date, account, comment) in notes {
            let row = vec![
                Value::Date(date),
                Value::String(account.to_string()),
                Value::String(comment.to_string()),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #documents table from document directives.
    ///
    /// The table has columns: date, account, filename, tags, links
    /// - date: The date of the document
    /// - account: The account the document is attached to
    /// - filename: The file path to the document
    /// - tags: The document tags (as a set)
    /// - links: The document links (as a set)
    fn build_documents_table(&self) -> Table {
        let columns = vec![
            "date".to_string(),
            "account".to_string(),
            "filename".to_string(),
            "tags".to_string(),
            "links".to_string(),
        ];
        let mut table = Table::new(columns);

        // Collect document directives
        let mut documents: Vec<_> = if let Some(spanned) = self.spanned_directives {
            spanned
                .iter()
                .filter_map(|s| {
                    if let Directive::Document(d) = &s.value {
                        Some((
                            d.date,
                            d.account.as_ref(),
                            d.path.as_str(),
                            &d.tags,
                            &d.links,
                        ))
                    } else {
                        None
                    }
                })
                .collect()
        } else {
            self.directives
                .iter()
                .filter_map(|d| {
                    if let Directive::Document(doc) = d {
                        Some((
                            doc.date,
                            doc.account.as_ref(),
                            doc.path.as_str(),
                            &doc.tags,
                            &doc.links,
                        ))
                    } else {
                        None
                    }
                })
                .collect()
        };

        // Sort by (date, account, filename) for consistent output
        documents.sort_by(
            |(date_a, account_a, file_a, _, _), (date_b, account_b, file_b, _, _)| {
                date_a
                    .cmp(date_b)
                    .then_with(|| account_a.cmp(account_b))
                    .then_with(|| file_a.cmp(file_b))
            },
        );

        for (date, account, filename, tags, links) in documents {
            let tags_vec: Vec<String> = tags.iter().map(ToString::to_string).collect();
            let links_vec: Vec<String> = links.iter().map(ToString::to_string).collect();
            let row = vec![
                Value::Date(date),
                Value::String(account.to_string()),
                Value::String(filename.to_string()),
                Value::StringSet(tags_vec),
                Value::StringSet(links_vec),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #accounts table from Open/Close directives.
    ///
    /// The table has columns: account, open, close, currencies, booking
    /// - account: The account name
    /// - open: The date the account was opened
    /// - close: The date the account was closed (NULL if still open)
    /// - currencies: Allowed currencies for the account
    /// - booking: Booking method (NULL if not specified)
    fn build_accounts_table(&self) -> Table {
        let columns = vec![
            "account".to_string(),
            "open".to_string(),
            "close".to_string(),
            "currencies".to_string(),
            "booking".to_string(),
        ];
        let mut table = Table::new(columns);

        // Build a map of account name -> (open_date, close_date, currencies, booking)
        let mut accounts: FxHashMap<
            &str,
            (
                Option<rustledger_core::NaiveDate>,
                Option<rustledger_core::NaiveDate>,
                Vec<String>,
                Option<&str>,
            ),
        > = FxHashMap::default();

        // Process directives
        let iter: Box<dyn Iterator<Item = &Directive>> =
            if let Some(spanned) = self.spanned_directives {
                Box::new(spanned.iter().map(|s| &s.value))
            } else {
                Box::new(self.directives.iter())
            };

        for directive in iter {
            match directive {
                Directive::Open(open) => {
                    let entry = accounts.entry(open.account.as_ref()).or_insert((
                        None,
                        None,
                        Vec::new(),
                        None,
                    ));
                    entry.0 = Some(open.date);
                    entry.2 = open.currencies.iter().map(ToString::to_string).collect();
                    entry.3 = open.booking.as_deref();
                }
                Directive::Close(close) => {
                    let entry = accounts.entry(close.account.as_ref()).or_insert((
                        None,
                        None,
                        Vec::new(),
                        None,
                    ));
                    entry.1 = Some(close.date);
                }
                _ => {}
            }
        }

        // Sort accounts by name for consistent output
        let mut account_list: Vec<_> = accounts.into_iter().collect();
        account_list.sort_by_key(|(a, _)| *a);

        for (account, (open_date, close_date, currencies, booking)) in account_list {
            let row = vec![
                Value::String(account.to_string()),
                open_date.map_or(Value::Null, Value::Date),
                close_date.map_or(Value::Null, Value::Date),
                Value::StringSet(currencies),
                booking.map_or(Value::Null, |b| Value::String(b.to_string())),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #transactions table from transaction directives.
    ///
    /// The table has columns: date, flag, payee, narration, tags, links, accounts
    /// - date: The transaction date
    /// - flag: The transaction flag (e.g., '*' or '!')
    /// - payee: The payee (NULL if not specified)
    /// - narration: The transaction description
    /// - tags: Transaction tags (as a set)
    /// - links: Transaction links (as a set)
    /// - accounts: Set of accounts involved in the transaction
    fn build_transactions_table(&self) -> Table {
        let columns = vec![
            "date".to_string(),
            "flag".to_string(),
            "payee".to_string(),
            "narration".to_string(),
            "tags".to_string(),
            "links".to_string(),
            "accounts".to_string(),
        ];
        let mut table = Table::new(columns);

        // Collect transaction directives
        let iter: Box<dyn Iterator<Item = &Directive>> =
            if let Some(spanned) = self.spanned_directives {
                Box::new(spanned.iter().map(|s| &s.value))
            } else {
                Box::new(self.directives.iter())
            };

        let mut transactions: Vec<_> = iter
            .filter_map(|d| {
                if let Directive::Transaction(txn) = d {
                    Some(txn)
                } else {
                    None
                }
            })
            .collect();

        // Sort by date for consistent output
        transactions.sort_by_key(|t| t.date);

        for txn in transactions {
            let tags: Vec<String> = txn.tags.iter().map(ToString::to_string).collect();
            let links: Vec<String> = txn.links.iter().map(ToString::to_string).collect();
            let mut accounts: Vec<String> = txn
                .postings
                .iter()
                .map(|p| p.account.to_string())
                .collect::<std::collections::HashSet<_>>()
                .into_iter()
                .collect();
            accounts.sort(); // Ensure deterministic ordering

            let row = vec![
                Value::Date(txn.date),
                Value::String(txn.flag.to_string()),
                txn.payee
                    .as_ref()
                    .map_or(Value::Null, |p| Value::String(p.to_string())),
                Value::String(txn.narration.to_string()),
                Value::StringSet(tags),
                Value::StringSet(links),
                Value::StringSet(accounts),
            ];
            table.add_row(row);
        }

        table
    }

    /// Build the #entries table from all directives.
    ///
    /// The table has columns: id, type, filename, lineno, date, flag, payee, narration, tags, links, accounts, `_entry_meta`
    /// This provides access to all directives with source location information.
    fn build_entries_table(&self) -> Table {
        let columns = vec![
            "id".to_string(),
            "type".to_string(),
            "filename".to_string(),
            "lineno".to_string(),
            "date".to_string(),
            "flag".to_string(),
            "payee".to_string(),
            "narration".to_string(),
            "tags".to_string(),
            "links".to_string(),
            "accounts".to_string(),
            "_entry_meta".to_string(),
        ];
        let mut table = Table::new(columns);

        // Process directives with optional source locations
        if let Some(spanned) = self.spanned_directives {
            for (idx, spanned_dir) in spanned.iter().enumerate() {
                let directive = &spanned_dir.value;
                let source_loc = self.get_source_location(idx);
                let row = self.directive_to_entry_row(idx, directive, source_loc);
                table.add_row(row);
            }
        } else {
            for (idx, directive) in self.directives.iter().enumerate() {
                let row = self.directive_to_entry_row(idx, directive, None);
                table.add_row(row);
            }
        }

        table
    }

    /// Convert a directive to a row for the #entries table.
    fn directive_to_entry_row(
        &self,
        idx: usize,
        directive: &Directive,
        source_loc: Option<&SourceLocation>,
    ) -> Vec<Value> {
        let type_name = match directive {
            Directive::Transaction(_) => "transaction",
            Directive::Balance(_) => "balance",
            Directive::Open(_) => "open",
            Directive::Close(_) => "close",
            Directive::Commodity(_) => "commodity",
            Directive::Pad(_) => "pad",
            Directive::Event(_) => "event",
            Directive::Query(_) => "query",
            Directive::Note(_) => "note",
            Directive::Document(_) => "document",
            Directive::Price(_) => "price",
            Directive::Custom(_) => "custom",
        };

        let date = match directive {
            Directive::Transaction(t) => Value::Date(t.date),
            Directive::Balance(b) => Value::Date(b.date),
            Directive::Open(o) => Value::Date(o.date),
            Directive::Close(c) => Value::Date(c.date),
            Directive::Commodity(c) => Value::Date(c.date),
            Directive::Pad(p) => Value::Date(p.date),
            Directive::Event(e) => Value::Date(e.date),
            Directive::Query(q) => Value::Date(q.date),
            Directive::Note(n) => Value::Date(n.date),
            Directive::Document(d) => Value::Date(d.date),
            Directive::Price(p) => Value::Date(p.date),
            Directive::Custom(c) => Value::Date(c.date),
        };

        let (flag, payee, narration, tags, links, accounts) =
            if let Directive::Transaction(txn) = directive {
                let tags: Vec<String> = txn.tags.iter().map(ToString::to_string).collect();
                let links: Vec<String> = txn.links.iter().map(ToString::to_string).collect();
                let mut accounts: Vec<String> = txn
                    .postings
                    .iter()
                    .map(|p| p.account.to_string())
                    .collect::<std::collections::HashSet<_>>()
                    .into_iter()
                    .collect();
                accounts.sort(); // Ensure deterministic ordering
                (
                    Value::String(txn.flag.to_string()),
                    txn.payee
                        .as_ref()
                        .map_or(Value::Null, |p| Value::String(p.to_string())),
                    Value::String(txn.narration.to_string()),
                    Value::StringSet(tags),
                    Value::StringSet(links),
                    Value::StringSet(accounts),
                )
            } else {
                (
                    Value::Null,
                    Value::Null,
                    Value::Null,
                    Value::StringSet(vec![]),
                    Value::StringSet(vec![]),
                    Value::StringSet(vec![]),
                )
            };

        let filename = source_loc.map_or(Value::Null, |loc| Value::String(loc.filename.clone()));
        let lineno = source_loc.map_or(Value::Null, |loc| Value::Integer(loc.lineno as i64));

        vec![
            Value::Integer(idx as i64), // id
            Value::String(type_name.to_string()),
            filename,
            lineno,
            date,
            flag,
            payee,
            narration,
            tags,
            links,
            accounts,
            // Hidden metadata column
            Self::metadata_to_value(directive.meta()),
        ]
    }

    /// Build the #postings table from transaction postings.
    ///
    /// Column schema matches Python beancount's `postings` table for compatibility.
    fn build_postings_table(&self) -> Table {
        let columns = vec![
            // Entry-level columns
            "type".to_string(),
            "id".to_string(),
            "date".to_string(),
            "year".to_string(),
            "month".to_string(),
            "day".to_string(),
            "filename".to_string(),
            "lineno".to_string(),
            "location".to_string(),
            // Transaction-level columns
            "flag".to_string(),
            "payee".to_string(),
            "narration".to_string(),
            "description".to_string(),
            "tags".to_string(),
            "links".to_string(),
            // Posting-level columns
            "posting_flag".to_string(),
            "account".to_string(),
            "other_accounts".to_string(),
            "number".to_string(),
            "currency".to_string(),
            "cost_number".to_string(),
            "cost_currency".to_string(),
            "cost_date".to_string(),
            "cost_label".to_string(),
            "position".to_string(),
            "price".to_string(),
            "weight".to_string(),
            "balance".to_string(),
            // Metadata and collection columns
            "meta".to_string(),
            "accounts".to_string(),
            // Hidden metadata columns for META/ENTRY_META functions
            "_entry_meta".to_string(),
            "_posting_meta".to_string(),
        ];
        let mut table = Table::new(columns);

        // Track running balances per account
        let mut running_balances: FxHashMap<InternedStr, Inventory> = FxHashMap::default();

        // Collect transactions with their directive indices for source location lookup
        let mut transactions: Vec<(usize, &rustledger_core::Transaction)> =
            if let Some(spanned) = self.spanned_directives {
                spanned
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, s)| {
                        if let Directive::Transaction(txn) = &s.value {
                            Some((idx, txn))
                        } else {
                            None
                        }
                    })
                    .collect()
            } else {
                self.directives
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, d)| {
                        if let Directive::Transaction(txn) = d {
                            Some((idx, txn))
                        } else {
                            None
                        }
                    })
                    .collect()
            };
        transactions.sort_by_key(|(_, t)| t.date);

        for (dir_idx, txn) in &transactions {
            // Pre-compute transaction-level values shared across all postings
            let source_loc = self.get_source_location(*dir_idx);
            let filename =
                source_loc.map_or(Value::Null, |loc| Value::String(loc.filename.clone()));
            let lineno = source_loc.map_or(Value::Null, |loc| Value::Integer(loc.lineno as i64));
            let location = source_loc.map_or(Value::Null, |loc| {
                Value::String(format!("{}:{}", loc.filename, loc.lineno))
            });

            let tags: Vec<String> = txn.tags.iter().map(ToString::to_string).collect();
            let links: Vec<String> = txn.links.iter().map(ToString::to_string).collect();

            let mut all_accounts: Vec<String> = txn
                .postings
                .iter()
                .map(|p| p.account.to_string())
                .collect::<std::collections::HashSet<_>>()
                .into_iter()
                .collect();
            all_accounts.sort();

            let description = match &txn.payee {
                Some(payee) => format!("{} | {}", payee, txn.narration),
                None => txn.narration.to_string(),
            };

            let year = Value::Integer(i64::from(txn.date.year()));
            let month = Value::Integer(i64::from(txn.date.month()));
            let day = Value::Integer(i64::from(txn.date.day()));

            for posting in &txn.postings {
                // Update running balance
                if let Some(units) = posting.amount() {
                    let balance = running_balances.entry(posting.account.clone()).or_default();
                    let pos = if let Some(cost_spec) = &posting.cost {
                        if let Some(cost) = cost_spec.resolve(units.number, txn.date) {
                            Position::with_cost(units.clone(), cost)
                        } else {
                            Position::simple(units.clone())
                        }
                    } else {
                        Position::simple(units.clone())
                    };
                    balance.add(pos);
                }

                // Extract posting data
                let (number, currency) = posting.amount().map_or((Value::Null, Value::Null), |a| {
                    (
                        Value::Number(a.number),
                        Value::String(a.currency.to_string()),
                    )
                });

                let (cost_number, cost_currency, cost_date, cost_label) = if let Some(cost_spec) =
                    &posting.cost
                {
                    let units = posting.amount();
                    if let Some(cost) = units.and_then(|u| cost_spec.resolve(u.number, txn.date)) {
                        (
                            Value::Number(cost.number),
                            Value::String(cost.currency.to_string()),
                            cost.date.map_or(Value::Null, Value::Date),
                            cost.label
                                .as_ref()
                                .map_or(Value::Null, |l| Value::String(l.clone())),
                        )
                    } else {
                        (Value::Null, Value::Null, Value::Null, Value::Null)
                    }
                } else {
                    (Value::Null, Value::Null, Value::Null, Value::Null)
                };

                let position_val = if let Some(units) = posting.amount() {
                    if let Some(cost_spec) = &posting.cost
                        && let Some(cost) = cost_spec.resolve(units.number, txn.date)
                    {
                        Value::Position(Box::new(Position::with_cost(units.clone(), cost)))
                    } else {
                        Value::Position(Box::new(Position::simple(units.clone())))
                    }
                } else {
                    Value::Null
                };

                let price_val = posting
                    .price
                    .as_ref()
                    .and_then(|p| p.amount())
                    .map_or(Value::Null, |a| Value::Amount(a.clone()));

                // Weight: the cost-converted amount used for transaction balancing.
                // With cost: units × cost (in cost currency)
                // With @ price: units × price (in price currency)
                // With @@ price: the total price directly (already in target currency)
                // Otherwise: units as-is
                let weight_val = if let Some(units) = posting.amount() {
                    if let Some(cost_spec) = &posting.cost {
                        if let Some(cost) = cost_spec.resolve(units.number, txn.date) {
                            Value::Amount(Amount::new(units.number * cost.number, cost.currency))
                        } else {
                            Value::Amount(units.clone())
                        }
                    } else if let Some(price_ann) = &posting.price {
                        if let Some(price_amt) = price_ann.amount() {
                            if price_ann.is_unit() {
                                // @ per-unit price: weight = units × price
                                Value::Amount(Amount::new(
                                    units.number * price_amt.number,
                                    price_amt.currency.clone(),
                                ))
                            } else {
                                // @@ total price: the amount IS the total weight
                                Value::Amount(price_amt.clone())
                            }
                        } else {
                            Value::Amount(units.clone())
                        }
                    } else {
                        Value::Amount(units.clone())
                    }
                } else {
                    Value::Null
                };

                let balance_val = running_balances
                    .get(&posting.account)
                    .map_or(Value::Null, |inv| Value::Inventory(Box::new(inv.clone())));

                // Other accounts: all accounts in the transaction except this posting's
                let other_accounts: Vec<String> = all_accounts
                    .iter()
                    .filter(|a| a.as_str() != posting.account.as_ref())
                    .cloned()
                    .collect();

                let posting_flag = posting
                    .flag
                    .map_or(Value::Null, |f| Value::String(f.to_string()));

                let row = vec![
                    // Entry-level
                    Value::String("transaction".to_string()),
                    Value::Integer(*dir_idx as i64),
                    Value::Date(txn.date),
                    year.clone(),
                    month.clone(),
                    day.clone(),
                    filename.clone(),
                    lineno.clone(),
                    location.clone(),
                    // Transaction-level
                    Value::String(txn.flag.to_string()),
                    txn.payee
                        .as_ref()
                        .map_or(Value::Null, |p| Value::String(p.to_string())),
                    Value::String(txn.narration.to_string()),
                    Value::String(description.clone()),
                    Value::StringSet(tags.clone()),
                    Value::StringSet(links.clone()),
                    // Posting-level
                    posting_flag,
                    Value::String(posting.account.to_string()),
                    Value::StringSet(other_accounts),
                    number,
                    currency,
                    cost_number,
                    cost_currency,
                    cost_date,
                    cost_label,
                    position_val,
                    price_val,
                    weight_val,
                    balance_val,
                    // Metadata and collection
                    Value::Metadata(Box::new(posting.meta.clone())),
                    Value::StringSet(all_accounts.clone()),
                    // Hidden metadata columns
                    Self::metadata_to_value(&txn.meta),
                    Self::metadata_to_value(&posting.meta),
                ];
                table.add_row(row);
            }
        }

        table
    }
}
#[cfg(test)]
mod tests {
    use super::types::{hash_row, hash_single_value};
    use super::*;
    use crate::parse;
    use rust_decimal_macros::dec;
    use rustledger_core::Posting;

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        rustledger_core::naive_date(year, month, day).unwrap()
    }

    fn sample_directives() -> Vec<Directive> {
        vec![
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Coffee")
                    .with_flag('*')
                    .with_payee("Coffee Shop")
                    .with_posting(Posting::new(
                        "Expenses:Food:Coffee",
                        Amount::new(dec!(5.00), "USD"),
                    ))
                    .with_posting(Posting::new(
                        "Assets:Bank:Checking",
                        Amount::new(dec!(-5.00), "USD"),
                    )),
            ),
            Directive::Transaction(
                Transaction::new(date(2024, 1, 16), "Groceries")
                    .with_flag('*')
                    .with_payee("Supermarket")
                    .with_posting(Posting::new(
                        "Expenses:Food:Groceries",
                        Amount::new(dec!(50.00), "USD"),
                    ))
                    .with_posting(Posting::new(
                        "Assets:Bank:Checking",
                        Amount::new(dec!(-50.00), "USD"),
                    )),
            ),
        ]
    }

    #[test]
    fn test_simple_select() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        let query = parse("SELECT date, account").unwrap();
        let result = executor.execute(&query).unwrap();

        assert_eq!(result.columns, vec!["date", "account"]);
        assert_eq!(result.len(), 4); // 2 transactions × 2 postings
    }

    #[test]
    fn test_where_clause() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        let query = parse("SELECT account WHERE account ~ \"Expenses:\"").unwrap();
        let result = executor.execute(&query).unwrap();

        assert_eq!(result.len(), 2); // Only expense postings
    }

    #[test]
    fn test_balances() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        let query = parse("BALANCES").unwrap();
        let result = executor.execute(&query).unwrap();

        assert_eq!(result.columns, vec!["account", "balance"]);
        assert!(result.len() >= 3); // At least 3 accounts
    }

    #[test]
    fn test_account_functions() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Test LEAF function
        let query = parse("SELECT DISTINCT LEAF(account) WHERE account ~ \"Expenses:\"").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 2); // Coffee, Groceries

        // Test ROOT function
        let query = parse("SELECT DISTINCT ROOT(account)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 2); // Expenses, Assets

        // Test PARENT function
        let query = parse("SELECT DISTINCT PARENT(account) WHERE account ~ \"Expenses:\"").unwrap();
        let result = executor.execute(&query).unwrap();
        assert!(!result.is_empty()); // At least "Expenses:Food"
    }

    #[test]
    fn test_min_max_aggregate() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Test MIN(date)
        let query = parse("SELECT MIN(date)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 15)));

        // Test MAX(date)
        let query = parse("SELECT MAX(date)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 16)));
    }

    #[test]
    fn test_order_by() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        let query = parse("SELECT date, account ORDER BY date DESC").unwrap();
        let result = executor.execute(&query).unwrap();

        // Should have all postings, ordered by date descending
        assert_eq!(result.len(), 4);
        // First row should be from 2024-01-16 (later date)
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 16)));
    }

    #[test]
    fn test_hash_value_all_variants() {
        use rustledger_core::{Cost, Inventory, Position};

        // Test that all Value variants can be hashed without panic
        let values = vec![
            Value::String("test".to_string()),
            Value::Number(dec!(123.45)),
            Value::Integer(42),
            Value::Date(date(2024, 1, 15)),
            Value::Boolean(true),
            Value::Boolean(false),
            Value::Amount(Amount::new(dec!(100), "USD")),
            Value::Position(Box::new(Position::simple(Amount::new(dec!(10), "AAPL")))),
            Value::Position(Box::new(Position::with_cost(
                Amount::new(dec!(10), "AAPL"),
                Cost::new(dec!(150), "USD"),
            ))),
            Value::Inventory(Box::new(Inventory::new())),
            Value::StringSet(vec!["tag1".to_string(), "tag2".to_string()]),
            Value::Null,
        ];

        // Hash each value and verify no panic
        for value in &values {
            let hash = hash_single_value(value);
            assert!(hash != 0 || matches!(value, Value::Null));
        }

        // Test that different values produce different hashes (usually)
        let hash1 = hash_single_value(&Value::String("a".to_string()));
        let hash2 = hash_single_value(&Value::String("b".to_string()));
        assert_ne!(hash1, hash2);

        // Test that same values produce same hashes
        let hash3 = hash_single_value(&Value::Integer(42));
        let hash4 = hash_single_value(&Value::Integer(42));
        assert_eq!(hash3, hash4);
    }

    #[test]
    fn test_hash_row_distinct() {
        // Test hash_row for DISTINCT deduplication
        let row1 = vec![Value::String("a".to_string()), Value::Integer(1)];
        let row2 = vec![Value::String("a".to_string()), Value::Integer(1)];
        let row3 = vec![Value::String("b".to_string()), Value::Integer(1)];

        assert_eq!(hash_row(&row1), hash_row(&row2));
        assert_ne!(hash_row(&row1), hash_row(&row3));
    }

    #[test]
    fn test_string_set_hash_order_independent() {
        // StringSet hash should be order-independent
        let set1 = Value::StringSet(vec!["a".to_string(), "b".to_string(), "c".to_string()]);
        let set2 = Value::StringSet(vec!["c".to_string(), "a".to_string(), "b".to_string()]);
        let set3 = Value::StringSet(vec!["b".to_string(), "c".to_string(), "a".to_string()]);

        let hash1 = hash_single_value(&set1);
        let hash2 = hash_single_value(&set2);
        let hash3 = hash_single_value(&set3);

        assert_eq!(hash1, hash2);
        assert_eq!(hash2, hash3);
    }

    #[test]
    fn test_inventory_hash_includes_cost() {
        use rustledger_core::{Cost, Inventory, Position};

        // Two inventories with same units but different costs should hash differently
        let mut inv1 = Inventory::new();
        inv1.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(100), "USD"),
        ));

        let mut inv2 = Inventory::new();
        inv2.add(Position::with_cost(
            Amount::new(dec!(10), "AAPL"),
            Cost::new(dec!(200), "USD"),
        ));

        let hash1 = hash_single_value(&Value::Inventory(Box::new(inv1)));
        let hash2 = hash_single_value(&Value::Inventory(Box::new(inv2)));

        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_distinct_deduplication() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Without DISTINCT - should have duplicates (same flag '*' for all)
        let query = parse("SELECT flag").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 4); // One per posting, all have flag '*'

        // With DISTINCT - should deduplicate
        let query = parse("SELECT DISTINCT flag").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 1); // Deduplicated to 1 (all '*')
    }

    #[test]
    fn test_limit_clause() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Test LIMIT restricts result count
        let query = parse("SELECT date, account LIMIT 2").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 2);

        // Test LIMIT 0 returns empty
        let query = parse("SELECT date LIMIT 0").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 0);

        // Test LIMIT larger than result set returns all
        let query = parse("SELECT date LIMIT 100").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 4);
    }

    #[test]
    fn test_group_by_with_count() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Group by account root and count postings
        let query = parse("SELECT ROOT(account), COUNT(account) GROUP BY ROOT(account)").unwrap();
        let result = executor.execute(&query).unwrap();

        assert_eq!(result.columns.len(), 2);
        // Should have 2 groups: Assets and Expenses
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_count_aggregate() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Count all postings
        let query = parse("SELECT COUNT(account)").unwrap();
        let result = executor.execute(&query).unwrap();

        assert_eq!(result.len(), 1);
        assert_eq!(result.rows[0][0], Value::Integer(4));

        // Count with GROUP BY
        let query = parse("SELECT ROOT(account), COUNT(account) GROUP BY ROOT(account)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 2); // Assets, Expenses
    }

    #[test]
    fn test_count_wildcard_direct() {
        // count(*) in the direct postings path (no FROM tablename)
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Pure count(*) with no GROUP BY
        let query = parse("SELECT count(*)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(result.rows[0][0], Value::Integer(4)); // 4 postings total

        // count(*) with GROUP BY in direct mode
        // Sample: Expenses:Food:Coffee (1), Assets:Bank:Checking (2), Expenses:Food:Groceries (1)
        let query = parse("SELECT account, count(*) GROUP BY account").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 3); // 3 distinct accounts
    }

    #[test]
    fn test_count_wildcard_from_postings_table() {
        // count(*) against the named postings table: FROM postings
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // GROUP BY with count(*)
        let query = parse("SELECT account, count(*) FROM postings GROUP BY account").unwrap();
        let result = executor.execute(&query).unwrap();
        // 3 distinct accounts: Expenses:Food:Coffee, Assets:Bank:Checking, Expenses:Food:Groceries
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn test_count_wildcard_from_entries_table() {
        // count(*) against the named entries table: FROM entries
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        let query = parse("SELECT type, count(*) FROM entries GROUP BY type").unwrap();
        let result = executor.execute(&query).unwrap();
        // Only transactions in the sample data
        assert_eq!(result.len(), 1);
        assert_eq!(result.rows[0][0], Value::String("transaction".to_string()));
        assert_eq!(result.rows[0][1], Value::Integer(2));
    }

    #[test]
    fn test_count_wildcard_having() {
        // count(*) in HAVING clause on postings table
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Accounts with more than 0 postings (all 3 distinct accounts)
        let query = parse(
            "SELECT account, count(*) AS cnt FROM postings GROUP BY account HAVING count(*) > 0",
        )
        .unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 3);

        // Accounts with more than 1 posting (only Assets:Bank:Checking has 2)
        let query = parse(
            "SELECT account, count(*) AS cnt FROM postings GROUP BY account HAVING count(*) > 1",
        )
        .unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(
            result.rows[0][0],
            Value::String("Assets:Bank:Checking".to_string())
        );
        assert_eq!(result.rows[0][1], Value::Integer(2));
    }

    #[test]
    fn test_journal_query() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // JOURNAL for Expenses account
        let query = parse("JOURNAL \"Expenses\"").unwrap();
        let result = executor.execute(&query).unwrap();

        // Should have columns for journal output
        assert!(result.columns.contains(&"account".to_string()));
        // Should only show expense account entries
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_print_query() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // PRINT outputs formatted directives
        let query = parse("PRINT").unwrap();
        let result = executor.execute(&query).unwrap();

        // PRINT returns single column "directive" with formatted output
        assert_eq!(result.columns.len(), 1);
        assert_eq!(result.columns[0], "directive");
        // Should have one row per directive (2 transactions)
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_empty_directives() {
        let directives: Vec<Directive> = vec![];
        let mut executor = Executor::new(&directives);

        // SELECT on empty directives
        let query = parse("SELECT date, account").unwrap();
        let result = executor.execute(&query).unwrap();
        assert!(result.is_empty());

        // BALANCES on empty directives
        let query = parse("BALANCES").unwrap();
        let result = executor.execute(&query).unwrap();
        assert!(result.is_empty());
    }

    #[test]
    fn test_comparison_operators() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Less than comparison on dates
        let query = parse("SELECT date WHERE date < 2024-01-16").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 2); // First transaction postings

        // Greater than comparison on year
        let query = parse("SELECT date WHERE year > 2023").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 4); // All 2024 postings

        // Equality comparison on day
        let query = parse("SELECT account WHERE day = 15").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 2); // First transaction postings (Jan 15)
    }

    #[test]
    fn test_logical_operators() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // AND operator
        let query = parse("SELECT account WHERE account ~ \"Expenses\" AND day > 14").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 2); // Expense postings on Jan 15 and 16

        // OR operator
        let query = parse("SELECT account WHERE day = 15 OR day = 16").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 4); // All postings (both days)
    }

    #[test]
    fn test_arithmetic_expressions() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Negation on integer
        let query = parse("SELECT -day WHERE day = 15").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 2);
        // Day 15 negated should be -15
        for row in &result.rows {
            if let Value::Integer(n) = &row[0] {
                assert_eq!(*n, -15);
            }
        }
    }

    #[test]
    fn test_first_last_aggregates() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // FIRST aggregate
        let query = parse("SELECT FIRST(date)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 15)));

        // LAST aggregate
        let query = parse("SELECT LAST(date)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 16)));
    }

    #[test]
    fn test_wildcard_select() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // SELECT * returns all postings with expanded column names
        let query = parse("SELECT *").unwrap();
        let result = executor.execute(&query).unwrap();

        // Wildcard expands to default column names (fixes issue #577)
        assert_eq!(
            result.columns,
            vec!["date", "flag", "payee", "narration", "account", "position"]
        );
        // Each row has expanded values matching the column names
        assert_eq!(result.len(), 4);
        assert_eq!(result.rows[0].len(), 6);
    }

    #[test]
    fn test_wildcard_alias_rejected() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // SELECT * AS alias should fail - wildcard expands to multiple columns
        let query = parse("SELECT * AS data").unwrap();
        let result = executor.execute(&query);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("Cannot alias wildcard"),
            "Expected wildcard alias error, got: {err}"
        );
    }

    #[test]
    fn test_query_result_methods() {
        let mut result = QueryResult::new(vec!["col1".to_string(), "col2".to_string()]);

        // Initially empty
        assert!(result.is_empty());
        assert_eq!(result.len(), 0);

        // Add rows
        result.add_row(vec![Value::Integer(1), Value::String("a".to_string())]);
        assert!(!result.is_empty());
        assert_eq!(result.len(), 1);

        result.add_row(vec![Value::Integer(2), Value::String("b".to_string())]);
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_type_cast_functions() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Test INT function
        let query = parse("SELECT int(5.7)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Integer(5));

        // Test DECIMAL function
        let query = parse("SELECT decimal(42)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Number(dec!(42)));

        // Test STR function
        let query = parse("SELECT str(123)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::String("123".to_string()));

        // Test BOOL function
        let query = parse("SELECT bool(1)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Boolean(true));

        let query = parse("SELECT bool(0)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Boolean(false));
    }

    /// Test that type casting functions work in aggregate context (issue #630).
    #[test]
    fn test_type_casting_in_aggregate_context() {
        let txn1 = Transaction::new(date(2024, 1, 15), "Item 1")
            .with_flag('*')
            .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(10), "USD")))
            .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-10), "USD")));

        let txn2 = Transaction::new(date(2024, 1, 16), "Item 2")
            .with_flag('*')
            .with_posting(Posting::new("Expenses:Food", Amount::new(dec!(20), "USD")))
            .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-20), "USD")));

        let directives = vec![Directive::Transaction(txn1), Directive::Transaction(txn2)];
        let mut executor = Executor::new(&directives);

        // Test STR wrapping an aggregate - this was the issue in #630
        // Each account has 2 postings summed: Expenses:Food = 30, Assets:Cash = -30
        let query =
            parse("SELECT account, str(sum(number(units))) GROUP BY account ORDER BY account")
                .unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows.len(), 2);
        // Verify actual string values
        assert_eq!(result.rows[0][0], Value::String("Assets:Cash".to_string()));
        assert_eq!(result.rows[0][1], Value::String("-30".to_string()));
        assert_eq!(
            result.rows[1][0],
            Value::String("Expenses:Food".to_string())
        );
        assert_eq!(result.rows[1][1], Value::String("30".to_string()));

        // Test INT in aggregate context - verify truncation works
        let query =
            parse("SELECT account, int(sum(number(units))) GROUP BY account ORDER BY account")
                .unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][1], Value::Integer(-30));
        assert_eq!(result.rows[1][1], Value::Integer(30));

        // Test DECIMAL in aggregate context - verify count conversion
        let query =
            parse("SELECT account, decimal(count(*)) GROUP BY account ORDER BY account").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][1], Value::Number(dec!(2))); // 2 postings per account
        assert_eq!(result.rows[1][1], Value::Number(dec!(2)));

        // Test BOOL in aggregate context - count > 0 should be true
        let query =
            parse("SELECT account, bool(count(*)) GROUP BY account ORDER BY account").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][1], Value::Boolean(true));
        assert_eq!(result.rows[1][1], Value::Boolean(true));
    }

    /// Test INT truncation behavior with decimals.
    #[test]
    fn test_int_truncation() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Test INT truncates toward zero (not floor/ceil)
        let query = parse("SELECT int(5.7)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Integer(5));

        let query = parse("SELECT int(-5.7)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Integer(-5));

        let query = parse("SELECT int(0.999)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Integer(0));
    }

    /// Test type casting error cases.
    #[test]
    fn test_type_casting_errors() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // INT with non-numeric string should error
        let query = parse("SELECT int('not-a-number')").unwrap();
        let result = executor.execute(&query);
        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .to_string()
                .contains("cannot parse 'not-a-number'")
        );

        // DECIMAL with invalid string should error
        let query = parse("SELECT decimal('invalid')").unwrap();
        let result = executor.execute(&query);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("cannot parse"));

        // BOOL with unrecognized string should error
        let query = parse("SELECT bool('maybe')").unwrap();
        let result = executor.execute(&query);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("cannot parse"));
    }

    #[test]
    fn test_meta_functions() {
        // Create directives with metadata
        let mut txn_meta: Metadata = Metadata::default();
        txn_meta.insert(
            "source".to_string(),
            MetaValue::String("bank_import".to_string()),
        );

        let mut posting_meta: Metadata = Metadata::default();
        posting_meta.insert(
            "category".to_string(),
            MetaValue::String("food".to_string()),
        );

        let txn = Transaction {
            date: date(2024, 1, 15),
            flag: '*',
            payee: Some("Coffee Shop".into()),
            narration: "Coffee".into(),
            tags: vec![],
            links: vec![],
            meta: txn_meta,
            postings: vec![
                Posting {
                    account: "Expenses:Food".into(),
                    units: Some(rustledger_core::IncompleteAmount::Complete(Amount::new(
                        dec!(5),
                        "USD",
                    ))),
                    cost: None,
                    price: None,
                    flag: None,
                    meta: posting_meta,
                    comments: Vec::new(),
                    trailing_comments: Vec::new(),
                },
                Posting::new("Assets:Cash", Amount::new(dec!(-5), "USD")),
            ],
            trailing_comments: Vec::new(),
        };

        let directives = vec![Directive::Transaction(txn)];
        let mut executor = Executor::new(&directives);

        // Test META (posting metadata)
        let query = parse("SELECT meta('category') WHERE account ~ 'Expenses'").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::String("food".to_string()));

        // Test ENTRY_META (transaction metadata)
        let query = parse("SELECT entry_meta('source') WHERE account ~ 'Expenses'").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::String("bank_import".to_string()));

        // Test ANY_META (falls back to txn meta when posting meta missing)
        let query = parse("SELECT any_meta('source') WHERE account ~ 'Expenses'").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::String("bank_import".to_string()));

        // Test ANY_META (uses posting meta when available)
        let query = parse("SELECT any_meta('category') WHERE account ~ 'Expenses'").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::String("food".to_string()));

        // Test missing meta returns NULL
        let query = parse("SELECT meta('nonexistent') WHERE account ~ 'Expenses'").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Null);
    }

    #[test]
    fn test_convert_function() {
        // Create directives with price information
        let price = rustledger_core::Price {
            date: date(2024, 1, 1),
            currency: "EUR".into(),
            amount: Amount::new(dec!(1.10), "USD"),
            meta: Metadata::default(),
        };

        let txn = Transaction::new(date(2024, 1, 15), "Test")
            .with_flag('*')
            .with_posting(Posting::new("Assets:Euro", Amount::new(dec!(100), "EUR")))
            .with_posting(Posting::new("Assets:Cash", Amount::new(dec!(-110), "USD")));

        let directives = vec![Directive::Price(price), Directive::Transaction(txn)];
        let mut executor = Executor::new(&directives);

        // Test CONVERT with amount
        let query = parse("SELECT convert(position, 'USD') WHERE account ~ 'Euro'").unwrap();
        let result = executor.execute(&query).unwrap();
        // 100 EUR × 1.10 = 110 USD
        match &result.rows[0][0] {
            Value::Amount(a) => {
                assert_eq!(a.number, dec!(110));
                assert_eq!(a.currency.as_ref(), "USD");
            }
            _ => panic!("Expected Amount, got {:?}", result.rows[0][0]),
        }
    }

    #[test]
    fn test_date_functions() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Test DATE construction from string
        let query = parse("SELECT date('2024-06-15')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 6, 15)));

        // Test DATE construction from components
        let query = parse("SELECT date(2024, 6, 15)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 6, 15)));

        // Test DATE_DIFF
        let query = parse("SELECT date_diff(date('2024-01-20'), date('2024-01-15'))").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Integer(5));

        // Test DATE_ADD
        let query = parse("SELECT date_add(date('2024-01-15'), 10)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 25)));

        // Test DATE_TRUNC year
        let query = parse("SELECT date_trunc('year', date('2024-06-15'))").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 1)));

        // Test DATE_TRUNC month
        let query = parse("SELECT date_trunc('month', date('2024-06-15'))").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 6, 1)));

        // Test DATE_PART
        let query = parse("SELECT date_part('month', date('2024-06-15'))").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Integer(6));

        // Test PARSE_DATE with custom format
        let query = parse("SELECT parse_date('15/06/2024', '%d/%m/%Y')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 6, 15)));

        // Test DATE_BIN with day stride
        let query =
            parse("SELECT date_bin('7 days', date('2024-01-15'), date('2024-01-01'))").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 15))); // 15 is 14 days from 1, so bucket starts at 15

        // Test DATE_BIN with week stride
        let query =
            parse("SELECT date_bin('1 week', date('2024-01-20'), date('2024-01-01'))").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 15))); // Week 3 starts at day 15

        // Test DATE_BIN with month stride
        let query =
            parse("SELECT date_bin('1 month', date('2024-06-15'), date('2024-01-01'))").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 6, 1))); // June bucket

        // Test DATE_BIN with year stride
        let query =
            parse("SELECT date_bin('1 year', date('2024-06-15'), date('2020-01-01'))").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 1, 1))); // 2024 bucket
    }

    #[test]
    fn test_string_functions_extended() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Test GREP - returns matched portion
        let query = parse("SELECT grep('Ex[a-z]+', 'Hello Expenses World')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::String("Expenses".to_string()));

        // Test GREP - no match returns NULL
        let query = parse("SELECT grep('xyz', 'Hello World')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Null);

        // Test GREPN - capture group (using [0-9] since \d is not escaped in BQL strings)
        let query = parse("SELECT grepn('([0-9]+)-([0-9]+)', '2024-01', 1)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::String("2024".to_string()));

        // Test SUBST - substitution
        let query = parse("SELECT subst('-', '/', '2024-01-15')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::String("2024/01/15".to_string()));

        // Test SPLITCOMP
        let query = parse("SELECT splitcomp('a:b:c', ':', 1)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::String("b".to_string()));

        // Test JOINSTR
        let query = parse("SELECT joinstr('hello', 'world')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::String("hello, world".to_string()));

        // Test MAXWIDTH - no truncation needed
        let query = parse("SELECT maxwidth('hello', 10)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::String("hello".to_string()));

        // Test MAXWIDTH - truncation with ellipsis
        let query = parse("SELECT maxwidth('hello world', 8)").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::String("hello...".to_string()));
    }

    #[test]
    fn test_inventory_functions() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Test EMPTY on sum of position (sum across all postings may cancel out)
        // Use a filter to get non-canceling positions
        let query = parse("SELECT empty(sum(position)) WHERE account ~ 'Assets'").unwrap();
        let result = executor.execute(&query).unwrap();
        // Should be a boolean (the actual value depends on sample data)
        assert!(matches!(result.rows[0][0], Value::Boolean(_)));

        // Test EMPTY with null returns true
        // (null handling is already tested in the function)

        // Test POSSIGN with debit account (Assets) - no sign change
        let query = parse("SELECT possign(100, 'Assets:Bank')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(
            result.rows[0][0],
            Value::Number(rust_decimal::Decimal::from(100))
        );

        // Test POSSIGN with credit account (Income) - sign is negated
        let query = parse("SELECT possign(100, 'Income:Salary')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(
            result.rows[0][0],
            Value::Number(rust_decimal::Decimal::from(-100))
        );

        // Test POSSIGN with Expenses (debit normal) - no sign change
        let query = parse("SELECT possign(50, 'Expenses:Food')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(
            result.rows[0][0],
            Value::Number(rust_decimal::Decimal::from(50))
        );

        // Test POSSIGN with Liabilities (credit normal) - sign is negated
        let query = parse("SELECT possign(200, 'Liabilities:CreditCard')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(
            result.rows[0][0],
            Value::Number(rust_decimal::Decimal::from(-200))
        );

        // Test POSSIGN with Equity (credit normal) - sign is negated
        let query = parse("SELECT possign(300, 'Equity:OpeningBalances')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(
            result.rows[0][0],
            Value::Number(rust_decimal::Decimal::from(-300))
        );
    }

    #[test]
    fn test_account_meta_functions() {
        use rustledger_core::{Close, Metadata, Open};

        // Create directives with Open/Close
        let mut open_meta = Metadata::default();
        open_meta.insert(
            "category".to_string(),
            MetaValue::String("checking".to_string()),
        );

        let directives = vec![
            Directive::Open(Open {
                date: date(2020, 1, 1),
                account: "Assets:Bank:Checking".into(),
                currencies: vec![],
                booking: None,
                meta: open_meta,
            }),
            Directive::Open(Open::new(date(2020, 2, 15), "Expenses:Food")),
            Directive::Close(Close::new(date(2024, 12, 31), "Assets:Bank:Checking")),
            // A transaction to have postings for the query context
            Directive::Transaction(
                Transaction::new(date(2024, 1, 15), "Coffee")
                    .with_posting(Posting::new(
                        "Expenses:Food",
                        Amount::new(dec!(5.00), "USD"),
                    ))
                    .with_posting(Posting::new(
                        "Assets:Bank:Checking",
                        Amount::new(dec!(-5.00), "USD"),
                    )),
            ),
        ];

        let mut executor = Executor::new(&directives);

        // Test OPEN_DATE - account with open directive
        let query = parse("SELECT open_date('Assets:Bank:Checking')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Date(date(2020, 1, 1)));

        // Test CLOSE_DATE - account with close directive
        let query = parse("SELECT close_date('Assets:Bank:Checking')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Date(date(2024, 12, 31)));

        // Test OPEN_DATE - account without close directive
        let query = parse("SELECT close_date('Expenses:Food')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Null);

        // Test OPEN_META - get metadata from open directive
        let query = parse("SELECT open_meta('Assets:Bank:Checking', 'category')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::String("checking".to_string()));

        // Test OPEN_META - non-existent key
        let query = parse("SELECT open_meta('Assets:Bank:Checking', 'nonexistent')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Null);

        // Test with non-existent account
        let query = parse("SELECT open_date('NonExistent:Account')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Null);
    }

    #[test]
    fn test_source_location_columns_return_null_without_sources() {
        // When using the regular constructor (without source location support),
        // the filename, lineno, and location columns should return Null
        let directives = vec![Directive::Transaction(Transaction {
            date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
            flag: '*',
            payee: Some("Test".into()),
            narration: "Test transaction".into(),
            tags: vec![],
            links: vec![],
            meta: Metadata::default(),
            postings: vec![
                Posting::new("Assets:Bank", Amount::new(dec!(100), "USD")),
                Posting::new("Expenses:Food", Amount::new(dec!(-100), "USD")),
            ],
            trailing_comments: Vec::new(),
        })];

        let mut executor = Executor::new(&directives);

        // Test filename column returns Null
        let query = parse("SELECT filename").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Null);

        // Test lineno column returns Null
        let query = parse("SELECT lineno").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Null);

        // Test location column returns Null
        let query = parse("SELECT location").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Null);
    }

    #[test]
    fn test_source_location_columns_with_sources() {
        use rustledger_loader::SourceMap;
        use rustledger_parser::Spanned;
        use std::sync::Arc;

        // Create a source map with a test file
        let mut source_map = SourceMap::new();
        let source: Arc<str> =
            "2024-01-15 * \"Test\"\n  Assets:Bank  100 USD\n  Expenses:Food".into();
        let file_id = source_map.add_file("test.beancount".into(), source);

        // Create a spanned directive
        let txn = Transaction {
            date: rustledger_core::naive_date(2024, 1, 15).unwrap(),
            flag: '*',
            payee: Some("Test".into()),
            narration: "Test transaction".into(),
            tags: vec![],
            links: vec![],
            meta: Metadata::default(),
            postings: vec![
                Posting::new("Assets:Bank", Amount::new(dec!(100), "USD")),
                Posting::new("Expenses:Food", Amount::new(dec!(-100), "USD")),
            ],
            trailing_comments: Vec::new(),
        };

        let spanned_directives = vec![Spanned {
            value: Directive::Transaction(txn),
            span: rustledger_parser::Span { start: 0, end: 50 },
            file_id: file_id as u16,
        }];

        let mut executor = Executor::new_with_sources(&spanned_directives, &source_map);

        // Test filename column returns the file path
        let query = parse("SELECT filename").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(
            result.rows[0][0],
            Value::String("test.beancount".to_string())
        );

        // Test lineno column returns line number
        let query = parse("SELECT lineno").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(result.rows[0][0], Value::Integer(1));

        // Test location column returns formatted location
        let query = parse("SELECT location").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(
            result.rows[0][0],
            Value::String("test.beancount:1".to_string())
        );
    }

    #[test]
    fn test_interval_function() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Test interval with single argument (unit only, count=1)
        let query = parse("SELECT interval('month')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(
            result.rows[0][0],
            Value::Interval(Interval::new(1, IntervalUnit::Month))
        );

        // Test interval with two arguments (count, unit)
        let query = parse("SELECT interval(3, 'day')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(
            result.rows[0][0],
            Value::Interval(Interval::new(3, IntervalUnit::Day))
        );

        // Test interval with negative count
        let query = parse("SELECT interval(-2, 'week')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(
            result.rows[0][0],
            Value::Interval(Interval::new(-2, IntervalUnit::Week))
        );
    }

    #[test]
    fn test_date_add_with_interval() {
        let directives = sample_directives();
        let mut executor = Executor::new(&directives);

        // Test date_add with interval
        let query = parse("SELECT date_add(date(2024, 1, 15), interval(1, 'month'))").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(
            result.rows[0][0],
            Value::Date(rustledger_core::naive_date(2024, 2, 15).unwrap())
        );

        // Test date + interval using binary operator
        let query = parse("SELECT date(2024, 1, 15) + interval(1, 'year')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(
            result.rows[0][0],
            Value::Date(rustledger_core::naive_date(2025, 1, 15).unwrap())
        );

        // Test date - interval
        let query = parse("SELECT date(2024, 3, 15) - interval(2, 'month')").unwrap();
        let result = executor.execute(&query).unwrap();
        assert_eq!(
            result.rows[0][0],
            Value::Date(rustledger_core::naive_date(2024, 1, 15).unwrap())
        );
    }
}
