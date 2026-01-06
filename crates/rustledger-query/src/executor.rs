//! BQL Query Executor.
//!
//! Executes parsed BQL queries against a set of Beancount directives.

use std::collections::HashMap;

use chrono::Datelike;
use rust_decimal::Decimal;
use rustledger_core::{Amount, Directive, Inventory, NaiveDate, Position, Transaction};

use crate::ast::{
    BalancesQuery, BinaryOp, BinaryOperator, Expr, FromClause, FunctionCall, JournalQuery, Literal,
    OrderSpec, PrintQuery, Query, SelectQuery, SortDirection, Target, UnaryOp, UnaryOperator,
};
use crate::error::QueryError;

/// A value that can result from evaluating a BQL expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    /// String value.
    String(String),
    /// Numeric value.
    Number(Decimal),
    /// Integer value.
    Integer(i64),
    /// Date value.
    Date(NaiveDate),
    /// Boolean value.
    Boolean(bool),
    /// Amount (number + currency).
    Amount(Amount),
    /// Position (amount + optional cost).
    Position(Position),
    /// Inventory (aggregated positions).
    Inventory(Inventory),
    /// Set of strings (tags, links).
    StringSet(Vec<String>),
    /// NULL value.
    Null,
}

/// A row of query results.
pub type Row = Vec<Value>;

/// Query result containing column names and rows.
#[derive(Debug, Clone)]
pub struct QueryResult {
    /// Column names.
    pub columns: Vec<String>,
    /// Result rows.
    pub rows: Vec<Row>,
}

impl QueryResult {
    /// Create a new empty result.
    pub const fn new(columns: Vec<String>) -> Self {
        Self {
            columns,
            rows: Vec::new(),
        }
    }

    /// Add a row to the result.
    pub fn add_row(&mut self, row: Row) {
        self.rows.push(row);
    }

    /// Number of rows.
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    /// Whether the result is empty.
    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }
}

/// Context for a single posting being evaluated.
#[derive(Debug)]
pub struct PostingContext<'a> {
    /// The transaction this posting belongs to.
    pub transaction: &'a Transaction,
    /// The posting index within the transaction.
    pub posting_index: usize,
    /// Running balance after this posting (optional).
    pub balance: Option<Inventory>,
}

/// Query executor.
pub struct Executor<'a> {
    /// All directives to query over.
    directives: &'a [Directive],
    /// Account balances (built up during query).
    balances: HashMap<String, Inventory>,
    /// Price database for `VALUE()` conversions.
    price_db: crate::price::PriceDatabase,
    /// Target currency for `VALUE()` conversions.
    target_currency: Option<String>,
}

impl<'a> Executor<'a> {
    /// Create a new executor with the given directives.
    pub fn new(directives: &'a [Directive]) -> Self {
        let price_db = crate::price::PriceDatabase::from_directives(directives);
        Self {
            directives,
            balances: HashMap::new(),
            price_db,
            target_currency: None,
        }
    }

    /// Set the target currency for `VALUE()` conversions.
    pub fn set_target_currency(&mut self, currency: impl Into<String>) {
        self.target_currency = Some(currency.into());
    }

    /// Execute a query and return the results.
    ///
    /// # Errors
    ///
    /// Returns `QueryError` if the query cannot be executed.
    pub fn execute(&mut self, query: &Query) -> Result<QueryResult, QueryError> {
        match query {
            Query::Select(select) => self.execute_select(select),
            Query::Journal(journal) => self.execute_journal(journal),
            Query::Balances(balances) => self.execute_balances(balances),
            Query::Print(print) => self.execute_print(print),
        }
    }

    /// Execute a SELECT query.
    fn execute_select(&self, query: &SelectQuery) -> Result<QueryResult, QueryError> {
        // Determine column names
        let column_names = self.resolve_column_names(&query.targets)?;
        let mut result = QueryResult::new(column_names);

        // Collect matching postings
        let postings = self.collect_postings(query.from.as_ref(), query.where_clause.as_ref())?;

        // Check if this is an aggregate query
        let is_aggregate = query
            .targets
            .iter()
            .any(|t| Self::is_aggregate_expr(&t.expr));

        if is_aggregate {
            // Group and aggregate
            let grouped = self.group_postings(&postings, query.group_by.as_ref())?;
            for (_, group) in grouped {
                let row = self.evaluate_aggregate_row(&query.targets, &group)?;
                result.add_row(row);
            }
        } else {
            // Simple query - one row per posting
            for ctx in &postings {
                let row = self.evaluate_row(&query.targets, ctx)?;
                if query.distinct {
                    // Check for duplicates
                    if !result.rows.contains(&row) {
                        result.add_row(row);
                    }
                } else {
                    result.add_row(row);
                }
            }
        }

        // Apply ORDER BY
        if let Some(order_by) = &query.order_by {
            self.sort_results(&mut result, order_by)?;
        }

        // Apply LIMIT
        if let Some(limit) = query.limit {
            result.rows.truncate(limit as usize);
        }

        Ok(result)
    }

    /// Execute a JOURNAL query.
    fn execute_journal(&mut self, query: &JournalQuery) -> Result<QueryResult, QueryError> {
        // JOURNAL is a shorthand for SELECT with specific columns
        let account_pattern = &query.account_pattern;

        // Try to compile as regex
        let account_regex = regex::Regex::new(account_pattern).ok();

        let columns = vec![
            "date".to_string(),
            "flag".to_string(),
            "payee".to_string(),
            "narration".to_string(),
            "account".to_string(),
            "position".to_string(),
            "balance".to_string(),
        ];
        let mut result = QueryResult::new(columns);

        // Filter transactions that touch the account
        for directive in self.directives {
            if let Directive::Transaction(txn) = directive {
                // Apply FROM clause filter if present
                if let Some(from) = &query.from {
                    if let Some(filter) = &from.filter {
                        if !self.evaluate_from_filter(filter, txn)? {
                            continue;
                        }
                    }
                }

                for posting in &txn.postings {
                    // Match account using regex or substring
                    let matches = if let Some(ref regex) = account_regex {
                        regex.is_match(&posting.account)
                    } else {
                        posting.account.contains(account_pattern)
                    };

                    if matches {
                        // Build the row
                        let balance = self.balances.entry(posting.account.clone()).or_default();

                        // Only process complete amounts
                        if let Some(units) = posting.amount() {
                            let pos = if let Some(cost_spec) = &posting.cost {
                                if let Some(cost) = cost_spec.resolve(units.number, txn.date) {
                                    Position::with_cost(units.clone(), cost)
                                } else {
                                    Position::simple(units.clone())
                                }
                            } else {
                                Position::simple(units.clone())
                            };
                            balance.add(pos.clone());
                        }

                        // Apply AT function if specified
                        let position_value = if let Some(at_func) = &query.at_function {
                            match at_func.to_uppercase().as_str() {
                                "COST" => {
                                    if let Some(units) = posting.amount() {
                                        if let Some(cost_spec) = &posting.cost {
                                            if let Some(cost) =
                                                cost_spec.resolve(units.number, txn.date)
                                            {
                                                let total = units.number * cost.number;
                                                Value::Amount(Amount::new(total, &cost.currency))
                                            } else {
                                                Value::Amount(units.clone())
                                            }
                                        } else {
                                            Value::Amount(units.clone())
                                        }
                                    } else {
                                        Value::Null
                                    }
                                }
                                "UNITS" => posting
                                    .amount()
                                    .map_or(Value::Null, |u| Value::Amount(u.clone())),
                                _ => posting
                                    .amount()
                                    .map_or(Value::Null, |u| Value::Amount(u.clone())),
                            }
                        } else {
                            posting
                                .amount()
                                .map_or(Value::Null, |u| Value::Amount(u.clone()))
                        };

                        let row = vec![
                            Value::Date(txn.date),
                            Value::String(txn.flag.to_string()),
                            Value::String(txn.payee.clone().unwrap_or_default()),
                            Value::String(txn.narration.clone()),
                            Value::String(posting.account.clone()),
                            position_value,
                            Value::Inventory(balance.clone()),
                        ];
                        result.add_row(row);
                    }
                }
            }
        }

        Ok(result)
    }

    /// Execute a BALANCES query.
    fn execute_balances(&mut self, query: &BalancesQuery) -> Result<QueryResult, QueryError> {
        // Build up balances by processing all transactions (with FROM filtering)
        self.build_balances_with_filter(query.from.as_ref())?;

        let columns = vec!["account".to_string(), "balance".to_string()];
        let mut result = QueryResult::new(columns);

        // Sort accounts for consistent output
        let mut accounts: Vec<_> = self.balances.keys().collect();
        accounts.sort();

        for account in accounts {
            // Safety: account comes from self.balances.keys(), so it's guaranteed to exist
            let Some(balance) = self.balances.get(account) else {
                continue; // Defensive: skip if somehow the key disappeared
            };

            // Apply AT function if specified
            let balance_value = if let Some(at_func) = &query.at_function {
                match at_func.to_uppercase().as_str() {
                    "COST" => {
                        // Sum up cost basis
                        let cost_inventory = balance.at_cost();
                        Value::Inventory(cost_inventory)
                    }
                    "UNITS" => {
                        // Just the units (remove cost info)
                        let units_inventory = balance.at_units();
                        Value::Inventory(units_inventory)
                    }
                    _ => Value::Inventory(balance.clone()),
                }
            } else {
                Value::Inventory(balance.clone())
            };

            let row = vec![Value::String(account.clone()), balance_value];
            result.add_row(row);
        }

        Ok(result)
    }

    /// Execute a PRINT query.
    fn execute_print(&self, query: &PrintQuery) -> Result<QueryResult, QueryError> {
        // PRINT outputs directives in Beancount format
        let columns = vec!["directive".to_string()];
        let mut result = QueryResult::new(columns);

        for directive in self.directives {
            // Apply FROM clause filter if present
            if let Some(from) = &query.from {
                if let Some(filter) = &from.filter {
                    // PRINT filters at transaction level
                    if let Directive::Transaction(txn) = directive {
                        if !self.evaluate_from_filter(filter, txn)? {
                            continue;
                        }
                    }
                }
            }

            // Format the directive as a string
            let formatted = self.format_directive(directive);
            result.add_row(vec![Value::String(formatted)]);
        }

        Ok(result)
    }

    /// Format a directive for PRINT output.
    fn format_directive(&self, directive: &Directive) -> String {
        match directive {
            Directive::Transaction(txn) => {
                let mut out = format!("{} {} ", txn.date, txn.flag);
                if let Some(payee) = &txn.payee {
                    out.push_str(&format!("\"{payee}\" "));
                }
                out.push_str(&format!("\"{}\"", txn.narration));

                for tag in &txn.tags {
                    out.push_str(&format!(" #{tag}"));
                }
                for link in &txn.links {
                    out.push_str(&format!(" ^{link}"));
                }
                out.push('\n');

                for posting in &txn.postings {
                    out.push_str(&format!("  {}", posting.account));
                    if let Some(units) = posting.amount() {
                        out.push_str(&format!("  {} {}", units.number, units.currency));
                    }
                    out.push('\n');
                }
                out
            }
            Directive::Balance(bal) => {
                format!(
                    "{} balance {} {} {}\n",
                    bal.date, bal.account, bal.amount.number, bal.amount.currency
                )
            }
            Directive::Open(open) => {
                let mut out = format!("{} open {}", open.date, open.account);
                if !open.currencies.is_empty() {
                    out.push_str(&format!(" {}", open.currencies.join(",")));
                }
                out.push('\n');
                out
            }
            Directive::Close(close) => {
                format!("{} close {}\n", close.date, close.account)
            }
            Directive::Commodity(comm) => {
                format!("{} commodity {}\n", comm.date, comm.currency)
            }
            Directive::Pad(pad) => {
                format!("{} pad {} {}\n", pad.date, pad.account, pad.source_account)
            }
            Directive::Event(event) => {
                format!(
                    "{} event \"{}\" \"{}\"\n",
                    event.date, event.event_type, event.value
                )
            }
            Directive::Query(query) => {
                format!(
                    "{} query \"{}\" \"{}\"\n",
                    query.date, query.name, query.query
                )
            }
            Directive::Note(note) => {
                format!("{} note {} \"{}\"\n", note.date, note.account, note.comment)
            }
            Directive::Document(doc) => {
                format!("{} document {} \"{}\"\n", doc.date, doc.account, doc.path)
            }
            Directive::Price(price) => {
                format!(
                    "{} price {} {} {}\n",
                    price.date, price.currency, price.amount.number, price.amount.currency
                )
            }
            Directive::Custom(custom) => {
                format!("{} custom \"{}\"\n", custom.date, custom.custom_type)
            }
        }
    }

    /// Build up account balances with optional FROM filtering.
    fn build_balances_with_filter(&mut self, from: Option<&FromClause>) -> Result<(), QueryError> {
        for directive in self.directives {
            if let Directive::Transaction(txn) = directive {
                // Apply FROM filter if present
                if let Some(from_clause) = from {
                    if let Some(filter) = &from_clause.filter {
                        if !self.evaluate_from_filter(filter, txn)? {
                            continue;
                        }
                    }
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
        let mut running_balances: std::collections::HashMap<String, Inventory> =
            std::collections::HashMap::new();

        for directive in self.directives {
            if let Directive::Transaction(txn) = directive {
                // Check FROM clause (transaction-level filter)
                if let Some(from) = from {
                    // Apply date filters
                    if let Some(open_date) = from.open_on {
                        if txn.date < open_date {
                            // Update balances but don't include in results
                            for posting in &txn.postings {
                                if let Some(units) = posting.amount() {
                                    let balance = running_balances
                                        .entry(posting.account.clone())
                                        .or_default();
                                    balance.add(Position::simple(units.clone()));
                                }
                            }
                            continue;
                        }
                    }
                    if let Some(close_date) = from.close_on {
                        if txn.date > close_date {
                            continue;
                        }
                    }
                    // Apply filter expression
                    if let Some(filter) = &from.filter {
                        if !self.evaluate_from_filter(filter, txn)? {
                            continue;
                        }
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

    /// Evaluate a FROM filter on a transaction.
    fn evaluate_from_filter(&self, filter: &Expr, txn: &Transaction) -> Result<bool, QueryError> {
        // Handle special FROM predicates
        match filter {
            Expr::Function(func) => {
                if func.name.to_uppercase().as_str() == "HAS_ACCOUNT" {
                    if func.args.len() != 1 {
                        return Err(QueryError::InvalidArguments(
                            "has_account".to_string(),
                            "expected 1 argument".to_string(),
                        ));
                    }
                    let pattern = match &func.args[0] {
                        Expr::Literal(Literal::String(s)) => s.clone(),
                        Expr::Column(s) => s.clone(),
                        _ => {
                            return Err(QueryError::Type(
                                "has_account expects a string pattern".to_string(),
                            ));
                        }
                    };
                    // Check if any posting matches the account pattern
                    let regex = regex::Regex::new(&pattern)
                        .map_err(|e| QueryError::Type(format!("invalid regex: {e}")))?;
                    for posting in &txn.postings {
                        if regex.is_match(&posting.account) {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                } else {
                    // For other functions, create a dummy context and evaluate
                    let dummy_ctx = PostingContext {
                        transaction: txn,
                        posting_index: 0,
                        balance: None,
                    };
                    self.evaluate_predicate(filter, &dummy_ctx)
                }
            }
            Expr::BinaryOp(op) => {
                // Handle YEAR = N, MONTH = N, etc.
                match (&op.left, &op.right) {
                    (Expr::Column(col), Expr::Literal(lit)) if col.to_uppercase() == "YEAR" => {
                        if let Literal::Integer(n) = lit {
                            let matches = txn.date.year() == *n as i32;
                            Ok(if op.op == BinaryOperator::Eq {
                                matches
                            } else {
                                !matches
                            })
                        } else {
                            Ok(false)
                        }
                    }
                    (Expr::Column(col), Expr::Literal(lit)) if col.to_uppercase() == "MONTH" => {
                        if let Literal::Integer(n) = lit {
                            let matches = txn.date.month() == *n as u32;
                            Ok(if op.op == BinaryOperator::Eq {
                                matches
                            } else {
                                !matches
                            })
                        } else {
                            Ok(false)
                        }
                    }
                    (Expr::Column(col), Expr::Literal(Literal::Date(d)))
                        if col.to_uppercase() == "DATE" =>
                    {
                        let matches = match op.op {
                            BinaryOperator::Eq => txn.date == *d,
                            BinaryOperator::Ne => txn.date != *d,
                            BinaryOperator::Lt => txn.date < *d,
                            BinaryOperator::Le => txn.date <= *d,
                            BinaryOperator::Gt => txn.date > *d,
                            BinaryOperator::Ge => txn.date >= *d,
                            _ => false,
                        };
                        Ok(matches)
                    }
                    _ => {
                        // Fall back to posting-level evaluation
                        let dummy_ctx = PostingContext {
                            transaction: txn,
                            posting_index: 0,
                            balance: None,
                        };
                        self.evaluate_predicate(filter, &dummy_ctx)
                    }
                }
            }
            _ => {
                // For other expressions, create a dummy context
                let dummy_ctx = PostingContext {
                    transaction: txn,
                    posting_index: 0,
                    balance: None,
                };
                self.evaluate_predicate(filter, &dummy_ctx)
            }
        }
    }

    /// Evaluate a predicate expression in the context of a posting.
    fn evaluate_predicate(&self, expr: &Expr, ctx: &PostingContext) -> Result<bool, QueryError> {
        let value = self.evaluate_expr(expr, ctx)?;
        match value {
            Value::Boolean(b) => Ok(b),
            Value::Null => Ok(false),
            _ => Err(QueryError::Type("expected boolean expression".to_string())),
        }
    }

    /// Evaluate an expression in the context of a posting.
    fn evaluate_expr(&self, expr: &Expr, ctx: &PostingContext) -> Result<Value, QueryError> {
        match expr {
            Expr::Wildcard => Ok(Value::Null), // Wildcard isn't really an expression
            Expr::Column(name) => self.evaluate_column(name, ctx),
            Expr::Literal(lit) => self.evaluate_literal(lit),
            Expr::Function(func) => self.evaluate_function(func, ctx),
            Expr::BinaryOp(op) => self.evaluate_binary_op(op, ctx),
            Expr::UnaryOp(op) => self.evaluate_unary_op(op, ctx),
            Expr::Paren(inner) => self.evaluate_expr(inner, ctx),
        }
    }

    /// Evaluate a column reference.
    fn evaluate_column(&self, name: &str, ctx: &PostingContext) -> Result<Value, QueryError> {
        let posting = &ctx.transaction.postings[ctx.posting_index];

        match name {
            "date" => Ok(Value::Date(ctx.transaction.date)),
            "account" => Ok(Value::String(posting.account.clone())),
            "narration" => Ok(Value::String(ctx.transaction.narration.clone())),
            "payee" => Ok(ctx
                .transaction
                .payee
                .clone()
                .map_or(Value::Null, Value::String)),
            "flag" => Ok(Value::String(ctx.transaction.flag.to_string())),
            "tags" => Ok(Value::StringSet(ctx.transaction.tags.clone())),
            "links" => Ok(Value::StringSet(ctx.transaction.links.clone())),
            "position" | "units" => Ok(posting
                .amount()
                .map_or(Value::Null, |u| Value::Amount(u.clone()))),
            "cost" => {
                // Get the cost of the posting
                if let Some(units) = posting.amount() {
                    if let Some(cost) = &posting.cost {
                        if let Some(number_per) = &cost.number_per {
                            if let Some(currency) = &cost.currency {
                                let total = units.number.abs() * number_per;
                                return Ok(Value::Amount(Amount::new(total, currency.clone())));
                            }
                        }
                    }
                }
                Ok(Value::Null)
            }
            "weight" => {
                // Weight is the amount used for transaction balancing
                // With cost: units × cost currency
                // Without cost: units amount
                if let Some(units) = posting.amount() {
                    if let Some(cost) = &posting.cost {
                        if let Some(number_per) = &cost.number_per {
                            if let Some(currency) = &cost.currency {
                                let total = units.number * number_per;
                                return Ok(Value::Amount(Amount::new(total, currency.clone())));
                            }
                        }
                    }
                    // No cost, use units
                    Ok(Value::Amount(units.clone()))
                } else {
                    Ok(Value::Null)
                }
            }
            "balance" => {
                // Running balance for this account
                if let Some(ref balance) = ctx.balance {
                    Ok(Value::Inventory(balance.clone()))
                } else {
                    Ok(Value::Null)
                }
            }
            "year" => Ok(Value::Integer(ctx.transaction.date.year().into())),
            "month" => Ok(Value::Integer(ctx.transaction.date.month().into())),
            "day" => Ok(Value::Integer(ctx.transaction.date.day().into())),
            _ => Err(QueryError::UnknownColumn(name.to_string())),
        }
    }

    /// Evaluate a literal.
    fn evaluate_literal(&self, lit: &Literal) -> Result<Value, QueryError> {
        Ok(match lit {
            Literal::String(s) => Value::String(s.clone()),
            Literal::Number(n) => Value::Number(*n),
            Literal::Integer(i) => Value::Integer(*i),
            Literal::Date(d) => Value::Date(*d),
            Literal::Boolean(b) => Value::Boolean(*b),
            Literal::Null => Value::Null,
        })
    }

    /// Evaluate a function call.
    fn evaluate_function(
        &self,
        func: &FunctionCall,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        // For now, only handle simple functions
        match func.name.to_uppercase().as_str() {
            "YEAR" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "YEAR".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Date(d) => Ok(Value::Integer(d.year().into())),
                    _ => Err(QueryError::Type("YEAR expects a date".to_string())),
                }
            }
            "MONTH" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "MONTH".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Date(d) => Ok(Value::Integer(d.month().into())),
                    _ => Err(QueryError::Type("MONTH expects a date".to_string())),
                }
            }
            "LENGTH" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "LENGTH".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => Ok(Value::Integer(s.len() as i64)),
                    Value::StringSet(s) => Ok(Value::Integer(s.len() as i64)),
                    _ => Err(QueryError::Type(
                        "LENGTH expects a string or set".to_string(),
                    )),
                }
            }
            "UPPER" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "UPPER".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => Ok(Value::String(s.to_uppercase())),
                    _ => Err(QueryError::Type("UPPER expects a string".to_string())),
                }
            }
            "LOWER" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "LOWER".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => Ok(Value::String(s.to_lowercase())),
                    _ => Err(QueryError::Type("LOWER expects a string".to_string())),
                }
            }
            "PARENT" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "PARENT".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => {
                        // Get parent account: "Expenses:Food:Coffee" -> "Expenses:Food"
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
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "LEAF".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => {
                        // Get leaf account: "Expenses:Food:Coffee" -> "Coffee"
                        if let Some(idx) = s.rfind(':') {
                            Ok(Value::String(s[idx + 1..].to_string()))
                        } else {
                            Ok(Value::String(s))
                        }
                    }
                    _ => Err(QueryError::Type(
                        "LEAF expects an account string".to_string(),
                    )),
                }
            }
            "ROOT" => {
                if func.args.is_empty() || func.args.len() > 2 {
                    return Err(QueryError::InvalidArguments(
                        "ROOT".to_string(),
                        "expected 1 or 2 arguments".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                let n = if func.args.len() == 2 {
                    match self.evaluate_expr(&func.args[1], ctx)? {
                        Value::Integer(i) => i as usize,
                        _ => {
                            return Err(QueryError::Type(
                                "ROOT second arg must be integer".to_string(),
                            ));
                        }
                    }
                } else {
                    1 // Default: return first component only
                };
                match val {
                    Value::String(s) => {
                        // Get first n components: "Expenses:Food:Coffee" with n=2 -> "Expenses:Food"
                        let parts: Vec<&str> = s.split(':').collect();
                        if n >= parts.len() {
                            Ok(Value::String(s))
                        } else {
                            Ok(Value::String(parts[..n].join(":")))
                        }
                    }
                    _ => Err(QueryError::Type(
                        "ROOT expects an account string".to_string(),
                    )),
                }
            }
            "ACCOUNT_SORTKEY" => {
                // Returns a sortable key for account ordering
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "ACCOUNT_SORTKEY".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => Ok(Value::String(s)),
                    _ => Err(QueryError::Type(
                        "ACCOUNT_SORTKEY expects an account string".to_string(),
                    )),
                }
            }
            "ABS" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "ABS".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Number(n) => Ok(Value::Number(n.abs())),
                    Value::Integer(i) => Ok(Value::Integer(i.abs())),
                    _ => Err(QueryError::Type("ABS expects a number".to_string())),
                }
            }
            "NEG" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "NEG".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Number(n) => Ok(Value::Number(-n)),
                    Value::Integer(i) => Ok(Value::Integer(-i)),
                    _ => Err(QueryError::Type("NEG expects a number".to_string())),
                }
            }
            "DAY" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "DAY".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Date(d) => Ok(Value::Integer(d.day().into())),
                    _ => Err(QueryError::Type("DAY expects a date".to_string())),
                }
            }
            "WEEKDAY" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "WEEKDAY".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Date(d) => {
                        // 0 = Monday, 6 = Sunday
                        Ok(Value::Integer(d.weekday().num_days_from_monday().into()))
                    }
                    _ => Err(QueryError::Type("WEEKDAY expects a date".to_string())),
                }
            }
            "QUARTER" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "QUARTER".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Date(d) => {
                        let quarter = (d.month() - 1) / 3 + 1;
                        Ok(Value::Integer(quarter.into()))
                    }
                    _ => Err(QueryError::Type("QUARTER expects a date".to_string())),
                }
            }
            "YMONTH" => {
                // Returns YYYY-MM format string
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "YMONTH".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Date(d) => {
                        Ok(Value::String(format!("{:04}-{:02}", d.year(), d.month())))
                    }
                    _ => Err(QueryError::Type("YMONTH expects a date".to_string())),
                }
            }
            "TODAY" => {
                // Return current date
                if !func.args.is_empty() {
                    return Err(QueryError::InvalidArguments(
                        "TODAY".to_string(),
                        "expected 0 arguments".to_string(),
                    ));
                }
                Ok(Value::Date(chrono::Local::now().date_naive()))
            }
            // String functions
            "SUBSTR" | "SUBSTRING" => {
                if func.args.len() < 2 || func.args.len() > 3 {
                    return Err(QueryError::InvalidArguments(
                        "SUBSTR".to_string(),
                        "expected 2 or 3 arguments".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                let start = self.evaluate_expr(&func.args[1], ctx)?;
                let len = if func.args.len() == 3 {
                    Some(self.evaluate_expr(&func.args[2], ctx)?)
                } else {
                    None
                };

                match (val, start, len) {
                    (Value::String(s), Value::Integer(start), None) => {
                        let start = start.max(0) as usize;
                        if start >= s.len() {
                            Ok(Value::String(String::new()))
                        } else {
                            Ok(Value::String(s[start..].to_string()))
                        }
                    }
                    (Value::String(s), Value::Integer(start), Some(Value::Integer(len))) => {
                        let start = start.max(0) as usize;
                        let len = len.max(0) as usize;
                        if start >= s.len() {
                            Ok(Value::String(String::new()))
                        } else {
                            let end = (start + len).min(s.len());
                            Ok(Value::String(s[start..end].to_string()))
                        }
                    }
                    _ => Err(QueryError::Type(
                        "SUBSTR expects (string, int, [int])".to_string(),
                    )),
                }
            }
            "TRIM" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "TRIM".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => Ok(Value::String(s.trim().to_string())),
                    _ => Err(QueryError::Type("TRIM expects a string".to_string())),
                }
            }
            "STARTSWITH" => {
                if func.args.len() != 2 {
                    return Err(QueryError::InvalidArguments(
                        "STARTSWITH".to_string(),
                        "expected 2 arguments".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                let prefix = self.evaluate_expr(&func.args[1], ctx)?;
                match (val, prefix) {
                    (Value::String(s), Value::String(p)) => Ok(Value::Boolean(s.starts_with(&p))),
                    _ => Err(QueryError::Type(
                        "STARTSWITH expects two strings".to_string(),
                    )),
                }
            }
            "ENDSWITH" => {
                if func.args.len() != 2 {
                    return Err(QueryError::InvalidArguments(
                        "ENDSWITH".to_string(),
                        "expected 2 arguments".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                let suffix = self.evaluate_expr(&func.args[1], ctx)?;
                match (val, suffix) {
                    (Value::String(s), Value::String(p)) => Ok(Value::Boolean(s.ends_with(&p))),
                    _ => Err(QueryError::Type("ENDSWITH expects two strings".to_string())),
                }
            }
            "COALESCE" => {
                // Return first non-null argument
                for arg in &func.args {
                    let val = self.evaluate_expr(arg, ctx)?;
                    if !matches!(val, Value::Null) {
                        return Ok(val);
                    }
                }
                Ok(Value::Null)
            }
            // Account functions
            "ACCOUNT_DEPTH" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "ACCOUNT_DEPTH".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::String(s) => {
                        // Depth = number of colons + 1
                        let depth = s.chars().filter(|c| *c == ':').count() + 1;
                        Ok(Value::Integer(depth as i64))
                    }
                    _ => Err(QueryError::Type(
                        "ACCOUNT_DEPTH expects an account string".to_string(),
                    )),
                }
            }
            // Amount/Position functions
            "NUMBER" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "NUMBER".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Amount(a) => Ok(Value::Number(a.number)),
                    Value::Position(p) => Ok(Value::Number(p.units.number)),
                    Value::Number(n) => Ok(Value::Number(n)),
                    Value::Integer(i) => Ok(Value::Number(Decimal::from(i))),
                    _ => Err(QueryError::Type(
                        "NUMBER expects an amount or position".to_string(),
                    )),
                }
            }
            "CURRENCY" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "CURRENCY".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Amount(a) => Ok(Value::String(a.currency)),
                    Value::Position(p) => Ok(Value::String(p.units.currency)),
                    _ => Err(QueryError::Type(
                        "CURRENCY expects an amount or position".to_string(),
                    )),
                }
            }
            "GETITEM" | "GET" => {
                // Get item from inventory by currency
                if func.args.len() != 2 {
                    return Err(QueryError::InvalidArguments(
                        "GETITEM".to_string(),
                        "expected 2 arguments".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                let key = self.evaluate_expr(&func.args[1], ctx)?;
                match (val, key) {
                    (Value::Inventory(inv), Value::String(currency)) => {
                        let total = inv.units(&currency);
                        if total.is_zero() {
                            Ok(Value::Null)
                        } else {
                            Ok(Value::Amount(Amount::new(total, currency)))
                        }
                    }
                    _ => Err(QueryError::Type(
                        "GETITEM expects (inventory, string)".to_string(),
                    )),
                }
            }
            "ROUND" => {
                if func.args.is_empty() || func.args.len() > 2 {
                    return Err(QueryError::InvalidArguments(
                        "ROUND".to_string(),
                        "expected 1 or 2 arguments".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                let decimals = if func.args.len() == 2 {
                    match self.evaluate_expr(&func.args[1], ctx)? {
                        Value::Integer(i) => i as u32,
                        _ => {
                            return Err(QueryError::Type(
                                "ROUND second arg must be integer".to_string(),
                            ));
                        }
                    }
                } else {
                    0
                };
                match val {
                    Value::Number(n) => Ok(Value::Number(n.round_dp(decimals))),
                    Value::Integer(i) => Ok(Value::Integer(i)),
                    _ => Err(QueryError::Type("ROUND expects a number".to_string())),
                }
            }
            "SAFEDIV" => {
                // Safe division that returns 0 on divide by zero
                if func.args.len() != 2 {
                    return Err(QueryError::InvalidArguments(
                        "SAFEDIV".to_string(),
                        "expected 2 arguments".to_string(),
                    ));
                }
                let num = self.evaluate_expr(&func.args[0], ctx)?;
                let den = self.evaluate_expr(&func.args[1], ctx)?;
                match (num, den) {
                    (Value::Number(n), Value::Number(d)) => {
                        if d.is_zero() {
                            Ok(Value::Number(Decimal::ZERO))
                        } else {
                            Ok(Value::Number(n / d))
                        }
                    }
                    (Value::Integer(n), Value::Integer(d)) => {
                        if d == 0 {
                            Ok(Value::Integer(0))
                        } else {
                            Ok(Value::Integer(n / d))
                        }
                    }
                    _ => Err(QueryError::Type("SAFEDIV expects two numbers".to_string())),
                }
            }
            // Position functions
            "UNITS" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "UNITS".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Position(p) => Ok(Value::Amount(p.units)),
                    Value::Amount(a) => Ok(Value::Amount(a)),
                    Value::Inventory(inv) => {
                        // Sum all units by currency
                        let positions: Vec<String> = inv
                            .positions()
                            .iter()
                            .map(|p| format!("{} {}", p.units.number, p.units.currency))
                            .collect();
                        Ok(Value::String(positions.join(", ")))
                    }
                    _ => Err(QueryError::Type(
                        "UNITS expects a position or inventory".to_string(),
                    )),
                }
            }
            "COST" => {
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "COST".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Position(p) => {
                        if let Some(cost) = &p.cost {
                            let total = p.units.number.abs() * cost.number;
                            Ok(Value::Amount(Amount::new(total, cost.currency.clone())))
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    Value::Amount(a) => Ok(Value::Amount(a)), // Amount is its own cost
                    Value::Inventory(inv) => {
                        // Sum all costs
                        let mut total = Decimal::ZERO;
                        let mut currency = String::new();
                        for pos in inv.positions() {
                            if let Some(cost) = &pos.cost {
                                total += pos.units.number.abs() * cost.number;
                                if currency.is_empty() {
                                    currency.clone_from(&cost.currency);
                                }
                            }
                        }
                        if currency.is_empty() {
                            Ok(Value::Null)
                        } else {
                            Ok(Value::Amount(Amount::new(total, currency)))
                        }
                    }
                    _ => Err(QueryError::Type(
                        "COST expects a position or inventory".to_string(),
                    )),
                }
            }
            "WEIGHT" => {
                // Weight is what's used for balancing (cost basis if available, else units)
                if func.args.len() != 1 {
                    return Err(QueryError::InvalidArguments(
                        "WEIGHT".to_string(),
                        "expected 1 argument".to_string(),
                    ));
                }
                let val = self.evaluate_expr(&func.args[0], ctx)?;
                match val {
                    Value::Position(p) => {
                        if let Some(cost) = &p.cost {
                            let total = p.units.number * cost.number;
                            Ok(Value::Amount(Amount::new(total, cost.currency.clone())))
                        } else {
                            Ok(Value::Amount(p.units))
                        }
                    }
                    Value::Amount(a) => Ok(Value::Amount(a)),
                    _ => Err(QueryError::Type(
                        "WEIGHT expects a position or amount".to_string(),
                    )),
                }
            }
            "VALUE" => {
                // Market value - convert to target currency using price database
                if func.args.is_empty() || func.args.len() > 2 {
                    return Err(QueryError::InvalidArguments(
                        "VALUE".to_string(),
                        "expected 1-2 arguments".to_string(),
                    ));
                }

                // Get target currency from second argument or default
                let target_currency = if func.args.len() == 2 {
                    match self.evaluate_expr(&func.args[1], ctx)? {
                        Value::String(s) => s,
                        _ => {
                            return Err(QueryError::Type(
                                "VALUE second argument must be a currency string".to_string(),
                            ));
                        }
                    }
                } else {
                    self.target_currency
                        .clone()
                        .unwrap_or_else(|| "USD".to_string())
                };

                let val = self.evaluate_expr(&func.args[0], ctx)?;
                let date = ctx.transaction.date;

                match val {
                    Value::Position(p) => {
                        // Convert position to target currency
                        if p.units.currency == target_currency {
                            Ok(Value::Amount(p.units))
                        } else if let Some(converted) =
                            self.price_db.convert(&p.units, &target_currency, date)
                        {
                            Ok(Value::Amount(converted))
                        } else {
                            // No price available, return units as-is
                            Ok(Value::Amount(p.units))
                        }
                    }
                    Value::Amount(a) => {
                        if a.currency == target_currency {
                            Ok(Value::Amount(a))
                        } else if let Some(converted) =
                            self.price_db.convert(&a, &target_currency, date)
                        {
                            Ok(Value::Amount(converted))
                        } else {
                            Ok(Value::Amount(a))
                        }
                    }
                    Value::Inventory(inv) => {
                        // Convert all positions in inventory to target currency and sum
                        let mut total = Decimal::ZERO;
                        for pos in inv.positions() {
                            if pos.units.currency == target_currency {
                                total += pos.units.number;
                            } else if let Some(converted) =
                                self.price_db.convert(&pos.units, &target_currency, date)
                            {
                                total += converted.number;
                            } else {
                                // No conversion available, skip this position
                                // (alternatively could return error or include unconverted)
                            }
                        }
                        Ok(Value::Amount(Amount::new(total, &target_currency)))
                    }
                    _ => Err(QueryError::Type(
                        "VALUE expects a position or inventory".to_string(),
                    )),
                }
            }
            // Aggregate functions return Null when evaluated on a single row
            // They're handled specially in aggregate evaluation
            "SUM" | "COUNT" | "MIN" | "MAX" | "FIRST" | "LAST" | "AVG" => Ok(Value::Null),
            _ => Err(QueryError::UnknownFunction(func.name.clone())),
        }
    }

    /// Evaluate a binary operation.
    fn evaluate_binary_op(&self, op: &BinaryOp, ctx: &PostingContext) -> Result<Value, QueryError> {
        let left = self.evaluate_expr(&op.left, ctx)?;
        let right = self.evaluate_expr(&op.right, ctx)?;

        match op.op {
            BinaryOperator::Eq => Ok(Value::Boolean(self.values_equal(&left, &right))),
            BinaryOperator::Ne => Ok(Value::Boolean(!self.values_equal(&left, &right))),
            BinaryOperator::Lt => self.compare_values(&left, &right, std::cmp::Ordering::is_lt),
            BinaryOperator::Le => self.compare_values(&left, &right, std::cmp::Ordering::is_le),
            BinaryOperator::Gt => self.compare_values(&left, &right, std::cmp::Ordering::is_gt),
            BinaryOperator::Ge => self.compare_values(&left, &right, std::cmp::Ordering::is_ge),
            BinaryOperator::And => {
                let l = self.to_bool(&left)?;
                let r = self.to_bool(&right)?;
                Ok(Value::Boolean(l && r))
            }
            BinaryOperator::Or => {
                let l = self.to_bool(&left)?;
                let r = self.to_bool(&right)?;
                Ok(Value::Boolean(l || r))
            }
            BinaryOperator::Regex => {
                // ~ operator: string matches regex pattern
                let s = match left {
                    Value::String(s) => s,
                    _ => {
                        return Err(QueryError::Type(
                            "regex requires string left operand".to_string(),
                        ));
                    }
                };
                let pattern = match right {
                    Value::String(p) => p,
                    _ => {
                        return Err(QueryError::Type(
                            "regex requires string pattern".to_string(),
                        ));
                    }
                };
                // Simple contains check (full regex would need regex crate)
                Ok(Value::Boolean(s.contains(&pattern)))
            }
            BinaryOperator::In => {
                // Check if left value is in right set
                match right {
                    Value::StringSet(set) => {
                        let needle = match left {
                            Value::String(s) => s,
                            _ => {
                                return Err(QueryError::Type(
                                    "IN requires string left operand".to_string(),
                                ));
                            }
                        };
                        Ok(Value::Boolean(set.contains(&needle)))
                    }
                    _ => Err(QueryError::Type(
                        "IN requires set right operand".to_string(),
                    )),
                }
            }
            BinaryOperator::Add => self.arithmetic_op(&left, &right, |a, b| a + b),
            BinaryOperator::Sub => self.arithmetic_op(&left, &right, |a, b| a - b),
            BinaryOperator::Mul => self.arithmetic_op(&left, &right, |a, b| a * b),
            BinaryOperator::Div => self.arithmetic_op(&left, &right, |a, b| a / b),
        }
    }

    /// Evaluate a unary operation.
    fn evaluate_unary_op(&self, op: &UnaryOp, ctx: &PostingContext) -> Result<Value, QueryError> {
        let val = self.evaluate_expr(&op.operand, ctx)?;
        match op.op {
            UnaryOperator::Not => {
                let b = self.to_bool(&val)?;
                Ok(Value::Boolean(!b))
            }
            UnaryOperator::Neg => match val {
                Value::Number(n) => Ok(Value::Number(-n)),
                Value::Integer(i) => Ok(Value::Integer(-i)),
                _ => Err(QueryError::Type(
                    "negation requires numeric value".to_string(),
                )),
            },
        }
    }

    /// Check if two values are equal.
    fn values_equal(&self, left: &Value, right: &Value) -> bool {
        // BQL treats NULL = NULL as TRUE
        match (left, right) {
            (Value::Null, Value::Null) => true,
            (Value::String(a), Value::String(b)) => a == b,
            (Value::Number(a), Value::Number(b)) => a == b,
            (Value::Integer(a), Value::Integer(b)) => a == b,
            (Value::Number(a), Value::Integer(b)) => *a == Decimal::from(*b),
            (Value::Integer(a), Value::Number(b)) => Decimal::from(*a) == *b,
            (Value::Date(a), Value::Date(b)) => a == b,
            (Value::Boolean(a), Value::Boolean(b)) => a == b,
            _ => false,
        }
    }

    /// Compare two values.
    fn compare_values<F>(&self, left: &Value, right: &Value, pred: F) -> Result<Value, QueryError>
    where
        F: FnOnce(std::cmp::Ordering) -> bool,
    {
        let ord = match (left, right) {
            (Value::Number(a), Value::Number(b)) => a.cmp(b),
            (Value::Integer(a), Value::Integer(b)) => a.cmp(b),
            (Value::Number(a), Value::Integer(b)) => a.cmp(&Decimal::from(*b)),
            (Value::Integer(a), Value::Number(b)) => Decimal::from(*a).cmp(b),
            (Value::String(a), Value::String(b)) => a.cmp(b),
            (Value::Date(a), Value::Date(b)) => a.cmp(b),
            _ => return Err(QueryError::Type("cannot compare values".to_string())),
        };
        Ok(Value::Boolean(pred(ord)))
    }

    /// Check if left value is less than right value.
    fn value_less_than(&self, left: &Value, right: &Value) -> Result<bool, QueryError> {
        let ord = match (left, right) {
            (Value::Number(a), Value::Number(b)) => a.cmp(b),
            (Value::Integer(a), Value::Integer(b)) => a.cmp(b),
            (Value::Number(a), Value::Integer(b)) => a.cmp(&Decimal::from(*b)),
            (Value::Integer(a), Value::Number(b)) => Decimal::from(*a).cmp(b),
            (Value::String(a), Value::String(b)) => a.cmp(b),
            (Value::Date(a), Value::Date(b)) => a.cmp(b),
            _ => return Err(QueryError::Type("cannot compare values".to_string())),
        };
        Ok(ord.is_lt())
    }

    /// Perform arithmetic operation.
    fn arithmetic_op<F>(&self, left: &Value, right: &Value, op: F) -> Result<Value, QueryError>
    where
        F: FnOnce(Decimal, Decimal) -> Decimal,
    {
        let (a, b) = match (left, right) {
            (Value::Number(a), Value::Number(b)) => (*a, *b),
            (Value::Integer(a), Value::Integer(b)) => (Decimal::from(*a), Decimal::from(*b)),
            (Value::Number(a), Value::Integer(b)) => (*a, Decimal::from(*b)),
            (Value::Integer(a), Value::Number(b)) => (Decimal::from(*a), *b),
            _ => {
                return Err(QueryError::Type(
                    "arithmetic requires numeric values".to_string(),
                ));
            }
        };
        Ok(Value::Number(op(a, b)))
    }

    /// Convert a value to boolean.
    fn to_bool(&self, val: &Value) -> Result<bool, QueryError> {
        match val {
            Value::Boolean(b) => Ok(*b),
            Value::Null => Ok(false),
            _ => Err(QueryError::Type("expected boolean".to_string())),
        }
    }

    /// Check if an expression contains aggregate functions.
    fn is_aggregate_expr(expr: &Expr) -> bool {
        match expr {
            Expr::Function(func) => {
                matches!(
                    func.name.to_uppercase().as_str(),
                    "SUM" | "COUNT" | "MIN" | "MAX" | "FIRST" | "LAST" | "AVG"
                )
            }
            Expr::BinaryOp(op) => {
                Self::is_aggregate_expr(&op.left) || Self::is_aggregate_expr(&op.right)
            }
            Expr::UnaryOp(op) => Self::is_aggregate_expr(&op.operand),
            Expr::Paren(inner) => Self::is_aggregate_expr(inner),
            _ => false,
        }
    }

    /// Resolve column names from targets.
    fn resolve_column_names(&self, targets: &[Target]) -> Result<Vec<String>, QueryError> {
        let mut names = Vec::new();
        for (i, target) in targets.iter().enumerate() {
            if let Some(alias) = &target.alias {
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
            _ => format!("col{index}"),
        }
    }

    /// Evaluate a row of results for non-aggregate query.
    fn evaluate_row(&self, targets: &[Target], ctx: &PostingContext) -> Result<Row, QueryError> {
        let mut row = Vec::new();
        for target in targets {
            if matches!(target.expr, Expr::Wildcard) {
                // Expand wildcard to default columns
                row.push(Value::Date(ctx.transaction.date));
                row.push(Value::String(ctx.transaction.flag.to_string()));
                row.push(
                    ctx.transaction
                        .payee
                        .clone()
                        .map_or(Value::Null, Value::String),
                );
                row.push(Value::String(ctx.transaction.narration.clone()));
                let posting = &ctx.transaction.postings[ctx.posting_index];
                row.push(Value::String(posting.account.clone()));
                row.push(
                    posting
                        .amount()
                        .map_or(Value::Null, |u| Value::Amount(u.clone())),
                );
            } else {
                row.push(self.evaluate_expr(&target.expr, ctx)?);
            }
        }
        Ok(row)
    }

    /// Group postings by the GROUP BY expressions.
    /// Returns a Vec of (key, group) pairs since Value doesn't implement Hash.
    fn group_postings<'b>(
        &self,
        postings: &'b [PostingContext<'a>],
        group_by: Option<&Vec<Expr>>,
    ) -> Result<Vec<(Vec<Value>, Vec<&'b PostingContext<'a>>)>, QueryError> {
        let mut groups: Vec<(Vec<Value>, Vec<&PostingContext<'a>>)> = Vec::new();

        if let Some(group_exprs) = group_by {
            for ctx in postings {
                let mut key = Vec::new();
                for expr in group_exprs {
                    key.push(self.evaluate_expr(expr, ctx)?);
                }
                // Find existing group with same key
                let mut found = false;
                for (existing_key, group) in &mut groups {
                    if self.keys_equal(existing_key, &key) {
                        group.push(ctx);
                        found = true;
                        break;
                    }
                }
                if !found {
                    groups.push((key, vec![ctx]));
                }
            }
        } else {
            // No GROUP BY - all postings in one group
            groups.push((Vec::new(), postings.iter().collect()));
        }

        Ok(groups)
    }

    /// Check if two grouping keys are equal.
    fn keys_equal(&self, a: &[Value], b: &[Value]) -> bool {
        if a.len() != b.len() {
            return false;
        }
        for (x, y) in a.iter().zip(b.iter()) {
            if !self.values_equal(x, y) {
                return false;
            }
        }
        true
    }

    /// Evaluate a row of aggregate results.
    fn evaluate_aggregate_row(
        &self,
        targets: &[Target],
        group: &[&PostingContext],
    ) -> Result<Row, QueryError> {
        let mut row = Vec::new();
        for target in targets {
            row.push(self.evaluate_aggregate_expr(&target.expr, group)?);
        }
        Ok(row)
    }

    /// Evaluate an expression in an aggregate context.
    fn evaluate_aggregate_expr(
        &self,
        expr: &Expr,
        group: &[&PostingContext],
    ) -> Result<Value, QueryError> {
        match expr {
            Expr::Function(func) => {
                match func.name.to_uppercase().as_str() {
                    "COUNT" => {
                        // COUNT(*) counts all rows
                        Ok(Value::Integer(group.len() as i64))
                    }
                    "SUM" => {
                        if func.args.len() != 1 {
                            return Err(QueryError::InvalidArguments(
                                "SUM".to_string(),
                                "expected 1 argument".to_string(),
                            ));
                        }
                        let mut total = Inventory::new();
                        for ctx in group {
                            let val = self.evaluate_expr(&func.args[0], ctx)?;
                            match val {
                                Value::Amount(amt) => {
                                    let pos = Position::simple(amt);
                                    total.add(pos);
                                }
                                Value::Position(pos) => {
                                    total.add(pos);
                                }
                                Value::Number(n) => {
                                    // Sum as raw number
                                    let pos =
                                        Position::simple(Amount::new(n, "__NUMBER__".to_string()));
                                    total.add(pos);
                                }
                                Value::Null => {}
                                _ => {
                                    return Err(QueryError::Type(
                                        "SUM requires numeric or position value".to_string(),
                                    ));
                                }
                            }
                        }
                        Ok(Value::Inventory(total))
                    }
                    "FIRST" => {
                        if func.args.len() != 1 {
                            return Err(QueryError::InvalidArguments(
                                "FIRST".to_string(),
                                "expected 1 argument".to_string(),
                            ));
                        }
                        if let Some(ctx) = group.first() {
                            self.evaluate_expr(&func.args[0], ctx)
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    "LAST" => {
                        if func.args.len() != 1 {
                            return Err(QueryError::InvalidArguments(
                                "LAST".to_string(),
                                "expected 1 argument".to_string(),
                            ));
                        }
                        if let Some(ctx) = group.last() {
                            self.evaluate_expr(&func.args[0], ctx)
                        } else {
                            Ok(Value::Null)
                        }
                    }
                    "MIN" => {
                        if func.args.len() != 1 {
                            return Err(QueryError::InvalidArguments(
                                "MIN".to_string(),
                                "expected 1 argument".to_string(),
                            ));
                        }
                        let mut min_val: Option<Value> = None;
                        for ctx in group {
                            let val = self.evaluate_expr(&func.args[0], ctx)?;
                            if matches!(val, Value::Null) {
                                continue;
                            }
                            min_val = Some(match min_val {
                                None => val,
                                Some(current) => {
                                    if self.value_less_than(&val, &current)? {
                                        val
                                    } else {
                                        current
                                    }
                                }
                            });
                        }
                        Ok(min_val.unwrap_or(Value::Null))
                    }
                    "MAX" => {
                        if func.args.len() != 1 {
                            return Err(QueryError::InvalidArguments(
                                "MAX".to_string(),
                                "expected 1 argument".to_string(),
                            ));
                        }
                        let mut max_val: Option<Value> = None;
                        for ctx in group {
                            let val = self.evaluate_expr(&func.args[0], ctx)?;
                            if matches!(val, Value::Null) {
                                continue;
                            }
                            max_val = Some(match max_val {
                                None => val,
                                Some(current) => {
                                    if self.value_less_than(&current, &val)? {
                                        val
                                    } else {
                                        current
                                    }
                                }
                            });
                        }
                        Ok(max_val.unwrap_or(Value::Null))
                    }
                    "AVG" => {
                        if func.args.len() != 1 {
                            return Err(QueryError::InvalidArguments(
                                "AVG".to_string(),
                                "expected 1 argument".to_string(),
                            ));
                        }
                        let mut sum = Decimal::ZERO;
                        let mut count = 0i64;
                        for ctx in group {
                            let val = self.evaluate_expr(&func.args[0], ctx)?;
                            match val {
                                Value::Number(n) => {
                                    sum += n;
                                    count += 1;
                                }
                                Value::Integer(i) => {
                                    sum += Decimal::from(i);
                                    count += 1;
                                }
                                Value::Null => {}
                                _ => {
                                    return Err(QueryError::Type(
                                        "AVG expects numeric values".to_string(),
                                    ));
                                }
                            }
                        }
                        if count == 0 {
                            Ok(Value::Null)
                        } else {
                            Ok(Value::Number(sum / Decimal::from(count)))
                        }
                    }
                    _ => {
                        // Non-aggregate function
                        if let Some(ctx) = group.first() {
                            self.evaluate_function(func, ctx)
                        } else {
                            Ok(Value::Null)
                        }
                    }
                }
            }
            Expr::Column(_) => {
                // For non-aggregate columns in aggregate query, take first value
                if let Some(ctx) = group.first() {
                    self.evaluate_expr(expr, ctx)
                } else {
                    Ok(Value::Null)
                }
            }
            Expr::BinaryOp(op) => {
                let left = self.evaluate_aggregate_expr(&op.left, group)?;
                let right = self.evaluate_aggregate_expr(&op.right, group)?;
                // Re-evaluate with computed values
                self.binary_op_on_values(op.op, &left, &right)
            }
            _ => {
                // For other expressions, evaluate on first row
                if let Some(ctx) = group.first() {
                    self.evaluate_expr(expr, ctx)
                } else {
                    Ok(Value::Null)
                }
            }
        }
    }

    /// Apply binary operator to already-evaluated values.
    fn binary_op_on_values(
        &self,
        op: BinaryOperator,
        left: &Value,
        right: &Value,
    ) -> Result<Value, QueryError> {
        match op {
            BinaryOperator::Eq => Ok(Value::Boolean(self.values_equal(left, right))),
            BinaryOperator::Ne => Ok(Value::Boolean(!self.values_equal(left, right))),
            BinaryOperator::Lt => self.compare_values(left, right, std::cmp::Ordering::is_lt),
            BinaryOperator::Le => self.compare_values(left, right, std::cmp::Ordering::is_le),
            BinaryOperator::Gt => self.compare_values(left, right, std::cmp::Ordering::is_gt),
            BinaryOperator::Ge => self.compare_values(left, right, std::cmp::Ordering::is_ge),
            BinaryOperator::And => {
                let l = self.to_bool(left)?;
                let r = self.to_bool(right)?;
                Ok(Value::Boolean(l && r))
            }
            BinaryOperator::Or => {
                let l = self.to_bool(left)?;
                let r = self.to_bool(right)?;
                Ok(Value::Boolean(l || r))
            }
            BinaryOperator::Add => self.arithmetic_op(left, right, |a, b| a + b),
            BinaryOperator::Sub => self.arithmetic_op(left, right, |a, b| a - b),
            BinaryOperator::Mul => self.arithmetic_op(left, right, |a, b| a * b),
            BinaryOperator::Div => self.arithmetic_op(left, right, |a, b| a / b),
            _ => Err(QueryError::Type("unsupported operation".to_string())),
        }
    }

    /// Sort results by ORDER BY clauses.
    fn sort_results(
        &self,
        result: &mut QueryResult,
        order_by: &[OrderSpec],
    ) -> Result<(), QueryError> {
        if order_by.is_empty() {
            return Ok(());
        }

        // Build a map from column names to indices
        let column_indices: std::collections::HashMap<&str, usize> = result
            .columns
            .iter()
            .enumerate()
            .map(|(i, name)| (name.as_str(), i))
            .collect();

        // Resolve ORDER BY expressions to column indices
        let mut sort_specs: Vec<(usize, bool)> = Vec::new();
        for spec in order_by {
            // Try to resolve the expression to a column index
            let idx = match &spec.expr {
                Expr::Column(name) => column_indices
                    .get(name.as_str())
                    .copied()
                    .ok_or_else(|| QueryError::UnknownColumn(name.clone()))?,
                Expr::Function(func) => {
                    // Try to find a column with the function name
                    column_indices
                        .get(func.name.as_str())
                        .copied()
                        .ok_or_else(|| {
                            QueryError::Evaluation(format!(
                                "ORDER BY expression not found in SELECT: {}",
                                func.name
                            ))
                        })?
                }
                _ => {
                    return Err(QueryError::Evaluation(
                        "ORDER BY expression must reference a selected column".to_string(),
                    ));
                }
            };
            let ascending = spec.direction != SortDirection::Desc;
            sort_specs.push((idx, ascending));
        }

        // Sort the rows
        result.rows.sort_by(|a, b| {
            for (idx, ascending) in &sort_specs {
                if *idx >= a.len() || *idx >= b.len() {
                    continue;
                }
                let ord = self.compare_values_for_sort(&a[*idx], &b[*idx]);
                if ord != std::cmp::Ordering::Equal {
                    return if *ascending { ord } else { ord.reverse() };
                }
            }
            std::cmp::Ordering::Equal
        });

        Ok(())
    }

    /// Compare two values for sorting purposes.
    fn compare_values_for_sort(&self, left: &Value, right: &Value) -> std::cmp::Ordering {
        match (left, right) {
            (Value::Null, Value::Null) => std::cmp::Ordering::Equal,
            (Value::Null, _) => std::cmp::Ordering::Greater, // Nulls sort last
            (_, Value::Null) => std::cmp::Ordering::Less,
            (Value::Number(a), Value::Number(b)) => a.cmp(b),
            (Value::Integer(a), Value::Integer(b)) => a.cmp(b),
            (Value::Number(a), Value::Integer(b)) => a.cmp(&Decimal::from(*b)),
            (Value::Integer(a), Value::Number(b)) => Decimal::from(*a).cmp(b),
            (Value::String(a), Value::String(b)) => a.cmp(b),
            (Value::Date(a), Value::Date(b)) => a.cmp(b),
            (Value::Boolean(a), Value::Boolean(b)) => a.cmp(b),
            _ => std::cmp::Ordering::Equal, // Can't compare other types
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;
    use rust_decimal_macros::dec;
    use rustledger_core::Posting;

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        NaiveDate::from_ymd_opt(year, month, day).unwrap()
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
}
