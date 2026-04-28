//! Core expression and predicate evaluation functions.

use std::collections::BTreeMap;

use rustledger_core::{Amount, Position, Transaction};

use crate::ast::{Expr, Literal, Target};
use crate::error::QueryError;

use super::Executor;
use super::types::{PostingContext, Row, Value, WindowContext};

impl Executor<'_> {
    /// Evaluate a FROM filter on a transaction.
    pub(super) fn evaluate_from_filter(
        &self,
        filter: &Expr,
        txn: &Transaction,
    ) -> Result<bool, QueryError> {
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
                    // Check if any posting matches the account pattern (using cache)
                    let regex = self.require_regex(&pattern)?;
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
                        account_balance: None,
                        directive_index: None,
                    };
                    self.evaluate_predicate(filter, &dummy_ctx)
                }
            }
            Expr::BinaryOp(op) => {
                use crate::ast::BinaryOperator;
                // Handle YEAR = N, MONTH = N, etc.
                match (&op.left, &op.right) {
                    (Expr::Column(col), Expr::Literal(lit)) if col.to_uppercase() == "YEAR" => {
                        // Handle both Integer and Number for year comparison
                        let year_val = match lit {
                            Literal::Integer(n) => Some(*n as i32),
                            Literal::Number(n) => n.to_string().parse::<i32>().ok(),
                            _ => None,
                        };
                        if let Some(n) = year_val {
                            let matches = i32::from(txn.date.year()) == n;
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
                        // Handle both Integer and Number for month comparison
                        let month_val = match lit {
                            Literal::Integer(n) => Some(*n as u32),
                            Literal::Number(n) => n.to_string().parse::<u32>().ok(),
                            _ => None,
                        };
                        if let Some(n) = month_val {
                            let matches = txn.date.month() as u32 == n;
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
                            account_balance: None,
                            directive_index: None,
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
                    account_balance: None,
                    directive_index: None,
                };
                self.evaluate_predicate(filter, &dummy_ctx)
            }
        }
    }

    /// Evaluate a predicate expression in the context of a posting.
    ///
    /// Uses SQL/beanquery truthiness via [`Self::to_bool`], so that functions
    /// such as `grep(pattern, text)` (which return the matched substring or
    /// NULL) can be used directly in a `WHERE` clause without an explicit
    /// `IS NOT NULL` comparison.
    pub(super) fn evaluate_predicate(
        &self,
        expr: &Expr,
        ctx: &PostingContext,
    ) -> Result<bool, QueryError> {
        let value = self.evaluate_expr(expr, ctx)?;
        self.to_bool(&value)
    }

    /// Evaluate an expression in the context of a posting.
    pub(super) fn evaluate_expr(
        &self,
        expr: &Expr,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        match expr {
            Expr::Wildcard => Ok(Value::Null), // Wildcard isn't really an expression
            Expr::Column(name) => self.evaluate_column(name, ctx),
            Expr::Literal(lit) => self.evaluate_literal(lit),
            Expr::Function(func) => self.evaluate_function(func, ctx),
            Expr::Window(_) => {
                // Window functions are evaluated at the query level, not per-posting
                // This case should not be reached; window values are pre-computed
                Err(QueryError::Evaluation(
                    "Window function cannot be evaluated in posting context".to_string(),
                ))
            }
            Expr::BinaryOp(op) => self.evaluate_binary_op(op, ctx),
            Expr::UnaryOp(op) => self.evaluate_unary_op(op, ctx),
            Expr::Paren(inner) => self.evaluate_expr(inner, ctx),
            Expr::Between { value, low, high } => {
                let val = self.evaluate_expr(value, ctx)?;
                let low_val = self.evaluate_expr(low, ctx)?;
                let high_val = self.evaluate_expr(high, ctx)?;

                let ge = self.compare_values(&val, &low_val, std::cmp::Ordering::is_ge)?;
                let le = self.compare_values(&val, &high_val, std::cmp::Ordering::is_le)?;

                match (ge, le) {
                    (Value::Boolean(g), Value::Boolean(l)) => Ok(Value::Boolean(g && l)),
                    _ => Err(QueryError::Type(
                        "BETWEEN requires comparable values".to_string(),
                    )),
                }
            }
            Expr::Set(elements) => {
                // Evaluate all elements and collect as Set (supports any value types)
                let mut values = Vec::with_capacity(elements.len());
                for elem in elements {
                    let val = self.evaluate_expr(elem, ctx)?;
                    if !matches!(val, Value::Null) {
                        values.push(val);
                    }
                }
                Ok(Value::Set(values))
            }
        }
    }

    /// Evaluate a column reference.
    pub(super) fn evaluate_column(
        &self,
        name: &str,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        let posting = &ctx.transaction.postings[ctx.posting_index];

        match name {
            "date" => Ok(Value::Date(ctx.transaction.date)),
            "account" => Ok(Value::String(posting.account.to_string())),
            "narration" => Ok(Value::String(ctx.transaction.narration.to_string())),
            "payee" => Ok(ctx
                .transaction
                .payee
                .as_ref()
                .map_or(Value::Null, |p| Value::String(p.to_string()))),
            "flag" => Ok(Value::String(ctx.transaction.flag.to_string())),
            "tags" => Ok(Value::StringSet(
                ctx.transaction
                    .tags
                    .iter()
                    .map(ToString::to_string)
                    .collect(),
            )),
            "links" => Ok(Value::StringSet(
                ctx.transaction
                    .links
                    .iter()
                    .map(ToString::to_string)
                    .collect(),
            )),
            "position" => {
                // Position includes both units and cost.
                // Uses resolve() to handle both per-unit and total cost syntax.
                if let Some(units) = posting.amount() {
                    if let Some(cost_spec) = &posting.cost
                        && let Some(cost) = cost_spec.resolve(units.number, ctx.transaction.date)
                    {
                        Ok(Value::Position(Box::new(Position::with_cost(
                            units.clone(),
                            cost,
                        ))))
                    } else {
                        Ok(Value::Position(Box::new(Position::simple(units.clone()))))
                    }
                } else {
                    Ok(Value::Null)
                }
            }
            "units" => Ok(posting
                .amount()
                .map_or(Value::Null, |u| Value::Amount(u.clone()))),
            "cost" => {
                // Get the cost of the posting
                if let Some(units) = posting.amount()
                    && let Some(cost) = &posting.cost
                    && let Some(number_per) = &cost.number_per
                    && let Some(currency) = &cost.currency
                {
                    let total = units.number.abs() * number_per;
                    return Ok(Value::Amount(Amount::new(total, currency.clone())));
                }
                Ok(Value::Null)
            }
            "weight" => {
                // Weight is the cost-converted amount used for transaction balancing.
                // With cost: units × cost (in cost currency)
                // With @ price: units × price (in price currency)
                // With @@ price: the total price directly
                // Otherwise: units as-is
                if let Some(units) = posting.amount() {
                    if let Some(cost) = &posting.cost
                        && let Some(number_per) = &cost.number_per
                        && let Some(currency) = &cost.currency
                    {
                        let total = units.number * number_per;
                        return Ok(Value::Amount(Amount::new(total, currency.clone())));
                    }
                    if let Some(price_ann) = &posting.price
                        && let Some(price_amt) = price_ann.amount()
                    {
                        return if price_ann.is_unit() {
                            Ok(Value::Amount(Amount::new(
                                units.number * price_amt.number,
                                price_amt.currency.clone(),
                            )))
                        } else {
                            Ok(Value::Amount(price_amt.clone()))
                        };
                    }
                    Ok(Value::Amount(units.clone()))
                } else {
                    Ok(Value::Null)
                }
            }
            "balance" => {
                // Cumulative running balance across WHERE-filtered postings —
                // matches bean-query semantics. See `PostingContext::balance`.
                if let Some(ref balance) = ctx.balance {
                    Ok(Value::Inventory(Box::new(balance.clone())))
                } else {
                    Ok(Value::Null)
                }
            }
            "account_balance" => {
                // Per-account running balance for this posting's account.
                // Always reflects the true ledger balance, independent of WHERE.
                if let Some(ref balance) = ctx.account_balance {
                    Ok(Value::Inventory(Box::new(balance.clone())))
                } else {
                    Ok(Value::Null)
                }
            }
            "year" => Ok(Value::Integer(ctx.transaction.date.year().into())),
            "month" => Ok(Value::Integer(ctx.transaction.date.month().into())),
            "day" => Ok(Value::Integer(ctx.transaction.date.day().into())),
            "currency" => Ok(posting
                .amount()
                .map_or(Value::Null, |u| Value::String(u.currency.to_string()))),
            "number" => Ok(posting
                .amount()
                .map_or(Value::Null, |u| Value::Number(u.number))),
            // Posting flag (separate from transaction flag)
            "posting_flag" => Ok(posting
                .flag
                .map_or(Value::Null, |f| Value::String(f.to_string()))),
            // Description: "payee | narration" or just narration (matches beancount)
            "description" => {
                let desc = match &ctx.transaction.payee {
                    Some(payee) => format!("{} | {}", payee, ctx.transaction.narration),
                    None => ctx.transaction.narration.to_string(),
                };
                Ok(Value::String(desc))
            }
            // Cost number (per-unit cost)
            "cost_number" => Ok(posting
                .cost
                .as_ref()
                .and_then(|c| c.number_per)
                .map_or(Value::Null, Value::Number)),
            // Cost currency
            "cost_currency" => Ok(posting
                .cost
                .as_ref()
                .and_then(|c| c.currency.as_ref())
                .map_or(Value::Null, |c| Value::String(c.to_string()))),
            // Cost date
            "cost_date" => Ok(posting
                .cost
                .as_ref()
                .and_then(|c| c.date)
                .map_or(Value::Null, Value::Date)),
            // Cost label
            "cost_label" => Ok(posting
                .cost
                .as_ref()
                .and_then(|c| c.label.as_ref())
                .map_or(Value::Null, |l| Value::String(l.clone()))),
            // Price annotation
            "price" => {
                use rustledger_core::PriceAnnotation;
                if let Some(price) = &posting.price {
                    match price {
                        PriceAnnotation::Unit(amount) | PriceAnnotation::Total(amount) => {
                            Ok(Value::Amount(amount.clone()))
                        }
                        PriceAnnotation::UnitIncomplete(inc)
                        | PriceAnnotation::TotalIncomplete(inc) => {
                            // Try to get complete amount from incomplete
                            if let Some(amount) = inc.as_amount().cloned() {
                                Ok(Value::Amount(amount))
                            } else {
                                Ok(Value::Null)
                            }
                        }
                        PriceAnnotation::UnitEmpty | PriceAnnotation::TotalEmpty => Ok(Value::Null),
                    }
                } else {
                    Ok(Value::Null)
                }
            }
            // All accounts in the transaction
            "accounts" => Ok(Value::StringSet(
                ctx.transaction
                    .postings
                    .iter()
                    .map(|p| p.account.to_string())
                    .collect(),
            )),
            // All accounts except the current posting's account
            "other_accounts" => {
                let current = &posting.account;
                Ok(Value::StringSet(
                    ctx.transaction
                        .postings
                        .iter()
                        .filter(|p| &p.account != current)
                        .map(|p| p.account.to_string())
                        .collect(),
                ))
            }
            // Posting metadata as dictionary
            "meta" => Ok(Value::Metadata(Box::new(posting.meta.clone()))),
            // Source location columns
            "filename" => {
                if let Some(idx) = ctx.directive_index {
                    if let Some(loc) = self.get_source_location(idx) {
                        Ok(Value::String(loc.filename.clone()))
                    } else {
                        Ok(Value::Null)
                    }
                } else {
                    Ok(Value::Null)
                }
            }
            "lineno" => {
                if let Some(idx) = ctx.directive_index {
                    if let Some(loc) = self.get_source_location(idx) {
                        Ok(Value::Integer(loc.lineno as i64))
                    } else {
                        Ok(Value::Null)
                    }
                } else {
                    Ok(Value::Null)
                }
            }
            "location" => {
                if let Some(idx) = ctx.directive_index {
                    if let Some(loc) = self.get_source_location(idx) {
                        Ok(Value::String(format!("{}:{}", loc.filename, loc.lineno)))
                    } else {
                        Ok(Value::Null)
                    }
                } else {
                    Ok(Value::Null)
                }
            }
            // has_cost - check if posting has cost specification
            "has_cost" => Ok(Value::Boolean(posting.cost.is_some())),
            // entry - parent transaction as structured object
            "entry" => {
                let txn = ctx.transaction;
                let mut obj = BTreeMap::new();
                obj.insert("date".to_string(), Value::Date(txn.date));
                obj.insert("flag".to_string(), Value::String(txn.flag.to_string()));
                if let Some(ref payee) = txn.payee {
                    obj.insert("payee".to_string(), Value::String(payee.to_string()));
                }
                obj.insert(
                    "narration".to_string(),
                    Value::String(txn.narration.to_string()),
                );
                obj.insert(
                    "tags".to_string(),
                    Value::StringSet(txn.tags.iter().map(ToString::to_string).collect()),
                );
                obj.insert(
                    "links".to_string(),
                    Value::StringSet(txn.links.iter().map(ToString::to_string).collect()),
                );
                // Include transaction metadata
                let mut meta_obj = BTreeMap::new();
                for (k, v) in &txn.meta {
                    meta_obj.insert(k.clone(), Self::meta_value_to_value(Some(v)));
                }
                obj.insert("meta".to_string(), Value::Object(Box::new(meta_obj)));
                Ok(Value::Object(Box::new(obj)))
            }
            // type - directive type (matches Python beancount's type column)
            // For SELECT FROM (default), this is always "Transaction"
            "type" => Ok(Value::String("Transaction".to_string())),
            // id - directive index (matches Python beancount's id column)
            "id" => Ok(ctx
                .directive_index
                .map_or(Value::Null, |idx| Value::Integer(idx as i64))),
            _ => Err(QueryError::UnknownColumn(name.to_string())),
        }
    }

    /// Evaluate a literal.
    pub(super) fn evaluate_literal(&self, lit: &Literal) -> Result<Value, QueryError> {
        Ok(match lit {
            Literal::String(s) => Value::String(s.clone()),
            Literal::Number(n) => Value::Number(*n),
            Literal::Integer(i) => Value::Integer(*i),
            Literal::Date(d) => Value::Date(*d),
            Literal::Boolean(b) => Value::Boolean(*b),
            Literal::Null => Value::Null,
        })
    }

    /// Evaluate a row of results for non-aggregate query.
    pub(super) fn evaluate_row(
        &self,
        targets: &[Target],
        ctx: &PostingContext,
    ) -> Result<Row, QueryError> {
        self.evaluate_row_with_window(targets, ctx, None)
    }

    /// Evaluate a row with optional window context.
    pub(super) fn evaluate_row_with_window(
        &self,
        targets: &[Target],
        ctx: &PostingContext,
        window_ctx: Option<&WindowContext>,
    ) -> Result<Row, QueryError> {
        let mut row = Vec::new();
        for target in targets {
            if matches!(target.expr, Expr::Wildcard) {
                // Expand wildcard to default columns.
                // Order must match WILDCARD_COLUMNS constant in mod.rs:
                // [date, flag, payee, narration, account, position]
                row.push(Value::Date(ctx.transaction.date));
                row.push(Value::String(ctx.transaction.flag.to_string()));
                row.push(
                    ctx.transaction
                        .payee
                        .as_ref()
                        .map_or(Value::Null, |p| Value::String(p.to_string())),
                );
                row.push(Value::String(ctx.transaction.narration.to_string()));
                let posting = &ctx.transaction.postings[ctx.posting_index];
                row.push(Value::String(posting.account.to_string()));
                row.push(
                    posting
                        .amount()
                        .map_or(Value::Null, |u| Value::Amount(u.clone())),
                );
            } else if let Expr::Window(wf) = &target.expr {
                // Handle window function
                row.push(self.evaluate_window_function(wf, window_ctx)?);
            } else {
                row.push(self.evaluate_expr(&target.expr, ctx)?);
            }
        }
        Ok(row)
    }
}
