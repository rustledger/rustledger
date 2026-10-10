//! Core expression and predicate evaluation functions.

use std::collections::BTreeMap;

use rustledger_core::{Amount, CostNumber, Position, Transaction};

use crate::ast::{Expr, Literal, Target};
use crate::error::QueryError;

use super::Executor;
use super::system_tables::TxnAccounts;
use super::types::{PostingContext, Row, Value, WindowContext};

impl Executor<'_> {
    /// Evaluate a FROM filter on one posting of a transaction.
    ///
    /// `posting_index` is the posting a posting column reads. An
    /// entry-level filter ([`from_filter_reads_postings`] is false) answers
    /// the same for every posting, so the posting sources evaluate it once
    /// per transaction; a posting-level one is evaluated per posting and
    /// filters ROWS (#2414). This used to be evaluated once per
    /// transaction against its FIRST posting, so `FROM account ~ 'Bank'`
    /// kept the transactions whose first posting was the bank's.
    pub(super) fn evaluate_from_filter(
        &self,
        filter: &Expr,
        txn: &Transaction,
        posting_index: usize,
        directive_index: Option<usize>,
    ) -> Result<bool, QueryError> {
        let ctx = || PostingContext {
            transaction: txn.into(),
            posting_index,
            balance: None,
            account_balance: None,
            directive_index,
            txn_accounts: None,
        };
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
                        Expr::Literal(Literal::String(s)) => s.value().to_string(),
                        Expr::Column(s) => s.clone(),
                        _ => {
                            return Err(QueryError::Type(
                                "has_account expects a string pattern".to_string(),
                            ));
                        }
                    };
                    // Same helper the projection arm uses, so the two spellings
                    // cannot drift.
                    self.entry_has_account(txn, &pattern)
                } else {
                    self.evaluate_predicate(filter, &ctx())
                }
            }
            Expr::BinaryOp(op) => {
                use crate::ast::BinaryOperator;
                // Handle YEAR = N, MONTH = N, etc. Only `=` and `!=`: these
                // arms answer `!matches` for any other operator, so
                // `FROM year > 2014` read as `year != 2014`. The rest go to
                // the general evaluation.
                let eq_or_ne = matches!(op.op, BinaryOperator::Eq | BinaryOperator::Ne);
                match (&op.left, &op.right) {
                    (Expr::Column(col), Expr::Literal(lit))
                        if eq_or_ne && col.to_uppercase() == "YEAR" =>
                    {
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
                    (Expr::Column(col), Expr::Literal(lit))
                        if eq_or_ne && col.to_uppercase() == "MONTH" =>
                    {
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
                    _ => self.evaluate_predicate(filter, &ctx()),
                }
            }
            _ => self.evaluate_predicate(filter, &ctx()),
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
            Expr::Attribute { operand, name } => {
                Self::eval_attribute(self.evaluate_expr(operand, ctx)?, name)
            }
            Expr::Subscript { operand, key } => {
                Self::eval_subscript(&self.evaluate_expr(operand, ctx)?, key)
            }
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
    /// The parent transaction as a structured [`Value::Object`] — the
    /// `entry` column (attribute-accessible via `entry.<field>`, #1796).
    /// CANONICAL builder: the default-path `entry` column and the
    /// `#postings` table's `entry` column both call this, so their
    /// shapes cannot drift.
    pub(super) fn entry_object(
        txn: &rustledger_core::Transaction,
        entry_loc: Option<&crate::executor::SourceLocation>,
    ) -> Value {
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
        // Same filename/lineno augmentation the ENTRY_META function and
        // the posting-level `meta` column apply (via `augmented_meta`), so
        // `entry.meta['filename']` agrees with `entry_meta('filename')` —
        // upstream's entry.meta always carries source location (#1800
        // review).
        let augmented = Self::augmented_meta(&txn.meta, entry_loc);
        let mut meta_obj = BTreeMap::new();
        for (k, v) in &augmented {
            meta_obj.insert(k.clone(), Self::meta_value_to_value(Some(v)));
        }
        obj.insert("meta".to_string(), Value::Object(Box::new(meta_obj)));
        Value::Object(Box::new(obj))
    }

    /// Dotted attribute access (`entry.meta`, #1796). Upstream compiles
    /// attributes against structured dtypes and errors on non-structured
    /// operands; rustledger's structured values are dynamic
    /// [`Value::Object`]s, so lookup happens here at evaluation time.
    ///
    /// Stricter-vs-looser note (Python Compatibility Policy): a MISSING
    /// attribute returns `NULL`, where upstream distinguishes "field
    /// exists but is None" (NULL) from "no such attribute" (compile
    /// error). rustledger's `entry` object omits empty fields (e.g. an
    /// absent payee), so the two cases are indistinguishable at runtime —
    /// NULL reproduces upstream for the common case and is lenient for
    /// typos. Pinned in `attribute_subscript_test.rs`.
    pub(super) fn eval_attribute(value: Value, name: &str) -> Result<Value, QueryError> {
        match value {
            Value::Object(obj) => Ok(obj.get(name).cloned().unwrap_or(Value::Null)),
            Value::Null => Ok(Value::Null),
            other => Err(QueryError::Type(format!(
                "cannot access attribute '{name}': operand {other:?} is not structured"
            ))),
        }
    }

    /// String-keyed subscript access (`meta['key']`, #1796). Delegates to
    /// the CANONICAL [`Self::getitem_lookup`] shared with the GETITEM
    /// function, so the two spellings of the same lookup cannot drift
    /// (the first draft re-implemented two of GETITEM's three arms and
    /// `balance['USD']` type-errored where `getitem(balance,'USD')`
    /// worked — #1800 review).
    pub(super) fn eval_subscript(value: &Value, key: &str) -> Result<Value, QueryError> {
        Self::getitem_lookup(value, key)
    }

    /// CANONICAL container lookup for GETITEM and `[...]` subscripts:
    /// inventory-by-currency, metadata-by-key, object-by-key. A missing
    /// key (or zero inventory units) is `NULL`, like upstream's `getitem`.
    pub(super) fn getitem_lookup(container: &Value, key: &str) -> Result<Value, QueryError> {
        match container {
            Value::Inventory(inv) => {
                let amount = inv.units(key);
                if amount.is_zero() {
                    Ok(Value::Null)
                } else {
                    Ok(Value::Amount(rustledger_core::Amount::new(amount, key)))
                }
            }
            Value::Metadata(meta) => Ok(Self::meta_value_to_value(meta.get(key))),
            Value::Object(obj) => Ok(obj.get(key).cloned().unwrap_or(Value::Null)),
            Value::Null => Ok(Value::Null),
            other => Err(QueryError::Type(format!(
                "cannot subscript with '{key}': operand {other:?} is not a mapping"
            ))),
        }
    }

    pub(super) fn evaluate_column(
        &self,
        name: &str,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        let placeholder;
        let posting = if let Some(posting) = ctx.transaction.postings.get(ctx.posting_index) {
            posting
        } else {
            // A transaction without postings, under an entry-level FROM
            // filter (`PRINT FROM narration ~ ...`). Its entry columns are
            // read; a posting column reads a posting with nothing in it.
            // This indexed the postings and panicked.
            placeholder = rustledger_core::Posting::auto("");
            &placeholder
        };

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
                    Ok(Value::Position(Box::new(Position::from_posting(
                        units,
                        posting.cost.as_deref(),
                        ctx.transaction.date,
                    ))))
                } else {
                    Ok(Value::Null)
                }
            }
            "units" => Ok(posting
                .amount()
                .map_or(Value::Null, |u| Value::Amount(u.clone()))),
            "cost" => {
                // The posting's cost, unsigned: what `units` cost, whichever
                // side of the lot they are on. From the canonical weight rule,
                // which for a per-unit cost is `|units| × per-unit` and for a
                // total-carrying one (`{{T}}`, or the sale that empties such a
                // lot) is that total exactly (#2425). This multiplied the
                // resolved per-unit cost back out, which gave 500.00…01 for a
                // lot that cost 500, with a bare `*` that panicked on overflow.
                if let Some(units) = posting.amount()
                    && let Some(cost) = &posting.cost
                    && let Some(number) = cost.number.as_ref()
                    && let Some(currency) = &cost.currency
                {
                    let total = rustledger_booking::cost_number_weight(units.number, number)
                        .ok_or_else(|| super::overflow_err(currency))?;
                    return Ok(Value::Amount(Amount::new(total.abs(), currency.clone())));
                }
                Ok(Value::Null)
            }
            "weight" => {
                // Delegate to the shared helper so this path can't drift
                // from `build_postings_table`'s weight column. The two
                // sites had drifted on `@@` sign handling, which was the
                // root cause of issue #1052.
                Ok(super::compute_posting_weight(posting))
            }
            "balance" => {
                // Cumulative running balance across WHERE-filtered postings —
                // matches bean-query semantics. See `PostingContext::balance`.
                if let Some(ref balance) = ctx.balance {
                    Ok(Value::Inventory(std::sync::Arc::new(balance.clone())))
                } else {
                    Ok(Value::Null)
                }
            }
            "account_balance" => {
                // Per-account running balance for this posting's account.
                // Always reflects the true ledger balance, independent of WHERE.
                if let Some(ref balance) = ctx.account_balance {
                    // `Arc::clone`, not a copy of the inventory. Reading this
                    // column used to deep-clone every lot a second time, on top
                    // of the copy the context already held — once per row that
                    // reads it (#2086).
                    Ok(Value::Inventory(std::sync::Arc::clone(balance)))
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
            // Cost number (per-unit cost). After booking, both
            // `PerUnit` and `PerUnitFromTotal` expose a per-unit
            // value via `per_unit()`. Pre-booking `Total` returns
            // None — callers wanting a per-unit must compute it from
            // units, which the booker has already done by the time
            // this column is queried.
            "cost_number" => Ok(posting
                .cost
                .as_ref()
                .and_then(|c| c.number.as_ref().and_then(CostNumber::per_unit))
                .map_or(Value::Null, Value::Number)),
            // Cost currency
            "cost_currency" => Ok(posting
                .cost
                .as_ref()
                .and_then(|c| c.currency.as_ref())
                .map_or(Value::Null, |c| Value::String(c.to_string()))),
            // Cost date — the *resolved* cost date, not the raw spec date: an
            // undated cost (`{150 USD}`) inherits the transaction date when
            // booked, which is what bean-query and the `#postings` table report.
            // Reading the raw `CostSpec.date` (often `None`) was the divergence.
            "cost_date" => Ok(posting
                .amount()
                .and_then(|units| {
                    posting
                        .cost
                        .as_ref()
                        .and_then(|cs| cs.resolve(units.number, ctx.transaction.date))
                })
                .and_then(|cost| cost.date)
                .map_or(Value::Null, Value::Date)),
            // Cost label
            "cost_label" => Ok(posting
                .cost
                .as_ref()
                .and_then(|c| c.label.as_ref())
                .map_or(Value::Null, |l| Value::String(l.clone()))),
            // Price annotation: return the complete amount (`kind`
            // doesn't matter for the BQL `price` accessor — Python
            // bean-query yields the same Amount for `@` and `@@`).
            // Incomplete amounts or bare-sigil prices return Null.
            "price" => {
                use rustledger_core::IncompleteAmount;
                Ok(posting
                    .price
                    .as_ref()
                    .and_then(|p| p.amount.as_ref())
                    .and_then(IncompleteAmount::as_amount)
                    .map_or(Value::Null, |a| Value::Amount(a.clone())))
            }
            // All accounts in the transaction, as a sorted set
            // (bean-query: `{p.account for p in entry.postings}`).
            "accounts" => Ok(Value::StringSet(ctx.txn_accounts.as_ref().map_or_else(
                || TxnAccounts::of(&ctx.transaction).accounts(),
                |set| set.accounts(),
            ))),
            // The accounts of every OTHER posting, as a sorted set. Only this
            // posting is excluded: another posting to the same account still
            // counts (bean-query: `sorted({p.account for p in entry.postings
            // if p is not context.posting})`, #2483).
            //
            // The scan builds the set once per transaction (#2504); a context
            // built without it (a FROM filter's) builds it here.
            "other_accounts" => {
                let account = posting.account.as_ref();
                Ok(Value::StringSet(ctx.txn_accounts.as_ref().map_or_else(
                    || TxnAccounts::of(&ctx.transaction).others(account),
                    |set| set.others(account),
                )))
            }
            // Posting metadata as dictionary
            "meta" => Ok(Value::Metadata(Box::new(Self::augmented_meta(
                &posting.meta,
                self.resolved_source_location(ctx).as_ref(),
            )))),
            // Source location columns — resolved from the posting's own span
            // (falling back to the enclosing directive's location).
            "filename" => Ok(Self::source_filename_value(
                self.resolved_source_location(ctx).as_ref(),
            )),
            "lineno" => Ok(Self::source_lineno_value(
                self.resolved_source_location(ctx).as_ref(),
            )),
            "location" => Ok(Self::source_location_value(
                self.resolved_source_location(ctx).as_ref(),
            )),
            // has_cost - check if posting has cost specification
            "has_cost" => Ok(Value::Boolean(posting.cost.is_some())),
            // entry - parent transaction as structured object. The
            // location is the enclosing DIRECTIVE's (like ENTRY_META),
            // not the posting's.
            "entry" => {
                let entry_loc = ctx
                    .directive_index
                    .and_then(|i| self.get_source_location(i).cloned());
                Ok(Self::entry_object(&ctx.transaction, entry_loc.as_ref()))
            }
            // type - directive type. bean-query lowercases it (`transaction`),
            // and the `#postings` table already emits lowercase; the default
            // posting source is always a transaction. (Confirmed against the
            // bean-query oracle.)
            "type" => Ok(Value::String("transaction".to_string())),
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
            Literal::String(s) => Value::String(s.value().to_string()),
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

/// Columns a `FROM` filter can read with one value per transaction: the
/// entry's own, which every posting row of a transaction shares.
///
/// An allowlist on purpose. A filter reading only these is evaluated once per
/// transaction and keeps or drops it whole; any other filter is evaluated per
/// posting and filters rows. Leaving an entry column off this list only costs
/// an evaluation per posting, with the same answer; putting a posting column
/// on it brings back #2414, where the first posting answered for all of them.
/// `filename`, `lineno` and `meta` are absent: on a posting row they are the
/// posting's. `from_filter_column_lists_match_the_executor` checks this list
/// against the row evaluator's columns.
pub(super) const FROM_ENTRY_COLUMNS: &[&str] = &[
    "date",
    "year",
    "month",
    "day",
    "flag",
    "payee",
    "narration",
    "description",
    "tags",
    "links",
    "accounts",
    "type",
    "id",
    "entry",
];

/// Does this `FROM` filter read anything that differs between the postings of
/// one transaction (#2414)?
///
/// beanquery compiles the `FROM` expression into the `WHERE` clause
/// (`compiler.py`, `_select`: `c_where = EvalAnd([c_from_expr, c_where])`), so
/// on the posting sources a posting column in it filters rows, after
/// `OPEN` / `CLOSE` / `CLEAR` have rewritten the stream. A filter that reads
/// only entry columns gives every row of a transaction the same answer, which
/// is why evaluating it once per transaction is the same thing.
pub(super) fn from_filter_reads_postings(expr: &Expr) -> bool {
    match expr {
        Expr::Column(name) => !FROM_ENTRY_COLUMNS
            .iter()
            .any(|c| c.eq_ignore_ascii_case(name)),
        Expr::Function(func) => match func.name.to_uppercase().as_str() {
            // Asks about the whole entry; its argument is a pattern, and a
            // bare word there is the pattern, not a column.
            "HAS_ACCOUNT" => false,
            // Read the row's posting metadata (`ENTRY_META` reads the entry's).
            "META" | "POSTING_META" | "ANY_META" => true,
            _ => func.args.iter().any(from_filter_reads_postings),
        },
        Expr::Attribute { operand, .. } | Expr::Subscript { operand, .. } => {
            from_filter_reads_postings(operand)
        }
        Expr::BinaryOp(op) => {
            from_filter_reads_postings(&op.left) || from_filter_reads_postings(&op.right)
        }
        Expr::UnaryOp(op) => from_filter_reads_postings(&op.operand),
        Expr::Paren(inner) => from_filter_reads_postings(inner),
        Expr::Between { value, low, high } => {
            from_filter_reads_postings(value)
                || from_filter_reads_postings(low)
                || from_filter_reads_postings(high)
        }
        Expr::Set(items) => items.iter().any(from_filter_reads_postings),
        Expr::Literal(_) => false,
        // Neither belongs in a FROM filter; answering per posting is the
        // reading that cannot be wrong.
        Expr::Wildcard | Expr::Window(_) => true,
    }
}

/// Columns of a posting row that the entries `PRINT` prints do not have:
/// beanquery's `postings` columns that its `entries` table lacks, plus
/// rledger's own posting columns. Checked by the same test as
/// [`FROM_ENTRY_COLUMNS`].
pub(super) const POSTING_ONLY_COLUMNS: &[&str] = &[
    "account",
    "other_accounts",
    "position",
    "units",
    "cost",
    "weight",
    "balance",
    "account_balance",
    "number",
    "currency",
    "posting_flag",
    "cost_number",
    "cost_currency",
    "cost_date",
    "cost_label",
    "price",
    "has_cost",
    "location",
    "entry",
];

/// The first posting-only column this `PRINT` `FROM` filter reads, if any.
///
/// `PRINT` returns whole entries, and a posting predicate does not say which
/// entries to print, so both bean-query versions reject it: beanquery 0.2
/// compiles `PRINT`'s `FROM` against its `entries` table (`column "account"
/// not found in table "entries"`), beancount v2 against its FROM context. This
/// used to read the entry's first posting instead (#2414).
pub(super) fn print_filter_posting_column(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Column(name) => POSTING_ONLY_COLUMNS
            .iter()
            .any(|c| c.eq_ignore_ascii_case(name))
            .then_some(name.as_str()),
        Expr::Function(func) => {
            if func.name.eq_ignore_ascii_case("HAS_ACCOUNT") {
                None
            } else {
                func.args.iter().find_map(print_filter_posting_column)
            }
        }
        Expr::Attribute { operand, .. } | Expr::Subscript { operand, .. } => {
            print_filter_posting_column(operand)
        }
        Expr::BinaryOp(op) => {
            print_filter_posting_column(&op.left).or_else(|| print_filter_posting_column(&op.right))
        }
        Expr::UnaryOp(op) => print_filter_posting_column(&op.operand),
        Expr::Paren(inner) => print_filter_posting_column(inner),
        Expr::Between { value, low, high } => print_filter_posting_column(value)
            .or_else(|| print_filter_posting_column(low))
            .or_else(|| print_filter_posting_column(high)),
        Expr::Set(items) => items.iter().find_map(print_filter_posting_column),
        Expr::Window(call) => call.args.iter().find_map(print_filter_posting_column),
        Expr::Literal(_) | Expr::Wildcard => None,
    }
}
