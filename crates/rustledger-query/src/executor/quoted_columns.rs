//! A double-quoted string that names a column is that column (#2596).
//!
//! bean-query accepts both quote styles for strings, which makes `"x"`
//! ambiguous between a string and a quoted identifier. Its compiler settles
//! it per table (`compiler.py`, `_constant`):
//!
//! ```python
//! # Strings delimited by double quotes are treated as column names when
//! # they resolve to an existing column in the current table.
//! if isinstance(node.value, str) and node.text and node.text[0] == '"':
//!     if node.value in self.table.columns:
//!         return self._column(ast.Column(node.value))
//! return EvalConstant(node.value)
//! ```
//!
//! Every expression goes through that compiler, so the rule holds in every
//! clause that takes one: the targets, `WHERE`, `GROUP BY`, `HAVING`,
//! `ORDER BY` and function arguments. The match is exact (`"ACCOUNT"` stays a
//! string, column names being lower case) and against the table the query
//! reads: the postings, a `FROM #table`, a created table, or a subquery's own
//! output names (`SELECT "x" FROM (SELECT account AS x)` reads `x`). A
//! single-quoted string is always a string, and so is a double-quoted one no
//! column has the name of (`WHERE account ~ "Cash"`).
//!
//! A target rewritten this way keeps the header bean-query gives it, its
//! source text: `SELECT "account"` heads `"account"`
//! (`get_target_name` returns `target.expression.text` for anything that was
//! not parsed as a column).
//!
//! `PIVOT BY` is different: its grammar takes identifiers, not expressions,
//! so a double-quoted name there is a quoted identifier whatever columns
//! exist, naming a target (`AS "2023" ... PIVOT BY "2023", ...`, #2577).

use crate::ast::{Expr, Literal, QuoteStyle, SelectQuery};

use super::Executor;

/// The double-quoted string `expr` is, if it is one.
fn double_quoted(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Literal(Literal::String(s)) if s.quote() == Some(QuoteStyle::Double) => {
            Some(s.value())
        }
        _ => None,
    }
}

/// Replace, in place, every double-quoted string in `expr` that `is_column`
/// accepts with that column. Returns whether anything changed.
fn rewrite_expr(expr: &mut Expr, is_column: &impl Fn(&str) -> bool) -> bool {
    if let Some(name) = double_quoted(expr) {
        if is_column(name) {
            *expr = Expr::Column(name.to_string());
            return true;
        }
        return false;
    }
    let mut changed = false;
    let mut go = |e: &mut Expr| changed |= rewrite_expr(e, is_column);
    match expr {
        Expr::Function(call) => call.args.iter_mut().for_each(&mut go),
        Expr::Window(call) => {
            call.args.iter_mut().for_each(&mut go);
            call.over
                .partition_by
                .iter_mut()
                .flatten()
                .for_each(&mut go);
            for spec in call.over.order_by.iter_mut().flatten() {
                go(&mut spec.expr);
            }
        }
        Expr::Attribute { operand, .. } | Expr::Subscript { operand, .. } => go(operand),
        Expr::BinaryOp(op) => {
            go(&mut op.left);
            go(&mut op.right);
        }
        Expr::UnaryOp(op) => go(&mut op.operand),
        Expr::Paren(inner) => go(inner),
        Expr::Between { value, low, high } => {
            go(value);
            go(low);
            go(high);
        }
        Expr::Set(items) => items.iter_mut().for_each(&mut go),
        Expr::Column(_) | Expr::Wildcard | Expr::Literal(_) => {}
    }
    changed
}

/// `expr` with the double-quote rule applied against the columns `is_column`
/// accepts, or `None` when nothing in it changes. For the clauses of
/// `JOURNAL`, `BALANCES` and `PRINT`, which bean-query compiles as it does a
/// `SELECT`'s: `PRINT FROM ("narration" = 'pay')` reads the narration.
pub(super) fn resolve_double_quoted_expr(
    expr: &Expr,
    is_column: impl Fn(&str) -> bool,
) -> Option<Expr> {
    let mut out = expr.clone();
    rewrite_expr(&mut out, &is_column).then_some(out)
}

/// Whether `name` is a column of the default posting row source.
pub(super) fn is_posting_column(name: &str) -> bool {
    super::POSTING_COLUMNS.iter().any(|c| c.name == name)
}

impl Executor<'_> {
    /// `query` with bean-query's double-quote rule applied (see the module
    /// docs), resolving against the columns `is_column` accepts, or `None`
    /// when nothing in it changes.
    ///
    /// Idempotent: a rewritten string is a column afterward, and a target
    /// rewritten keeps its header as an alias, so running this again on the
    /// result changes nothing.
    pub(super) fn resolve_double_quoted_columns(
        &self,
        query: &SelectQuery,
        is_column: impl Fn(&str) -> bool,
    ) -> Option<SelectQuery> {
        let mut out = query.clone();
        let mut changed = false;

        for target in &mut out.targets {
            // The header bean-query gives the target: its source text, which
            // is what the target was named before the rewrite.
            let header = self.expr_to_name(&target.expr);
            if rewrite_expr(&mut target.expr, &is_column) {
                changed = true;
                if target.alias.is_none() {
                    target.alias = Some(header);
                }
            }
        }
        if let Some(from) = &mut out.from
            && let Some(filter) = &mut from.filter
        {
            changed |= rewrite_expr(filter, &is_column);
        }
        for expr in out
            .where_clause
            .iter_mut()
            .chain(out.having.iter_mut())
            .chain(out.group_by.iter_mut().flatten())
        {
            changed |= rewrite_expr(expr, &is_column);
        }
        for spec in out.order_by.iter_mut().flatten() {
            changed |= rewrite_expr(&mut spec.expr, &is_column);
        }
        // A quoted identifier, whatever the columns are (module docs).
        for expr in out.pivot_by.iter_mut().flatten() {
            if let Some(name) = double_quoted(expr) {
                *expr = Expr::Column(name.to_string());
                changed = true;
            }
        }

        changed.then_some(out)
    }
}
