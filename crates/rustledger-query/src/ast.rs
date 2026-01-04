//! BQL Abstract Syntax Tree types.
//!
//! This module defines the AST for Beancount Query Language (BQL),
//! a SQL-like query language for financial data analysis.

use rust_decimal::Decimal;
use rustledger_core::NaiveDate;

/// A complete BQL query.
#[derive(Debug, Clone, PartialEq)]
pub enum Query {
    /// SELECT query.
    Select(SelectQuery),
    /// JOURNAL shorthand query.
    Journal(JournalQuery),
    /// BALANCES shorthand query.
    Balances(BalancesQuery),
    /// PRINT shorthand query.
    Print(PrintQuery),
}

/// A SELECT query.
#[derive(Debug, Clone, PartialEq)]
pub struct SelectQuery {
    /// Whether DISTINCT was specified.
    pub distinct: bool,
    /// Target columns/expressions.
    pub targets: Vec<Target>,
    /// FROM clause (transaction-level filtering).
    pub from: Option<FromClause>,
    /// WHERE clause (posting-level filtering).
    pub where_clause: Option<Expr>,
    /// GROUP BY clause.
    pub group_by: Option<Vec<Expr>>,
    /// ORDER BY clause.
    pub order_by: Option<Vec<OrderSpec>>,
    /// LIMIT clause.
    pub limit: Option<u64>,
}

/// A target in the SELECT clause.
#[derive(Debug, Clone, PartialEq)]
pub struct Target {
    /// The expression to select.
    pub expr: Expr,
    /// Optional alias (AS name).
    pub alias: Option<String>,
}

/// FROM clause with transaction-level modifiers.
#[derive(Debug, Clone, PartialEq)]
pub struct FromClause {
    /// OPEN ON date - summarize entries before this date.
    pub open_on: Option<NaiveDate>,
    /// CLOSE ON date - truncate entries after this date.
    pub close_on: Option<NaiveDate>,
    /// CLEAR - transfer income/expense to equity.
    pub clear: bool,
    /// Filter expression.
    pub filter: Option<Expr>,
}

/// ORDER BY specification.
#[derive(Debug, Clone, PartialEq)]
pub struct OrderSpec {
    /// Expression to order by.
    pub expr: Expr,
    /// Sort direction.
    pub direction: SortDirection,
}

/// Sort direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SortDirection {
    /// Ascending (default).
    #[default]
    Asc,
    /// Descending.
    Desc,
}

/// JOURNAL shorthand query.
#[derive(Debug, Clone, PartialEq)]
pub struct JournalQuery {
    /// Account pattern to filter by.
    pub account_pattern: String,
    /// Optional aggregation function (AT cost, AT units, etc.).
    pub at_function: Option<String>,
    /// Optional FROM clause.
    pub from: Option<FromClause>,
}

/// BALANCES shorthand query.
#[derive(Debug, Clone, PartialEq)]
pub struct BalancesQuery {
    /// Optional aggregation function.
    pub at_function: Option<String>,
    /// Optional FROM clause.
    pub from: Option<FromClause>,
}

/// PRINT shorthand query.
#[derive(Debug, Clone, PartialEq)]
pub struct PrintQuery {
    /// Optional FROM clause.
    pub from: Option<FromClause>,
}

/// An expression in BQL.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// Wildcard (*).
    Wildcard,
    /// Column reference.
    Column(String),
    /// Literal value.
    Literal(Literal),
    /// Function call.
    Function(FunctionCall),
    /// Binary operation.
    BinaryOp(Box<BinaryOp>),
    /// Unary operation.
    UnaryOp(Box<UnaryOp>),
    /// Parenthesized expression.
    Paren(Box<Self>),
}

/// A literal value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    /// String literal.
    String(String),
    /// Numeric literal.
    Number(Decimal),
    /// Integer literal.
    Integer(i64),
    /// Date literal.
    Date(NaiveDate),
    /// Boolean literal.
    Boolean(bool),
    /// NULL literal.
    Null,
}

/// A function call.
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionCall {
    /// Function name.
    pub name: String,
    /// Arguments.
    pub args: Vec<Expr>,
}

/// A binary operation.
#[derive(Debug, Clone, PartialEq)]
pub struct BinaryOp {
    /// Left operand.
    pub left: Expr,
    /// Operator.
    pub op: BinaryOperator,
    /// Right operand.
    pub right: Expr,
}

/// Binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOperator {
    // Comparison
    /// Equal (=).
    Eq,
    /// Not equal (!=).
    Ne,
    /// Less than (<).
    Lt,
    /// Less than or equal (<=).
    Le,
    /// Greater than (>).
    Gt,
    /// Greater than or equal (>=).
    Ge,
    /// Regular expression match (~).
    Regex,
    /// IN operator.
    In,

    // Logical
    /// Logical AND.
    And,
    /// Logical OR.
    Or,

    // Arithmetic
    /// Addition (+).
    Add,
    /// Subtraction (-).
    Sub,
    /// Multiplication (*).
    Mul,
    /// Division (/).
    Div,
}

/// A unary operation.
#[derive(Debug, Clone, PartialEq)]
pub struct UnaryOp {
    /// Operator.
    pub op: UnaryOperator,
    /// Operand.
    pub operand: Expr,
}

/// Unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOperator {
    /// Logical NOT.
    Not,
    /// Negation (-).
    Neg,
}

impl SelectQuery {
    /// Create a new SELECT query with the given targets.
    pub const fn new(targets: Vec<Target>) -> Self {
        Self {
            distinct: false,
            targets,
            from: None,
            where_clause: None,
            group_by: None,
            order_by: None,
            limit: None,
        }
    }

    /// Set the DISTINCT flag.
    pub const fn distinct(mut self) -> Self {
        self.distinct = true;
        self
    }

    /// Set the FROM clause.
    pub fn from(mut self, from: FromClause) -> Self {
        self.from = Some(from);
        self
    }

    /// Set the WHERE clause.
    pub fn where_clause(mut self, expr: Expr) -> Self {
        self.where_clause = Some(expr);
        self
    }

    /// Set the GROUP BY clause.
    pub fn group_by(mut self, exprs: Vec<Expr>) -> Self {
        self.group_by = Some(exprs);
        self
    }

    /// Set the ORDER BY clause.
    pub fn order_by(mut self, specs: Vec<OrderSpec>) -> Self {
        self.order_by = Some(specs);
        self
    }

    /// Set the LIMIT.
    pub const fn limit(mut self, n: u64) -> Self {
        self.limit = Some(n);
        self
    }
}

impl Target {
    /// Create a new target from an expression.
    pub const fn new(expr: Expr) -> Self {
        Self { expr, alias: None }
    }

    /// Create a target with an alias.
    pub fn with_alias(expr: Expr, alias: impl Into<String>) -> Self {
        Self {
            expr,
            alias: Some(alias.into()),
        }
    }
}

impl FromClause {
    /// Create a new empty FROM clause.
    pub const fn new() -> Self {
        Self {
            open_on: None,
            close_on: None,
            clear: false,
            filter: None,
        }
    }

    /// Set the OPEN ON date.
    pub const fn open_on(mut self, date: NaiveDate) -> Self {
        self.open_on = Some(date);
        self
    }

    /// Set the CLOSE ON date.
    pub const fn close_on(mut self, date: NaiveDate) -> Self {
        self.close_on = Some(date);
        self
    }

    /// Set the CLEAR flag.
    pub const fn clear(mut self) -> Self {
        self.clear = true;
        self
    }

    /// Set the filter expression.
    pub fn filter(mut self, expr: Expr) -> Self {
        self.filter = Some(expr);
        self
    }
}

impl Default for FromClause {
    fn default() -> Self {
        Self::new()
    }
}

impl Expr {
    /// Create a column reference.
    pub fn column(name: impl Into<String>) -> Self {
        Self::Column(name.into())
    }

    /// Create a string literal.
    pub fn string(s: impl Into<String>) -> Self {
        Self::Literal(Literal::String(s.into()))
    }

    /// Create a number literal.
    pub const fn number(n: Decimal) -> Self {
        Self::Literal(Literal::Number(n))
    }

    /// Create an integer literal.
    pub const fn integer(n: i64) -> Self {
        Self::Literal(Literal::Integer(n))
    }

    /// Create a date literal.
    pub const fn date(d: NaiveDate) -> Self {
        Self::Literal(Literal::Date(d))
    }

    /// Create a boolean literal.
    pub const fn boolean(b: bool) -> Self {
        Self::Literal(Literal::Boolean(b))
    }

    /// Create a NULL literal.
    pub const fn null() -> Self {
        Self::Literal(Literal::Null)
    }

    /// Create a function call.
    pub fn function(name: impl Into<String>, args: Vec<Self>) -> Self {
        Self::Function(FunctionCall {
            name: name.into(),
            args,
        })
    }

    /// Create a binary operation.
    pub fn binary(left: Self, op: BinaryOperator, right: Self) -> Self {
        Self::BinaryOp(Box::new(BinaryOp { left, op, right }))
    }

    /// Create a unary operation.
    pub fn unary(op: UnaryOperator, operand: Self) -> Self {
        Self::UnaryOp(Box::new(UnaryOp { op, operand }))
    }
}

impl OrderSpec {
    /// Create an ascending order spec.
    pub const fn asc(expr: Expr) -> Self {
        Self {
            expr,
            direction: SortDirection::Asc,
        }
    }

    /// Create a descending order spec.
    pub const fn desc(expr: Expr) -> Self {
        Self {
            expr,
            direction: SortDirection::Desc,
        }
    }
}
