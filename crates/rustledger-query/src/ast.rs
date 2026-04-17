//! BQL Abstract Syntax Tree types.
//!
//! This module defines the AST for Beancount Query Language (BQL),
//! a SQL-like query language for financial data analysis.

use rust_decimal::Decimal;
use rustledger_core::NaiveDate;
use std::fmt;

/// A complete BQL query.
#[derive(Debug, Clone, PartialEq)]
pub enum Query {
    /// SELECT query (boxed to reduce enum size).
    Select(Box<SelectQuery>),
    /// JOURNAL shorthand query.
    Journal(JournalQuery),
    /// BALANCES shorthand query.
    Balances(BalancesQuery),
    /// PRINT shorthand query.
    Print(PrintQuery),
    /// CREATE TABLE statement.
    CreateTable(CreateTableStmt),
    /// INSERT statement.
    Insert(InsertStmt),
}

/// Column definition for CREATE TABLE.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ColumnDef {
    /// Column name.
    pub name: String,
    /// Optional type hint (BQL is dynamically typed, but hints are allowed).
    pub type_hint: Option<String>,
}

/// CREATE TABLE statement.
#[derive(Debug, Clone, PartialEq)]
pub struct CreateTableStmt {
    /// Table name.
    pub table_name: String,
    /// Column definitions.
    pub columns: Vec<ColumnDef>,
    /// Optional AS SELECT (create from query).
    pub as_select: Option<Box<SelectQuery>>,
}

/// INSERT statement.
#[derive(Debug, Clone, PartialEq)]
pub struct InsertStmt {
    /// Target table name.
    pub table_name: String,
    /// Optional column list (if omitted, uses all columns in order).
    pub columns: Option<Vec<String>>,
    /// Source data: either VALUES or SELECT.
    pub source: InsertSource,
}

/// Source data for INSERT.
#[derive(Debug, Clone, PartialEq)]
pub enum InsertSource {
    /// VALUES clause with literal rows.
    Values(Vec<Vec<Expr>>),
    /// SELECT query as source.
    Select(Box<SelectQuery>),
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
    /// HAVING clause (filter on aggregated results).
    pub having: Option<Expr>,
    /// PIVOT BY clause (pivot table transformation).
    pub pivot_by: Option<Vec<Expr>>,
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
    /// Subquery (derived table).
    pub subquery: Option<Box<SelectQuery>>,
    /// Table name (for querying user-created tables).
    pub table_name: Option<String>,
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
    /// Optional WHERE clause.
    pub where_clause: Option<Expr>,
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
    /// Window function call (with OVER clause).
    Window(WindowFunction),
    /// Binary operation.
    BinaryOp(Box<BinaryOp>),
    /// Unary operation.
    UnaryOp(Box<UnaryOp>),
    /// Parenthesized expression.
    Paren(Box<Self>),
    /// BETWEEN ... AND expression.
    Between {
        /// Value to test.
        value: Box<Self>,
        /// Lower bound.
        low: Box<Self>,
        /// Upper bound.
        high: Box<Self>,
    },
    /// Set literal for IN operator, e.g., `('EUR', 'USD')`.
    Set(Vec<Self>),
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

/// A window function call (function with OVER clause).
#[derive(Debug, Clone, PartialEq)]
pub struct WindowFunction {
    /// Function name (`ROW_NUMBER`, RANK, SUM, etc.).
    pub name: String,
    /// Function arguments.
    pub args: Vec<Expr>,
    /// Window specification.
    pub over: WindowSpec,
}

/// Window specification for OVER clause.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct WindowSpec {
    /// PARTITION BY expressions.
    pub partition_by: Option<Vec<Expr>>,
    /// ORDER BY specifications.
    pub order_by: Option<Vec<OrderSpec>>,
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
    /// Regular expression not match (!~).
    NotRegex,
    /// IN operator.
    In,
    /// NOT IN operator.
    NotIn,

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
    /// Modulo (%).
    Mod,
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
    /// IS NULL.
    IsNull,
    /// IS NOT NULL.
    IsNotNull,
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
            having: None,
            pivot_by: None,
            order_by: None,
            limit: None,
        }
    }

    /// Set the DISTINCT flag.
    #[must_use]
    pub const fn distinct(mut self) -> Self {
        self.distinct = true;
        self
    }

    /// Set the FROM clause.
    #[must_use]
    pub fn from(mut self, from: FromClause) -> Self {
        self.from = Some(from);
        self
    }

    /// Set the WHERE clause.
    #[must_use]
    pub fn where_clause(mut self, expr: Expr) -> Self {
        self.where_clause = Some(expr);
        self
    }

    /// Set the GROUP BY clause.
    #[must_use]
    pub fn group_by(mut self, exprs: Vec<Expr>) -> Self {
        self.group_by = Some(exprs);
        self
    }

    /// Set the HAVING clause.
    #[must_use]
    pub fn having(mut self, expr: Expr) -> Self {
        self.having = Some(expr);
        self
    }

    /// Set the PIVOT BY clause.
    #[must_use]
    pub fn pivot_by(mut self, exprs: Vec<Expr>) -> Self {
        self.pivot_by = Some(exprs);
        self
    }

    /// Set the ORDER BY clause.
    #[must_use]
    pub fn order_by(mut self, specs: Vec<OrderSpec>) -> Self {
        self.order_by = Some(specs);
        self
    }

    /// Set the LIMIT.
    #[must_use]
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
            subquery: None,
            table_name: None,
        }
    }

    /// Create a FROM clause from a subquery.
    pub fn from_subquery(query: SelectQuery) -> Self {
        Self {
            open_on: None,
            close_on: None,
            clear: false,
            filter: None,
            subquery: Some(Box::new(query)),
            table_name: None,
        }
    }

    /// Create a FROM clause from a table name.
    pub fn from_table(name: impl Into<String>) -> Self {
        Self {
            open_on: None,
            close_on: None,
            clear: false,
            filter: None,
            subquery: None,
            table_name: Some(name.into()),
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

    /// Set the subquery.
    pub fn subquery(mut self, query: SelectQuery) -> Self {
        self.subquery = Some(Box::new(query));
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

    /// Create a BETWEEN ... AND expression.
    pub fn between(value: Self, low: Self, high: Self) -> Self {
        Self::Between {
            value: Box::new(value),
            low: Box::new(low),
            high: Box::new(high),
        }
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

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wildcard => write!(f, "*"),
            Self::Column(name) => write!(f, "{name}"),
            Self::Literal(lit) => write!(f, "{lit}"),
            Self::Function(func) => {
                write!(f, "{}(", func.name)?;
                for (i, arg) in func.args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            Self::Window(wf) => {
                write!(f, "{}(", wf.name)?;
                for (i, arg) in wf.args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ") OVER ()")
            }
            Self::BinaryOp(op) => write!(f, "({} {} {})", op.left, op.op, op.right),
            Self::UnaryOp(op) => {
                // IS NULL and IS NOT NULL are postfix operators
                match op.op {
                    UnaryOperator::IsNull => write!(f, "{} IS NULL", op.operand),
                    UnaryOperator::IsNotNull => write!(f, "{} IS NOT NULL", op.operand),
                    _ => write!(f, "{}{}", op.op, op.operand),
                }
            }
            Self::Paren(inner) => write!(f, "({inner})"),
            Self::Between { value, low, high } => {
                write!(f, "{value} BETWEEN {low} AND {high}")
            }
            Self::Set(elements) => {
                write!(f, "(")?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{elem}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::String(s) => write!(f, "\"{s}\""),
            Self::Number(n) => write!(f, "{n}"),
            Self::Integer(n) => write!(f, "{n}"),
            Self::Date(d) => write!(f, "{d}"),
            Self::Boolean(b) => write!(f, "{b}"),
            Self::Null => write!(f, "NULL"),
        }
    }
}

impl fmt::Display for BinaryOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Eq => "=",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::Regex => "~",
            Self::NotRegex => "!~",
            Self::In => "IN",
            Self::NotIn => "NOT IN",
            Self::And => "AND",
            Self::Or => "OR",
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",
        };
        write!(f, "{s}")
    }
}

impl fmt::Display for UnaryOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Not => "NOT ",
            Self::Neg => "-",
            Self::IsNull => " IS NULL",
            Self::IsNotNull => " IS NOT NULL",
        };
        write!(f, "{s}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    #[test]
    fn test_expr_display_wildcard() {
        assert_eq!(Expr::Wildcard.to_string(), "*");
    }

    #[test]
    fn test_expr_display_column() {
        assert_eq!(Expr::Column("account".to_string()).to_string(), "account");
    }

    #[test]
    fn test_expr_display_literals() {
        assert_eq!(Expr::string("hello").to_string(), "\"hello\"");
        assert_eq!(Expr::integer(42).to_string(), "42");
        assert_eq!(Expr::number(dec!(3.14)).to_string(), "3.14");
        assert_eq!(Expr::boolean(true).to_string(), "true");
        assert_eq!(Expr::null().to_string(), "NULL");
    }

    #[test]
    fn test_expr_display_date() {
        let date = NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        assert_eq!(Expr::date(date).to_string(), "2024-01-15");
    }

    #[test]
    fn test_expr_display_function_no_args() {
        let func = Expr::function("now", vec![]);
        assert_eq!(func.to_string(), "now()");
    }

    #[test]
    fn test_expr_display_function_one_arg() {
        let func = Expr::function("account_sortkey", vec![Expr::column("account")]);
        assert_eq!(func.to_string(), "account_sortkey(account)");
    }

    #[test]
    fn test_expr_display_function_multiple_args() {
        let func = Expr::function(
            "coalesce",
            vec![Expr::column("a"), Expr::column("b"), Expr::integer(0)],
        );
        assert_eq!(func.to_string(), "coalesce(a, b, 0)");
    }

    #[test]
    fn test_expr_display_window() {
        let wf = Expr::Window(WindowFunction {
            name: "row_number".to_string(),
            args: vec![],
            over: WindowSpec::default(),
        });
        assert_eq!(wf.to_string(), "row_number() OVER ()");
    }

    #[test]
    fn test_expr_display_window_with_args() {
        let wf = Expr::Window(WindowFunction {
            name: "sum".to_string(),
            args: vec![Expr::column("amount")],
            over: WindowSpec::default(),
        });
        assert_eq!(wf.to_string(), "sum(amount) OVER ()");
    }

    #[test]
    fn test_expr_display_binary_op() {
        let expr = Expr::binary(Expr::column("a"), BinaryOperator::Add, Expr::integer(1));
        assert_eq!(expr.to_string(), "(a + 1)");
    }

    #[test]
    fn test_expr_display_unary_not() {
        let expr = Expr::unary(UnaryOperator::Not, Expr::column("flag"));
        assert_eq!(expr.to_string(), "NOT flag");
    }

    #[test]
    fn test_expr_display_unary_neg() {
        let expr = Expr::unary(UnaryOperator::Neg, Expr::column("x"));
        assert_eq!(expr.to_string(), "-x");
    }

    #[test]
    fn test_expr_display_is_null() {
        let expr = Expr::unary(UnaryOperator::IsNull, Expr::column("x"));
        assert_eq!(expr.to_string(), "x IS NULL");
    }

    #[test]
    fn test_expr_display_is_not_null() {
        let expr = Expr::unary(UnaryOperator::IsNotNull, Expr::column("x"));
        assert_eq!(expr.to_string(), "x IS NOT NULL");
    }

    #[test]
    fn test_expr_display_paren() {
        let inner = Expr::binary(Expr::column("a"), BinaryOperator::Add, Expr::column("b"));
        let expr = Expr::Paren(Box::new(inner));
        assert_eq!(expr.to_string(), "((a + b))");
    }

    #[test]
    fn test_expr_display_between() {
        let expr = Expr::between(Expr::column("x"), Expr::integer(1), Expr::integer(10));
        assert_eq!(expr.to_string(), "x BETWEEN 1 AND 10");
    }

    #[test]
    fn test_expr_display_set() {
        // Empty set is not valid in parsing, but test single element
        let single = Expr::Set(vec![Expr::string("EUR")]);
        assert_eq!(single.to_string(), r#"("EUR")"#);

        // Multiple elements
        let multi = Expr::Set(vec![
            Expr::string("EUR"),
            Expr::string("USD"),
            Expr::string("GBP"),
        ]);
        assert_eq!(multi.to_string(), r#"("EUR", "USD", "GBP")"#);

        // Mixed types (integers)
        let numeric = Expr::Set(vec![Expr::integer(2023), Expr::integer(2024)]);
        assert_eq!(numeric.to_string(), "(2023, 2024)");
    }

    #[test]
    fn test_binary_operator_display() {
        assert_eq!(BinaryOperator::Eq.to_string(), "=");
        assert_eq!(BinaryOperator::Ne.to_string(), "!=");
        assert_eq!(BinaryOperator::Lt.to_string(), "<");
        assert_eq!(BinaryOperator::Le.to_string(), "<=");
        assert_eq!(BinaryOperator::Gt.to_string(), ">");
        assert_eq!(BinaryOperator::Ge.to_string(), ">=");
        assert_eq!(BinaryOperator::Regex.to_string(), "~");
        assert_eq!(BinaryOperator::NotRegex.to_string(), "!~");
        assert_eq!(BinaryOperator::In.to_string(), "IN");
        assert_eq!(BinaryOperator::NotIn.to_string(), "NOT IN");
        assert_eq!(BinaryOperator::And.to_string(), "AND");
        assert_eq!(BinaryOperator::Or.to_string(), "OR");
        assert_eq!(BinaryOperator::Add.to_string(), "+");
        assert_eq!(BinaryOperator::Sub.to_string(), "-");
        assert_eq!(BinaryOperator::Mul.to_string(), "*");
        assert_eq!(BinaryOperator::Div.to_string(), "/");
        assert_eq!(BinaryOperator::Mod.to_string(), "%");
    }

    #[test]
    fn test_unary_operator_display() {
        assert_eq!(UnaryOperator::Not.to_string(), "NOT ");
        assert_eq!(UnaryOperator::Neg.to_string(), "-");
        assert_eq!(UnaryOperator::IsNull.to_string(), " IS NULL");
        assert_eq!(UnaryOperator::IsNotNull.to_string(), " IS NOT NULL");
    }

    #[test]
    fn test_literal_display() {
        assert_eq!(Literal::String("test".to_string()).to_string(), "\"test\"");
        assert_eq!(Literal::Number(dec!(1.5)).to_string(), "1.5");
        assert_eq!(Literal::Integer(42).to_string(), "42");
        assert_eq!(Literal::Boolean(false).to_string(), "false");
        assert_eq!(Literal::Null.to_string(), "NULL");
    }
}
