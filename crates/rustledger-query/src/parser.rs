//! BQL Parser implementation.
//!
//! Uses chumsky for parser combinators.

use chumsky::prelude::*;
use rust_decimal::Decimal;
use std::str::FromStr;

use crate::ast::{
    BalancesQuery, BinaryOperator, ColumnDef, CreateTableStmt, Expr, FromClause, FunctionCall,
    InsertSource, InsertStmt, JournalQuery, Literal, OrderSpec, PrintQuery, Query, SelectQuery,
    SortDirection, Target, UnaryOperator, WindowFunction, WindowSpec,
};
use crate::error::{ParseError, ParseErrorKind};
use rustledger_core::NaiveDate;

type ParserInput<'a> = &'a str;
type ParserExtra<'a> = extra::Err<Rich<'a, char>>;

/// Helper enum for parsing comparison suffix (BETWEEN, IN, or binary comparison).
enum ComparisonSuffix {
    Between(Expr, Expr),
    Binary(BinaryOperator, Expr),
    /// IN with right-hand side (set literal or expression).
    In(Expr),
    /// NOT IN with right-hand side (set literal or expression).
    NotIn(Expr),
}

/// Parse a BQL query string.
///
/// # Errors
///
/// Returns a `ParseError` if the query string is malformed.
pub fn parse(source: &str) -> Result<Query, ParseError> {
    let (result, errs) = query_parser()
        .then_ignore(ws())
        .then_ignore(end())
        .parse(source)
        .into_output_errors();

    if let Some(query) = result {
        Ok(query)
    } else {
        let err = errs.first().map(|e| {
            let kind = if e.found().is_none() {
                ParseErrorKind::UnexpectedEof
            } else {
                ParseErrorKind::SyntaxError(e.to_string())
            };
            ParseError::new(kind, e.span().start)
        });
        Err(err.unwrap_or_else(|| ParseError::new(ParseErrorKind::UnexpectedEof, 0)))
    }
}

/// Parse whitespace (spaces, tabs, newlines).
fn ws<'a>() -> impl Parser<'a, ParserInput<'a>, (), ParserExtra<'a>> + Clone {
    one_of(" \t\r\n").repeated().ignored()
}

/// Parse required whitespace.
fn ws1<'a>() -> impl Parser<'a, ParserInput<'a>, (), ParserExtra<'a>> + Clone {
    one_of(" \t\r\n").repeated().at_least(1).ignored()
}

/// Case-insensitive keyword parser.
fn kw<'a>(keyword: &'static str) -> impl Parser<'a, ParserInput<'a>, (), ParserExtra<'a>> + Clone {
    text::ident().try_map(move |s: &str, span| {
        if s.eq_ignore_ascii_case(keyword) {
            Ok(())
        } else {
            Err(Rich::custom(span, format!("expected keyword '{keyword}'")))
        }
    })
}

/// Parse digits.
fn digits<'a>() -> impl Parser<'a, ParserInput<'a>, &'a str, ParserExtra<'a>> + Clone {
    one_of("0123456789").repeated().at_least(1).to_slice()
}

/// Parse the main query.
fn query_parser<'a>() -> impl Parser<'a, ParserInput<'a>, Query, ParserExtra<'a>> {
    ws().ignore_then(choice((
        create_table_stmt().map(Query::CreateTable),
        insert_stmt().map(Query::Insert),
        select_query().map(|sq| Query::Select(Box::new(sq))),
        journal_query().map(Query::Journal),
        balances_query().map(Query::Balances),
        print_query().map(Query::Print),
    )))
    .then_ignore(ws())
    .then_ignore(just(';').or_not())
}

/// Parse a SELECT query with optional subquery support.
fn select_query<'a>() -> impl Parser<'a, ParserInput<'a>, SelectQuery, ParserExtra<'a>> {
    recursive(|select_parser| {
        // Subquery in FROM clause: FROM (SELECT ...)
        let subquery_from = ws1()
            .ignore_then(kw("FROM"))
            .ignore_then(ws1())
            .ignore_then(just('('))
            .ignore_then(ws())
            .ignore_then(select_parser)
            .then_ignore(ws())
            .then_ignore(just(')'))
            .map(|sq| Some(FromClause::from_subquery(sq)));

        // Table name FROM clause: FROM tablename (where tablename is not a keyword)
        // A table name is an identifier followed by WHERE/GROUP/ORDER/HAVING/LIMIT/PIVOT or end
        // Supports system tables like #prices, #entries
        let table_from = ws1()
            .ignore_then(kw("FROM"))
            .ignore_then(ws1())
            .ignore_then(table_identifier().try_map(|name, span| {
                // Check if this looks like a table name (uppercase convention or doesn't look like account)
                // Table names should not contain ':' which accounts have
                // System tables starting with '#' are always valid
                if !name.starts_with('#') && name.contains(':') {
                    Err(Rich::custom(
                        span,
                        "table names cannot contain ':' - this looks like an account filter expression",
                    ))
                } else {
                    Ok(name)
                }
            }))
            .then_ignore(
                // Must be followed by WHERE, GROUP, ORDER, HAVING, LIMIT, PIVOT, or end
                ws().then(choice((
                    kw("WHERE").ignored(),
                    kw("GROUP").ignored(),
                    kw("ORDER").ignored(),
                    kw("HAVING").ignored(),
                    kw("LIMIT").ignored(),
                    kw("PIVOT").ignored(),
                    end().ignored(),
                )))
                .rewind(),
            )
            .map(|name| Some(FromClause::from_table(name)));

        // Regular FROM clause
        let regular_from = from_clause().map(Some);

        kw("SELECT")
            .ignore_then(ws1())
            .ignore_then(
                kw("DISTINCT")
                    .then_ignore(ws())
                    .or_not()
                    .map(|d| d.is_some()),
            )
            .then(targets())
            .then(
                subquery_from
                    .or(table_from)
                    .or(regular_from)
                    .or_not()
                    .map(std::option::Option::flatten),
            )
            .then(where_clause().or_not())
            .then(group_by_clause().or_not())
            .then(having_clause().or_not())
            .then(pivot_by_clause().or_not())
            .then(order_by_clause().or_not())
            .then(limit_clause().or_not())
            .map(
                |(
                    (
                        (
                            (((((distinct, targets), from), where_clause), group_by), having),
                            pivot_by,
                        ),
                        order_by,
                    ),
                    limit,
                )| {
                    SelectQuery {
                        distinct,
                        targets,
                        from,
                        where_clause,
                        group_by,
                        having,
                        pivot_by,
                        order_by,
                        limit,
                    }
                },
            )
    })
}

/// Parse FROM clause.
fn from_clause<'a>() -> impl Parser<'a, ParserInput<'a>, FromClause, ParserExtra<'a>> + Clone {
    ws1()
        .ignore_then(kw("FROM"))
        .ignore_then(ws1())
        .ignore_then(from_modifiers())
}

/// Parse target expressions.
fn targets<'a>() -> impl Parser<'a, ParserInput<'a>, Vec<Target>, ParserExtra<'a>> + Clone {
    target()
        .separated_by(ws().then(just(',')).then(ws()))
        .at_least(1)
        .collect()
}

/// Parse a single target.
fn target<'a>() -> impl Parser<'a, ParserInput<'a>, Target, ParserExtra<'a>> + Clone {
    expr()
        .then(
            ws1()
                .ignore_then(kw("AS"))
                .ignore_then(ws1())
                .ignore_then(identifier())
                .or_not(),
        )
        .map(|(expr, alias)| Target { expr, alias })
}

/// Parse FROM modifiers (OPEN ON, CLOSE ON, CLEAR, filter).
fn from_modifiers<'a>() -> impl Parser<'a, ParserInput<'a>, FromClause, ParserExtra<'a>> + Clone {
    let open_on = kw("OPEN")
        .ignore_then(ws1())
        .ignore_then(kw("ON"))
        .ignore_then(ws1())
        .ignore_then(date_literal())
        .then_ignore(ws());

    let close_on = kw("CLOSE")
        .ignore_then(ws().then(kw("ON")).then(ws()).or_not())
        .ignore_then(date_literal())
        .then_ignore(ws());

    let clear = kw("CLEAR").then_ignore(ws());

    // Parse modifiers in order: OPEN ON, CLOSE ON, CLEAR, filter
    // Or just a table name for user-created tables
    open_on
        .or_not()
        .then(close_on.or_not())
        .then(clear.or_not().map(|c| c.is_some()))
        .then(from_filter().or_not())
        .map(|(((open_on, close_on), clear), filter)| FromClause {
            open_on,
            close_on,
            clear,
            filter,
            subquery: None,
            table_name: None,
        })
}

/// Parse FROM filter expression (predicates).
fn from_filter<'a>() -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    expr()
}

/// Parse WHERE clause.
fn where_clause<'a>() -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    ws1()
        .ignore_then(kw("WHERE"))
        .ignore_then(ws1())
        .ignore_then(expr())
}

/// Parse GROUP BY clause.
fn group_by_clause<'a>() -> impl Parser<'a, ParserInput<'a>, Vec<Expr>, ParserExtra<'a>> + Clone {
    ws1()
        .ignore_then(kw("GROUP"))
        .ignore_then(ws1())
        .ignore_then(kw("BY"))
        .ignore_then(ws1())
        .ignore_then(
            expr()
                .separated_by(ws().then(just(',')).then(ws()))
                .at_least(1)
                .collect(),
        )
}

/// Parse HAVING clause (filter on aggregated results).
fn having_clause<'a>() -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    ws1()
        .ignore_then(kw("HAVING"))
        .ignore_then(ws1())
        .ignore_then(expr())
}

/// Parse PIVOT BY clause (pivot table transformation).
fn pivot_by_clause<'a>() -> impl Parser<'a, ParserInput<'a>, Vec<Expr>, ParserExtra<'a>> + Clone {
    ws1()
        .ignore_then(kw("PIVOT"))
        .ignore_then(ws1())
        .ignore_then(kw("BY"))
        .ignore_then(ws1())
        .ignore_then(
            expr()
                .separated_by(ws().then(just(',')).then(ws()))
                .at_least(1)
                .collect(),
        )
}

/// Parse ORDER BY clause.
fn order_by_clause<'a>() -> impl Parser<'a, ParserInput<'a>, Vec<OrderSpec>, ParserExtra<'a>> + Clone
{
    ws1()
        .ignore_then(kw("ORDER"))
        .ignore_then(ws1())
        .ignore_then(kw("BY"))
        .ignore_then(ws1())
        .ignore_then(
            order_spec()
                .separated_by(ws().then(just(',')).then(ws()))
                .at_least(1)
                .collect(),
        )
}

/// Parse a single ORDER BY spec.
fn order_spec<'a>() -> impl Parser<'a, ParserInput<'a>, OrderSpec, ParserExtra<'a>> + Clone {
    expr()
        .then(
            ws1()
                .ignore_then(choice((
                    kw("ASC").to(SortDirection::Asc),
                    kw("DESC").to(SortDirection::Desc),
                )))
                .or_not(),
        )
        .map(|(expr, dir)| OrderSpec {
            expr,
            direction: dir.unwrap_or_default(),
        })
}

/// Parse LIMIT clause.
fn limit_clause<'a>() -> impl Parser<'a, ParserInput<'a>, u64, ParserExtra<'a>> + Clone {
    ws1()
        .ignore_then(kw("LIMIT"))
        .ignore_then(ws1())
        .ignore_then(integer())
        .map(|n| n as u64)
}

/// Parse JOURNAL query.
fn journal_query<'a>() -> impl Parser<'a, ParserInput<'a>, JournalQuery, ParserExtra<'a>> + Clone {
    kw("JOURNAL")
        .ignore_then(
            // Account pattern is optional - can be JOURNAL or JOURNAL "pattern"
            ws1().ignore_then(string_literal()).or_not(),
        )
        .then(at_function().or_not())
        .then(
            ws1()
                .ignore_then(kw("FROM"))
                .ignore_then(ws1())
                .ignore_then(from_modifiers())
                .or_not(),
        )
        .map(|((account_pattern, at_function), from)| JournalQuery {
            account_pattern: account_pattern.unwrap_or_default(),
            at_function,
            from,
        })
}

/// Parse BALANCES query.
fn balances_query<'a>() -> impl Parser<'a, ParserInput<'a>, BalancesQuery, ParserExtra<'a>> + Clone
{
    // Use rewind-based lookahead so optional clauses don't consume whitespace
    // that subsequent clauses need. Without this, `BALANCES WHERE ...` fails
    // because at_function() consumes whitespace before failing on "WHERE" != "AT".
    let at_fn = ws1().then(kw("AT")).rewind().ignore_then(at_function());

    let from = ws1().then(kw("FROM")).rewind().ignore_then(
        ws1()
            .ignore_then(kw("FROM"))
            .ignore_then(ws1())
            .ignore_then(from_modifiers()),
    );

    kw("BALANCES")
        .ignore_then(at_fn.or_not())
        .then(from.or_not())
        .then(where_clause().or_not())
        .map(|((at_function, from), where_clause)| BalancesQuery {
            at_function,
            from,
            where_clause,
        })
}

/// Parse PRINT query.
fn print_query<'a>() -> impl Parser<'a, ParserInput<'a>, PrintQuery, ParserExtra<'a>> + Clone {
    kw("PRINT")
        .ignore_then(
            ws1()
                .ignore_then(kw("FROM"))
                .ignore_then(ws1())
                .ignore_then(from_modifiers())
                .or_not(),
        )
        .map(|from| PrintQuery { from })
}

/// Parse CREATE TABLE statement.
fn create_table_stmt<'a>() -> impl Parser<'a, ParserInput<'a>, CreateTableStmt, ParserExtra<'a>> {
    // CREATE TABLE name (col1, col2, ...) or CREATE TABLE name AS SELECT ...
    let column_def = identifier()
        .then(ws().ignore_then(identifier()).or_not())
        .map(|(name, type_hint)| ColumnDef { name, type_hint });

    let column_list = just('(')
        .ignore_then(ws())
        .ignore_then(
            column_def
                .separated_by(ws().ignore_then(just(',')).then_ignore(ws()))
                .collect::<Vec<_>>(),
        )
        .then_ignore(ws())
        .then_ignore(just(')'));

    let as_select = ws1()
        .ignore_then(kw("AS"))
        .ignore_then(ws1())
        .ignore_then(select_query())
        .map(Box::new);

    kw("CREATE")
        .ignore_then(ws1())
        .ignore_then(kw("TABLE"))
        .ignore_then(ws1())
        .ignore_then(identifier())
        .then(ws().ignore_then(column_list).or_not())
        .then(as_select.or_not())
        .map(|((table_name, columns), as_select)| CreateTableStmt {
            table_name,
            columns: columns.unwrap_or_default(),
            as_select,
        })
}

/// Parse INSERT statement.
fn insert_stmt<'a>() -> impl Parser<'a, ParserInput<'a>, InsertStmt, ParserExtra<'a>> {
    // Column list: (col1, col2, ...)
    let column_list = just('(')
        .ignore_then(ws())
        .ignore_then(
            identifier()
                .separated_by(ws().ignore_then(just(',')).then_ignore(ws()))
                .collect::<Vec<_>>(),
        )
        .then_ignore(ws())
        .then_ignore(just(')'));

    // VALUES clause: VALUES (v1, v2), (v3, v4), ...
    let value_row = just('(')
        .ignore_then(ws())
        .ignore_then(
            expr()
                .separated_by(ws().ignore_then(just(',')).then_ignore(ws()))
                .collect::<Vec<_>>(),
        )
        .then_ignore(ws())
        .then_ignore(just(')'));

    let values_source = kw("VALUES")
        .ignore_then(ws())
        .ignore_then(
            value_row
                .separated_by(ws().ignore_then(just(',')).then_ignore(ws()))
                .collect::<Vec<_>>(),
        )
        .map(InsertSource::Values);

    // SELECT as source
    let select_source = select_query().map(|sq| InsertSource::Select(Box::new(sq)));

    let source = choice((values_source, select_source));

    kw("INSERT")
        .ignore_then(ws1())
        .ignore_then(kw("INTO"))
        .ignore_then(ws1())
        .ignore_then(identifier())
        .then(ws().ignore_then(column_list).or_not())
        .then_ignore(ws())
        .then(source)
        .map(|((table_name, columns), source)| InsertStmt {
            table_name,
            columns,
            source,
        })
}

/// Parse AT function (e.g., AT cost, AT units).
fn at_function<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    ws1()
        .ignore_then(kw("AT"))
        .ignore_then(ws1())
        .ignore_then(identifier())
}

/// Parse an expression (with precedence climbing).
#[allow(clippy::large_stack_frames)]
fn expr<'a>() -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    recursive(|expr| {
        let primary = primary_expr(expr.clone());

        // Unary minus
        let unary = just('-')
            .then_ignore(ws())
            .or_not()
            .then(primary)
            .map(|(neg, e)| {
                if neg.is_some() {
                    Expr::unary(UnaryOperator::Neg, e)
                } else {
                    e
                }
            });

        // Multiplicative: * / %
        let multiplicative = unary.clone().foldl(
            ws().ignore_then(choice((
                just('*').to(BinaryOperator::Mul),
                just('/').to(BinaryOperator::Div),
                just('%').to(BinaryOperator::Mod),
            )))
            .then_ignore(ws())
            .then(unary)
            .repeated(),
            |left, (op, right)| Expr::binary(left, op, right),
        );

        // Additive: + -
        let additive = multiplicative.clone().foldl(
            ws().ignore_then(choice((
                just('+').to(BinaryOperator::Add),
                just('-').to(BinaryOperator::Sub),
            )))
            .then_ignore(ws())
            .then(multiplicative)
            .repeated(),
            |left, (op, right)| Expr::binary(left, op, right),
        );

        // Comparison: = != < <= > >= ~ !~ IN NOT IN BETWEEN IS NULL
        let comparison = additive
            .clone()
            .then(
                choice((
                    // BETWEEN ... AND
                    ws1()
                        .ignore_then(kw("BETWEEN"))
                        .ignore_then(ws1())
                        .ignore_then(additive.clone())
                        .then_ignore(ws1())
                        .then_ignore(kw("AND"))
                        .then_ignore(ws1())
                        .then(additive.clone())
                        .map(|(low, high)| ComparisonSuffix::Between(low, high)),
                    // NOT IN - try set literal first, then fall back to expression
                    ws1()
                        .ignore_then(kw("NOT"))
                        .ignore_then(ws1())
                        .ignore_then(kw("IN"))
                        .ignore_then(ws())
                        .ignore_then(choice((
                            set_literal(expr.clone()),
                            additive.clone(),
                        )))
                        .map(ComparisonSuffix::NotIn),
                    // IN - try set literal first, then fall back to expression
                    ws1()
                        .ignore_then(kw("IN"))
                        .ignore_then(ws())
                        .ignore_then(choice((
                            set_literal(expr.clone()),
                            additive.clone(),
                        )))
                        .map(ComparisonSuffix::In),
                    // Regular comparison operators
                    ws()
                        .ignore_then(comparison_op())
                        .then_ignore(ws())
                        .then(additive)
                        .map(|(op, right)| ComparisonSuffix::Binary(op, right)),
                ))
                .or_not(),
            )
            .map(|(left, suffix)| match suffix {
                Some(ComparisonSuffix::Between(low, high)) => Expr::between(left, low, high),
                Some(ComparisonSuffix::Binary(op, right)) => Expr::binary(left, op, right),
                Some(ComparisonSuffix::In(right)) => Expr::binary(left, BinaryOperator::In, right),
                Some(ComparisonSuffix::NotIn(right)) => {
                    Expr::binary(left, BinaryOperator::NotIn, right)
                }
                None => left,
            })
            // IS NULL / IS NOT NULL (postfix)
            .then(
                ws1()
                    .ignore_then(kw("IS"))
                    .ignore_then(ws1())
                    .ignore_then(choice((
                        kw("NOT")
                            .ignore_then(ws1())
                            .ignore_then(kw("NULL"))
                            .to(UnaryOperator::IsNotNull),
                        kw("NULL").to(UnaryOperator::IsNull),
                    )))
                    .or_not(),
            )
            .map(|(expr, is_null)| {
                if let Some(op) = is_null {
                    Expr::unary(op, expr)
                } else {
                    expr
                }
            });

        // NOT
        let not_expr = kw("NOT")
            .ignore_then(ws1())
            .repeated()
            .collect::<Vec<_>>()
            .then(comparison)
            .map(|(nots, e)| {
                nots.into_iter()
                    .fold(e, |acc, ()| Expr::unary(UnaryOperator::Not, acc))
            });

        // AND
        let and_expr = not_expr.clone().foldl(
            ws1()
                .ignore_then(kw("AND"))
                .ignore_then(ws1())
                .ignore_then(not_expr)
                .repeated(),
            |left, right| Expr::binary(left, BinaryOperator::And, right),
        );

        // OR (lowest precedence)
        and_expr.clone().foldl(
            ws1()
                .ignore_then(kw("OR"))
                .ignore_then(ws1())
                .ignore_then(and_expr)
                .repeated(),
            |left, right| Expr::binary(left, BinaryOperator::Or, right),
        )
    })
}

/// Parse comparison operators (excluding IN/NOT IN which are handled specially).
fn comparison_op<'a>() -> impl Parser<'a, ParserInput<'a>, BinaryOperator, ParserExtra<'a>> + Clone
{
    choice((
        // Multi-char operators first
        just("!=").to(BinaryOperator::Ne),
        just("!~").to(BinaryOperator::NotRegex),
        just("<=").to(BinaryOperator::Le),
        just(">=").to(BinaryOperator::Ge),
        // Single-char operators
        just('=').to(BinaryOperator::Eq),
        just('<').to(BinaryOperator::Lt),
        just('>').to(BinaryOperator::Gt),
        just('~').to(BinaryOperator::Regex),
    ))
}

/// Parse a set literal for IN operator, e.g., `('EUR', 'USD')`.
///
/// To distinguish from parenthesized expressions like `IN (tags)`, set literals
/// require either:
/// - Two or more comma-separated elements: `('EUR', 'USD')`
/// - A single element with trailing comma: `('EUR',)`
///
/// This ensures `IN (tags)` is parsed as `IN <parenthesized-column>` rather than
/// `IN <single-element-set>`.
fn set_literal<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone + 'a,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    just('(')
        .ignore_then(ws())
        .ignore_then(
            // Parse first element
            expr.clone()
                .then(
                    // Then require either:
                    // - comma + more elements (with optional trailing comma)
                    // - trailing comma (for single-element sets)
                    ws().ignore_then(just(',')).ignore_then(ws()).ignore_then(
                        expr.separated_by(ws().then(just(',')).then(ws()))
                            .allow_trailing()
                            .collect::<Vec<_>>(),
                    ),
                )
                .map(|(first, rest)| {
                    let mut elements = Vec::with_capacity(1 + rest.len());
                    elements.push(first);
                    elements.extend(rest);
                    elements
                }),
        )
        .then_ignore(ws())
        .then_ignore(just(')'))
        .map(Expr::Set)
}

/// Parse primary expressions.
fn primary_expr<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone + 'a,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    choice((
        // Parenthesized expression
        just('(')
            .ignore_then(ws())
            .ignore_then(expr.clone())
            .then_ignore(ws())
            .then_ignore(just(')'))
            .map(|e| Expr::Paren(Box::new(e))),
        // Function call or column reference (must come before wildcard check)
        // Pass expr to allow nested function calls like units(sum(position))
        function_call_or_column(expr),
        // Literals
        literal().map(Expr::Literal),
        // Wildcard (fallback if nothing else matched)
        just('*').to(Expr::Wildcard),
    ))
}

/// Parse function call, window function, or column reference.
fn function_call_or_column<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone + 'a,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    identifier()
        .then(
            ws().ignore_then(just('('))
                .ignore_then(ws())
                .ignore_then(function_args(expr))
                .then_ignore(ws())
                .then_ignore(just(')'))
                .or_not(),
        )
        .then(
            // Optional OVER clause for window functions
            ws1()
                .ignore_then(kw("OVER"))
                .ignore_then(ws())
                .ignore_then(just('('))
                .ignore_then(ws())
                .ignore_then(window_spec())
                .then_ignore(ws())
                .then_ignore(just(')'))
                .or_not(),
        )
        .map(|((name, args), over)| {
            if let Some(args) = args {
                if let Some(window_spec) = over {
                    // Window function
                    Expr::Window(WindowFunction {
                        name,
                        args,
                        over: window_spec,
                    })
                } else {
                    // Regular function
                    Expr::Function(FunctionCall { name, args })
                }
            } else {
                Expr::Column(name)
            }
        })
}

/// Parse window specification (PARTITION BY and ORDER BY).
fn window_spec<'a>() -> impl Parser<'a, ParserInput<'a>, WindowSpec, ParserExtra<'a>> + Clone {
    let partition_by = kw("PARTITION")
        .ignore_then(ws1())
        .ignore_then(kw("BY"))
        .ignore_then(ws1())
        .ignore_then(
            simple_arg()
                .separated_by(ws().then(just(',')).then(ws()))
                .at_least(1)
                .collect::<Vec<_>>(),
        )
        .then_ignore(ws());

    let window_order_by = kw("ORDER")
        .ignore_then(ws1())
        .ignore_then(kw("BY"))
        .ignore_then(ws1())
        .ignore_then(
            window_order_spec()
                .separated_by(ws().then(just(',')).then(ws()))
                .at_least(1)
                .collect::<Vec<_>>(),
        );

    partition_by
        .or_not()
        .then(window_order_by.or_not())
        .map(|(partition_by, order_by)| WindowSpec {
            partition_by,
            order_by,
        })
}

/// Parse ORDER BY spec within window (simple version).
fn window_order_spec<'a>() -> impl Parser<'a, ParserInput<'a>, OrderSpec, ParserExtra<'a>> + Clone {
    simple_arg()
        .then(
            ws1()
                .ignore_then(choice((
                    kw("ASC").to(SortDirection::Asc),
                    kw("DESC").to(SortDirection::Desc),
                )))
                .or_not(),
        )
        .map(|(expr, dir)| OrderSpec {
            expr,
            direction: dir.unwrap_or_default(),
        })
}

/// Parse function arguments.
fn function_args<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone + 'a,
) -> impl Parser<'a, ParserInput<'a>, Vec<Expr>, ParserExtra<'a>> + Clone {
    // Allow empty args or comma-separated full expressions
    // This enables nested function calls like units(sum(position))
    expr.separated_by(ws().then(just(',')).then(ws())).collect()
}

/// Parse a simple function argument (column, wildcard, or literal).
fn simple_arg<'a>() -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    choice((
        just('*').to(Expr::Wildcard),
        identifier().map(Expr::Column),
        literal().map(Expr::Literal),
    ))
}

/// Parse a literal.
fn literal<'a>() -> impl Parser<'a, ParserInput<'a>, Literal, ParserExtra<'a>> + Clone {
    choice((
        // Keywords first
        kw("TRUE").to(Literal::Boolean(true)),
        kw("FALSE").to(Literal::Boolean(false)),
        kw("NULL").to(Literal::Null),
        // Date literal (must be before number to avoid parsing year as number)
        date_literal().map(Literal::Date),
        // Number
        decimal().map(Literal::Number),
        // String
        string_literal().map(Literal::String),
    ))
}

/// Parse an identifier (column name, function name).
fn identifier<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    text::ident().map(|s: &str| s.to_string())
}

/// Parse a table identifier, which can be a regular identifier or a system table
/// starting with `#` (e.g., `#prices`, `#entries`).
fn table_identifier<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    choice((
        // System table: #identifier (e.g., #prices)
        just('#')
            .ignore_then(text::ident())
            .map(|s: &str| format!("#{s}")),
        // Regular table identifier
        text::ident().map(|s: &str| s.to_string()),
    ))
}

/// Parse a string literal.
fn string_literal<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    // Double-quoted string
    let double_quoted = just('"')
        .ignore_then(
            none_of("\"\\")
                .or(just('\\').ignore_then(any()))
                .repeated()
                .collect::<String>(),
        )
        .then_ignore(just('"'));

    // Single-quoted string (SQL-style)
    let single_quoted = just('\'')
        .ignore_then(
            none_of("'\\")
                .or(just('\\').ignore_then(any()))
                .repeated()
                .collect::<String>(),
        )
        .then_ignore(just('\''));

    choice((double_quoted, single_quoted))
}

/// Parse a date literal (YYYY-MM-DD).
fn date_literal<'a>() -> impl Parser<'a, ParserInput<'a>, NaiveDate, ParserExtra<'a>> + Clone {
    digits()
        .then_ignore(just('-'))
        .then(digits())
        .then_ignore(just('-'))
        .then(digits())
        .try_map(|((year, month), day): ((&str, &str), &str), span| {
            let year: i32 = year
                .parse()
                .map_err(|_| Rich::custom(span, "invalid year"))?;
            let month: u32 = month
                .parse()
                .map_err(|_| Rich::custom(span, "invalid month"))?;
            let day: u32 = day.parse().map_err(|_| Rich::custom(span, "invalid day"))?;
            NaiveDate::from_ymd_opt(year, month, day)
                .ok_or_else(|| Rich::custom(span, "invalid date"))
        })
}

/// Parse a decimal number.
fn decimal<'a>() -> impl Parser<'a, ParserInput<'a>, Decimal, ParserExtra<'a>> + Clone {
    just('-')
        .or_not()
        .then(digits())
        .then(just('.').then(digits()).or_not())
        .try_map(
            |((neg, int_part), frac_part): ((Option<char>, &str), Option<(char, &str)>), span| {
                let mut s = String::new();
                if neg.is_some() {
                    s.push('-');
                }
                s.push_str(int_part);
                if let Some((_, frac)) = frac_part {
                    s.push('.');
                    s.push_str(frac);
                }
                Decimal::from_str(&s).map_err(|_| Rich::custom(span, "invalid number"))
            },
        )
}

/// Parse an integer.
fn integer<'a>() -> impl Parser<'a, ParserInput<'a>, i64, ParserExtra<'a>> + Clone {
    digits().try_map(|s: &str, span| {
        s.parse::<i64>()
            .map_err(|_| Rich::custom(span, "invalid integer"))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    #[test]
    fn test_simple_select() {
        let query = parse("SELECT * FROM year = 2024").unwrap();
        match query {
            Query::Select(sel) => {
                assert!(!sel.distinct);
                assert_eq!(sel.targets.len(), 1);
                assert!(matches!(sel.targets[0].expr, Expr::Wildcard));
                assert!(sel.from.is_some());
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_select_columns() {
        let query = parse("SELECT date, account, position").unwrap();
        match query {
            Query::Select(sel) => {
                assert_eq!(sel.targets.len(), 3);
                assert!(matches!(&sel.targets[0].expr, Expr::Column(c) if c == "date"));
                assert!(matches!(&sel.targets[1].expr, Expr::Column(c) if c == "account"));
                assert!(matches!(&sel.targets[2].expr, Expr::Column(c) if c == "position"));
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_select_with_alias() {
        let query = parse("SELECT SUM(position) AS total").unwrap();
        match query {
            Query::Select(sel) => {
                assert_eq!(sel.targets.len(), 1);
                assert_eq!(sel.targets[0].alias, Some("total".to_string()));
                match &sel.targets[0].expr {
                    Expr::Function(f) => {
                        assert_eq!(f.name, "SUM");
                        assert_eq!(f.args.len(), 1);
                    }
                    _ => panic!("Expected function"),
                }
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_select_distinct() {
        let query = parse("SELECT DISTINCT account").unwrap();
        match query {
            Query::Select(sel) => {
                assert!(sel.distinct);
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_select_distinct_no_space() {
        // Issue #640: DISTINCT(expr) without space should not be parsed as a function call
        let query = parse("SELECT DISTINCT(account) FROM postings").unwrap();
        match query {
            Query::Select(sel) => {
                assert!(sel.distinct);
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_select_distinct_coalesce_no_space() {
        // Issue #640: DISTINCT(COALESCE(payee, narration)) should work
        let query = parse("SELECT DISTINCT(COALESCE(payee, narration)) as payee FROM transactions")
            .unwrap();
        match query {
            Query::Select(sel) => {
                assert!(sel.distinct);
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_where_clause() {
        let query = parse("SELECT * WHERE account ~ \"Expenses:\"").unwrap();
        match query {
            Query::Select(sel) => {
                assert!(sel.where_clause.is_some());
                match sel.where_clause.unwrap() {
                    Expr::BinaryOp(op) => {
                        assert_eq!(op.op, BinaryOperator::Regex);
                    }
                    _ => panic!("Expected binary op"),
                }
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_group_by() {
        let query = parse("SELECT account, SUM(position) GROUP BY account").unwrap();
        match query {
            Query::Select(sel) => {
                assert!(sel.group_by.is_some());
                assert_eq!(sel.group_by.unwrap().len(), 1);
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_order_by() {
        let query = parse("SELECT * ORDER BY date DESC, account ASC").unwrap();
        match query {
            Query::Select(sel) => {
                assert!(sel.order_by.is_some());
                let order = sel.order_by.unwrap();
                assert_eq!(order.len(), 2);
                assert_eq!(order[0].direction, SortDirection::Desc);
                assert_eq!(order[1].direction, SortDirection::Asc);
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_limit() {
        let query = parse("SELECT * LIMIT 100").unwrap();
        match query {
            Query::Select(sel) => {
                assert_eq!(sel.limit, Some(100));
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_from_open_close_clear() {
        let query = parse("SELECT * FROM OPEN ON 2024-01-01 CLOSE ON 2024-12-31 CLEAR").unwrap();
        match query {
            Query::Select(sel) => {
                let from = sel.from.unwrap();
                assert_eq!(
                    from.open_on,
                    Some(NaiveDate::from_ymd_opt(2024, 1, 1).unwrap())
                );
                assert_eq!(
                    from.close_on,
                    Some(NaiveDate::from_ymd_opt(2024, 12, 31).unwrap())
                );
                assert!(from.clear);
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_from_year_filter() {
        let query = parse("SELECT date, account FROM year = 2024").unwrap();
        match query {
            Query::Select(sel) => {
                let from = sel.from.unwrap();
                assert!(from.filter.is_some(), "FROM filter should be present");
                match from.filter.unwrap() {
                    Expr::BinaryOp(op) => {
                        assert_eq!(op.op, BinaryOperator::Eq);
                        assert!(matches!(op.left, Expr::Column(ref c) if c == "year"));
                        // Right side can be Integer or Number (parser produces Number)
                        match op.right {
                            Expr::Literal(Literal::Integer(n)) => assert_eq!(n, 2024),
                            Expr::Literal(Literal::Number(n)) => assert_eq!(n, dec!(2024)),
                            other => panic!("Expected numeric literal, got {other:?}"),
                        }
                    }
                    other => panic!("Expected BinaryOp, got {other:?}"),
                }
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_journal_query() {
        let query = parse("JOURNAL \"Assets:Bank\" AT cost").unwrap();
        match query {
            Query::Journal(j) => {
                assert_eq!(j.account_pattern, "Assets:Bank");
                assert_eq!(j.at_function, Some("cost".to_string()));
            }
            _ => panic!("Expected JOURNAL query"),
        }
    }

    #[test]
    fn test_balances_query() {
        let query = parse("BALANCES AT units FROM year = 2024").unwrap();
        match query {
            Query::Balances(b) => {
                assert_eq!(b.at_function, Some("units".to_string()));
                assert!(b.from.is_some());
            }
            _ => panic!("Expected BALANCES query"),
        }
    }

    #[test]
    fn test_print_query() {
        let query = parse("PRINT").unwrap();
        assert!(matches!(query, Query::Print(_)));
    }

    #[test]
    fn test_complex_expression() {
        let query = parse("SELECT * WHERE date >= 2024-01-01 AND account ~ \"Expenses:\"").unwrap();
        match query {
            Query::Select(sel) => match sel.where_clause.unwrap() {
                Expr::BinaryOp(op) => {
                    assert_eq!(op.op, BinaryOperator::And);
                }
                _ => panic!("Expected AND"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_number_literal() {
        let query = parse("SELECT * WHERE year = 2024").unwrap();
        match query {
            Query::Select(sel) => match sel.where_clause.unwrap() {
                Expr::BinaryOp(op) => match op.right {
                    Expr::Literal(Literal::Number(n)) => {
                        assert_eq!(n, dec!(2024));
                    }
                    _ => panic!("Expected number literal"),
                },
                _ => panic!("Expected binary op"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_semicolon_optional() {
        assert!(parse("SELECT *").is_ok());
        assert!(parse("SELECT *;").is_ok());
    }

    #[test]
    fn test_subquery_basic() {
        let query = parse("SELECT * FROM (SELECT account, position)").unwrap();
        match query {
            Query::Select(sel) => {
                assert!(sel.from.is_some());
                let from = sel.from.unwrap();
                assert!(from.subquery.is_some());
                let subquery = from.subquery.unwrap();
                assert_eq!(subquery.targets.len(), 2);
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_subquery_with_groupby() {
        let query = parse(
            "SELECT account, total FROM (SELECT account, SUM(position) AS total GROUP BY account)",
        )
        .unwrap();
        match query {
            Query::Select(sel) => {
                assert_eq!(sel.targets.len(), 2);
                let from = sel.from.unwrap();
                assert!(from.subquery.is_some());
                let subquery = from.subquery.unwrap();
                assert!(subquery.group_by.is_some());
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_subquery_with_outer_where() {
        let query =
            parse("SELECT * FROM (SELECT * WHERE year = 2024) WHERE account ~ \"Expenses:\"")
                .unwrap();
        match query {
            Query::Select(sel) => {
                // Outer WHERE
                assert!(sel.where_clause.is_some());
                // Subquery with its own WHERE
                let from = sel.from.unwrap();
                let subquery = from.subquery.unwrap();
                assert!(subquery.where_clause.is_some());
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_nested_subquery() {
        // Two levels of nesting
        let query = parse("SELECT * FROM (SELECT * FROM (SELECT account))").unwrap();
        match query {
            Query::Select(sel) => {
                let from = sel.from.unwrap();
                let subquery1 = from.subquery.unwrap();
                let from2 = subquery1.from.unwrap();
                assert!(from2.subquery.is_some());
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_nested_function_calls() {
        // Test units(sum(position)) pattern
        let query = parse("SELECT units(sum(position))").unwrap();
        match query {
            Query::Select(sel) => {
                assert_eq!(sel.targets.len(), 1);
                match &sel.targets[0].expr {
                    Expr::Function(outer) => {
                        assert_eq!(outer.name, "units");
                        assert_eq!(outer.args.len(), 1);
                        match &outer.args[0] {
                            Expr::Function(inner) => {
                                assert_eq!(inner.name, "sum");
                                assert_eq!(inner.args.len(), 1);
                                assert!(
                                    matches!(&inner.args[0], Expr::Column(c) if c == "position")
                                );
                            }
                            _ => panic!("Expected inner function call"),
                        }
                    }
                    _ => panic!("Expected outer function call"),
                }
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_deeply_nested_function_calls() {
        // Test three levels of nesting
        let query = parse("SELECT foo(bar(baz(x)))").unwrap();
        match query {
            Query::Select(sel) => {
                assert_eq!(sel.targets.len(), 1);
                match &sel.targets[0].expr {
                    Expr::Function(f1) => {
                        assert_eq!(f1.name, "foo");
                        match &f1.args[0] {
                            Expr::Function(f2) => {
                                assert_eq!(f2.name, "bar");
                                match &f2.args[0] {
                                    Expr::Function(f3) => {
                                        assert_eq!(f3.name, "baz");
                                        assert!(matches!(&f3.args[0], Expr::Column(c) if c == "x"));
                                    }
                                    _ => panic!("Expected f3"),
                                }
                            }
                            _ => panic!("Expected f2"),
                        }
                    }
                    _ => panic!("Expected f1"),
                }
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_function_with_arithmetic() {
        // Test function with arithmetic expression as argument
        let query = parse("SELECT sum(amount * 2)").unwrap();
        match query {
            Query::Select(sel) => match &sel.targets[0].expr {
                Expr::Function(f) => {
                    assert_eq!(f.name, "sum");
                    assert!(matches!(&f.args[0], Expr::BinaryOp(_)));
                }
                _ => panic!("Expected function"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_is_null() {
        let query = parse("SELECT * WHERE payee IS NULL").unwrap();
        match query {
            Query::Select(sel) => match sel.where_clause.unwrap() {
                Expr::UnaryOp(op) => {
                    assert_eq!(op.op, UnaryOperator::IsNull);
                    assert!(matches!(&op.operand, Expr::Column(c) if c == "payee"));
                }
                _ => panic!("Expected unary op"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_is_not_null() {
        let query = parse("SELECT * WHERE payee IS NOT NULL").unwrap();
        match query {
            Query::Select(sel) => match sel.where_clause.unwrap() {
                Expr::UnaryOp(op) => {
                    assert_eq!(op.op, UnaryOperator::IsNotNull);
                    assert!(matches!(&op.operand, Expr::Column(c) if c == "payee"));
                }
                _ => panic!("Expected unary op"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_not_regex() {
        let query = parse("SELECT * WHERE account !~ \"Assets:\"").unwrap();
        match query {
            Query::Select(sel) => match sel.where_clause.unwrap() {
                Expr::BinaryOp(op) => {
                    assert_eq!(op.op, BinaryOperator::NotRegex);
                }
                _ => panic!("Expected binary op"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_modulo() {
        let query = parse("SELECT year % 4").unwrap();
        match query {
            Query::Select(sel) => match &sel.targets[0].expr {
                Expr::BinaryOp(op) => {
                    assert_eq!(op.op, BinaryOperator::Mod);
                }
                _ => panic!("Expected binary op"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_between() {
        let query = parse("SELECT * WHERE year BETWEEN 2020 AND 2024").unwrap();
        match query {
            Query::Select(sel) => match sel.where_clause.unwrap() {
                Expr::Between { value, low, high } => {
                    assert!(matches!(*value, Expr::Column(c) if c == "year"));
                    assert!(matches!(*low, Expr::Literal(Literal::Number(_))));
                    assert!(matches!(*high, Expr::Literal(Literal::Number(_))));
                }
                _ => panic!("Expected BETWEEN"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_not_in() {
        let query = parse("SELECT * WHERE account NOT IN tags").unwrap();
        match query {
            Query::Select(sel) => match sel.where_clause.unwrap() {
                Expr::BinaryOp(op) => {
                    assert_eq!(op.op, BinaryOperator::NotIn);
                }
                _ => panic!("Expected binary op"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_in_set_literal() {
        // Multi-element set literal
        let query = parse("SELECT * WHERE currency IN ('EUR', 'USD')").unwrap();
        match query {
            Query::Select(sel) => match sel.where_clause.unwrap() {
                Expr::BinaryOp(op) => {
                    assert_eq!(op.op, BinaryOperator::In);
                    match op.right {
                        Expr::Set(elements) => {
                            assert_eq!(elements.len(), 2);
                        }
                        _ => panic!("Expected Set"),
                    }
                }
                _ => panic!("Expected binary op"),
            },
            _ => panic!("Expected SELECT query"),
        }

        // Single-element set with trailing comma
        let query = parse("SELECT * WHERE currency IN ('EUR',)").unwrap();
        match query {
            Query::Select(sel) => match sel.where_clause.unwrap() {
                Expr::BinaryOp(op) => {
                    assert_eq!(op.op, BinaryOperator::In);
                    match op.right {
                        Expr::Set(elements) => {
                            assert_eq!(elements.len(), 1);
                        }
                        _ => panic!("Expected Set"),
                    }
                }
                _ => panic!("Expected binary op"),
            },
            _ => panic!("Expected SELECT query"),
        }

        // Parenthesized column (not a set literal)
        let query = parse("SELECT * WHERE 'x' IN (tags)").unwrap();
        match query {
            Query::Select(sel) => match sel.where_clause.unwrap() {
                Expr::BinaryOp(op) => {
                    assert_eq!(op.op, BinaryOperator::In);
                    // Should be Paren(Column), not Set([Column])
                    match op.right {
                        Expr::Paren(inner) => match *inner {
                            Expr::Column(name) => assert_eq!(name, "tags"),
                            _ => panic!("Expected Column inside Paren"),
                        },
                        other => panic!("Expected Paren, got {other:?}"),
                    }
                }
                _ => panic!("Expected binary op"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_string_arg_function() {
        // First test a function with a column reference - should work
        let query = parse("SELECT foo(x)").unwrap();
        match query {
            Query::Select(sel) => match &sel.targets[0].expr {
                Expr::Function(f) => {
                    assert_eq!(f.name, "foo");
                }
                _ => panic!("Expected function"),
            },
            _ => panic!("Expected SELECT query"),
        }

        // Now test a function with a string literal argument
        let query = parse("SELECT foo('bar')").unwrap();
        match query {
            Query::Select(sel) => match &sel.targets[0].expr {
                Expr::Function(f) => {
                    assert_eq!(f.name, "foo");
                    assert!(matches!(&f.args[0], Expr::Literal(Literal::String(s)) if s == "bar"));
                }
                _ => panic!("Expected function"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_meta_function() {
        let query = parse("SELECT meta('category')").unwrap();
        match query {
            Query::Select(sel) => match &sel.targets[0].expr {
                Expr::Function(f) => {
                    assert_eq!(f.name.to_uppercase(), "META");
                    assert_eq!(f.args.len(), 1);
                    assert!(
                        matches!(&f.args[0], Expr::Literal(Literal::String(s)) if s == "category")
                    );
                }
                _ => panic!("Expected function"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_entry_meta_function() {
        let query = parse("SELECT entry_meta('source')").unwrap();
        match query {
            Query::Select(sel) => match &sel.targets[0].expr {
                Expr::Function(f) => {
                    assert_eq!(f.name.to_uppercase(), "ENTRY_META");
                    assert_eq!(f.args.len(), 1);
                }
                _ => panic!("Expected function"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_convert_function() {
        let query = parse("SELECT convert(position, 'USD')").unwrap();
        match query {
            Query::Select(sel) => match &sel.targets[0].expr {
                Expr::Function(f) => {
                    assert_eq!(f.name.to_uppercase(), "CONVERT");
                    assert_eq!(f.args.len(), 2);
                }
                _ => panic!("Expected function"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_type_cast_functions() {
        // Test INT
        let query = parse("SELECT int(number)").unwrap();
        match query {
            Query::Select(sel) => match &sel.targets[0].expr {
                Expr::Function(f) => {
                    assert_eq!(f.name.to_uppercase(), "INT");
                    assert_eq!(f.args.len(), 1);
                }
                _ => panic!("Expected function"),
            },
            _ => panic!("Expected SELECT query"),
        }

        // Test DECIMAL
        let query = parse("SELECT decimal('123.45')").unwrap();
        match query {
            Query::Select(sel) => match &sel.targets[0].expr {
                Expr::Function(f) => {
                    assert_eq!(f.name.to_uppercase(), "DECIMAL");
                }
                _ => panic!("Expected function"),
            },
            _ => panic!("Expected SELECT query"),
        }

        // Test STR
        let query = parse("SELECT str(123)").unwrap();
        match query {
            Query::Select(sel) => match &sel.targets[0].expr {
                Expr::Function(f) => {
                    assert_eq!(f.name.to_uppercase(), "STR");
                }
                _ => panic!("Expected function"),
            },
            _ => panic!("Expected SELECT query"),
        }

        // Test BOOL
        let query = parse("SELECT bool(1)").unwrap();
        match query {
            Query::Select(sel) => match &sel.targets[0].expr {
                Expr::Function(f) => {
                    assert_eq!(f.name.to_uppercase(), "BOOL");
                }
                _ => panic!("Expected function"),
            },
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_system_table_prices() {
        // Test parsing SELECT FROM #prices (system table)
        let query = parse("SELECT date, currency, amount FROM #prices").unwrap();
        match query {
            Query::Select(sel) => {
                assert_eq!(sel.targets.len(), 3);
                assert!(matches!(&sel.targets[0].expr, Expr::Column(c) if c == "date"));
                assert!(matches!(&sel.targets[1].expr, Expr::Column(c) if c == "currency"));
                assert!(matches!(&sel.targets[2].expr, Expr::Column(c) if c == "amount"));
                let from = sel.from.unwrap();
                assert_eq!(from.table_name, Some("#prices".to_string()));
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_system_table_with_where() {
        // Test parsing system table with WHERE clause
        let query = parse("SELECT * FROM #prices WHERE currency = 'EUR'").unwrap();
        match query {
            Query::Select(sel) => {
                let from = sel.from.unwrap();
                assert_eq!(from.table_name, Some("#prices".to_string()));
                assert!(sel.where_clause.is_some());
            }
            _ => panic!("Expected SELECT query"),
        }
    }

    #[test]
    fn test_regular_table_identifier() {
        // Test parsing a regular (non-system) table
        let query = parse("SELECT * FROM MyTable WHERE x = 1").unwrap();
        match query {
            Query::Select(sel) => {
                let from = sel.from.unwrap();
                assert_eq!(from.table_name, Some("MyTable".to_string()));
            }
            _ => panic!("Expected SELECT query"),
        }
    }
}
