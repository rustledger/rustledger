//! BQL Parser implementation.
//!
//! Uses chumsky for parser combinators.

use chumsky::prelude::*;
use rust_decimal::Decimal;
use std::str::FromStr;

use crate::ast::{
    BalancesQuery, BinaryOperator, Expr, FromClause, FunctionCall, JournalQuery, Literal,
    OrderSpec, PrintQuery, Query, SelectQuery, SortDirection, Target, UnaryOperator,
};
use crate::error::{ParseError, ParseErrorKind};
use rustledger_core::NaiveDate;

type ParserInput<'a> = &'a str;
type ParserExtra<'a> = extra::Err<Rich<'a, char>>;

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
    text::keyword(keyword).ignored()
}

/// Parse digits.
fn digits<'a>() -> impl Parser<'a, ParserInput<'a>, &'a str, ParserExtra<'a>> + Clone {
    one_of("0123456789").repeated().at_least(1).to_slice()
}

/// Parse the main query.
fn query_parser<'a>() -> impl Parser<'a, ParserInput<'a>, Query, ParserExtra<'a>> {
    ws().ignore_then(choice((
        select_query().map(Query::Select),
        journal_query().map(Query::Journal),
        balances_query().map(Query::Balances),
        print_query().map(Query::Print),
    )))
    .then_ignore(ws())
    .then_ignore(just(';').or_not())
}

/// Parse a SELECT query.
fn select_query<'a>() -> impl Parser<'a, ParserInput<'a>, SelectQuery, ParserExtra<'a>> {
    kw("SELECT")
        .ignore_then(ws1())
        .ignore_then(
            kw("DISTINCT")
                .then_ignore(ws1())
                .or_not()
                .map(|d| d.is_some()),
        )
        .then(targets())
        .then(from_clause().or_not())
        .then(where_clause().or_not())
        .then(group_by_clause().or_not())
        .then(order_by_clause().or_not())
        .then(limit_clause().or_not())
        .map(
            |((((((distinct, targets), from), where_clause), group_by), order_by), limit)| {
                SelectQuery {
                    distinct,
                    targets,
                    from,
                    where_clause,
                    group_by,
                    order_by,
                    limit,
                }
            },
        )
}

/// Parse target expressions.
fn targets<'a>() -> impl Parser<'a, ParserInput<'a>, Vec<Target>, ParserExtra<'a>> {
    target()
        .separated_by(ws().then(just(',')).then(ws()))
        .at_least(1)
        .collect()
}

/// Parse a single target.
fn target<'a>() -> impl Parser<'a, ParserInput<'a>, Target, ParserExtra<'a>> {
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

/// Parse FROM clause.
fn from_clause<'a>() -> impl Parser<'a, ParserInput<'a>, FromClause, ParserExtra<'a>> {
    ws1()
        .ignore_then(kw("FROM"))
        .ignore_then(ws1())
        .ignore_then(from_modifiers())
}

/// Parse FROM modifiers (OPEN ON, CLOSE ON, CLEAR, filter).
fn from_modifiers<'a>() -> impl Parser<'a, ParserInput<'a>, FromClause, ParserExtra<'a>> {
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
        })
}

/// Parse FROM filter expression (predicates).
fn from_filter<'a>() -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> {
    expr()
}

/// Parse WHERE clause.
fn where_clause<'a>() -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> {
    ws1()
        .ignore_then(kw("WHERE"))
        .ignore_then(ws1())
        .ignore_then(expr())
}

/// Parse GROUP BY clause.
fn group_by_clause<'a>() -> impl Parser<'a, ParserInput<'a>, Vec<Expr>, ParserExtra<'a>> {
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

/// Parse ORDER BY clause.
fn order_by_clause<'a>() -> impl Parser<'a, ParserInput<'a>, Vec<OrderSpec>, ParserExtra<'a>> {
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
fn order_spec<'a>() -> impl Parser<'a, ParserInput<'a>, OrderSpec, ParserExtra<'a>> {
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
fn limit_clause<'a>() -> impl Parser<'a, ParserInput<'a>, u64, ParserExtra<'a>> {
    ws1()
        .ignore_then(kw("LIMIT"))
        .ignore_then(ws1())
        .ignore_then(integer())
        .map(|n| n as u64)
}

/// Parse JOURNAL query.
fn journal_query<'a>() -> impl Parser<'a, ParserInput<'a>, JournalQuery, ParserExtra<'a>> {
    kw("JOURNAL")
        .ignore_then(ws1())
        .ignore_then(string_literal())
        .then(at_function().or_not())
        .then(
            ws1()
                .ignore_then(kw("FROM"))
                .ignore_then(ws1())
                .ignore_then(from_modifiers())
                .or_not(),
        )
        .map(|((account_pattern, at_function), from)| JournalQuery {
            account_pattern,
            at_function,
            from,
        })
}

/// Parse BALANCES query.
fn balances_query<'a>() -> impl Parser<'a, ParserInput<'a>, BalancesQuery, ParserExtra<'a>> {
    kw("BALANCES")
        .ignore_then(at_function().or_not())
        .then(
            ws1()
                .ignore_then(kw("FROM"))
                .ignore_then(ws1())
                .ignore_then(from_modifiers())
                .or_not(),
        )
        .map(|(at_function, from)| BalancesQuery { at_function, from })
}

/// Parse PRINT query.
fn print_query<'a>() -> impl Parser<'a, ParserInput<'a>, PrintQuery, ParserExtra<'a>> {
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

/// Parse AT function (e.g., AT cost, AT units).
fn at_function<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> {
    ws1()
        .ignore_then(kw("AT"))
        .ignore_then(ws1())
        .ignore_then(identifier())
}

/// Parse an expression (with precedence climbing).
#[allow(clippy::large_stack_frames)]
fn expr<'a>() -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> {
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

        // Multiplicative: * /
        let multiplicative = unary.clone().foldl(
            ws().ignore_then(choice((
                just('*').to(BinaryOperator::Mul),
                just('/').to(BinaryOperator::Div),
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

        // Comparison: = != < <= > >= ~ IN
        let comparison = additive
            .clone()
            .then(
                ws().ignore_then(comparison_op())
                    .then_ignore(ws())
                    .then(additive)
                    .or_not(),
            )
            .map(|(left, rest)| {
                if let Some((op, right)) = rest {
                    Expr::binary(left, op, right)
                } else {
                    left
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

/// Parse comparison operators.
fn comparison_op<'a>() -> impl Parser<'a, ParserInput<'a>, BinaryOperator, ParserExtra<'a>> + Clone
{
    choice((
        just("!=").to(BinaryOperator::Ne),
        just("<=").to(BinaryOperator::Le),
        just(">=").to(BinaryOperator::Ge),
        just('=').to(BinaryOperator::Eq),
        just('<').to(BinaryOperator::Lt),
        just('>').to(BinaryOperator::Gt),
        just('~').to(BinaryOperator::Regex),
        kw("IN").to(BinaryOperator::In),
    ))
}

/// Parse primary expressions.
fn primary_expr<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone + 'a,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    choice((
        // Parenthesized expression
        just('(')
            .ignore_then(ws())
            .ignore_then(expr)
            .then_ignore(ws())
            .then_ignore(just(')'))
            .map(|e| Expr::Paren(Box::new(e))),
        // Function call or column reference (must come before wildcard check)
        function_call_or_column(),
        // Literals
        literal().map(Expr::Literal),
        // Wildcard (fallback if nothing else matched)
        just('*').to(Expr::Wildcard),
    ))
}

/// Parse function call or column reference.
fn function_call_or_column<'a>() -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone
{
    identifier()
        .then(
            ws().ignore_then(just('('))
                .ignore_then(ws())
                .ignore_then(function_args())
                .then_ignore(ws())
                .then_ignore(just(')'))
                .or_not(),
        )
        .map(|(name, args)| {
            if let Some(args) = args {
                Expr::Function(FunctionCall { name, args })
            } else {
                Expr::Column(name)
            }
        })
}

/// Parse function arguments.
fn function_args<'a>() -> impl Parser<'a, ParserInput<'a>, Vec<Expr>, ParserExtra<'a>> + Clone {
    // Allow empty args or comma-separated expressions
    // Simple version: only allow columns and wildcards as function args (not full expressions)
    simple_arg()
        .separated_by(ws().then(just(',')).then(ws()))
        .collect()
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

/// Parse a string literal.
fn string_literal<'a>() -> impl Parser<'a, ParserInput<'a>, String, ParserExtra<'a>> + Clone {
    // Double-quoted string
    just('"')
        .ignore_then(
            none_of("\"\\")
                .or(just('\\').ignore_then(any()))
                .repeated()
                .collect::<String>(),
        )
        .then_ignore(just('"'))
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
}
