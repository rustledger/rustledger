//! Binary and unary operators, comparisons, and arithmetic operations.

use rust_decimal::Decimal;

use crate::ast::{BinaryOp, BinaryOperator, UnaryOp, UnaryOperator};
use crate::error::QueryError;
use rustledger_core::{Amount, NaiveDate, Position};

use super::Executor;
use super::types::{DayCount, Interval, PostingContext, Value};

/// Whether `op` is an equality or ordering comparison — the operators for which
/// a NULL operand yields SQL "UNKNOWN" (treated as not-matched).
/// Operators for which a NULL operand makes the whole expression NULL (#2213).
///
/// The equality and ordering operators, plus regex matching and set
/// membership. Verified against beanquery 0.2.0: on a payee-less posting,
/// `payee ~ 'x'`, `payee !~ 'x'` and `payee IN ('a')` are each NULL there, not
/// the FALSE/TRUE/FALSE this returned.
///
/// `IS NULL` / `IS NOT NULL` are excluded on purpose -- they are null TESTS,
/// and must answer TRUE/FALSE precisely when the operand is NULL. `AND` and
/// `OR` are excluded too: they coerce, as `NOT` does.
///
/// Note this fires only on a genuine NULL. An empty `tags` is an empty SET,
/// not NULL, so `'food' IN tags` on an untagged posting is still FALSE --
/// which is what bean-query answers.
const fn propagates_null(op: BinaryOperator) -> bool {
    matches!(
        op,
        BinaryOperator::Eq
            | BinaryOperator::Ne
            | BinaryOperator::Lt
            | BinaryOperator::Le
            | BinaryOperator::Gt
            | BinaryOperator::Ge
            | BinaryOperator::Regex
            | BinaryOperator::NotRegex
            | BinaryOperator::In
            | BinaryOperator::NotIn
    )
}

/// Apply `date ± n` when `n` names a count of days.
///
/// `None` means the operand is not a number at all, and ordinary arithmetic
/// should decide instead -- which is what carries NULL propagation and the
/// `date + date` / `date + 'x'` errors.
fn date_plus_days(
    date: NaiveDate,
    other: &Value,
    negate: bool,
) -> Option<Result<Value, QueryError>> {
    let overflow = || Err(QueryError::Evaluation("date overflow".to_string()));
    match other.as_day_count() {
        DayCount::Whole(n) => {
            // `checked_neg` for the one value that cannot be negated, i64::MIN.
            let days = if negate { n.checked_neg() } else { Some(n) };
            Some(days.map_or_else(overflow, |d| shift_date(date, d)))
        }
        DayCount::Fraction => Some(Err(QueryError::Type(
            "date arithmetic takes a whole number of days".to_string(),
        ))),
        DayCount::OutOfRange => Some(overflow()),
        DayCount::NotNumeric => None,
    }
}

/// Shift `date` by a whole number of days, forward or back.
///
/// Both ends are fallible: `try_days` rejects a span too large to build, and
/// `checked_add` rejects a result outside the calendar's range. Neither
/// panics, which a bare `+` on a span would.
fn shift_date(date: NaiveDate, days: i64) -> Result<Value, QueryError> {
    let span = jiff::Span::new()
        .try_days(days)
        .map_err(|_| QueryError::Evaluation("date overflow".to_string()))?;
    date.checked_add(span)
        .map(Value::Date)
        .map_err(|_| QueryError::Evaluation("date overflow".to_string()))
}

impl Executor<'_> {
    /// Evaluate a binary operation.
    pub(super) fn evaluate_binary_op(
        &self,
        op: &BinaryOp,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        let left = self.evaluate_expr(&op.left, ctx)?;
        let right = self.evaluate_expr(&op.right, ctx)?;
        // `binary_op_on_values` owns the operator semantics — including the
        // NULL-comparison rule (a comparison involving NULL yields NULL, which
        // is falsy, so WHERE still drops rows with a missing optional field).
        self.binary_op_on_values(op.op, &left, &right)
    }

    /// Evaluate a unary operation.
    pub(super) fn evaluate_unary_op(
        &self,
        op: &UnaryOp,
        ctx: &PostingContext,
    ) -> Result<Value, QueryError> {
        let val = self.evaluate_expr(&op.operand, ctx)?;
        self.unary_op_on_value(op.op, &val)
    }

    /// Apply a unary operator to a value.
    pub(super) fn unary_op_on_value(
        &self,
        op: UnaryOperator,
        val: &Value,
    ) -> Result<Value, QueryError> {
        match op {
            UnaryOperator::Not => {
                let b = self.to_bool(val)?;
                Ok(Value::Boolean(!b))
            }
            UnaryOperator::Neg => match val {
                Value::Number(n) => Ok(Value::Number(-*n)),
                Value::Integer(i) => Ok(Value::Integer(-*i)),
                _ => Err(QueryError::Type(
                    "negation requires numeric value".to_string(),
                )),
            },
            UnaryOperator::IsNull => Ok(Value::Boolean(matches!(val, Value::Null))),
            UnaryOperator::IsNotNull => Ok(Value::Boolean(!matches!(val, Value::Null))),
        }
    }

    /// Check if two values are equal.
    pub(super) fn values_equal(&self, left: &Value, right: &Value) -> bool {
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
    pub(super) fn compare_values<F>(
        &self,
        left: &Value,
        right: &Value,
        pred: F,
    ) -> Result<Value, QueryError>
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
    ///
    /// One of THREE comparison paths in this file, which deliberately disagree
    /// about booleans. Anyone tempted to unify them should read this first:
    ///
    /// | function | used by | booleans |
    /// |---|---|---|
    /// | `compare_values` | the `<` `>` `<=` `>=` operators | rejected |
    /// | `value_less_than` | the `MIN`/`MAX` aggregates | ordered, `false < true` |
    /// | `compare_values_for_sort` | `ORDER BY` | ordered, and total |
    ///
    /// That is not drift, it is bean-query's shape. It answers
    /// `max(number > 0)` and sorts a boolean column, and refuses
    /// `(number > 0) < (number > 5)` with `operator "less(bool, bool)" not
    /// supported`. Collapsing the three would either accept a query it rejects
    /// or reject two it answers.
    ///
    /// On amounts, positions and inventories `value_less_than` and
    /// `compare_values_for_sort` agree, so `MIN`/`MAX` are `ORDER BY`'s first
    /// and last values (#2447); `compare_values` still refuses them.
    ///
    /// `compare_values_for_sort` is also total where the other two are
    /// fallible: sorting cannot fail partway through a result set, so it
    /// orders NULL rather than erroring on it.
    pub(super) fn value_less_than(&self, left: &Value, right: &Value) -> Result<bool, QueryError> {
        let ord = match (left, right) {
            (Value::Number(a), Value::Number(b)) => a.cmp(b),
            (Value::Integer(a), Value::Integer(b)) => a.cmp(b),
            (Value::Number(a), Value::Integer(b)) => a.cmp(&Decimal::from(*b)),
            (Value::Integer(a), Value::Number(b)) => Decimal::from(*a).cmp(b),
            (Value::String(a), Value::String(b)) => a.cmp(b),
            (Value::Date(a), Value::Date(b)) => a.cmp(b),
            // `false < true`, so `MAX` over booleans is `any` and `MIN` is
            // `all` -- which is what bean-query gives, because Python's
            // `max`/`min` order bools that way and it does not special-case
            // them (#2183).
            //
            // Deliberately NOT added to `compare_values`, which backs the `<`
            // and `>` operators. bean-query REFUSES those on booleans:
            //
            //     SELECT (number > 0) < (number > 5) FROM #postings
            //     -> operator "less(bool, bool)" not supported
            //
            // so defining the order there would accept a query it rejects.
            // The order exists for the aggregates and stops there.
            (Value::Boolean(a), Value::Boolean(b)) => a.cmp(b),
            // Amounts, positions and inventories in `ORDER BY`'s order, so
            // `MIN` and `MAX` are the first and last value `ORDER BY` gives
            // (#2447). They used to fail with "cannot compare values".
            //
            // MIN agrees with bean-query. MAX deliberately does NOT always:
            // bean-query's `Max` updates on `value > cur`, and beancount's
            // `Amount` and `Position` are NamedTuples defining only `__lt__`,
            // so `>` falls back to plain tuple comparison, NUMBER first. Over
            // `5 EUR` and `3 USD` it answers `5 EUR` for both MIN and MAX,
            // while its own ORDER BY puts `5 EUR` first. We answer MAX with
            // the last value in ORDER BY's order, `3 USD`. Within one
            // currency the two rules agree. Documented in
            // docs/reference/compatibility.md section 15.
            (Value::Amount(a), Value::Amount(b)) => Self::amount_order(a, b),
            (Value::Position(a), Value::Position(b)) => Self::position_order(a, b),
            (Value::Inventory(a), Value::Inventory(b)) => Self::inventory_order(a, b),
            _ => return Err(QueryError::Type("cannot compare values".to_string())),
        };
        Ok(ord.is_lt())
    }

    /// Perform arithmetic operation.
    pub(super) fn arithmetic_op<F>(
        &self,
        left: &Value,
        right: &Value,
        op: F,
    ) -> Result<Value, QueryError>
    where
        F: FnOnce(Decimal, Decimal) -> Option<Decimal>,
    {
        let (a, b) = match (left, right) {
            (Value::Number(a), Value::Number(b)) => (*a, *b),
            (Value::Integer(a), Value::Integer(b)) => (Decimal::from(*a), Decimal::from(*b)),
            (Value::Number(a), Value::Integer(b)) => (*a, Decimal::from(*b)),
            (Value::Integer(a), Value::Number(b)) => (Decimal::from(*a), *b),
            // NULL propagates through arithmetic (SQL/beanquery semantics) —
            // e.g. `safediv(...) * 100` where the division yielded NULL.
            (Value::Null, _) | (_, Value::Null) => return Ok(Value::Null),
            _ => {
                return Err(QueryError::Type(
                    "arithmetic requires numeric values".to_string(),
                ));
            }
        };
        // `op` returns `None` for undefined results (e.g. division/modulo by
        // zero, where `checked_div`/`checked_rem` yield `None`). Match
        // beanquery, which produces NULL rather than raising — and crucially
        // avoid the underlying `rust_decimal` panic on `a / 0`.
        Ok(op(a, b).map_or(Value::Null, Value::Number))
    }

    /// Modulo (`%`) matching beanquery/Python semantics.
    ///
    /// Integers use Python's FLOORED modulo (the result's sign follows the
    /// divisor): `-5 % 3 == 1`, `5 % -3 == -1`. Decimal operands keep truncated
    /// remainder, which matches Python's `Decimal.__mod__`. A zero divisor
    /// yields NULL (consistent with division). The previous code applied
    /// `Decimal::checked_rem` to integers too, giving the truncated (wrong) sign.
    pub(super) fn modulo_op(&self, left: &Value, right: &Value) -> Result<Value, QueryError> {
        if let (Value::Integer(a), Value::Integer(b)) = (left, right) {
            let (a, b) = (*a, *b);
            if b == 0 {
                return Ok(Value::Null);
            }
            // `i64::MIN % -1` overflows the truncated remainder but is
            // mathematically 0 (every integer is divisible by -1), so map the
            // overflow case to 0.
            let Some(rem) = a.checked_rem(b) else {
                return Ok(Value::Integer(0));
            };
            // Floored modulo: when the truncated remainder's sign differs from
            // the divisor's, shift by the divisor. This `rem + b` cannot
            // overflow — in the differing-sign branch `|rem| < |b|`, so the sum
            // stays within range and takes the divisor's sign.
            let result = if rem != 0 && (rem < 0) != (b < 0) {
                rem + b
            } else {
                rem
            };
            return Ok(Value::Integer(result));
        }
        self.arithmetic_op(left, right, Decimal::checked_rem)
    }

    /// Convert a value to boolean using SQL/beanquery truthiness rules.
    ///
    /// Booleans pass through directly. NULL is false. Other types follow
    /// Python beanquery's implicit truthiness so that functions like
    /// `grep(pattern, text)` — which return the matched substring on success
    /// and NULL on failure — work in `WHERE` and as operands of `AND`/`OR`/
    /// `NOT` without an explicit comparison.
    ///
    /// - Strings: non-empty is true.
    /// - Integers / numbers: non-zero is true.
    /// - Sets / metadata / objects: non-empty is true.
    /// - Other structured types (Date, Amount, Position, …): always true.
    pub(super) fn to_bool(&self, val: &Value) -> Result<bool, QueryError> {
        Ok(match val {
            Value::Boolean(b) => *b,
            Value::Null => false,
            Value::String(s) => !s.is_empty(),
            Value::Integer(i) => *i != 0,
            Value::Number(n) => !n.is_zero(),
            Value::StringSet(s) => !s.is_empty(),
            Value::Set(s) => !s.is_empty(),
            Value::Metadata(m) => !m.is_empty(),
            Value::Object(o) => !o.is_empty(),
            // Date, Amount, Position, Inventory, Interval — present implies truthy.
            Value::Date(_)
            | Value::Amount(_)
            | Value::Position(_)
            | Value::Inventory(_)
            | Value::Interval(_) => true,
        })
    }

    /// Apply a binary operator to pre-evaluated values (for subquery context).
    pub(super) fn binary_op_on_values(
        &self,
        op: BinaryOperator,
        left: &Value,
        right: &Value,
    ) -> Result<Value, QueryError> {
        // A comparison with a NULL operand is NULL, not FALSE (#2213). The two
        // are not interchangeable: `COUNT` skips NULLs but counts every FALSE,
        // so `count(payee != '')` over payee-less rows answered 4 where it
        // should answer 0. Filtering is unaffected -- `to_bool(NULL)` is false,
        // so `WHERE` still drops the row. See `propagates_null` for which
        // operators this covers and which deliberately coerce instead.
        if propagates_null(op) && (matches!(left, Value::Null) || matches!(right, Value::Null)) {
            return Ok(Value::Null);
        }
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
            BinaryOperator::Regex => {
                // ~ operator: string matches regex pattern. A NULL operand
                // never reaches here -- `propagates_null` short-circuits it to
                // NULL above, which is what bean-query answers. This arm used
                // to return FALSE and claim that matched beancount; it did not.
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
                // Use cached regex matching
                let re = self.require_regex(pattern)?;
                Ok(Value::Boolean(re.is_match(s)))
            }
            BinaryOperator::In => {
                // Check if left value is in right set
                match right {
                    Value::StringSet(set) => {
                        // StringSet from columns like tags, links
                        let needle = match left {
                            Value::String(s) => s,
                            _ => {
                                return Err(QueryError::Type(
                                    "IN requires string left operand for StringSet".to_string(),
                                ));
                            }
                        };
                        Ok(Value::Boolean(set.contains(needle)))
                    }
                    Value::Set(values) => {
                        // Generic set from set literal - check if left equals any element
                        let found = values.iter().any(|v| self.values_equal(left, v));
                        Ok(Value::Boolean(found))
                    }
                    // Fall back to scalar equality so `x IN ('a')` ≡ `x = 'a'`,
                    // matching SQL/bean-query semantics (issue #916).
                    _ => Ok(Value::Boolean(self.values_equal(left, right))),
                }
            }
            BinaryOperator::NotRegex => {
                // !~ operator: string does not match regex pattern. As with
                // `~`, a NULL operand is short-circuited to NULL above and
                // never reaches this arm.
                let s = match left {
                    Value::String(s) => s,
                    _ => {
                        return Err(QueryError::Type(
                            "!~ requires string left operand".to_string(),
                        ));
                    }
                };
                let pattern = match right {
                    Value::String(p) => p,
                    _ => {
                        return Err(QueryError::Type("!~ requires string pattern".to_string()));
                    }
                };
                let re = self.require_regex(pattern)?;
                Ok(Value::Boolean(!re.is_match(s)))
            }
            BinaryOperator::NotIn => {
                // NOT IN: check if left value is not in right set
                match right {
                    Value::StringSet(set) => {
                        // StringSet from columns like tags, links
                        let needle = match left {
                            Value::String(s) => s,
                            _ => {
                                return Err(QueryError::Type(
                                    "NOT IN requires string left operand for StringSet".to_string(),
                                ));
                            }
                        };
                        Ok(Value::Boolean(!set.contains(needle)))
                    }
                    Value::Set(values) => {
                        // Generic set from set literal - check if left does not equal any element
                        let found = values.iter().any(|v| self.values_equal(left, v));
                        Ok(Value::Boolean(!found))
                    }
                    // Fall back to scalar inequality so `x NOT IN ('a')` ≡ `x != 'a'`,
                    // matching SQL/bean-query semantics (issue #916).
                    _ => Ok(Value::Boolean(!self.values_equal(left, right))),
                }
            }
            BinaryOperator::Add => {
                // Handle date + interval
                match (left, right) {
                    (Value::Date(d), Value::Interval(i)) | (Value::Interval(i), Value::Date(d)) => {
                        i.add_to_date(*d)
                            .map(Value::Date)
                            .ok_or_else(|| QueryError::Evaluation("date overflow".to_string()))
                    }
                    // A plain number on either side of `+` is a count of days
                    // (#2324): `2026-07-01 + 365` and `365 + 2026-07-01` both
                    // give 2027-07-01, as bean-query does. `interval(365,
                    // 'day')` remains the explicit spelling of the same shift.
                    (Value::Date(d), other) | (other, Value::Date(d)) => {
                        date_plus_days(*d, other, false).unwrap_or_else(|| {
                            self.arithmetic_op(
                                left,
                                right,
                                rustledger_core::checked_add_python_scale,
                            )
                        })
                    }
                    // Checked so a value-range overflow yields NULL (like
                    // div-by-zero — see `arithmetic_op`) instead of panicking;
                    // `rust_decimal` panics on raw `+`/`-`/`*` overflow.
                    //
                    // Python scale semantics, so `0.00 + 1` is `1.00` as
                    // bean-query renders it, not `1` — the same rule SUM
                    // accumulates by. See `rustledger_core::add_python_scale`.
                    _ => self.arithmetic_op(left, right, rustledger_core::checked_add_python_scale),
                }
            }
            BinaryOperator::Sub => {
                // Handle date - interval
                match (left, right) {
                    (Value::Date(d), Value::Interval(i)) => {
                        let neg_count = i.count.checked_neg().ok_or_else(|| {
                            QueryError::Evaluation("interval count overflow".to_string())
                        })?;
                        let neg_interval = Interval::new(neg_count, i.unit);
                        neg_interval
                            .add_to_date(*d)
                            .map(Value::Date)
                            .ok_or_else(|| QueryError::Evaluation("date overflow".to_string()))
                    }
                    // `date - date` is the count of days between them -- the
                    // same answer `date_diff` gives, computed the same way so
                    // the two cannot drift -- and `date - n` shifts back
                    // (#2324). `n - date` stays an error, as in bean-query.
                    (Value::Date(a), Value::Date(b)) => Ok(Value::Integer(i64::from(
                        a.since(*b).unwrap_or_default().get_days(),
                    ))),
                    (Value::Date(d), other) => {
                        date_plus_days(*d, other, true).unwrap_or_else(|| {
                            self.arithmetic_op(
                                left,
                                right,
                                rustledger_core::checked_sub_python_scale,
                            )
                        })
                    }
                    _ => self.arithmetic_op(left, right, rustledger_core::checked_sub_python_scale),
                }
            }
            BinaryOperator::Mul => self.arithmetic_op(left, right, Decimal::checked_mul),
            // Python's ideal-exponent rule, same as AVG — see
            // `rustledger_core::checked_div_python_scale`. Unlike `avg`, this
            // operator DOES exist in bean-query, so the divergence was
            // user-visible on both sides: `0.00 / 4` rendered `0` against its
            // `0.00`, and `7 / 2` rendered `3.50` against its `3.5`.
            BinaryOperator::Div => {
                self.arithmetic_op(left, right, rustledger_core::checked_div_python_scale)
            }
            BinaryOperator::Mod => self.modulo_op(left, right),
        }
    }

    /// ORDER BY's order for amounts: currency, then number, as beancount's
    /// `amount.sortkey` orders them (#2445).
    fn amount_order(a: &Amount, b: &Amount) -> std::cmp::Ordering {
        a.currency
            .as_str()
            .cmp(b.currency.as_str())
            .then_with(|| a.number.cmp(&b.number))
    }

    /// ORDER BY's order for positions: units currency, then cost number,
    /// cost currency, and units number, a position with no cost counting as
    /// cost `0` in `""`. That is beancount's `Position.sortkey`, whose first
    /// key ranks the units currency: `USD`, `EUR`, `JPY`, `CAD`, `GBP`,
    /// `AUD`, `NZD`, `CHF` first, in that order, so an operating currency sorts
    /// before the commodities held against it. It ranks every other currency
    /// by the LENGTH of its name, though its comment says alphabetical, so all
    /// other currencies of one length tie and their positions interleave by
    /// cost: `GLD` and `VHT` lots mixed. Those sort alphabetically here, a
    /// deliberate divergence (#2445).
    pub(super) fn position_order(a: &Position, b: &Position) -> std::cmp::Ordering {
        fn cost(p: &Position) -> (Decimal, &str) {
            p.cost
                .as_ref()
                .map_or((Decimal::ZERO, ""), |c| (c.number, c.currency.as_str()))
        }
        /// beancount's `CURRENCY_ORDER`, then the rest alphabetically.
        fn rank(currency: &str) -> (usize, &str) {
            const LISTED: [&str; 8] = ["USD", "EUR", "JPY", "CAD", "GBP", "AUD", "NZD", "CHF"];
            LISTED
                .iter()
                .position(|listed| *listed == currency)
                .map_or((LISTED.len(), currency), |i| (i, ""))
        }
        rank(a.units.currency.as_str())
            .cmp(&rank(b.units.currency.as_str()))
            .then_with(|| cost(a).cmp(&cost(b)))
            .then_with(|| a.units.number.cmp(&b.units.number))
    }

    /// ORDER BY's order for inventories: each one's positions sorted in the
    /// position order, then compared in turn, a shorter list that agrees so
    /// far sorting first (so an empty inventory sorts first). That is
    /// beancount's `Inventory.__lt__`, `sorted(self) < sorted(other)`, with
    /// this file's position order. It compared their FIRST positions, in the
    /// order the ledger added them, so a group's place depended on which of
    /// its lots came first in the ledger (#2445).
    fn inventory_order(
        a: &rustledger_core::Inventory,
        b: &rustledger_core::Inventory,
    ) -> std::cmp::Ordering {
        Self::position_lists_order(&Self::sorted_positions(a), &Self::sorted_positions(b))
    }

    /// An inventory's positions in the position order, leaving out those of
    /// zero units: an inventory keeps a cost-less position that nets to zero
    /// (#2378), which holds nothing, and beancount has none to sort.
    pub(super) fn sorted_positions(inv: &rustledger_core::Inventory) -> Vec<&Position> {
        let mut positions: Vec<&Position> = inv
            .positions()
            .filter(|p| !p.units.number.is_zero())
            .collect();
        positions.sort_by(|x, y| Self::position_order(x, y));
        positions
    }

    /// Two sorted position lists compared in turn, a shorter list that agrees
    /// so far sorting first: the inventory order, over positions sorted once.
    pub(super) fn position_lists_order<P: std::borrow::Borrow<Position>>(
        a: &[P],
        b: &[P],
    ) -> std::cmp::Ordering {
        a.iter()
            .zip(b)
            .map(|(x, y)| Self::position_order(x.borrow(), y.borrow()))
            .find(|ord| ord.is_ne())
            .unwrap_or_else(|| a.len().cmp(&b.len()))
    }

    /// Compare two values for sorting purposes.
    pub(super) fn compare_values_for_sort(
        &self,
        left: &Value,
        right: &Value,
    ) -> std::cmp::Ordering {
        match (left, right) {
            // NULL sorts as the smallest value, matching beanquery: ORDER BY ...
            // ASC places NULLs first, DESC (via the caller's `.reverse()`) places
            // them last. (`SELECT payee ORDER BY payee` on a payee-less txn now
            // matches bean-query.)
            (Value::Null, Value::Null) => std::cmp::Ordering::Equal,
            (Value::Null, _) => std::cmp::Ordering::Less,
            (_, Value::Null) => std::cmp::Ordering::Greater,
            (Value::Number(a), Value::Number(b)) => a.cmp(b),
            (Value::Integer(a), Value::Integer(b)) => a.cmp(b),
            (Value::Number(a), Value::Integer(b)) => a.cmp(&Decimal::from(*b)),
            (Value::Integer(a), Value::Number(b)) => Decimal::from(*a).cmp(b),
            (Value::String(a), Value::String(b)) => a.cmp(b),
            (Value::Date(a), Value::Date(b)) => a.cmp(b),
            (Value::Boolean(a), Value::Boolean(b)) => a.cmp(b),
            // Amounts by currency, then number: beancount's `amount.sortkey`,
            // and so bean-query's ORDER BY. By number alone, `5 USD` and
            // `5 EUR` compared equal and one currency's values scattered
            // through another's (#2445).
            (Value::Amount(a), Value::Amount(b)) => Self::amount_order(a, b),
            (Value::Position(a), Value::Position(b)) => Self::position_order(a, b),
            (Value::Inventory(a), Value::Inventory(b)) => Self::inventory_order(a, b),
            // Compare intervals by approximate days
            (Value::Interval(a), Value::Interval(b)) => a.to_approx_days().cmp(&b.to_approx_days()),
            _ => std::cmp::Ordering::Equal, // Can't compare other types
        }
    }
}
