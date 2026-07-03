//! Math function implementations for the BQL executor.

use rust_decimal::Decimal;

use crate::error::QueryError;

use super::super::Executor;
use super::super::types::Value;

impl Executor<'_> {
    /// Value-core for ROUND, called by the eager registry; the lazy path reaches
    /// it through delegation. Supports negative precision (rounds tens/hundreds),
    /// matching Python/beanquery `round`.
    pub(crate) fn round_on_values(args: &[Value]) -> Result<Value, QueryError> {
        if args.is_empty() || args.len() > 2 {
            return Err(QueryError::InvalidArguments(
                "ROUND".to_string(),
                "expected 1 or 2 arguments".to_string(),
            ));
        }

        let val = args[0].clone();
        let decimals: i64 = if args.len() == 2 {
            match &args[1] {
                Value::Integer(i) => *i,
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
            Value::Number(n) => Ok(Value::Number(round_decimal(n, decimals))),
            Value::Integer(i) => {
                // Rounding an integer to >= 0 places is a no-op; a negative
                // precision rounds it to tens/hundreds (beanquery `round(1234,
                // -2)` = 1200). The result is integral — keep it an integer when
                // it still fits in i64, else fall back to a decimal.
                if decimals >= 0 {
                    Ok(Value::Integer(i))
                } else {
                    use rust_decimal::prelude::ToPrimitive;
                    let r = round_decimal(Decimal::from(i), decimals);
                    Ok(r.to_i64().map_or(Value::Number(r), Value::Integer))
                }
            }
            Value::Null => Ok(Value::Null),
            _ => Err(QueryError::Type("ROUND expects a number".to_string())),
        }
    }
}

/// Round `n` to `places` decimal places, matching Python's `round` (and thus
/// beanquery): a NEGATIVE `places` rounds to the left of the decimal point
/// (tens, hundreds, …). Uses banker's rounding (half-to-even), consistent with
/// `Decimal::round_dp`.
///
/// The old code cast `places` to `u32`, so a negative value wrapped to a huge
/// precision and `round_dp` became a silent no-op.
fn round_decimal(n: Decimal, places: i64) -> Decimal {
    if places >= 0 {
        // `round_dp` caps at Decimal's 28-digit precision; clamp to avoid a
        // needless huge argument.
        return n.round_dp(u32::try_from(places).unwrap_or(u32::MAX).min(28));
    }
    // `checked_neg` guards `places == i64::MIN` (where `-places` would overflow).
    // 10^k also stops fitting in Decimal beyond 28 digits; in either case any
    // representable number rounds to 0 at that magnitude.
    let Some(k) = places.checked_neg() else {
        return Decimal::ZERO;
    };
    if k > 28 {
        return Decimal::ZERO;
    }
    let scale = Decimal::from_i128_with_scale(10i128.pow(k as u32), 0);
    (n / scale).round() * scale
}
