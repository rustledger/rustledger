//! String function implementations for the BQL executor.

use crate::error::QueryError;

use super::super::Executor;
use super::super::types::Value;

/// Ellipsis marker `MAXWIDTH` appends when it shortens text (Python
/// `textwrap.shorten`'s default `placeholder`, sans the leading space).
const MAXWIDTH_PLACEHOLDER: &str = "[...]";

impl Executor<'_> {
    /// Value-core for MAXWIDTH, called by the eager registry
    /// (`evaluate_function_on_values`); the lazy path reaches it through
    /// delegation. Canonical behavior matches Python `textwrap.shorten`
    /// (beanquery's MAXWIDTH).
    pub(crate) fn maxwidth_on_values(args: &[Value]) -> Result<Value, QueryError> {
        Self::require_args_count("MAXWIDTH", args, 2)?;

        let string = match &args[0] {
            Value::String(s) => s.clone(),
            _ => {
                return Err(QueryError::Type(
                    "MAXWIDTH: first argument must be a string".to_string(),
                ));
            }
        };
        let n = match &args[1] {
            Value::Integer(i) => usize::try_from(*i).map_err(|_| {
                QueryError::Type("MAXWIDTH: second argument must be a positive integer".to_string())
            })?,
            Value::Number(n) => {
                use rust_decimal::prelude::ToPrimitive;
                n.to_usize().ok_or_else(|| {
                    QueryError::Type("MAXWIDTH: second argument must be a positive integer".into())
                })?
            }
            _ => {
                return Err(QueryError::Type(
                    "MAXWIDTH: second argument must be an integer".to_string(),
                ));
            }
        };

        // Match Python `textwrap.shorten` (beanquery's MAXWIDTH): collapse
        // runs of whitespace to single spaces, and if the result exceeds `n`,
        // drop whole trailing words and append the placeholder ` [...]`. A
        // single over-long word collapses to `[...]`. A width too small for the
        // placeholder itself is an error (textwrap raises ValueError).
        let words: Vec<&str> = string.split_whitespace().collect();
        let collapsed = words.join(" ");
        if collapsed.chars().count() <= n {
            return Ok(Value::String(collapsed));
        }
        let placeholder_len = MAXWIDTH_PLACEHOLDER.chars().count();
        if placeholder_len > n {
            return Err(QueryError::Evaluation(
                "MAXWIDTH: placeholder too large for max width".to_string(),
            ));
        }
        // Greedily keep words while "<kept> [...]" still fits in `n`.
        let mut kept = String::new();
        let mut kept_len = 0usize;
        for word in &words {
            let wlen = word.chars().count();
            let candidate_len = if kept.is_empty() {
                wlen
            } else {
                kept_len + 1 + wlen
            };
            // candidate + a leading-space placeholder (" [...]").
            if candidate_len + 1 + placeholder_len <= n {
                if !kept.is_empty() {
                    kept.push(' ');
                }
                kept.push_str(word);
                kept_len = candidate_len;
            } else {
                break;
            }
        }
        if kept.is_empty() {
            Ok(Value::String(MAXWIDTH_PLACEHOLDER.to_string()))
        } else {
            Ok(Value::String(format!("{kept} {MAXWIDTH_PLACEHOLDER}")))
        }
    }
}

/// Python-style slice `chars[start:end]` over a character vector.
///
/// Matches `CPython` (and thus beanquery) semantics: negative indices count from
/// the end, both bounds are clamped into `0..=len`, and `start >= end` yields an
/// empty string. `end == None` slices to the end (`chars[start:]`).
pub(in crate::executor) fn py_slice(chars: &[char], start: i64, end: Option<i64>) -> String {
    let n = chars.len() as i64;
    // `saturating_add` so a very negative index (e.g. `i64::MIN`) clamps to 0
    // instead of overflowing and panicking in debug builds.
    let normalize = |i: i64| -> i64 {
        if i < 0 {
            n.saturating_add(i).max(0)
        } else {
            i.min(n)
        }
    };
    let s = normalize(start);
    let e = end.map_or(n, normalize);
    if s >= e {
        String::new()
    } else {
        chars[s as usize..e as usize].iter().collect()
    }
}
