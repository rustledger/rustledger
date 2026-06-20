//! Types used by the BQL query executor.

// ratchet: fxhash-only — hot path; use FxHashMap/FxHashSet, not std SipHash collections (#1237).
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};

use rust_decimal::Decimal;
use rustledger_core::{Amount, Inventory, Metadata, NaiveDate, Position, Transaction};

/// Source location information for a directive.
#[derive(Debug, Clone)]
pub struct SourceLocation {
    /// File path.
    pub filename: String,
    /// Line number (1-based).
    pub lineno: usize,
}

/// An interval unit for date arithmetic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntervalUnit {
    /// Days.
    Day,
    /// Weeks.
    Week,
    /// Months.
    Month,
    /// Quarters.
    Quarter,
    /// Years.
    Year,
}

impl IntervalUnit {
    /// Parse an interval unit from a string.
    pub fn parse_unit(s: &str) -> Option<Self> {
        match s.to_uppercase().as_str() {
            "DAY" | "DAYS" | "D" => Some(Self::Day),
            "WEEK" | "WEEKS" | "W" => Some(Self::Week),
            "MONTH" | "MONTHS" | "M" => Some(Self::Month),
            "QUARTER" | "QUARTERS" | "Q" => Some(Self::Quarter),
            "YEAR" | "YEARS" | "Y" => Some(Self::Year),
            _ => None,
        }
    }
}

/// An interval value for date arithmetic.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Interval {
    /// The count (can be negative).
    pub count: i64,
    /// The unit.
    pub unit: IntervalUnit,
}

impl Interval {
    /// Create a new interval.
    pub const fn new(count: i64, unit: IntervalUnit) -> Self {
        Self { count, unit }
    }

    /// Convert interval to an approximate number of days for comparison.
    /// Uses: Day=1, Week=7, Month=30, Quarter=91, Year=365.
    pub(crate) const fn to_approx_days(&self) -> i64 {
        let days_per_unit = match self.unit {
            IntervalUnit::Day => 1,
            IntervalUnit::Week => 7,
            IntervalUnit::Month => 30,
            IntervalUnit::Quarter => 91,
            IntervalUnit::Year => 365,
        };
        self.count.saturating_mul(days_per_unit)
    }

    /// Add this interval to a date.
    pub fn add_to_date(&self, date: NaiveDate) -> Option<NaiveDate> {
        use jiff::ToSpan;

        let span = match self.unit {
            IntervalUnit::Day => self.count.days(),
            IntervalUnit::Week => self.count.weeks(),
            IntervalUnit::Month => self.count.months(),
            IntervalUnit::Quarter => (self.count * 3).months(),
            IntervalUnit::Year => self.count.years(),
        };
        date.checked_add(span).ok()
    }
}

/// A value that can result from evaluating a BQL expression.
///
/// Heavy variants (Inventory, Position, Metadata, Object) are boxed to reduce
/// the size of the enum from 120 bytes to 32 bytes, improving cache efficiency
/// when processing large result sets.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    /// String value.
    String(String),
    /// Numeric value.
    Number(Decimal),
    /// Integer value.
    Integer(i64),
    /// Date value.
    Date(NaiveDate),
    /// Boolean value.
    Boolean(bool),
    /// Amount (number + currency).
    Amount(Amount),
    /// Position (amount + optional cost). Boxed to reduce enum size.
    Position(Box<Position>),
    /// Inventory (aggregated positions). Boxed to reduce enum size.
    Inventory(Box<Inventory>),
    /// Set of strings (tags, links).
    StringSet(Vec<String>),
    /// Generic set of values for IN operator (supports mixed types).
    Set(Vec<Self>),
    /// Metadata dictionary. Boxed to reduce enum size.
    Metadata(Box<Metadata>),
    /// Interval for date arithmetic.
    Interval(Interval),
    /// Structured object (for entry, meta columns). Boxed to reduce enum size.
    Object(Box<BTreeMap<String, Self>>),
    /// NULL value.
    Null,
}

impl Value {
    /// Compute a hash for this value.
    ///
    /// Note: This is not the standard Hash trait because some contained types
    /// (Decimal, Inventory) don't implement Hash. We use byte representations
    /// for those types.
    pub(crate) fn hash_value<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Self::String(s) => s.hash(state),
            Self::Number(d) => d.serialize().hash(state),
            Self::Integer(i) => i.hash(state),
            Self::Date(d) => {
                d.year().hash(state);
                d.month().hash(state);
                d.day().hash(state);
            }
            Self::Boolean(b) => b.hash(state),
            Self::Amount(a) => {
                a.number.serialize().hash(state);
                a.currency.as_str().hash(state);
            }
            Self::Position(p) => {
                // Dereference boxed position
                p.units.number.serialize().hash(state);
                p.units.currency.as_str().hash(state);
                if let Some(cost) = &p.cost {
                    cost.number.serialize().hash(state);
                    cost.currency.as_str().hash(state);
                }
            }
            Self::Inventory(inv) => {
                // Dereference boxed inventory
                for pos in inv.positions() {
                    pos.units.number.serialize().hash(state);
                    pos.units.currency.as_str().hash(state);
                    if let Some(cost) = &pos.cost {
                        cost.number.serialize().hash(state);
                        cost.currency.as_str().hash(state);
                    }
                }
            }
            Self::StringSet(ss) => {
                // Hash StringSet in a canonical, order-independent way by sorting first.
                let mut sorted = ss.clone();
                sorted.sort();
                for s in &sorted {
                    s.hash(state);
                }
            }
            Self::Set(values) => {
                // Hash each value in order (sets from literals maintain order)
                for v in values {
                    v.hash_value(state);
                }
            }
            Self::Metadata(meta) => {
                // Hash metadata in canonical order by sorting keys (boxed)
                let mut keys: Vec<_> = meta.keys().collect();
                keys.sort();
                for key in keys {
                    key.hash(state);
                    // Hash the debug representation of the value
                    format!("{:?}", meta.get(key)).hash(state);
                }
            }
            Self::Interval(interval) => {
                interval.count.hash(state);
                interval.unit.hash(state);
            }
            Self::Object(obj) => {
                // BTreeMap is already sorted by key, so iteration order is deterministic (boxed)
                for (k, v) in obj.as_ref() {
                    k.hash(state);
                    v.hash_value(state);
                }
            }
            Self::Null => {}
        }
    }
}

/// A row of query results.
pub type Row = Vec<Value>;

/// Compute a hash for a row (for DISTINCT deduplication).
///
/// Uses `FxHasher` (the same non-cryptographic hash backing every
/// `FxHashMap` in the workspace). DISTINCT / GROUP BY keys are internal
/// dedup tokens — they need speed, not DoS-resistance.
pub fn hash_row(row: &Row) -> u64 {
    let mut hasher = rustc_hash::FxHasher::default();
    for value in row {
        value.hash_value(&mut hasher);
    }
    hasher.finish()
}

/// Compute a hash for a single value (for PIVOT lookups).
pub fn hash_single_value(value: &Value) -> u64 {
    let mut hasher = rustc_hash::FxHasher::default();
    value.hash_value(&mut hasher);
    hasher.finish()
}

/// Query result containing column names and rows.
///
/// **Invariant**: `rows.len() == row_group_keys.len()`. Always. Mutating
/// either field directly will violate this; use the helper methods
/// (`add_row`, `add_aggregate_row`, `truncate`, `sort_by`, etc.) that
/// keep both vectors in lockstep. The invariant is enforced at runtime
/// with `assert_eq!` inside `sort_by`.
#[derive(Debug, Clone)]
pub struct QueryResult {
    /// Column names.
    pub columns: Vec<String>,
    /// Result rows.
    pub rows: Vec<Row>,
    /// Per-row GROUP BY key values, parallel to `rows`. `None` for rows
    /// produced outside aggregation. Populated by the aggregate execution
    /// path; used by the text renderer to recover the per-row currency
    /// context for `Value::Number` cells emitted by `SUM` / `AVG` (issue
    /// #988 — display-precision fix that stays lossless for JSON/CSV).
    ///
    /// `pub(crate)` so external consumers can't accidentally violate the
    /// parallel-vector invariant; reach in directly only inside this crate
    /// and only with extreme care. External access goes through
    /// [`Self::group_key`].
    pub(crate) row_group_keys: Vec<Option<Vec<Value>>>,
}

impl QueryResult {
    /// Create a new empty result.
    pub const fn new(columns: Vec<String>) -> Self {
        Self {
            columns,
            rows: Vec::new(),
            row_group_keys: Vec::new(),
        }
    }

    /// Add a row to the result with no GROUP BY context (non-aggregate path).
    /// The sidecar (`row_group_keys`) records `None` for this row, so the
    /// text renderer applies no per-currency quantization (issue #988).
    /// Aggregate paths must use [`Self::add_aggregate_row`] instead.
    pub fn add_row(&mut self, row: Row) {
        self.rows.push(row);
        self.row_group_keys.push(None);
    }

    /// Add a row produced by aggregation, recording the GROUP BY key values
    /// alongside it. The renderer consults the key to quantize numeric
    /// aggregates against the per-currency display precision (issue #988).
    ///
    /// Multi-column GROUP BY note: when several columns are grouped (e.g.
    /// `GROUP BY account, currency`), the entire key is preserved here.
    /// The renderer's currency-hint extraction (`currency_hint_for_row`
    /// in `rustledger/src/cmd/query/output.rs`) takes the *first*
    /// currency-shaped string in iteration order — so put the currency
    /// column first if both are currency-shaped, which is rare in
    /// practice but possible.
    pub fn add_aggregate_row(&mut self, row: Row, group_key: Vec<Value>) {
        self.rows.push(row);
        self.row_group_keys.push(if group_key.is_empty() {
            None
        } else {
            Some(group_key)
        });
    }

    /// Get the GROUP BY key for a given row, if it was produced by
    /// aggregation. Returns `None` for non-aggregate rows or when the
    /// row index is out of range. This is the public read-side of the
    /// `row_group_keys` sidecar — prefer it over reaching into the
    /// field directly.
    ///
    /// Returns `&[Value]` rather than `&Vec<Value>` so callers aren't
    /// tied to the specific container type.
    #[must_use]
    pub fn group_key(&self, row_idx: usize) -> Option<&[Value]> {
        self.row_group_keys.get(row_idx).and_then(|k| k.as_deref())
    }

    /// Whether any row in the result was produced by aggregation. Lets
    /// downstream renderers short-circuit per-row hint lookups when
    /// the cache would be all `None` anyway (issue #988 follow-up).
    #[must_use]
    pub fn has_aggregate_rows(&self) -> bool {
        self.row_group_keys.iter().any(Option::is_some)
    }

    /// Truncate to the first `len` rows, keeping `row_group_keys` in
    /// lockstep so the parallel-vector invariant survives LIMIT.
    pub fn truncate(&mut self, len: usize) {
        self.rows.truncate(len);
        self.row_group_keys.truncate(len);
    }

    /// Sort rows by a comparator, keeping `row_group_keys` in lockstep.
    /// Pair-sort prevents the sidecar from desynchronizing after ORDER BY
    /// (otherwise text rendering would apply the wrong currency hint to
    /// a row).
    pub fn sort_by<F>(&mut self, mut compare: F)
    where
        F: FnMut(&Row, &Row) -> std::cmp::Ordering,
    {
        // Hard assert (not debug_assert!): the invariant is load-bearing
        // for correctness; a release-mode mismatch would silently apply
        // the wrong currency hint to rows after sort.
        assert_eq!(
            self.rows.len(),
            self.row_group_keys.len(),
            "QueryResult invariant violated: rows.len() must equal row_group_keys.len()"
        );
        let n = self.rows.len();
        let mut paired: Vec<(Row, Option<Vec<Value>>)> = std::mem::take(&mut self.rows)
            .into_iter()
            .zip(std::mem::take(&mut self.row_group_keys))
            .collect();
        paired.sort_by(|(a, _), (b, _)| compare(a, b));
        // Pre-allocate the now-empty Vecs back to known capacity to skip
        // the incremental-grow allocations during push-back.
        self.rows.reserve_exact(n);
        self.row_group_keys.reserve_exact(n);
        for (row, key) in paired {
            self.rows.push(row);
            self.row_group_keys.push(key);
        }
    }

    /// Number of rows.
    pub const fn len(&self) -> usize {
        self.rows.len()
    }

    /// Whether the result is empty.
    pub const fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }
}

/// Context for a single posting being evaluated.
#[derive(Debug)]
pub struct PostingContext<'a> {
    /// The transaction this posting belongs to.
    pub transaction: &'a Transaction,
    /// The posting index within the transaction.
    pub posting_index: usize,
    /// Cumulative running balance across all WHERE-filtered postings up to and
    /// including this one, in iteration order. This is what bean-query exposes
    /// as the `balance` column — a single Inventory that grows as the result
    /// set is built, regardless of which account each posting belongs to.
    pub balance: Option<Inventory>,
    /// Per-account running balance for this posting's account. Exposed as the
    /// `account_balance` column. Updated for every posting, independent of the
    /// WHERE filter, so it always reflects the true ledger balance for the
    /// account at this point in time.
    pub account_balance: Option<Inventory>,
    /// The directive index (for source location lookup).
    pub directive_index: Option<usize>,
}

/// Context for window function evaluation.
#[derive(Debug, Clone)]
pub struct WindowContext {
    /// Row number within the partition (1-based).
    pub row_number: usize,
    /// Rank within the partition (1-based, ties get same rank).
    pub rank: usize,
    /// Dense rank within the partition (1-based, no gaps after ties).
    pub dense_rank: usize,
}

/// Account information cached from Open/Close directives.
#[derive(Debug, Clone, Default)]
pub struct AccountInfo {
    /// Date the account was opened.
    pub open_date: Option<NaiveDate>,
    /// Date the account was closed (if any).
    pub close_date: Option<NaiveDate>,
    /// Metadata from the Open directive.
    pub open_meta: Metadata,
    /// Booking method string from the Open directive (e.g. `"AVERAGE"`), if any.
    /// Stored raw to avoid coupling the query crate to the booking-method enum;
    /// used to realize AVERAGE accounts as a single weighted-average pool.
    pub booking: Option<String>,
}

/// An in-memory table created by CREATE TABLE.
#[derive(Debug, Clone)]
pub struct Table {
    /// Column names.
    pub columns: Vec<String>,
    /// Rows of data.
    pub rows: Vec<Vec<Value>>,
}

impl Table {
    /// Create a new empty table with the given column names.
    #[allow(clippy::missing_const_for_fn)] // Vec::new() isn't const with owned columns
    pub fn new(columns: Vec<String>) -> Self {
        Self {
            columns,
            rows: Vec::new(),
        }
    }

    /// Add a row to the table.
    pub fn add_row(&mut self, row: Vec<Value>) {
        self.rows.push(row);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Verify Value enum size is reasonable after boxing heavy variants.
    /// Previously 120 bytes, now 40 bytes (67% reduction).
    #[test]
    fn test_value_size() {
        use std::mem::size_of;
        // Value should be ~40 bytes with boxed variants (vs 120 unboxed)
        assert!(
            size_of::<Value>() <= 48,
            "Value enum too large: {} bytes",
            size_of::<Value>()
        );
    }

    // ─── QueryResult parallel-vector invariant (issue #988) ───────────
    //
    // The `row_group_keys` sidecar must stay aligned with `rows` across
    // every mutation. These tests pin the contract for the helpers that
    // mutate both vectors. A failure here means future renderer logic
    // would apply the wrong currency hint to a row.

    fn make_keyed_result() -> QueryResult {
        let mut r = QueryResult::new(vec!["currency".into(), "sum".into()]);
        r.add_aggregate_row(
            vec![Value::String("USD".into()), Value::Integer(100)],
            vec![Value::String("USD".into())],
        );
        r.add_aggregate_row(
            vec![Value::String("EUR".into()), Value::Integer(50)],
            vec![Value::String("EUR".into())],
        );
        r.add_aggregate_row(
            vec![Value::String("GBP".into()), Value::Integer(75)],
            vec![Value::String("GBP".into())],
        );
        r
    }

    /// `sort_by` reorders rows AND `row_group_keys` together.
    #[test]
    fn test_sort_by_keeps_row_group_keys_in_lockstep() {
        let mut r = make_keyed_result();
        // Sort by the integer column ascending: 50 (EUR), 75 (GBP), 100 (USD).
        r.sort_by(|a, b| match (&a[1], &b[1]) {
            (Value::Integer(x), Value::Integer(y)) => x.cmp(y),
            _ => std::cmp::Ordering::Equal,
        });

        // After sort, row[0] is EUR, row[1] is GBP, row[2] is USD.
        // The sidecar MUST have followed.
        assert_eq!(r.group_key(0), Some(&[Value::String("EUR".into())][..]));
        assert_eq!(r.group_key(1), Some(&[Value::String("GBP".into())][..]));
        assert_eq!(r.group_key(2), Some(&[Value::String("USD".into())][..]));
    }

    /// `truncate` drops the same suffix from rows AND `row_group_keys`.
    #[test]
    fn test_truncate_keeps_row_group_keys_in_lockstep() {
        let mut r = make_keyed_result();
        r.truncate(2);

        assert_eq!(r.rows.len(), 2);
        assert_eq!(r.row_group_keys.len(), 2);
        // Surviving keys are the first two: USD, EUR.
        assert_eq!(r.group_key(0), Some(&[Value::String("USD".into())][..]));
        assert_eq!(r.group_key(1), Some(&[Value::String("EUR".into())][..]));
        // Out-of-range index returns None gracefully.
        assert_eq!(r.group_key(2), None);
    }

    /// Mixed aggregate / non-aggregate rows: `add_row` writes `None` to
    /// the sidecar so the invariant is preserved when the two paths
    /// interleave (e.g. a synthetic explanatory row appended after an
    /// aggregate).
    #[test]
    fn test_add_row_and_add_aggregate_row_mixed() {
        let mut r = QueryResult::new(vec!["x".into()]);
        r.add_aggregate_row(vec![Value::Integer(1)], vec![Value::String("USD".into())]);
        r.add_row(vec![Value::Integer(2)]);
        r.add_aggregate_row(vec![Value::Integer(3)], vec![Value::String("EUR".into())]);

        assert_eq!(r.rows.len(), 3);
        assert_eq!(r.row_group_keys.len(), 3);
        assert_eq!(r.group_key(0), Some(&[Value::String("USD".into())][..]));
        assert_eq!(r.group_key(1), None);
        assert_eq!(r.group_key(2), Some(&[Value::String("EUR".into())][..]));
    }

    /// Empty `group_key` arg means "no GROUP BY context" — sidecar
    /// records `None` so callers don't see a misleading `Some(vec![])`.
    #[test]
    fn test_add_aggregate_row_empty_key_records_none() {
        let mut r = QueryResult::new(vec!["count".into()]);
        // Pure aggregate (e.g. SELECT COUNT(*)) has no GROUP BY at all.
        r.add_aggregate_row(vec![Value::Integer(42)], vec![]);

        assert_eq!(r.group_key(0), None);
    }

    /// `sort_by`'s lockstep invariant is enforced by an unconditional
    /// `assert_eq!`. This test deliberately corrupts the sidecar (by
    /// pushing to `rows` without a matching push to `row_group_keys`)
    /// then calls `sort_by`, expecting a panic. Pins the safety net
    /// against accidental removal of the assert.
    #[test]
    #[should_panic(expected = "QueryResult invariant violated")]
    fn test_sort_by_panics_on_lockstep_violation() {
        let mut r = QueryResult::new(vec!["x".into()]);
        // Reach in directly to corrupt the sidecar — the only way to
        // hit the assert without going through the helpers (which are
        // designed to make it impossible). Available because tests live
        // inside `rustledger-query` and `row_group_keys` is `pub(crate)`.
        r.rows.push(vec![Value::Integer(1)]);
        // Deliberately skip pushing to `row_group_keys`.
        r.sort_by(|_, _| std::cmp::Ordering::Equal);
    }

    /// Direct test for `add_row`: the non-aggregate path records `None`
    /// in the sidecar, keeping the parallel-vector invariant. Covered
    /// indirectly by `test_add_row_and_add_aggregate_row_mixed` but
    /// pinned standalone here so the contract is unambiguous.
    #[test]
    fn test_add_row_records_none_in_sidecar() {
        let mut r = QueryResult::new(vec!["x".into()]);
        r.add_row(vec![Value::Integer(1)]);

        assert_eq!(r.rows.len(), 1);
        assert_eq!(r.row_group_keys.len(), 1);
        assert_eq!(r.group_key(0), None);
    }
}
