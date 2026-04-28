//! Types used by the BQL query executor.

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
pub fn hash_row(row: &Row) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    let mut hasher = DefaultHasher::new();
    for value in row {
        value.hash_value(&mut hasher);
    }
    hasher.finish()
}

/// Compute a hash for a single value (for PIVOT lookups).
pub fn hash_single_value(value: &Value) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    let mut hasher = DefaultHasher::new();
    value.hash_value(&mut hasher);
    hasher.finish()
}

/// Query result containing column names and rows.
#[derive(Debug, Clone)]
pub struct QueryResult {
    /// Column names.
    pub columns: Vec<String>,
    /// Result rows.
    pub rows: Vec<Row>,
}

impl QueryResult {
    /// Create a new empty result.
    pub const fn new(columns: Vec<String>) -> Self {
        Self {
            columns,
            rows: Vec::new(),
        }
    }

    /// Add a row to the result.
    pub fn add_row(&mut self, row: Row) {
        self.rows.push(row);
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
#[derive(Debug, Clone)]
pub struct AccountInfo {
    /// Date the account was opened.
    pub open_date: Option<NaiveDate>,
    /// Date the account was closed (if any).
    pub close_date: Option<NaiveDate>,
    /// Metadata from the Open directive.
    pub open_meta: Metadata,
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
}
