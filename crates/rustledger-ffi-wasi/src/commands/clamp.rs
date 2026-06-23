//! Clamp and filter functions for entries.

use rustledger_core::NaiveDate;
use serde::Serialize;

/// Result of a clamp operation.
#[derive(Serialize)]
pub struct ClampResult {
    pub entries: Vec<serde_json::Value>,
}

/// Result of a filter operation.
#[derive(Serialize)]
pub struct FilterResult {
    pub entries: Vec<serde_json::Value>,
}

/// Filter entries by date range (simple filtering, no summarization).
///
/// Rules:
/// - `commodity`: Always excluded
/// - `open`: Included if date < `end` (still active)
/// - `close`: Included if date >= `begin`
/// - Others: Included if `begin` <= date < `end`
pub fn filter_entries(
    entries: Vec<serde_json::Value>,
    begin: NaiveDate,
    end: NaiveDate,
) -> FilterResult {
    let filtered = entries
        .into_iter()
        .filter(|entry| {
            let entry_type = entry.get("type").and_then(|t| t.as_str()).unwrap_or("");
            let date_str = entry.get("date").and_then(|d| d.as_str()).unwrap_or("");

            let Ok(entry_date) = date_str.parse::<NaiveDate>() else {
                // Drop entries without valid dates (consistent with clamp_entries)
                return false;
            };

            match entry_type {
                "commodity" => false,
                "open" => entry_date < end,
                "close" => entry_date >= begin,
                _ => entry_date >= begin && entry_date < end,
            }
        })
        .collect();

    FilterResult { entries: filtered }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_entry(entry_type: &str, date: &str) -> serde_json::Value {
        serde_json::json!({
            "type": entry_type,
            "date": date,
            "meta": {"filename": "test.beancount", "lineno": 1, "hash": "abc123"}
        })
    }

    #[allow(clippy::needless_pass_by_value)] // test helper; ergonomic with `vec![]` literals
    fn make_transaction(date: &str, postings: Vec<serde_json::Value>) -> serde_json::Value {
        serde_json::json!({
            "type": "transaction",
            "date": date,
            "flag": "*",
            "payee": "Test",
            "narration": "Test transaction",
            "postings": postings,
            "meta": {"filename": "test.beancount", "lineno": 1, "hash": format!("txn-{date}")}
        })
    }

    fn make_posting(account: &str, number: &str, currency: &str) -> serde_json::Value {
        serde_json::json!({
            "account": account,
            "units": {"number": number, "currency": currency}
        })
    }

    // ==========================================================================
    // filter_entries tests
    // ==========================================================================

    #[test]
    fn test_filter_entries_basic() {
        let entries = vec![
            make_entry("open", "2024-01-01"),
            make_entry("transaction", "2024-01-15"),
            make_entry("transaction", "2024-02-15"),
            make_entry("close", "2024-01-05"), // Before begin, should be excluded
        ];

        let begin = rustledger_core::naive_date(2024, 1, 10).unwrap();
        let end = rustledger_core::naive_date(2024, 2, 20).unwrap();

        let result = filter_entries(entries, begin, end);

        // Should include: open (before end), txn on 1/15, txn on 2/15
        // Should exclude: close (before begin)
        assert_eq!(result.entries.len(), 3);
    }

    #[test]
    fn test_filter_entries_excludes_commodity() {
        let entries = vec![
            make_entry("commodity", "2024-01-15"),
            make_entry("transaction", "2024-01-15"),
        ];

        let begin = rustledger_core::naive_date(2024, 1, 1).unwrap();
        let end = rustledger_core::naive_date(2024, 12, 31).unwrap();

        let result = filter_entries(entries, begin, end);

        assert_eq!(result.entries.len(), 1);
        assert_eq!(result.entries[0]["type"], "transaction");
    }

    #[test]
    fn test_filter_entries_open_before_end() {
        let entries = vec![
            make_entry("open", "2024-01-01"),
            make_entry("open", "2024-06-01"),
        ];

        let begin = rustledger_core::naive_date(2024, 3, 1).unwrap();
        let end = rustledger_core::naive_date(2024, 4, 1).unwrap();

        let result = filter_entries(entries, begin, end);

        // Open on 1/1 included (date < end)
        // Open on 6/1 excluded (date >= end)
        assert_eq!(result.entries.len(), 1);
        assert_eq!(result.entries[0]["date"], "2024-01-01");
    }

    #[test]
    fn test_filter_entries_close_after_begin() {
        let entries = vec![
            make_entry("close", "2024-01-01"),
            make_entry("close", "2024-06-01"),
        ];

        let begin = rustledger_core::naive_date(2024, 3, 1).unwrap();
        let end = rustledger_core::naive_date(2024, 12, 31).unwrap();

        let result = filter_entries(entries, begin, end);

        // Close on 1/1 excluded (date < begin)
        // Close on 6/1 included (date >= begin)
        assert_eq!(result.entries.len(), 1);
        assert_eq!(result.entries[0]["date"], "2024-06-01");
    }

    #[test]
    fn test_filter_entries_drops_invalid_dates() {
        let entries = vec![
            make_entry("transaction", "2024-01-15"),
            serde_json::json!({"type": "transaction", "date": "invalid"}),
            serde_json::json!({"type": "transaction"}), // no date
        ];

        let begin = rustledger_core::naive_date(2024, 1, 1).unwrap();
        let end = rustledger_core::naive_date(2024, 12, 31).unwrap();

        let result = filter_entries(entries, begin, end);

        // Only the valid date entry should be included
        assert_eq!(result.entries.len(), 1);
    }
}
