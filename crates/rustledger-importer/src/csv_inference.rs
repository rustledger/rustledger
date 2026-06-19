//! CSV format auto-inference.
//!
//! Given raw CSV content, detects:
//! - Delimiter (`,`, `;`, `\t`, `|`)
//! - Whether headers are present
//! - Which column is the date (and its format)
//! - Which column(s) contain amounts
//! - Which column contains the description/narration
//! - Which column contains the payee (if separate)
//!
//! This enables zero-config import for ~80% of bank CSV exports.

use format_num_pattern::Locale;

use crate::config::{ColumnSpec, CsvConfig};

/// Result of CSV format inference.
///
/// Constructed only by [`infer_csv_config`]. Marked `#[non_exhaustive]` so that
/// *future* inferred fields can be added without breaking downstream consumers
/// of `rustledger-importer`. Adding the attribute is itself a one-time breaking
/// change for any external code that built this struct with a literal or matched
/// it exhaustively (there is none in this workspace — it is only constructed
/// here and consumed by field access via [`Self::to_csv_config`]).
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct InferredCsvConfig {
    /// Detected field delimiter.
    pub delimiter: char,
    /// Whether the first row appears to be a header.
    pub has_header: bool,
    /// The date column.
    pub date_column: ColumnSpec,
    /// The detected date format (strftime-style).
    pub date_format: String,
    /// Single amount column (if amounts are in one column).
    pub amount_column: Option<ColumnSpec>,
    /// Debit column (if amounts are split debit/credit).
    pub debit_column: Option<ColumnSpec>,
    /// Credit column (if amounts are split debit/credit).
    pub credit_column: Option<ColumnSpec>,
    /// Description/narration column.
    pub narration_column: Option<ColumnSpec>,
    /// Payee column (if separate from narration).
    pub payee_column: Option<ColumnSpec>,
    /// Inferred amount locale (decimal/grouping separators). `Some(de_DE)` when
    /// the amounts look comma-decimal (e.g. `-54,23`, `2.500,00`); `None` when
    /// they look period-decimal or carry no signal (the parser defaults to
    /// POSIX). An explicit `--amount-locale` overrides this.
    pub amount_locale: Option<Locale>,
    /// Overall confidence in the inference (0.0 to 1.0).
    pub confidence: f64,
}

impl InferredCsvConfig {
    /// Convert to a [`CsvConfig`] for use with the CSV importer.
    #[must_use]
    pub fn to_csv_config(&self) -> CsvConfig {
        CsvConfig {
            date_column: self.date_column.clone(),
            date_format: self.date_format.clone(),
            narration_column: self.narration_column.clone(),
            payee_column: self.payee_column.clone(),
            amount_column: self.amount_column.clone(),
            debit_column: self.debit_column.clone(),
            credit_column: self.credit_column.clone(),
            amount_locale: self.amount_locale.or(Some(Locale::POSIX)),
            has_header: self.has_header,
            delimiter: self.delimiter,
            ..CsvConfig::default()
        }
    }
}

/// Infer the CSV format from file content.
///
/// Reads the first few rows to detect delimiter, headers, column types, and
/// date format. Returns `None` if the content doesn't look like a parseable CSV.
#[must_use]
pub fn infer_csv_config(content: &str) -> Option<InferredCsvConfig> {
    if content.trim().is_empty() {
        return None;
    }

    let delimiter = detect_delimiter(content);
    let rows = parse_rows(content, delimiter);

    if rows.len() < 2 {
        return None;
    }

    let has_header = detect_header(&rows);
    let headers: Vec<&str> = if has_header {
        rows[0].iter().map(String::as_str).collect()
    } else {
        vec![]
    };
    let data_rows: Vec<&Vec<String>> = if has_header {
        rows[1..].iter().collect()
    } else {
        rows.iter().collect()
    };

    // Sample up to 10 data rows for classification
    let sample: Vec<&Vec<String>> = data_rows.iter().take(10).copied().collect();
    if sample.is_empty() {
        return None;
    }

    let num_cols = rows[0].len();
    let mut confidence = 0.0;

    // Classify each column
    let date_col = find_date_column(&headers, &sample, num_cols);
    let date_col_idx = date_col.as_ref().map(|(i, _)| *i);
    let (amount_col, debit_col, credit_col) =
        find_amount_columns(&headers, &sample, num_cols, date_col_idx);
    let (narration_col, payee_col) = find_text_columns(
        &headers,
        num_cols,
        date_col.as_ref().map(|(i, _)| *i),
        amount_col,
        debit_col,
        credit_col,
    );

    // Build result
    let (date_column, date_format) = match date_col {
        Some((i, fmt)) => {
            confidence += 0.4;
            let col = if has_header && i < headers.len() {
                ColumnSpec::Name(headers[i].to_string())
            } else {
                ColumnSpec::Index(i)
            };
            (col, fmt)
        }
        None => return None, // Can't do anything without a date
    };

    let amount_column = amount_col.map(|i| {
        confidence += 0.3;
        if has_header && i < headers.len() {
            ColumnSpec::Name(headers[i].to_string())
        } else {
            ColumnSpec::Index(i)
        }
    });

    let debit_column = debit_col.map(|i| {
        confidence += 0.15;
        if has_header && i < headers.len() {
            ColumnSpec::Name(headers[i].to_string())
        } else {
            ColumnSpec::Index(i)
        }
    });

    let credit_column = credit_col.map(|i| {
        confidence += 0.15;
        if has_header && i < headers.len() {
            ColumnSpec::Name(headers[i].to_string())
        } else {
            ColumnSpec::Index(i)
        }
    });

    if amount_column.is_none() && debit_column.is_none() {
        return None; // Can't do anything without amounts
    }

    let narration_column = narration_col.map(|i| {
        confidence += 0.2;
        if has_header && i < headers.len() {
            ColumnSpec::Name(headers[i].to_string())
        } else {
            ColumnSpec::Index(i)
        }
    });

    let payee_column = payee_col.map(|i| {
        confidence += 0.1;
        if has_header && i < headers.len() {
            ColumnSpec::Name(headers[i].to_string())
        } else {
            ColumnSpec::Index(i)
        }
    });

    // Infer the decimal separator from the amount-bearing columns so that
    // comma-decimal exports (e.g. "-54,23", "2.500,00") parse correctly under
    // --auto instead of being read with a POSIX (period-decimal) locale.
    let amount_locale = infer_amount_locale(
        &sample,
        [amount_col, debit_col, credit_col].into_iter().flatten(),
    );

    Some(InferredCsvConfig {
        delimiter,
        has_header,
        date_column,
        date_format,
        amount_column,
        debit_column,
        credit_column,
        narration_column,
        payee_column,
        amount_locale,
        confidence: f64::min(confidence, 1.0),
    })
}

/// Infer an amount [`Locale`] from the sampled values in the amount-bearing
/// columns. Returns `Some(de_DE)` when the values look comma-decimal, else
/// `None` (callers default to POSIX).
///
/// When a value has both `.` and `,`, the rightmost is taken as the decimal
/// separator (`2.500,00` -> comma-decimal, `1,234.56` -> period-decimal). A
/// lone comma counts as a decimal separator only when it is immediately
/// followed by 1-2 digits, so a thousands group like `1,234` stays
/// period-style while a decorated amount like `-54,23€` is still comma-decimal.
/// Each sampled cell across the amount-bearing columns votes; the majority wins.
///
/// # Limitation
///
/// Inference needs a comma somewhere in the sample. A comma-decimal export
/// whose sampled amounts are all period-grouped integers (`1.234` meaning 1234)
/// carries no distinguishing signal from period-decimal `1.234` (= 1.234), so
/// it returns `None` and the amounts are read as POSIX. There is no local way to
/// disambiguate the two; pass `--amount-locale de_DE` for such files.
fn infer_amount_locale(
    sample: &[&Vec<String>],
    cols: impl Iterator<Item = usize>,
) -> Option<Locale> {
    let cols: Vec<usize> = cols.collect();
    let mut comma_decimal = 0usize;
    let mut period_decimal = 0usize;
    for row in sample {
        for &col in &cols {
            let Some(cell) = row.get(col) else { continue };
            let v = cell.trim();
            if v.is_empty() {
                continue;
            }
            match (v.rfind(','), v.rfind('.')) {
                (Some(comma), Some(dot)) => {
                    if comma > dot {
                        comma_decimal += 1;
                    } else {
                        period_decimal += 1;
                    }
                }
                (Some(comma), None) => {
                    // Count the digits immediately after the comma, ignoring any
                    // trailing currency symbol / suffix (looks_like_number admits
                    // `$ € £ ¥` etc.), so `-54,23€` stays comma-decimal.
                    let trailing_digits = v[comma + 1..]
                        .chars()
                        .take_while(char::is_ascii_digit)
                        .count();
                    if (1..=2).contains(&trailing_digits) {
                        comma_decimal += 1;
                    } else {
                        period_decimal += 1;
                    }
                }
                (None, Some(_)) => period_decimal += 1,
                (None, None) => {}
            }
        }
    }
    (comma_decimal > period_decimal).then_some(Locale::de_DE)
}

// ============================================================================
// Detection heuristics
// ============================================================================

/// Detect the most likely delimiter by trying each candidate and picking
/// the one that produces the most consistent column count.
fn detect_delimiter(content: &str) -> char {
    let candidates = [',', ';', '\t', '|'];
    let mut best_delimiter = ',';
    let mut best_score = f64::MAX;

    for &delim in &candidates {
        let counts: Vec<usize> = content
            .lines()
            .take(10)
            .filter(|l| !l.trim().is_empty())
            .map(|line| line.matches(delim).count())
            .collect();

        if counts.is_empty() || counts.iter().all(|&c| c == 0) {
            continue;
        }

        // Score = variance of column counts (lower is better)
        let mean = counts.iter().sum::<usize>() as f64 / counts.len() as f64;
        let variance = counts
            .iter()
            .map(|&c| (c as f64 - mean).powi(2))
            .sum::<f64>()
            / counts.len() as f64;

        // Prefer delimiters that produce more columns (break ties)
        let score = mean.mul_add(-0.01, variance);

        if score < best_score {
            best_score = score;
            best_delimiter = delim;
        }
    }

    best_delimiter
}

/// Parse content into rows of fields using the given delimiter.
fn parse_rows(content: &str, delimiter: char) -> Vec<Vec<String>> {
    let mut reader = csv::ReaderBuilder::new()
        .has_headers(false)
        .delimiter(delimiter as u8)
        .from_reader(content.as_bytes());

    reader
        .records()
        .take(20) // Only need first ~20 rows
        .filter_map(Result::ok)
        .map(|record| record.iter().map(String::from).collect())
        .collect()
}

/// Detect if the first row is a header by checking if it contains
/// common header keywords and/or looks different from data rows.
fn detect_header(rows: &[Vec<String>]) -> bool {
    if rows.is_empty() {
        return false;
    }

    let first_row = &rows[0];

    // Check for common header keywords
    let keywords = [
        "date",
        "amount",
        "description",
        "narration",
        "memo",
        "payee",
        "debit",
        "credit",
        "balance",
        "reference",
        "transaction",
        "type",
        "category",
        "account",
        "details",
        "particulars",
        "value",
        "posting",
        "merchant",
        "name",
        "note",
        "status",
        "check",
        "num",
        "ref",
    ];

    let keyword_matches = first_row
        .iter()
        .filter(|cell| {
            let lower = cell.to_lowercase();
            keywords.iter().any(|kw| lower.contains(kw))
        })
        .count();

    // If 2+ cells match keywords, it's likely a header
    if keyword_matches >= 2 {
        return true;
    }

    // Check if first row has no numbers but data rows do
    let first_has_numbers = first_row.iter().any(|cell| looks_like_number(cell));
    let second_has_numbers = rows
        .get(1)
        .is_some_and(|row| row.iter().any(|cell| looks_like_number(cell)));

    if !first_has_numbers && second_has_numbers {
        return true;
    }

    false
}

/// Common date formats to try, ordered by prevalence.
const DATE_FORMATS: &[&str] = &[
    "%Y-%m-%d",  // 2024-01-15
    "%m/%d/%Y",  // 01/15/2024
    "%d/%m/%Y",  // 15/01/2024
    "%Y/%m/%d",  // 2024/01/15
    "%m-%d-%Y",  // 01-15-2024
    "%d-%m-%Y",  // 15-01-2024
    "%d.%m.%Y",  // 15.01.2024
    "%m.%d.%Y",  // 01.15.2024
    "%Y.%m.%d",  // 2024.01.15
    "%b %d, %Y", // Jan 15, 2024
    "%d %b %Y",  // 15 Jan 2024
    "%B %d, %Y", // January 15, 2024
    "%d %B %Y",  // 15 January 2024
    "%m/%d/%y",  // 01/15/24
    "%d/%m/%y",  // 15/01/24
];

/// Whole-word keyword match against a (lowercased) CSV header.
///
/// A keyword matches only when it appears delimited by non-alphanumeric
/// characters or string boundaries, so short tokens like "in"/"out" no longer
/// match inside "running balance", "routing number", "beginning balance", etc.
/// (which made `--auto` steal a running-balance column as the credit/amount).
/// Multi-word keywords such as "transaction date" are matched as phrases.
fn header_matches(header_lower: &str, keywords: &[&str]) -> bool {
    keywords.iter().any(|kw| {
        header_lower.match_indices(kw).any(|(start, matched)| {
            let before = header_lower[..start].chars().next_back();
            let after = header_lower[start + matched.len()..].chars().next();
            before.is_none_or(|c| !c.is_alphanumeric())
                && after.is_none_or(|c| !c.is_alphanumeric())
        })
    })
}

/// Find the date column and its format.
fn find_date_column(
    headers: &[&str],
    sample: &[&Vec<String>],
    num_cols: usize,
) -> Option<(usize, String)> {
    // First, check headers for date keywords
    let date_keywords = [
        "date",
        "posted",
        "transaction date",
        "value date",
        "booking",
    ];
    let mut candidates: Vec<usize> = Vec::new();

    for (i, header) in headers.iter().enumerate() {
        let lower = header.to_lowercase();
        if header_matches(&lower, &date_keywords) {
            candidates.push(i);
        }
    }

    // If no header matches, try all columns
    if candidates.is_empty() {
        candidates = (0..num_cols).collect();
    }

    // Try each candidate column with each date format
    for &col_idx in &candidates {
        let values: Vec<&str> = sample
            .iter()
            .filter_map(|row| row.get(col_idx).map(String::as_str))
            .filter(|v| !v.trim().is_empty())
            .collect();

        if values.is_empty() {
            continue;
        }

        for &fmt in DATE_FORMATS {
            let parse_count = values
                .iter()
                .filter(|v| jiff::fmt::strtime::parse(fmt, v.trim()).is_ok())
                .count();

            // Require at least 80% of non-empty values to parse
            if parse_count > 0 && parse_count * 5 >= values.len() * 4 {
                return Some((col_idx, fmt.to_string()));
            }
        }
    }

    None
}

/// Find amount column(s). Returns `(single_amount, debit, credit)`.
///
/// `date_col` is the already-detected date column index, which is skipped
/// during the fallback numeric-column scan (dates can look numeric).
fn find_amount_columns(
    headers: &[&str],
    sample: &[&Vec<String>],
    num_cols: usize,
    date_col: Option<usize>,
) -> (Option<usize>, Option<usize>, Option<usize>) {
    let amount_keywords = ["amount", "sum", "value", "total"];
    let debit_keywords = ["debit", "withdrawal", "out", "charge"];
    let credit_keywords = ["credit", "deposit", "in", "payment"];

    let mut amount_col = None;
    let mut debit_col = None;
    let mut credit_col = None;

    // Check headers first
    for (i, header) in headers.iter().enumerate() {
        let lower = header.to_lowercase();
        if header_matches(&lower, &debit_keywords) {
            debit_col = Some(i);
        } else if header_matches(&lower, &credit_keywords) {
            credit_col = Some(i);
        } else if header_matches(&lower, &amount_keywords) {
            amount_col = Some(i);
        }
    }

    // If we found debit/credit pair, prefer that
    if debit_col.is_some() && credit_col.is_some() {
        return (None, debit_col, credit_col);
    }

    // If we found a single amount column by header, verify it has numbers
    if let Some(col) = amount_col {
        let has_numbers = sample
            .iter()
            .filter_map(|row| row.get(col))
            .any(|v| looks_like_number(v));
        if has_numbers {
            return (Some(col), None, None);
        }
    }

    // Fall back to finding numeric columns
    for col_idx in 0..num_cols {
        // Skip the date column — dates can look numeric
        if date_col == Some(col_idx) {
            continue;
        }

        let values: Vec<&str> = sample
            .iter()
            .filter_map(|row| row.get(col_idx).map(String::as_str))
            .filter(|v| !v.trim().is_empty())
            .collect();

        if values.is_empty() {
            continue;
        }

        let number_count = values.iter().filter(|v| looks_like_number(v)).count();

        // If 80%+ look like numbers, this is probably an amount column
        if number_count * 5 >= values.len() * 4 && amount_col.is_none() {
            amount_col = Some(col_idx);
        }
    }

    (amount_col, None, None)
}

/// Find text columns for narration and payee.
fn find_text_columns(
    headers: &[&str],
    num_cols: usize,
    date_col: Option<usize>,
    amount_col: Option<usize>,
    debit_col: Option<usize>,
    credit_col: Option<usize>,
) -> (Option<usize>, Option<usize>) {
    let narration_keywords = [
        "description",
        "narration",
        "memo",
        "details",
        "particulars",
        "reference",
        "transaction",
        "text",
    ];
    let payee_keywords = [
        "payee",
        "merchant",
        "name",
        "vendor",
        "beneficiary",
        "recipient",
    ];

    let used_cols: Vec<usize> = [date_col, amount_col, debit_col, credit_col]
        .iter()
        .filter_map(|c| *c)
        .collect();

    let mut narration_col = None;
    let mut payee_col = None;

    // Check headers
    for (i, header) in headers.iter().enumerate() {
        if used_cols.contains(&i) {
            continue;
        }
        let lower = header.to_lowercase();
        if header_matches(&lower, &payee_keywords) && payee_col.is_none() {
            payee_col = Some(i);
        } else if header_matches(&lower, &narration_keywords) && narration_col.is_none() {
            narration_col = Some(i);
        }
    }

    // If no narration found by header, pick the first unused text column
    if narration_col.is_none() {
        for i in 0..num_cols {
            if !used_cols.contains(&i) && payee_col != Some(i) {
                narration_col = Some(i);
                break;
            }
        }
    }

    (narration_col, payee_col)
}

/// Check if a string looks like a number (for amount/date detection).
fn looks_like_number(s: &str) -> bool {
    let trimmed = s.trim();
    if trimmed.is_empty() {
        return false;
    }
    // Strip currency symbols and parentheses
    let cleaned: String = trimmed
        .chars()
        .filter(|c| !matches!(c, '$' | '€' | '£' | '¥' | '(' | ')'))
        .collect();
    let cleaned = cleaned.trim();
    if cleaned.is_empty() {
        return false;
    }
    // Check if it's a number with optional sign, commas, and one decimal point
    let mut has_digit = false;
    let mut dot_count = 0;
    for (i, c) in cleaned.chars().enumerate() {
        match c {
            '0'..='9' => has_digit = true,
            '.' => dot_count += 1,
            ',' => {}
            '-' | '+' if i == 0 => {}
            _ => return false,
        }
    }
    has_digit && dot_count <= 1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detect_comma_delimiter() {
        let csv = "Date,Amount,Description\n2024-01-15,-50.00,Coffee\n2024-01-16,-12.00,Lunch\n";
        assert_eq!(detect_delimiter(csv), ',');
    }

    #[test]
    fn detect_semicolon_delimiter() {
        let csv = "Date;Amount;Description\n2024-01-15;-50.00;Coffee\n2024-01-16;-12.00;Lunch\n";
        assert_eq!(detect_delimiter(csv), ';');
    }

    #[test]
    fn detect_tab_delimiter() {
        let csv =
            "Date\tAmount\tDescription\n2024-01-15\t-50.00\tCoffee\n2024-01-16\t-12.00\tLunch\n";
        assert_eq!(detect_delimiter(csv), '\t');
    }

    #[test]
    fn detect_header_with_keywords() {
        let rows = vec![
            vec![
                "Date".to_string(),
                "Amount".to_string(),
                "Description".to_string(),
            ],
            vec![
                "2024-01-15".to_string(),
                "-50.00".to_string(),
                "Coffee".to_string(),
            ],
        ];
        assert!(detect_header(&rows));
    }

    #[test]
    fn detect_no_header() {
        let rows = vec![
            vec![
                "2024-01-15".to_string(),
                "-50.00".to_string(),
                "Coffee".to_string(),
            ],
            vec![
                "2024-01-16".to_string(),
                "-12.00".to_string(),
                "Lunch".to_string(),
            ],
        ];
        assert!(!detect_header(&rows));
    }

    #[test]
    fn looks_like_number_positive() {
        assert!(looks_like_number("50.00"));
        assert!(looks_like_number("-50.00"));
        assert!(looks_like_number("+50.00"));
        assert!(looks_like_number("1,234.56"));
        assert!(looks_like_number("$50.00"));
        assert!(looks_like_number("(50.00)"));
    }

    #[test]
    fn looks_like_number_negative() {
        assert!(!looks_like_number("Coffee"));
        assert!(!looks_like_number("2024-01-15"));
        assert!(!looks_like_number(""));
        assert!(!looks_like_number("ABC123"));
    }

    #[test]
    fn infer_simple_csv() {
        let csv = "\
Date,Description,Amount
2024-01-15,Coffee shop,-5.50
2024-01-16,Grocery store,-42.00
2024-01-17,Salary,3000.00
";
        let config = infer_csv_config(csv).expect("should infer config");
        assert_eq!(config.delimiter, ',');
        assert!(config.has_header);
        assert_eq!(config.date_format, "%Y-%m-%d");
        assert!(config.amount_column.is_some());
        assert!(config.narration_column.is_some());
        assert!(config.confidence > 0.5);
    }

    #[test]
    fn infer_us_date_format() {
        let csv = "\
Date,Description,Amount
01/15/2024,Coffee shop,-5.50
01/16/2024,Grocery store,-42.00
";
        let config = infer_csv_config(csv).expect("should infer config");
        assert_eq!(config.date_format, "%m/%d/%Y");
    }

    #[test]
    fn infer_semicolon_csv() {
        let csv = "\
Date;Description;Amount
2024-01-15;Coffee shop;-5.50
2024-01-16;Grocery store;-42.00
";
        let config = infer_csv_config(csv).expect("should infer config");
        assert_eq!(config.delimiter, ';');
    }

    #[test]
    fn infer_debit_credit_columns() {
        let csv = "\
Date,Description,Debit,Credit
2024-01-15,Coffee shop,5.50,
2024-01-16,Salary,,3000.00
";
        let config = infer_csv_config(csv).expect("should infer config");
        assert!(config.debit_column.is_some());
        assert!(config.credit_column.is_some());
        assert!(config.amount_column.is_none());
    }

    #[test]
    fn infer_does_not_steal_running_balance_as_credit() {
        // Regression: "Running Balance" must not be classified as the credit
        // column. The word "running" contains the letters "in", which the old
        // substring match treated as the `in` credit keyword, stealing the
        // running balance as the amount. With Debit + Credit + Running Balance,
        // the pair must be the real Debit/Credit columns.
        let csv = "\
Date,Description,Debit,Credit,Running Balance
2024-01-15,Deposit,,100.00,1100.00
2024-01-16,Withdraw,40.00,,1060.00
";
        let config = infer_csv_config(csv).expect("should infer config");
        match &config.debit_column {
            Some(ColumnSpec::Name(n)) => assert_eq!(n, "Debit"),
            other => panic!("debit column should be 'Debit', got {other:?}"),
        }
        match &config.credit_column {
            Some(ColumnSpec::Name(n)) => assert_eq!(n, "Credit"),
            other => panic!("credit column should be 'Credit', got {other:?}"),
        }
    }

    #[test]
    fn infer_with_payee_column() {
        let csv = "\
Date,Payee,Description,Amount
2024-01-15,Starbucks,Morning coffee,-5.50
2024-01-16,Whole Foods,Groceries,-42.00
";
        let config = infer_csv_config(csv).expect("should infer config");
        assert!(config.payee_column.is_some());
        assert!(config.narration_column.is_some());
    }

    #[test]
    fn infer_comma_decimal_locale() {
        // Comma-decimal exports (-54,23 ; 2.500,00) must infer a comma-decimal
        // locale so --auto parses them correctly instead of as POSIX (which
        // read -54,23 as -5423 and 2.500,00 as 2.50000).
        let csv = "\
Date;Description;Amount
2024-01-15;Coffee;-54,23
2024-01-16;Salary;2.500,00
";
        let config = infer_csv_config(csv).expect("should infer config");
        assert!(
            config.amount_locale.is_some(),
            "expected a comma-decimal locale, got {:?}",
            config.amount_locale
        );
    }

    #[test]
    fn infer_period_decimal_locale_is_none() {
        // Period-decimal amounts must not be mistaken for European.
        let csv = "\
Date,Description,Amount
2024-01-15,Coffee,-54.23
2024-01-16,Salary,2500.00
";
        let config = infer_csv_config(csv).expect("should infer config");
        assert!(config.amount_locale.is_none());
    }

    #[test]
    fn infer_thousands_comma_not_mistaken_for_decimal() {
        // A lone comma with 3 trailing digits is a thousands group, not a
        // decimal separator, so it must stay period-style.
        let csv = "\
Date;Description;Amount
2024-01-15;Coffee;1,234
2024-01-16;Salary;5,678
";
        let config = infer_csv_config(csv).expect("should infer config");
        assert!(config.amount_locale.is_none());
    }

    #[test]
    fn infer_comma_decimal_with_currency_suffix() {
        // A trailing currency symbol must not defeat comma-decimal inference:
        // the digit count after the comma is what matters, not the byte length.
        let csv = "\
Date;Description;Amount
2024-01-15;Coffee;-54,23€
2024-01-16;Salary;1.500,00€
";
        let config = infer_csv_config(csv).expect("should infer config");
        assert!(
            config.amount_locale.is_some(),
            "currency-decorated comma-decimal should infer European, got {:?}",
            config.amount_locale
        );
    }

    #[test]
    fn infer_empty_content_returns_none() {
        assert!(infer_csv_config("").is_none());
        assert!(infer_csv_config("   \n  \n").is_none());
    }

    #[test]
    fn infer_single_row_returns_none() {
        assert!(infer_csv_config("Date,Amount\n").is_none());
    }

    #[test]
    fn inferred_to_csv_config() {
        let csv = "\
Date,Description,Amount
2024-01-15,Coffee,-5.50
2024-01-16,Lunch,-12.00
";
        let inferred = infer_csv_config(csv).expect("should infer");
        let config = inferred.to_csv_config();
        assert_eq!(config.delimiter, ',');
        assert!(config.has_header);
        assert_eq!(config.date_format, "%Y-%m-%d");
    }
}
