//! BQL query completion engine.
//!
//! Provides context-aware completions for the BQL query language,
//! suitable for IDE integration, CLI autocomplete, or WASM playgrounds.
//!
//! # Example
//!
//! ```
//! use rustledger_query::completions::{complete, Completion};
//!
//! let completions = complete("SELECT ", 7);
//! assert!(completions.completions.iter().any(|c| c.text == "account"));
//! ```

/// A completion suggestion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Completion {
    /// The completion text to insert.
    pub text: String,
    /// Category: keyword, function, column, operator, literal.
    pub category: CompletionCategory,
    /// Optional description/documentation.
    pub description: Option<String>,
}

/// Category of completion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompletionCategory {
    /// SQL keyword (SELECT, WHERE, etc.).
    Keyword,
    /// Aggregate or scalar function.
    Function,
    /// Column name.
    Column,
    /// Operator (+, -, =, etc.).
    Operator,
    /// Literal value.
    Literal,
}

impl CompletionCategory {
    /// Returns the category as a string for serialization.
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::Keyword => "keyword",
            Self::Function => "function",
            Self::Column => "column",
            Self::Operator => "operator",
            Self::Literal => "literal",
        }
    }
}

/// Result of a completion request.
#[derive(Debug, Clone)]
pub struct CompletionResult {
    /// List of completions.
    pub completions: Vec<Completion>,
    /// Current parsing context (for debugging).
    pub context: BqlContext,
}

/// BQL parsing context state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BqlContext {
    /// At the start, expecting a statement keyword.
    Start,
    /// After SELECT, expecting columns/expressions.
    AfterSelect,
    /// After SELECT columns, could have FROM, WHERE, GROUP BY, etc.
    AfterSelectTargets,
    /// After FROM keyword.
    AfterFrom,
    /// After FROM clause modifiers (OPEN ON, CLOSE ON, CLEAR).
    AfterFromModifiers,
    /// After WHERE keyword, expecting expression.
    AfterWhere,
    /// Inside WHERE expression.
    InWhereExpr,
    /// After GROUP keyword, expecting BY.
    AfterGroup,
    /// After GROUP BY, expecting columns.
    AfterGroupBy,
    /// After ORDER keyword, expecting BY.
    AfterOrder,
    /// After ORDER BY, expecting columns.
    AfterOrderBy,
    /// After LIMIT keyword, expecting number.
    AfterLimit,
    /// After JOURNAL keyword.
    AfterJournal,
    /// After BALANCES keyword.
    AfterBalances,
    /// After PRINT keyword.
    AfterPrint,
    /// Inside a function call, after opening paren.
    InFunction(String),
    /// After a comparison operator, expecting value.
    AfterOperator,
    /// After AS keyword, expecting alias.
    AfterAs,
    /// Inside a string literal.
    InString,
}

/// Get BQL query completions at cursor position.
///
/// Returns context-aware completions for the BQL query language.
///
/// # Arguments
///
/// * `partial_query` - The query text so far
/// * `cursor_pos` - Byte offset of cursor position
///
/// # Example
///
/// ```
/// use rustledger_query::completions::complete;
///
/// let result = complete("SELECT ", 7);
/// assert!(!result.completions.is_empty());
/// ```
#[must_use]
pub fn complete(partial_query: &str, cursor_pos: usize) -> CompletionResult {
    // Get the text up to cursor
    let text = if cursor_pos <= partial_query.len() {
        &partial_query[..cursor_pos]
    } else {
        partial_query
    };

    // Tokenize (simple whitespace/punctuation split)
    let tokens = tokenize_bql(text);
    let context = determine_context(&tokens);
    let completions = get_completions_for_context(&context);

    CompletionResult {
        completions,
        context,
    }
}

/// Simple tokenizer for BQL.
fn tokenize_bql(text: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut in_string = false;
    let mut chars = text.chars().peekable();

    while let Some(c) = chars.next() {
        if in_string {
            current.push(c);
            if c == '"' {
                tokens.push(current.clone());
                current.clear();
                in_string = false;
            }
        } else if c == '"' {
            if !current.is_empty() {
                tokens.push(current.clone());
                current.clear();
            }
            current.push(c);
            in_string = true;
        } else if c.is_whitespace() {
            if !current.is_empty() {
                tokens.push(current.clone());
                current.clear();
            }
        } else if "(),*+-/=<>!~".contains(c) {
            if !current.is_empty() {
                tokens.push(current.clone());
                current.clear();
            }
            // Handle multi-char operators (!=, <=, >=)
            if (c == '!' || c == '<' || c == '>') && chars.peek() == Some(&'=') {
                // Safety: we just checked peek() == Some(&'='), so next() is guaranteed
                if let Some(next_char) = chars.next() {
                    tokens.push(format!("{c}{next_char}"));
                }
            } else {
                tokens.push(c.to_string());
            }
        } else {
            current.push(c);
        }
    }

    if !current.is_empty() {
        tokens.push(current);
    }

    tokens
}

/// Determine the current context from tokens.
fn determine_context(tokens: &[String]) -> BqlContext {
    if tokens.is_empty() {
        return BqlContext::Start;
    }

    let upper_tokens: Vec<String> = tokens.iter().map(|t| t.to_uppercase()).collect();

    // Check for incomplete string
    if let Some(last) = tokens.last() {
        if last.starts_with('"') && !last.ends_with('"') {
            return BqlContext::InString;
        }
    }

    // Find the main statement type
    let first = upper_tokens.first().map_or("", String::as_str);

    match first {
        "SELECT" => determine_select_context(&upper_tokens),
        "JOURNAL" => BqlContext::AfterJournal,
        "BALANCES" => BqlContext::AfterBalances,
        "PRINT" => BqlContext::AfterPrint,
        _ => BqlContext::Start,
    }
}

/// Determine context within a SELECT statement.
fn determine_select_context(tokens: &[String]) -> BqlContext {
    // Find positions of key clauses
    let mut from_pos = None;
    let mut where_pos = None;
    let mut group_pos = None;
    let mut order_pos = None;
    let mut limit_pos = None;
    let mut last_as_pos = None;

    for (i, token) in tokens.iter().enumerate() {
        match token.as_str() {
            "FROM" => from_pos = Some(i),
            "WHERE" => where_pos = Some(i),
            "GROUP" => group_pos = Some(i),
            "ORDER" => order_pos = Some(i),
            "LIMIT" => limit_pos = Some(i),
            "AS" => last_as_pos = Some(i),
            _ => {}
        }
    }

    let last_idx = tokens.len() - 1;
    let last = tokens.last().map_or("", String::as_str);

    // Check for AS context
    if last == "AS" || last_as_pos == Some(last_idx) {
        return BqlContext::AfterAs;
    }

    // Determine context based on last keyword position
    if let Some(pos) = limit_pos {
        if last_idx == pos {
            return BqlContext::AfterLimit;
        }
    }

    if let Some(pos) = order_pos {
        if last_idx == pos {
            return BqlContext::AfterOrder;
        }
        if last_idx > pos {
            if tokens.get(pos + 1).map(String::as_str) == Some("BY") {
                return BqlContext::AfterOrderBy;
            }
            return BqlContext::AfterOrder;
        }
    }

    if let Some(pos) = group_pos {
        if last_idx == pos {
            return BqlContext::AfterGroup;
        }
        if last_idx > pos {
            if tokens.get(pos + 1).map(String::as_str) == Some("BY") {
                return BqlContext::AfterGroupBy;
            }
            return BqlContext::AfterGroup;
        }
    }

    if let Some(pos) = where_pos {
        if last_idx == pos {
            return BqlContext::AfterWhere;
        }
        // Check if last token is an operator
        if [
            "=", "!=", "<", "<=", ">", ">=", "~", "AND", "OR", "NOT", "IN",
        ]
        .contains(&last)
        {
            return BqlContext::AfterOperator;
        }
        return BqlContext::InWhereExpr;
    }

    if let Some(pos) = from_pos {
        if last_idx == pos {
            return BqlContext::AfterFrom;
        }
        // Check for FROM modifiers
        if ["OPEN", "CLOSE", "CLEAR", "ON"].contains(&last) {
            return BqlContext::AfterFromModifiers;
        }
        return BqlContext::AfterFromModifiers;
    }

    // We're still in SELECT targets
    if last_idx == 0 {
        return BqlContext::AfterSelect;
    }

    // Check if we just finished a function call or have comma
    if last == "," || last == "(" {
        return BqlContext::AfterSelect;
    }

    BqlContext::AfterSelectTargets
}

/// Get completions for the given context.
fn get_completions_for_context(context: &BqlContext) -> Vec<Completion> {
    match context {
        BqlContext::Start => vec![
            keyword("SELECT", Some("Query with filtering and aggregation")),
            keyword("BALANCES", Some("Show account balances")),
            keyword("JOURNAL", Some("Show account journal")),
            keyword("PRINT", Some("Print transactions")),
        ],

        BqlContext::AfterSelect => {
            let mut completions = vec![
                keyword("DISTINCT", Some("Remove duplicate rows")),
                keyword("*", Some("Select all columns")),
            ];
            completions.extend(column_completions());
            completions.extend(function_completions());
            completions
        }

        BqlContext::AfterSelectTargets => vec![
            keyword("FROM", Some("Specify data source")),
            keyword("WHERE", Some("Filter results")),
            keyword("GROUP BY", Some("Group results")),
            keyword("ORDER BY", Some("Sort results")),
            keyword("LIMIT", Some("Limit result count")),
            keyword("FLATTEN", Some("Expand inventory rows")),
            keyword("AS", Some("Alias column")),
            operator(",", Some("Add another column")),
        ],

        BqlContext::AfterFrom => vec![
            keyword("OPEN ON", Some("Summarize entries before date")),
            keyword("CLOSE ON", Some("Truncate entries after date")),
            keyword("CLEAR", Some("Transfer income/expense to equity")),
            keyword("WHERE", Some("Filter results")),
            keyword("GROUP BY", Some("Group results")),
            keyword("ORDER BY", Some("Sort results")),
        ],

        BqlContext::AfterFromModifiers => vec![
            keyword("WHERE", Some("Filter results")),
            keyword("GROUP BY", Some("Group results")),
            keyword("ORDER BY", Some("Sort results")),
            keyword("LIMIT", Some("Limit result count")),
            keyword("FLATTEN", Some("Expand inventory rows")),
        ],

        BqlContext::AfterWhere | BqlContext::AfterOperator => {
            let mut completions = column_completions();
            completions.extend(function_completions());
            completions.extend(vec![
                literal("TRUE"),
                literal("FALSE"),
                literal("NULL"),
                keyword("NOT", Some("Negate condition")),
            ]);
            completions
        }

        BqlContext::InWhereExpr => {
            vec![
                keyword("AND", Some("Logical AND")),
                keyword("OR", Some("Logical OR")),
                operator("=", Some("Equals")),
                operator("!=", Some("Not equals")),
                operator("~", Some("Regex match (case-insensitive)")),
                operator("!~", Some("Negative regex match")),
                operator("?~", Some("Pattern matches string")),
                operator("<", Some("Less than")),
                operator(">", Some("Greater than")),
                operator("<=", Some("Less or equal")),
                operator(">=", Some("Greater or equal")),
                operator("%", Some("Modulo")),
                keyword("IN", Some("Set membership")),
                keyword("NOT IN", Some("Not in set")),
                keyword("IS NULL", Some("Check for null")),
                keyword("IS NOT NULL", Some("Check for non-null")),
                keyword("GROUP BY", Some("Group results")),
                keyword("ORDER BY", Some("Sort results")),
                keyword("LIMIT", Some("Limit result count")),
                keyword("FLATTEN", Some("Expand inventory rows")),
            ]
        }

        BqlContext::AfterGroup => vec![keyword("BY", None)],

        BqlContext::AfterGroupBy => {
            let mut completions = column_completions();
            completions.extend(vec![
                keyword("ORDER BY", Some("Sort results")),
                keyword("LIMIT", Some("Limit result count")),
                operator(",", Some("Add another group column")),
            ]);
            completions
        }

        BqlContext::AfterOrder => vec![keyword("BY", None)],

        BqlContext::AfterOrderBy => {
            let mut completions = column_completions();
            completions.extend(vec![
                keyword("ASC", Some("Ascending order")),
                keyword("DESC", Some("Descending order")),
                keyword("LIMIT", Some("Limit result count")),
                operator(",", Some("Add another sort column")),
            ]);
            completions
        }

        BqlContext::AfterLimit => vec![literal("10"), literal("100"), literal("1000")],

        BqlContext::AfterJournal | BqlContext::AfterBalances | BqlContext::AfterPrint => vec![
            keyword("AT", Some("Apply function to results")),
            keyword("FROM", Some("Specify data source")),
        ],

        BqlContext::AfterAs | BqlContext::InString | BqlContext::InFunction(_) => vec![],
    }
}

// Helper constructors

fn keyword(text: &str, description: Option<&str>) -> Completion {
    Completion {
        text: text.to_string(),
        category: CompletionCategory::Keyword,
        description: description.map(String::from),
    }
}

fn operator(text: &str, description: Option<&str>) -> Completion {
    Completion {
        text: text.to_string(),
        category: CompletionCategory::Operator,
        description: description.map(String::from),
    }
}

fn literal(text: &str) -> Completion {
    Completion {
        text: text.to_string(),
        category: CompletionCategory::Literal,
        description: None,
    }
}

fn column(text: &str, description: &str) -> Completion {
    Completion {
        text: text.to_string(),
        category: CompletionCategory::Column,
        description: Some(description.to_string()),
    }
}

fn function(text: &str, description: &str) -> Completion {
    Completion {
        text: text.to_string(),
        category: CompletionCategory::Function,
        description: Some(description.to_string()),
    }
}

/// Get column completions.
fn column_completions() -> Vec<Completion> {
    vec![
        // Core columns
        column("account", "Account name"),
        column("date", "Transaction date"),
        column("narration", "Transaction description"),
        column("payee", "Transaction payee"),
        column("flag", "Transaction flag"),
        column("tags", "Transaction tags"),
        column("links", "Document links"),
        column("position", "Posting amount"),
        column("units", "Posting units"),
        column("cost", "Cost basis"),
        column("weight", "Balancing weight"),
        column("balance", "Running balance"),
        column("year", "Transaction year"),
        column("month", "Transaction month"),
        column("day", "Transaction day"),
        // Transaction-level columns
        column("type", "Directive type (txn)"),
        column("description", "Payee | narration"),
        column("accounts", "All accounts in transaction"),
        // Posting-level columns
        column("number", "Numeric part of amount"),
        column("currency", "Currency of amount"),
        column("cost_number", "Cost per unit"),
        column("cost_currency", "Cost currency"),
        column("cost_date", "Cost acquisition date"),
        column("cost_label", "Cost lot label"),
        column("price", "Price annotation"),
        column("posting_flag", "Posting-level flag"),
        column("other_accounts", "Other accounts in txn"),
    ]
}

/// Get function completions.
fn function_completions() -> Vec<Completion> {
    vec![
        // Aggregates
        function("SUM(", "Sum of values"),
        function("COUNT(", "Count of rows"),
        function("MIN(", "Minimum value"),
        function("MAX(", "Maximum value"),
        function("AVG(", "Average value"),
        function("FIRST(", "First value"),
        function("LAST(", "Last value"),
        // Type casting
        function("BOOL(", "Convert to boolean"),
        function("INT(", "Convert to integer"),
        function("DECIMAL(", "Convert to decimal"),
        function("STR(", "Convert to string"),
        function("DATE(", "Convert to date"),
        // Date functions
        function("YEAR(", "Extract year"),
        function("MONTH(", "Extract month"),
        function("DAY(", "Extract day"),
        function("QUARTER(", "Extract quarter"),
        function("WEEKDAY(", "Day of week (0=Mon)"),
        function("YMONTH(", "Year-month format"),
        function("TODAY()", "Current date"),
        function("DATE_DIFF(", "Days between dates"),
        function("DATE_ADD(", "Add days to date"),
        function("DATE_TRUNC(", "Truncate to precision"),
        function("DATE_PART(", "Extract date component"),
        function("DATE_FROM_YMD(", "Construct date from y/m/d"),
        function("PARSE_DATE(", "Parse date from string"),
        // String functions
        function("LENGTH(", "String length"),
        function("UPPER(", "Uppercase"),
        function("LOWER(", "Lowercase"),
        function("TRIM(", "Trim whitespace"),
        function("SUBSTR(", "Substring"),
        function("STARTSWITH(", "Check prefix"),
        function("ENDSWITH(", "Check suffix"),
        function("GREP(", "Regex match portion"),
        function("GREPN(", "Regex capture group"),
        function("SUBST(", "Regex substitution"),
        function("MAXWIDTH(", "Truncate with ellipsis"),
        function("SPLITCOMP(", "Split and get component"),
        function("JOINSTR(", "Join set to string"),
        function("COALESCE(", "First non-null"),
        // Account functions
        function("PARENT(", "Parent account"),
        function("LEAF(", "Leaf component"),
        function("ROOT(", "Root components"),
        function("ACCOUNT_DEPTH(", "Account depth"),
        function("ACCOUNT_SORTKEY(", "Sort key for account"),
        function("OPEN_DATE(", "Account open date"),
        function("CLOSE_DATE(", "Account close date"),
        function("OPEN_META(", "Open directive metadata"),
        function("COMMODITY_META(", "Commodity metadata"),
        function("META(", "Posting metadata value"),
        function("ENTRY_META(", "Transaction metadata value"),
        function("ANY_META(", "Posting or transaction metadata"),
        // Utility functions
        function("HAS_ACCOUNT(", "Check if txn has account"),
        function("FINDFIRST(", "First matching element"),
        function("REPR(", "Debug representation"),
        // Amount/Position functions
        function("NUMBER(", "Extract number"),
        function("CURRENCY(", "Extract currency"),
        function("ABS(", "Absolute value"),
        function("NEG(", "Negate value"),
        function("ROUND(", "Round number"),
        function("SAFEDIV(", "Safe division"),
        function("UNITS(", "Position units"),
        function("COST(", "Cost basis"),
        function("WEIGHT(", "Balancing weight"),
        function("VALUE(", "Market value"),
        function("GETITEM(", "Get from inventory"),
        function("ONLY(", "Single currency from inventory"),
        function("EMPTY(", "Check if inventory empty"),
        function("FILTER_CURRENCY(", "Filter by currency"),
        function("POSSIGN(", "Sign by account type"),
        function("GETPRICE(", "Get price between currencies"),
        function("CONVERT(", "Convert amount to currency"),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_complete_start() {
        let result = complete("", 0);
        assert_eq!(result.context, BqlContext::Start);
        assert!(result.completions.iter().any(|c| c.text == "SELECT"));
    }

    #[test]
    fn test_complete_after_select() {
        let result = complete("SELECT ", 7);
        assert_eq!(result.context, BqlContext::AfterSelect);
        assert!(result.completions.iter().any(|c| c.text == "account"));
        assert!(result.completions.iter().any(|c| c.text == "SUM("));
    }

    #[test]
    fn test_complete_after_where() {
        let result = complete("SELECT * WHERE ", 15);
        assert_eq!(result.context, BqlContext::AfterWhere);
        assert!(result.completions.iter().any(|c| c.text == "account"));
    }

    #[test]
    fn test_complete_in_where_expr() {
        let result = complete("SELECT * WHERE account ", 23);
        assert_eq!(result.context, BqlContext::InWhereExpr);
        assert!(result.completions.iter().any(|c| c.text == "="));
        assert!(result.completions.iter().any(|c| c.text == "~"));
    }

    #[test]
    fn test_complete_group_by() {
        let result = complete("SELECT * GROUP ", 15);
        assert_eq!(result.context, BqlContext::AfterGroup);
        assert!(result.completions.iter().any(|c| c.text == "BY"));
    }

    #[test]
    fn test_tokenize_bql() {
        let tokens = tokenize_bql("SELECT account, SUM(position)");
        assert_eq!(
            tokens,
            vec!["SELECT", "account", ",", "SUM", "(", "position", ")"]
        );
    }

    #[test]
    fn test_tokenize_bql_with_string() {
        let tokens = tokenize_bql("WHERE account ~ \"Expenses\"");
        assert_eq!(tokens, vec!["WHERE", "account", "~", "\"Expenses\""]);
    }

    #[test]
    fn test_tokenize_multi_char_operators() {
        let tokens = tokenize_bql("WHERE x >= 10 AND y != 5");
        assert!(tokens.contains(&">=".to_string()));
        assert!(tokens.contains(&"!=".to_string()));
    }
}
