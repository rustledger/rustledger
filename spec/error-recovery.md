# Error Recovery and Source Location Specification

This document specifies how the parser recovers from errors and how source locations are tracked through transformations.

## Error Recovery Philosophy

1. **Parse as much as possible** - Don't stop at first error
2. **Produce useful AST** - Partial results are valuable
3. **Accurate locations** - Errors point to exact source positions
4. **Cascading prevention** - Avoid spurious errors from earlier failures

## Source Locations

### Span Type

```rust
/// A span in source code
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    /// Byte offset of start
    pub start: usize,
    /// Byte offset of end (exclusive)
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Merge two spans
    pub fn merge(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    /// Extract text from source
    pub fn text<'a>(&self, source: &'a str) -> &'a str {
        &source[self.start..self.end]
    }
}
```

### Source Location

```rust
/// Human-readable source location
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceLocation {
    /// File path
    pub file: PathBuf,
    /// 1-based line number
    pub line: u32,
    /// 1-based column number
    pub column: u32,
    /// Length in characters
    pub length: u32,
    /// Byte span for precise slicing
    pub span: Span,
}

impl SourceLocation {
    /// Convert byte offset to line/column
    pub fn from_span(source: &str, file: PathBuf, span: Span) -> Self {
        let (line, column) = byte_to_line_col(source, span.start);
        Self {
            file,
            line: line as u32,
            column: column as u32,
            length: (span.end - span.start) as u32,
            span,
        }
    }
}

fn byte_to_line_col(source: &str, byte_offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut col = 1;
    let mut current_line_start = 0;

    for (i, c) in source.char_indices() {
        if i >= byte_offset {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 1;
            current_line_start = i + 1;
        } else {
            col += 1;
        }
    }

    (line, byte_offset - current_line_start + 1)
}
```

### Spanned AST Nodes

Every AST node carries its span:

```rust
#[derive(Debug)]
pub struct Spanned<T> {
    pub value: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(value: T, span: Span) -> Self {
        Self { value, span }
    }
}

// Usage in AST
pub struct Transaction {
    pub date: Spanned<NaiveDate>,
    pub flag: Spanned<Flag>,
    pub payee: Option<Spanned<String>>,
    pub narration: Spanned<String>,
    pub postings: Vec<Spanned<Posting>>,
    // Span of entire transaction (from date to last posting)
    pub span: Span,
}
```

## Parser Error Recovery

### Recovery Strategies

#### 1. Synchronization Points

Recover at well-defined syntax boundaries:

```rust
fn parse_directive(&mut self) -> Result<Directive, ParseError> {
    match self.parse_directive_inner() {
        Ok(d) => Ok(d),
        Err(e) => {
            self.errors.push(e);
            // Synchronize: skip to next line starting with date
            self.synchronize_to_next_directive();
            Err(ParseError::Recovered)
        }
    }
}

fn synchronize_to_next_directive(&mut self) {
    while !self.is_at_end() {
        // Skip current line
        self.skip_to_newline();
        self.advance_newline();

        // Check if next line starts a directive (date pattern)
        if self.peek_is_date() {
            return;
        }
    }
}
```

#### 2. Error Productions

Include error cases in grammar:

```rust
fn parse_posting(&mut self) -> Result<Posting, ParseError> {
    let account = self.parse_account()?;

    let units = match self.parse_amount() {
        Ok(amt) => Some(amt),
        Err(e) if e.is_recoverable() => {
            self.errors.push(e.into_warning("Invalid amount, treating as missing"));
            None  // Treat as interpolated posting
        }
        Err(e) => return Err(e),
    };

    // Continue parsing cost, price, etc.
    Ok(Posting { account, units, .. })
}
```

#### 3. Insertion Recovery

Insert missing tokens:

```rust
fn parse_transaction(&mut self) -> Result<Transaction, ParseError> {
    let date = self.parse_date()?;

    let flag = if self.check(&Token::Star) || self.check(&Token::Bang) {
        self.parse_flag()?
    } else {
        // Insert missing flag, emit warning
        self.errors.push(ParseError::warning(
            "Missing transaction flag, assuming '*'",
            self.current_span(),
        ));
        Spanned::new(Flag::Complete, self.current_span())
    };

    // Continue...
}
```

#### 4. Deletion Recovery

Skip unexpected tokens:

```rust
fn parse_postings(&mut self) -> Vec<Spanned<Posting>> {
    let mut postings = Vec::new();

    while self.check_indent() {
        match self.parse_posting() {
            Ok(p) => postings.push(p),
            Err(e) => {
                self.errors.push(e);
                // Skip to next line
                self.skip_to_newline();
            }
        }
    }

    postings
}
```

### Error Messages

#### Quality Criteria

1. **Specific** - "Expected ')' to close '(' at line 42" not "Syntax error"
2. **Actionable** - Suggest fixes when possible
3. **Located** - Point to exact character
4. **Contextual** - Show surrounding code

#### Error Structure

```rust
pub struct ParseError {
    pub kind: ParseErrorKind,
    pub message: String,
    pub span: Span,
    pub notes: Vec<Note>,
    pub suggestions: Vec<Suggestion>,
}

pub struct Note {
    pub message: String,
    pub span: Option<Span>,
}

pub struct Suggestion {
    pub message: String,
    pub replacement: String,
    pub span: Span,
}

pub enum ParseErrorKind {
    UnexpectedToken { expected: Vec<TokenKind>, found: TokenKind },
    UnexpectedEof { expected: Vec<TokenKind> },
    InvalidNumber { text: String },
    InvalidDate { text: String },
    InvalidAccount { text: String, reason: String },
    UnclosedString { start: Span },
    UnclosedBrace { start: Span },
    IndentationError { expected: usize, found: usize },
}
```

#### Example Error Output

```
error[E0001]: Unexpected token
  --> ledger.beancount:42:15
   |
42 |   Assets:Cash  100 $USD
   |               ^^^^
   |               expected amount, found '$'
   |
   = note: currency names cannot start with '$'
   = suggestion: remove the '$' prefix
```

### Rendering Errors

Using `ariadne` for beautiful output:

```rust
use ariadne::{Report, ReportKind, Source, Label, Color};

fn render_error(error: &ParseError, source: &str, file: &str) {
    Report::build(ReportKind::Error, file, error.span.start)
        .with_code(error.code())
        .with_message(&error.message)
        .with_label(
            Label::new((file, error.span.start..error.span.end))
                .with_message(&error.detail)
                .with_color(Color::Red)
        )
        .with_notes(error.notes.iter().map(|n| n.message.clone()))
        .finish()
        .print((file, Source::from(source)))
        .unwrap();
}
```

## Source Location Through Transformations

### Problem

Directives are transformed through multiple phases:
1. Parse → AST with spans
2. Include expansion → Multiple files merged
3. Interpolation → New amounts added
4. Pad expansion → Synthetic transactions
5. Plugin processing → Arbitrary transformations

Errors in later phases must point to original source.

### Solution: Location Preservation

#### Approach 1: Carry Original Spans

```rust
pub struct Amount {
    pub number: Decimal,
    pub currency: Currency,
    /// None if synthesized (interpolation, padding)
    pub span: Option<Span>,
    /// Origin for synthesized values
    pub origin: Option<Origin>,
}

pub enum Origin {
    Interpolated { from_transaction: Span },
    Padded { from_pad: Span, from_balance: Span },
    Plugin { plugin_name: String },
}
```

#### Approach 2: Transformation Log

```rust
pub struct TransformationLog {
    entries: Vec<TransformEntry>,
}

pub enum TransformEntry {
    Interpolated {
        transaction_span: Span,
        posting_index: usize,
        computed_amount: Amount,
    },
    PadExpanded {
        pad_span: Span,
        balance_span: Span,
        generated_transaction: Transaction,
    },
    PluginModified {
        plugin: String,
        original_span: Span,
        description: String,
    },
}

impl TransformationLog {
    /// Get original source for a transformed element
    pub fn trace_origin(&self, element_id: ElementId) -> Vec<Span>;
}
```

### Include File Tracking

```rust
pub struct SourceMap {
    /// All loaded files
    files: Vec<SourceFile>,
    /// Mapping from merged offset to (file_id, local_offset)
    offset_map: Vec<(usize, usize)>,
}

pub struct SourceFile {
    pub path: PathBuf,
    pub content: String,
    /// Offset in merged source
    pub start_offset: usize,
}

impl SourceMap {
    /// Convert merged offset to file location
    pub fn locate(&self, offset: usize) -> SourceLocation {
        let (file_id, local_offset) = self.offset_map
            .binary_search_by_key(&offset, |(o, _)| *o)
            .map_or_else(|i| self.offset_map[i - 1], |i| self.offset_map[i]);

        let file = &self.files[file_id];
        SourceLocation::from_span(
            &file.content,
            file.path.clone(),
            Span::new(local_offset, local_offset),
        )
    }
}
```

## Error Aggregation

### Collecting Errors

```rust
pub struct ErrorCollector {
    errors: Vec<Error>,
    warnings: Vec<Error>,
    max_errors: usize,
}

impl ErrorCollector {
    pub fn error(&mut self, error: Error) {
        if self.errors.len() < self.max_errors {
            self.errors.push(error);
        }
    }

    pub fn warning(&mut self, warning: Error) {
        self.warnings.push(warning);
    }

    /// Check if we should stop processing
    pub fn should_abort(&self) -> bool {
        self.errors.len() >= self.max_errors
    }

    /// Take all errors
    pub fn finish(self) -> (Vec<Error>, Vec<Error>) {
        (self.errors, self.warnings)
    }
}
```

### Error Deduplication

Avoid duplicate errors from cascading failures:

```rust
impl ErrorCollector {
    pub fn error_if_new(&mut self, error: Error) {
        // Don't add if we have an error at same location
        if !self.errors.iter().any(|e| e.span.overlaps(&error.span)) {
            self.error(error);
        }
    }
}
```

### Cascading Prevention

Mark tokens as "error recovery" to prevent cascading:

```rust
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    /// True if this token was inserted/synthesized during error recovery
    pub is_synthetic: bool,
}

impl Parser {
    fn parse_account(&mut self) -> Result<Spanned<Account>, ParseError> {
        let token = self.current();

        if token.is_synthetic {
            // Don't report errors for synthetic tokens
            return Err(ParseError::suppressed());
        }

        // Normal parsing...
    }
}
```

## Testing Error Recovery

```rust
#[test]
fn test_recovery_missing_flag() {
    let source = r#"
2024-01-01 "Deposit"
  Assets:Cash  100 USD
  Income:Salary
"#;
    let (ledger, errors) = parse_with_recovery(source);

    // Should recover and parse transaction
    assert_eq!(ledger.transactions().count(), 1);

    // Should have warning about missing flag
    assert!(errors.iter().any(|e| e.message.contains("flag")));
}

#[test]
fn test_recovery_continues_after_error() {
    let source = r#"
2024-01-01 * "First"
  Assets:Cash  100 USD
  Income:Salary

2024-01-02 * "Invalid number"
  Assets:Cash  not_a_number USD
  Expenses:Food

2024-01-03 * "Third"
  Assets:Cash  50 USD
  Expenses:Food
"#;
    let (ledger, errors) = parse_with_recovery(source);

    // Should parse first and third, skip second
    assert_eq!(ledger.transactions().count(), 2);
    assert!(errors.len() >= 1);
}

#[test]
fn test_error_location_accuracy() {
    let source = "2024-01-01 * \"Test\"\n  Invalid:Account  100 USD\n";
    let (_, errors) = parse_with_recovery(source);

    let error = &errors[0];
    assert_eq!(error.location.line, 2);
    assert_eq!(error.location.column, 3);
}
```

## LSP Integration

For editor support:

```rust
pub struct Diagnostic {
    pub range: Range,
    pub severity: DiagnosticSeverity,
    pub code: String,
    pub message: String,
    pub related: Vec<RelatedInformation>,
}

pub struct Range {
    pub start: Position,
    pub end: Position,
}

pub struct Position {
    pub line: u32,      // 0-based for LSP
    pub character: u32, // UTF-16 code units
}

impl From<&Error> for Diagnostic {
    fn from(error: &Error) -> Self {
        Diagnostic {
            range: error.span.to_lsp_range(),
            severity: error.severity.to_lsp(),
            code: error.code.to_string(),
            message: error.message.clone(),
            related: error.notes.iter().map(|n| n.to_related()).collect(),
        }
    }
}
```
