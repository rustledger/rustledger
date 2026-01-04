# Library API and Serialization Specification

This document specifies the public API for embedding rustledger and the serialization format for caching and WASM boundary.

## Design Principles

1. **Zero-copy where possible** - Avoid allocations in hot paths
2. **Builder pattern** - Fluent configuration
3. **Error types over panics** - All errors are recoverable
4. **Streaming support** - Process large ledgers incrementally
5. **WASM-compatible** - No OS dependencies in core

## Core API

### Loading a Ledger

```rust
use beancount::{Ledger, LoadOptions, Error};

// Simple loading
let ledger = Ledger::load("ledger.beancount")?;

// With options
let ledger = Ledger::builder()
    .path("ledger.beancount")
    .encoding(Encoding::Utf8)
    .include_documents(false)
    .build()?;

// From string
let ledger = Ledger::parse(source_text)?;

// Streaming (for large ledgers)
let loader = Ledger::stream("ledger.beancount")?;
for directive in loader {
    let directive = directive?;
    process(directive);
}
```

### Ledger Structure

```rust
pub struct Ledger {
    /// Parsed options from `option` directives
    pub options: Options,

    /// All directives, sorted by date
    pub directives: Vec<Directive>,

    /// Parse and validation errors
    pub errors: Vec<Error>,

    /// Account states (open/close dates, booking methods)
    pub accounts: HashMap<AccountName, AccountState>,

    /// Current inventory per account
    pub inventories: HashMap<AccountName, Inventory>,

    /// Price database
    pub prices: PriceMap,
}

impl Ledger {
    /// Check if ledger is valid (no errors)
    pub fn is_valid(&self) -> bool;

    /// Get all transactions
    pub fn transactions(&self) -> impl Iterator<Item = &Transaction>;

    /// Get balance for account at date
    pub fn balance(&self, account: &str, date: NaiveDate) -> Inventory;

    /// Query with BQL
    pub fn query(&self, bql: &str) -> QueryResult;
}
```

### Directive Types

```rust
pub enum Directive {
    Transaction(Transaction),
    Balance(BalanceAssertion),
    Open(OpenAccount),
    Close(CloseAccount),
    Commodity(CommodityDecl),
    Pad(PadDirective),
    Event(Event),
    Query(QueryDirective),
    Note(Note),
    Document(Document),
    Price(PriceDirective),
    Custom(Custom),
}

impl Directive {
    /// Get directive date
    pub fn date(&self) -> NaiveDate;

    /// Get source location
    pub fn location(&self) -> &SourceLocation;

    /// Get metadata
    pub fn metadata(&self) -> &Metadata;
}
```

### Transactions

```rust
pub struct Transaction {
    pub date: NaiveDate,
    pub flag: Flag,
    pub payee: Option<String>,
    pub narration: String,
    pub tags: HashSet<Tag>,
    pub links: HashSet<Link>,
    pub metadata: Metadata,
    pub postings: Vec<Posting>,
    pub location: SourceLocation,
}

pub struct Posting {
    pub account: AccountName,
    pub units: Option<Amount>,
    pub cost: Option<CostSpec>,
    pub price: Option<Amount>,
    pub flag: Option<Flag>,
    pub metadata: Metadata,
    pub location: SourceLocation,
}

impl Transaction {
    /// Check if transaction balances
    pub fn balances(&self) -> bool;

    /// Get postings for account
    pub fn postings_for(&self, account: &str) -> impl Iterator<Item = &Posting>;
}
```

### Amounts and Inventory

```rust
pub struct Amount {
    pub number: Decimal,
    pub currency: Currency,
}

pub struct Position {
    pub units: Amount,
    pub cost: Option<Cost>,
}

pub struct Inventory {
    positions: Vec<Position>,
}

impl Inventory {
    pub fn new() -> Self;

    /// Total units of a currency (ignoring cost lots)
    pub fn units(&self, currency: &str) -> Decimal;

    /// Get all positions
    pub fn positions(&self) -> &[Position];

    /// Add position
    pub fn augment(&mut self, position: Position);

    /// Reduce position with booking
    pub fn reduce(
        &mut self,
        units: Amount,
        cost_spec: Option<CostSpec>,
        method: BookingMethod,
    ) -> Result<Vec<MatchedLot>, BookingError>;

    /// Check if empty
    pub fn is_empty(&self) -> bool;
}
```

### Error Handling

```rust
pub struct Error {
    pub code: ErrorCode,
    pub message: String,
    pub severity: Severity,
    pub location: Option<SourceLocation>,
    pub notes: Vec<String>,
}

pub struct SourceLocation {
    pub file: PathBuf,
    pub line: u32,
    pub column: u32,
    pub length: u32,
}

pub enum Severity {
    Error,
    Warning,
    Info,
}

// Errors implement Display for pretty printing
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Produces: "error[E1001]: Account not opened at ledger.beancount:42:3"
    }
}

// Integration with miette/ariadne for beautiful errors
impl miette::Diagnostic for Error {
    fn code(&self) -> Option<Box<dyn std::fmt::Display>>;
    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan>>>;
}
```

### Query API

```rust
pub struct QueryEngine<'a> {
    ledger: &'a Ledger,
}

impl<'a> QueryEngine<'a> {
    pub fn new(ledger: &'a Ledger) -> Self;

    /// Execute BQL query
    pub fn query(&self, bql: &str) -> Result<QueryResult, QueryError>;

    /// Execute with parameters
    pub fn query_with_params(
        &self,
        bql: &str,
        params: &[(&str, Value)],
    ) -> Result<QueryResult, QueryError>;
}

pub struct QueryResult {
    pub columns: Vec<ColumnInfo>,
    pub rows: Vec<Row>,
}

pub struct Row {
    pub values: Vec<Value>,
}

pub enum Value {
    Null,
    Bool(bool),
    Integer(i64),
    Decimal(Decimal),
    String(String),
    Date(NaiveDate),
    Amount(Amount),
    Position(Position),
    Inventory(Inventory),
    Set(HashSet<String>),
}
```

## WASM API

For browser/embedded use:

```rust
#[wasm_bindgen]
pub struct WasmLedger {
    inner: Ledger,
}

#[wasm_bindgen]
impl WasmLedger {
    #[wasm_bindgen(constructor)]
    pub fn new(source: &str) -> Result<WasmLedger, JsValue>;

    #[wasm_bindgen]
    pub fn is_valid(&self) -> bool;

    #[wasm_bindgen]
    pub fn errors(&self) -> JsValue;  // Returns JSON array

    #[wasm_bindgen]
    pub fn query(&self, bql: &str) -> Result<JsValue, JsValue>;

    #[wasm_bindgen]
    pub fn balance(&self, account: &str, date: &str) -> JsValue;
}
```

JavaScript usage:

```javascript
import init, { WasmLedger } from 'beancount-wasm';

await init();

const ledger = new WasmLedger(`
2024-01-01 open Assets:Cash
2024-01-15 * "Deposit"
  Assets:Cash  100 USD
  Income:Salary
`);

if (ledger.is_valid()) {
    const result = ledger.query("SELECT account, sum(position) GROUP BY account");
    console.log(result);
}
```

## Serialization Format

### Binary Format (for caching)

We use MessagePack for compact binary serialization:

```rust
use rmp_serde::{Serializer, Deserializer};

impl Ledger {
    /// Serialize to bytes
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.serialize(&mut Serializer::new(&mut buf)).unwrap();
        buf
    }

    /// Deserialize from bytes
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DeserializeError> {
        let mut de = Deserializer::new(bytes);
        Deserialize::deserialize(&mut de)
    }

    /// Save to cache file
    pub fn save_cache(&self, path: &Path) -> io::Result<()>;

    /// Load from cache (with freshness check)
    pub fn load_cache(path: &Path, source_mtime: SystemTime) -> Option<Self>;
}
```

### Cache Format

```
+----------------+
| Magic: "BC01"  |  4 bytes
+----------------+
| Version        |  2 bytes
+----------------+
| Source Hash    |  32 bytes (SHA-256)
+----------------+
| Source Mtime   |  8 bytes
+----------------+
| Compressed     |  1 byte (0=none, 1=zstd)
+----------------+
| Payload Length |  4 bytes
+----------------+
| Payload        |  MessagePack data
+----------------+
```

### JSON Export

For interop with other tools:

```rust
impl Ledger {
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).unwrap()
    }

    pub fn to_json_writer(&self, writer: impl Write) -> io::Result<()>;
}
```

### Beancount Format (Print)

```rust
impl Ledger {
    /// Print back to beancount format
    pub fn to_beancount(&self) -> String;

    /// Print with formatting options
    pub fn to_beancount_with(&self, options: &FormatOptions) -> String;
}

pub struct FormatOptions {
    /// Indent width for postings
    pub indent: usize,

    /// Align amounts at column
    pub amount_column: Option<usize>,

    /// Include metadata
    pub include_metadata: bool,

    /// Currency column alignment
    pub align_currencies: bool,
}
```

## Plugin API

For WASM plugins:

```rust
/// Trait for plugins (implemented by WASM modules)
pub trait Plugin {
    /// Plugin name
    fn name(&self) -> &str;

    /// Process directives
    fn process(
        &self,
        directives: Vec<Directive>,
        options: &Options,
        config: Option<&str>,
    ) -> PluginResult;
}

pub struct PluginResult {
    pub directives: Vec<Directive>,
    pub errors: Vec<Error>,
}

/// Plugin host for loading WASM plugins
pub struct PluginHost {
    runtime: wasmtime::Engine,
    plugins: Vec<LoadedPlugin>,
}

impl PluginHost {
    pub fn new() -> Self;
    pub fn load(&mut self, path: &Path) -> Result<(), PluginError>;
    pub fn process(&self, ledger: &mut Ledger) -> Vec<Error>;
}
```

## Thread Safety

```rust
// Ledger is Send + Sync (can be shared across threads)
fn example() {
    let ledger = Arc::new(Ledger::load("ledger.beancount").unwrap());

    let handles: Vec<_> = (0..4).map(|_| {
        let ledger = Arc::clone(&ledger);
        thread::spawn(move || {
            ledger.query("SELECT sum(position) WHERE account ~ 'Expenses'")
        })
    }).collect();
}

// Mutable operations require &mut or interior mutability
impl Ledger {
    pub fn add_directive(&mut self, directive: Directive);
    pub fn reprocess(&mut self);  // Re-run booking/validation
}
```

## Builder API

```rust
// Transaction builder
let txn = Transaction::builder()
    .date(NaiveDate::from_ymd(2024, 1, 15))
    .payee("Store")
    .narration("Groceries")
    .tag("food")
    .posting("Expenses:Food", amount!(50 USD))
    .posting("Assets:Cash", None)  // Will be interpolated
    .build()?;

// Ledger modification
let mut ledger = Ledger::new();
ledger.add_directive(Directive::Open(OpenAccount {
    date: date!(2024-01-01),
    account: "Assets:Cash".parse()?,
    currencies: vec![],
    booking: None,
}));
ledger.add_directive(Directive::Transaction(txn));
ledger.process()?;  // Run interpolation, booking, validation
```

## Performance Considerations

### Lazy Processing

```rust
impl Ledger {
    /// Parse only, don't process
    pub fn parse_only(source: &str) -> Result<Vec<Directive>, ParseError>;

    /// Process incrementally
    pub fn process_directive(&mut self, directive: Directive) -> Vec<Error>;
}
```

### Parallel Processing

```rust
impl Ledger {
    /// Process with parallelism
    pub fn process_parallel(&mut self, threads: usize) -> Vec<Error>;
}
```

### Memory-Mapped Files

```rust
impl Ledger {
    /// Load with memory mapping (for very large files)
    pub fn load_mmap(path: &Path) -> Result<Self, LoadError>;
}
```
