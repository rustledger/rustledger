//! Directive types representing all beancount directives.
//!
//! Beancount has 12 directive types that can appear in a ledger file:
//!
//! - [`Transaction`] - The most common directive, recording transfers between accounts
//! - [`Balance`] - Assert that an account has a specific balance
//! - [`Open`] - Open an account for use
//! - [`Close`] - Close an account
//! - [`Commodity`] - Declare a commodity/currency
//! - [`Pad`] - Automatically pad an account to match a balance assertion
//! - [`Event`] - Record a life event
//! - [`Query`] - Store a named BQL query
//! - [`Note`] - Add a note to an account
//! - [`Document`] - Link a document to an account
//! - [`Price`] - Record a price for a commodity
//! - [`Custom`] - Custom directive type

use chrono::NaiveDate;
use rust_decimal::Decimal;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;

use crate::{Amount, CostSpec, IncompleteAmount};

/// Metadata value types.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum MetaValue {
    /// String value
    String(String),
    /// Account reference
    Account(String),
    /// Currency code
    Currency(String),
    /// Tag reference
    Tag(String),
    /// Link reference
    Link(String),
    /// Date value
    Date(NaiveDate),
    /// Numeric value
    Number(Decimal),
    /// Boolean value
    Bool(bool),
    /// Amount value
    Amount(Amount),
    /// Null/None value
    None,
}

impl fmt::Display for MetaValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::String(s) => write!(f, "\"{s}\""),
            Self::Account(a) => write!(f, "{a}"),
            Self::Currency(c) => write!(f, "{c}"),
            Self::Tag(t) => write!(f, "#{t}"),
            Self::Link(l) => write!(f, "^{l}"),
            Self::Date(d) => write!(f, "{d}"),
            Self::Number(n) => write!(f, "{n}"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Amount(a) => write!(f, "{a}"),
            Self::None => write!(f, "None"),
        }
    }
}

/// Metadata is a key-value map attached to directives and postings.
pub type Metadata = HashMap<String, MetaValue>;

/// A posting within a transaction.
///
/// Postings represent the individual legs of a transaction. Each posting
/// specifies an account and optionally an amount, cost, and price.
///
/// When the units are `None`, the entire amount will be inferred by the
/// interpolation algorithm to balance the transaction. When units is
/// `Some(IncompleteAmount)`, it may still have missing components that
/// need to be filled in.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Posting {
    /// The account for this posting
    pub account: String,
    /// The units (may be incomplete or None for auto-calculated postings)
    pub units: Option<IncompleteAmount>,
    /// Cost specification for the position
    pub cost: Option<CostSpec>,
    /// Price annotation (@ or @@)
    pub price: Option<PriceAnnotation>,
    /// Whether this posting has the "!" flag
    pub flag: Option<char>,
    /// Posting metadata
    pub meta: Metadata,
}

impl Posting {
    /// Create a new posting with the given account and complete units.
    #[must_use]
    pub fn new(account: impl Into<String>, units: Amount) -> Self {
        Self {
            account: account.into(),
            units: Some(IncompleteAmount::Complete(units)),
            cost: None,
            price: None,
            flag: None,
            meta: Metadata::new(),
        }
    }

    /// Create a new posting with an incomplete amount.
    #[must_use]
    pub fn with_incomplete(account: impl Into<String>, units: IncompleteAmount) -> Self {
        Self {
            account: account.into(),
            units: Some(units),
            cost: None,
            price: None,
            flag: None,
            meta: Metadata::new(),
        }
    }

    /// Create a posting without any amount (to be fully interpolated).
    #[must_use]
    pub fn auto(account: impl Into<String>) -> Self {
        Self {
            account: account.into(),
            units: None,
            cost: None,
            price: None,
            flag: None,
            meta: Metadata::new(),
        }
    }

    /// Get the complete amount if available.
    #[must_use]
    pub fn amount(&self) -> Option<&Amount> {
        self.units.as_ref().and_then(|u| u.as_amount())
    }

    /// Add a cost specification.
    #[must_use]
    pub fn with_cost(mut self, cost: CostSpec) -> Self {
        self.cost = Some(cost);
        self
    }

    /// Add a price annotation.
    #[must_use]
    pub fn with_price(mut self, price: PriceAnnotation) -> Self {
        self.price = Some(price);
        self
    }

    /// Add a flag.
    #[must_use]
    pub const fn with_flag(mut self, flag: char) -> Self {
        self.flag = Some(flag);
        self
    }

    /// Check if this posting has an amount.
    #[must_use]
    pub const fn has_units(&self) -> bool {
        self.units.is_some()
    }
}

impl fmt::Display for Posting {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "  ")?;
        if let Some(flag) = self.flag {
            write!(f, "{flag} ")?;
        }
        write!(f, "{}", self.account)?;
        if let Some(units) = &self.units {
            write!(f, "  {units}")?;
        }
        if let Some(cost) = &self.cost {
            write!(f, " {cost}")?;
        }
        if let Some(price) = &self.price {
            write!(f, " {price}")?;
        }
        Ok(())
    }
}

/// Price annotation for a posting (@ or @@).
///
/// Price annotations can be incomplete (missing number or currency)
/// before interpolation fills in the missing values.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum PriceAnnotation {
    /// Per-unit price (@) with complete amount
    Unit(Amount),
    /// Total price (@@) with complete amount
    Total(Amount),
    /// Per-unit price (@) with incomplete amount
    UnitIncomplete(IncompleteAmount),
    /// Total price (@@) with incomplete amount
    TotalIncomplete(IncompleteAmount),
    /// Empty per-unit price (@ with no amount)
    UnitEmpty,
    /// Empty total price (@@ with no amount)
    TotalEmpty,
}

impl PriceAnnotation {
    /// Get the complete amount if available.
    #[must_use]
    pub const fn amount(&self) -> Option<&Amount> {
        match self {
            Self::Unit(a) | Self::Total(a) => Some(a),
            Self::UnitIncomplete(ia) | Self::TotalIncomplete(ia) => ia.as_amount(),
            Self::UnitEmpty | Self::TotalEmpty => None,
        }
    }

    /// Check if this is a per-unit price (@ vs @@).
    #[must_use]
    pub const fn is_unit(&self) -> bool {
        matches!(
            self,
            Self::Unit(_) | Self::UnitIncomplete(_) | Self::UnitEmpty
        )
    }
}

impl fmt::Display for PriceAnnotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit(a) => write!(f, "@ {a}"),
            Self::Total(a) => write!(f, "@@ {a}"),
            Self::UnitIncomplete(ia) => write!(f, "@ {ia}"),
            Self::TotalIncomplete(ia) => write!(f, "@@ {ia}"),
            Self::UnitEmpty => write!(f, "@"),
            Self::TotalEmpty => write!(f, "@@"),
        }
    }
}

/// Directive ordering priority for sorting.
///
/// When directives have the same date, they are sorted by type priority
/// to ensure proper processing order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DirectivePriority {
    /// Open accounts first so they exist before use
    Open = 0,
    /// Commodities declared before use
    Commodity = 1,
    /// Padding before balance assertions
    Pad = 2,
    /// Balance assertions checked at start of day
    Balance = 3,
    /// Main entries
    Transaction = 4,
    /// Annotations after transactions
    Note = 5,
    /// Attachments after transactions
    Document = 6,
    /// State changes
    Event = 7,
    /// Queries defined after data
    Query = 8,
    /// Prices at end of day
    Price = 9,
    /// Accounts closed after all activity
    Close = 10,
    /// User extensions last
    Custom = 11,
}

/// All directive types in beancount.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Directive {
    /// Transaction directive - records transfers between accounts
    Transaction(Transaction),
    /// Balance assertion - asserts an account balance at a point in time
    Balance(Balance),
    /// Open account - opens an account for use
    Open(Open),
    /// Close account - closes an account
    Close(Close),
    /// Commodity declaration - declares a currency/commodity
    Commodity(Commodity),
    /// Pad directive - auto-pad an account to match a balance
    Pad(Pad),
    /// Event directive - records a life event
    Event(Event),
    /// Query directive - stores a named BQL query
    Query(Query),
    /// Note directive - adds a note to an account
    Note(Note),
    /// Document directive - links a document to an account
    Document(Document),
    /// Price directive - records a commodity price
    Price(Price),
    /// Custom directive - custom user-defined directive
    Custom(Custom),
}

impl Directive {
    /// Get the date of this directive.
    #[must_use]
    pub const fn date(&self) -> NaiveDate {
        match self {
            Self::Transaction(t) => t.date,
            Self::Balance(b) => b.date,
            Self::Open(o) => o.date,
            Self::Close(c) => c.date,
            Self::Commodity(c) => c.date,
            Self::Pad(p) => p.date,
            Self::Event(e) => e.date,
            Self::Query(q) => q.date,
            Self::Note(n) => n.date,
            Self::Document(d) => d.date,
            Self::Price(p) => p.date,
            Self::Custom(c) => c.date,
        }
    }

    /// Get the metadata of this directive.
    #[must_use]
    pub const fn meta(&self) -> &Metadata {
        match self {
            Self::Transaction(t) => &t.meta,
            Self::Balance(b) => &b.meta,
            Self::Open(o) => &o.meta,
            Self::Close(c) => &c.meta,
            Self::Commodity(c) => &c.meta,
            Self::Pad(p) => &p.meta,
            Self::Event(e) => &e.meta,
            Self::Query(q) => &q.meta,
            Self::Note(n) => &n.meta,
            Self::Document(d) => &d.meta,
            Self::Price(p) => &p.meta,
            Self::Custom(c) => &c.meta,
        }
    }

    /// Check if this is a transaction.
    #[must_use]
    pub const fn is_transaction(&self) -> bool {
        matches!(self, Self::Transaction(_))
    }

    /// Get as a transaction, if this is one.
    #[must_use]
    pub const fn as_transaction(&self) -> Option<&Transaction> {
        match self {
            Self::Transaction(t) => Some(t),
            _ => None,
        }
    }

    /// Get the directive type name.
    #[must_use]
    pub const fn type_name(&self) -> &'static str {
        match self {
            Self::Transaction(_) => "transaction",
            Self::Balance(_) => "balance",
            Self::Open(_) => "open",
            Self::Close(_) => "close",
            Self::Commodity(_) => "commodity",
            Self::Pad(_) => "pad",
            Self::Event(_) => "event",
            Self::Query(_) => "query",
            Self::Note(_) => "note",
            Self::Document(_) => "document",
            Self::Price(_) => "price",
            Self::Custom(_) => "custom",
        }
    }

    /// Get the sorting priority for this directive.
    ///
    /// Used to determine order when directives have the same date.
    #[must_use]
    pub const fn priority(&self) -> DirectivePriority {
        match self {
            Self::Open(_) => DirectivePriority::Open,
            Self::Commodity(_) => DirectivePriority::Commodity,
            Self::Pad(_) => DirectivePriority::Pad,
            Self::Balance(_) => DirectivePriority::Balance,
            Self::Transaction(_) => DirectivePriority::Transaction,
            Self::Note(_) => DirectivePriority::Note,
            Self::Document(_) => DirectivePriority::Document,
            Self::Event(_) => DirectivePriority::Event,
            Self::Query(_) => DirectivePriority::Query,
            Self::Price(_) => DirectivePriority::Price,
            Self::Close(_) => DirectivePriority::Close,
            Self::Custom(_) => DirectivePriority::Custom,
        }
    }
}

/// Sort directives by date, then by type priority.
///
/// This is a stable sort that preserves file order for directives
/// with the same date and type.
pub fn sort_directives(directives: &mut [Directive]) {
    directives.sort_by(|a, b| {
        // Primary: date ascending
        a.date()
            .cmp(&b.date())
            // Secondary: type priority
            .then_with(|| a.priority().cmp(&b.priority()))
    });
}

/// A transaction directive.
///
/// Transactions are the most common directive type. They record transfers
/// between accounts and must balance (sum of all postings equals zero).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Transaction {
    /// Transaction date
    pub date: NaiveDate,
    /// Transaction flag (* or !)
    pub flag: char,
    /// Payee (optional)
    pub payee: Option<String>,
    /// Narration (description)
    pub narration: String,
    /// Tags attached to this transaction
    pub tags: Vec<String>,
    /// Links attached to this transaction
    pub links: Vec<String>,
    /// Transaction metadata
    pub meta: Metadata,
    /// Postings (account entries)
    pub postings: Vec<Posting>,
}

impl Transaction {
    /// Create a new transaction.
    #[must_use]
    pub fn new(date: NaiveDate, narration: impl Into<String>) -> Self {
        Self {
            date,
            flag: '*',
            payee: None,
            narration: narration.into(),
            tags: Vec::new(),
            links: Vec::new(),
            meta: Metadata::new(),
            postings: Vec::new(),
        }
    }

    /// Set the flag.
    #[must_use]
    pub const fn with_flag(mut self, flag: char) -> Self {
        self.flag = flag;
        self
    }

    /// Set the payee.
    #[must_use]
    pub fn with_payee(mut self, payee: impl Into<String>) -> Self {
        self.payee = Some(payee.into());
        self
    }

    /// Add a tag.
    #[must_use]
    pub fn with_tag(mut self, tag: impl Into<String>) -> Self {
        self.tags.push(tag.into());
        self
    }

    /// Add a link.
    #[must_use]
    pub fn with_link(mut self, link: impl Into<String>) -> Self {
        self.links.push(link.into());
        self
    }

    /// Add a posting.
    #[must_use]
    pub fn with_posting(mut self, posting: Posting) -> Self {
        self.postings.push(posting);
        self
    }

    /// Check if this transaction is marked as complete (*).
    #[must_use]
    pub const fn is_complete(&self) -> bool {
        self.flag == '*'
    }

    /// Check if this transaction is marked as incomplete (!).
    #[must_use]
    pub const fn is_incomplete(&self) -> bool {
        self.flag == '!'
    }
}

impl fmt::Display for Transaction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} ", self.date, self.flag)?;
        if let Some(payee) = &self.payee {
            write!(f, "\"{payee}\" ")?;
        }
        write!(f, "\"{}\"", self.narration)?;
        for tag in &self.tags {
            write!(f, " #{tag}")?;
        }
        for link in &self.links {
            write!(f, " ^{link}")?;
        }
        for posting in &self.postings {
            write!(f, "\n{posting}")?;
        }
        Ok(())
    }
}

/// A balance assertion directive.
///
/// Asserts that an account has a specific balance at the beginning of a date.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Balance {
    /// Assertion date
    pub date: NaiveDate,
    /// Account to check
    pub account: String,
    /// Expected amount
    pub amount: Amount,
    /// Tolerance (if explicitly specified)
    pub tolerance: Option<Decimal>,
    /// Metadata
    pub meta: Metadata,
}

impl Balance {
    /// Create a new balance assertion.
    #[must_use]
    pub fn new(date: NaiveDate, account: impl Into<String>, amount: Amount) -> Self {
        Self {
            date,
            account: account.into(),
            amount,
            tolerance: None,
            meta: Metadata::new(),
        }
    }

    /// Set explicit tolerance.
    #[must_use]
    pub const fn with_tolerance(mut self, tolerance: Decimal) -> Self {
        self.tolerance = Some(tolerance);
        self
    }
}

impl fmt::Display for Balance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} balance {} {}", self.date, self.account, self.amount)?;
        if let Some(tol) = self.tolerance {
            write!(f, " ~ {tol}")?;
        }
        Ok(())
    }
}

/// An open account directive.
///
/// Opens an account for use. Accounts must be opened before they can be used.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Open {
    /// Date account was opened
    pub date: NaiveDate,
    /// Account name (e.g., "Assets:Bank:Checking")
    pub account: String,
    /// Allowed currencies (empty = any currency allowed)
    pub currencies: Vec<String>,
    /// Booking method for this account
    pub booking: Option<String>,
    /// Metadata
    pub meta: Metadata,
}

impl Open {
    /// Create a new open directive.
    #[must_use]
    pub fn new(date: NaiveDate, account: impl Into<String>) -> Self {
        Self {
            date,
            account: account.into(),
            currencies: Vec::new(),
            booking: None,
            meta: Metadata::new(),
        }
    }

    /// Set allowed currencies.
    #[must_use]
    pub fn with_currencies(mut self, currencies: Vec<String>) -> Self {
        self.currencies = currencies;
        self
    }

    /// Set booking method.
    #[must_use]
    pub fn with_booking(mut self, booking: impl Into<String>) -> Self {
        self.booking = Some(booking.into());
        self
    }
}

impl fmt::Display for Open {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} open {}", self.date, self.account)?;
        if !self.currencies.is_empty() {
            write!(f, " {}", self.currencies.join(","))?;
        }
        if let Some(booking) = &self.booking {
            write!(f, " \"{booking}\"")?;
        }
        Ok(())
    }
}

/// A close account directive.
///
/// Closes an account. The account should have zero balance when closed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Close {
    /// Date account was closed
    pub date: NaiveDate,
    /// Account name
    pub account: String,
    /// Metadata
    pub meta: Metadata,
}

impl Close {
    /// Create a new close directive.
    #[must_use]
    pub fn new(date: NaiveDate, account: impl Into<String>) -> Self {
        Self {
            date,
            account: account.into(),
            meta: Metadata::new(),
        }
    }
}

impl fmt::Display for Close {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} close {}", self.date, self.account)
    }
}

/// A commodity declaration directive.
///
/// Declares a commodity/currency that can be used in the ledger.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Commodity {
    /// Declaration date
    pub date: NaiveDate,
    /// Currency/commodity code (e.g., "USD", "AAPL")
    pub currency: String,
    /// Metadata
    pub meta: Metadata,
}

impl Commodity {
    /// Create a new commodity declaration.
    #[must_use]
    pub fn new(date: NaiveDate, currency: impl Into<String>) -> Self {
        Self {
            date,
            currency: currency.into(),
            meta: Metadata::new(),
        }
    }
}

impl fmt::Display for Commodity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} commodity {}", self.date, self.currency)
    }
}

/// A pad directive.
///
/// Automatically inserts a transaction to pad an account to match
/// a subsequent balance assertion.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Pad {
    /// Pad date
    pub date: NaiveDate,
    /// Account to pad
    pub account: String,
    /// Source account for padding (e.g., Equity:Opening-Balances)
    pub source_account: String,
    /// Metadata
    pub meta: Metadata,
}

impl Pad {
    /// Create a new pad directive.
    #[must_use]
    pub fn new(
        date: NaiveDate,
        account: impl Into<String>,
        source_account: impl Into<String>,
    ) -> Self {
        Self {
            date,
            account: account.into(),
            source_account: source_account.into(),
            meta: Metadata::new(),
        }
    }
}

impl fmt::Display for Pad {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} pad {} {}",
            self.date, self.account, self.source_account
        )
    }
}

/// An event directive.
///
/// Records a life event (e.g., location changes, employment changes).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Event {
    /// Event date
    pub date: NaiveDate,
    /// Event type (e.g., "location", "employer")
    pub event_type: String,
    /// Event value
    pub value: String,
    /// Metadata
    pub meta: Metadata,
}

impl Event {
    /// Create a new event directive.
    #[must_use]
    pub fn new(date: NaiveDate, event_type: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            date,
            event_type: event_type.into(),
            value: value.into(),
            meta: Metadata::new(),
        }
    }
}

impl fmt::Display for Event {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} event \"{}\" \"{}\"",
            self.date, self.event_type, self.value
        )
    }
}

/// A query directive.
///
/// Stores a named BQL query that can be referenced later.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Query {
    /// Query date
    pub date: NaiveDate,
    /// Query name
    pub name: String,
    /// BQL query string
    pub query: String,
    /// Metadata
    pub meta: Metadata,
}

impl Query {
    /// Create a new query directive.
    #[must_use]
    pub fn new(date: NaiveDate, name: impl Into<String>, query: impl Into<String>) -> Self {
        Self {
            date,
            name: name.into(),
            query: query.into(),
            meta: Metadata::new(),
        }
    }
}

impl fmt::Display for Query {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} query \"{}\" \"{}\"",
            self.date, self.name, self.query
        )
    }
}

/// A note directive.
///
/// Adds a note/comment to an account on a specific date.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Note {
    /// Note date
    pub date: NaiveDate,
    /// Account
    pub account: String,
    /// Note text
    pub comment: String,
    /// Metadata
    pub meta: Metadata,
}

impl Note {
    /// Create a new note directive.
    #[must_use]
    pub fn new(date: NaiveDate, account: impl Into<String>, comment: impl Into<String>) -> Self {
        Self {
            date,
            account: account.into(),
            comment: comment.into(),
            meta: Metadata::new(),
        }
    }
}

impl fmt::Display for Note {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} note {} \"{}\"",
            self.date, self.account, self.comment
        )
    }
}

/// A document directive.
///
/// Links an external document file to an account.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Document {
    /// Document date
    pub date: NaiveDate,
    /// Account
    pub account: String,
    /// File path to the document
    pub path: String,
    /// Tags
    pub tags: Vec<String>,
    /// Links
    pub links: Vec<String>,
    /// Metadata
    pub meta: Metadata,
}

impl Document {
    /// Create a new document directive.
    #[must_use]
    pub fn new(date: NaiveDate, account: impl Into<String>, path: impl Into<String>) -> Self {
        Self {
            date,
            account: account.into(),
            path: path.into(),
            tags: Vec::new(),
            links: Vec::new(),
            meta: Metadata::new(),
        }
    }
}

impl fmt::Display for Document {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} document {} \"{}\"",
            self.date, self.account, self.path
        )
    }
}

/// A price directive.
///
/// Records the price of a commodity in another currency.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Price {
    /// Price date
    pub date: NaiveDate,
    /// Currency being priced
    pub currency: String,
    /// Price amount (in another currency)
    pub amount: Amount,
    /// Metadata
    pub meta: Metadata,
}

impl Price {
    /// Create a new price directive.
    #[must_use]
    pub fn new(date: NaiveDate, currency: impl Into<String>, amount: Amount) -> Self {
        Self {
            date,
            currency: currency.into(),
            amount,
            meta: Metadata::new(),
        }
    }
}

impl fmt::Display for Price {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} price {} {}", self.date, self.currency, self.amount)
    }
}

/// A custom directive.
///
/// User-defined directive type for extensions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Custom {
    /// Custom directive date
    pub date: NaiveDate,
    /// Custom type name (e.g., "budget", "autopay")
    pub custom_type: String,
    /// Values/arguments for this custom directive
    pub values: Vec<MetaValue>,
    /// Metadata
    pub meta: Metadata,
}

impl Custom {
    /// Create a new custom directive.
    #[must_use]
    pub fn new(date: NaiveDate, custom_type: impl Into<String>) -> Self {
        Self {
            date,
            custom_type: custom_type.into(),
            values: Vec::new(),
            meta: Metadata::new(),
        }
    }

    /// Add a value.
    #[must_use]
    pub fn with_value(mut self, value: MetaValue) -> Self {
        self.values.push(value);
        self
    }
}

impl fmt::Display for Custom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} custom \"{}\"", self.date, self.custom_type)?;
        for value in &self.values {
            write!(f, " {value}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    fn date(year: i32, month: u32, day: u32) -> NaiveDate {
        NaiveDate::from_ymd_opt(year, month, day).unwrap()
    }

    #[test]
    fn test_transaction() {
        let txn = Transaction::new(date(2024, 1, 15), "Grocery shopping")
            .with_payee("Whole Foods")
            .with_flag('*')
            .with_tag("food")
            .with_posting(Posting::new(
                "Expenses:Food",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_posting(Posting::auto("Assets:Checking"));

        assert_eq!(txn.flag, '*');
        assert_eq!(txn.payee, Some("Whole Foods".to_string()));
        assert_eq!(txn.postings.len(), 2);
        assert!(txn.is_complete());
    }

    #[test]
    fn test_balance() {
        let bal = Balance::new(
            date(2024, 1, 1),
            "Assets:Checking",
            Amount::new(dec!(1000.00), "USD"),
        );

        assert_eq!(bal.account, "Assets:Checking");
        assert_eq!(bal.amount.number, dec!(1000.00));
    }

    #[test]
    fn test_open() {
        let open = Open::new(date(2024, 1, 1), "Assets:Bank:Checking")
            .with_currencies(vec!["USD".to_string()])
            .with_booking("FIFO");

        assert_eq!(open.currencies, vec!["USD"]);
        assert_eq!(open.booking, Some("FIFO".to_string()));
    }

    #[test]
    fn test_directive_date() {
        let txn = Transaction::new(date(2024, 1, 15), "Test");
        let dir = Directive::Transaction(txn);

        assert_eq!(dir.date(), date(2024, 1, 15));
        assert!(dir.is_transaction());
        assert_eq!(dir.type_name(), "transaction");
    }

    #[test]
    fn test_posting_display() {
        let posting = Posting::new("Assets:Checking", Amount::new(dec!(100.00), "USD"));
        let s = format!("{posting}");
        assert!(s.contains("Assets:Checking"));
        assert!(s.contains("100.00 USD"));
    }

    #[test]
    fn test_transaction_display() {
        let txn = Transaction::new(date(2024, 1, 15), "Test transaction")
            .with_payee("Test Payee")
            .with_posting(Posting::new(
                "Expenses:Test",
                Amount::new(dec!(50.00), "USD"),
            ))
            .with_posting(Posting::auto("Assets:Cash"));

        let s = format!("{txn}");
        assert!(s.contains("2024-01-15"));
        assert!(s.contains("Test Payee"));
        assert!(s.contains("Test transaction"));
    }

    #[test]
    fn test_directive_priority() {
        // Test that priorities are ordered correctly
        assert!(DirectivePriority::Open < DirectivePriority::Transaction);
        assert!(DirectivePriority::Pad < DirectivePriority::Balance);
        assert!(DirectivePriority::Balance < DirectivePriority::Transaction);
        assert!(DirectivePriority::Transaction < DirectivePriority::Close);
        assert!(DirectivePriority::Price < DirectivePriority::Close);
    }

    #[test]
    fn test_sort_directives_by_date() {
        let mut directives = vec![
            Directive::Transaction(Transaction::new(date(2024, 1, 15), "Third")),
            Directive::Transaction(Transaction::new(date(2024, 1, 1), "First")),
            Directive::Transaction(Transaction::new(date(2024, 1, 10), "Second")),
        ];

        sort_directives(&mut directives);

        assert_eq!(directives[0].date(), date(2024, 1, 1));
        assert_eq!(directives[1].date(), date(2024, 1, 10));
        assert_eq!(directives[2].date(), date(2024, 1, 15));
    }

    #[test]
    fn test_sort_directives_by_type_same_date() {
        // On the same date, open should come before transaction, transaction before close
        let mut directives = vec![
            Directive::Close(Close::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Transaction(Transaction::new(date(2024, 1, 1), "Payment")),
            Directive::Open(Open::new(date(2024, 1, 1), "Assets:Bank")),
            Directive::Balance(Balance::new(
                date(2024, 1, 1),
                "Assets:Bank",
                Amount::new(dec!(0), "USD"),
            )),
        ];

        sort_directives(&mut directives);

        assert_eq!(directives[0].type_name(), "open");
        assert_eq!(directives[1].type_name(), "balance");
        assert_eq!(directives[2].type_name(), "transaction");
        assert_eq!(directives[3].type_name(), "close");
    }

    #[test]
    fn test_sort_directives_pad_before_balance() {
        // Pad must come before balance assertion on the same day
        let mut directives = vec![
            Directive::Balance(Balance::new(
                date(2024, 1, 1),
                "Assets:Bank",
                Amount::new(dec!(1000), "USD"),
            )),
            Directive::Pad(Pad::new(
                date(2024, 1, 1),
                "Assets:Bank",
                "Equity:Opening-Balances",
            )),
        ];

        sort_directives(&mut directives);

        assert_eq!(directives[0].type_name(), "pad");
        assert_eq!(directives[1].type_name(), "balance");
    }
}
