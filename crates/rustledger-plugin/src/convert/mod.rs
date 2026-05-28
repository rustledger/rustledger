//! Conversion between core types and plugin serialization types.

mod from_wrapper;
mod to_wrapper;

use rustledger_core::{Directive, NaiveDate};

use crate::types::{DirectiveData, DirectiveWrapper};

// Re-export conversion functions
use from_wrapper::{
    data_to_balance, data_to_close, data_to_commodity, data_to_custom, data_to_document,
    data_to_event, data_to_note, data_to_open, data_to_pad, data_to_price, data_to_query,
    data_to_transaction,
};
use to_wrapper::{
    balance_to_data, close_to_data, commodity_to_data, custom_to_data, document_to_data,
    event_to_data, note_to_data, open_to_data, pad_to_data, price_to_data, query_to_data,
    transaction_to_data,
};

/// Error returned when converting a wrapper back to a directive fails.
#[derive(Debug, Clone, thiserror::Error)]
pub enum ConversionError {
    /// Invalid date format.
    #[error("invalid date format: {0}")]
    InvalidDate(String),
    /// Invalid number format. Use for parse failures only — for a pair
    /// of valid numbers that fail a cross-field invariant, see
    /// [`Self::BookedCostInvariantViolated`].
    #[error("invalid number format: {0}")]
    InvalidNumber(String),
    /// Invalid flag format.
    #[error("invalid flag: {0}")]
    InvalidFlag(String),
    /// A `PerUnitFromTotal` cost spec carries a (`per_unit`, `total`)
    /// pair that doesn't agree with the posting's units. Returned by
    /// the plugin egress and FFI input bridges when a plugin author
    /// or JSON client supplies the post-booking shape with
    /// inconsistent values — e.g. mutates `per_unit` without updating
    /// `total`. The inner [`rustledger_core::BookedCostInvariantError`]
    /// carries the supplied values, the derived total, and the
    /// tolerance for plugin-author diagnostics.
    #[error("cost spec invariant violated: {0}")]
    BookedCostInvariantViolated(#[from] rustledger_core::BookedCostInvariantError),
    /// A plugin emitted a `PerUnitFromTotal` cost spec without
    /// supplying the posting's units. The post-booking shape is
    /// undefined without units (`per_unit = total / |units|` requires
    /// them) — a plugin emitting it untouched should keep the units
    /// the host gave it; a plugin emitting a fresh post-booking spec
    /// must include matching units. Distinct from
    /// [`Self::BookedCostInvariantViolated`] because "missing" is a
    /// different category from "inconsistent" — plugin authors fix
    /// each with different actions (forgot vs miscalculated).
    #[error(
        "PerUnitFromTotal cost spec requires units on the posting (got per_unit {per_unit}, total {total}, no units)"
    )]
    PerUnitFromTotalMissingUnits {
        /// The per-unit value the plugin supplied.
        per_unit: rustledger_core::Decimal,
        /// The total value the plugin supplied.
        total: rustledger_core::Decimal,
    },
    /// A `SourceSpan` byte offset from the plugin wire format does not
    /// fit in `usize` on the host. This is effectively impossible in
    /// practice — `SourceSpan` is `u64` and the host is 64-bit on every
    /// platform rustledger supports today, so the only way to surface
    /// this variant is to run the host on a 32-bit target with source
    /// files larger than 4 GiB. If you see it: please file a bug
    /// report; the offset is almost certainly corrupt.
    #[error("source span overflow: {0}")]
    SpanOverflow(String),
}

/// Convert a directive to its serializable wrapper with source location.
///
/// The `filename` and `lineno` parameters are used for error reporting
/// when the directive is later processed by plugins.
pub fn directive_to_wrapper_with_location(
    directive: &Directive,
    filename: Option<String>,
    lineno: Option<u32>,
) -> DirectiveWrapper {
    let mut wrapper = directive_to_wrapper(directive);
    wrapper.filename = filename;
    wrapper.lineno = lineno;
    wrapper
}

/// Convert a directive to its serializable wrapper.
///
/// Note: This does not set filename/lineno - those must be set by the caller
/// if source location tracking is needed.
pub fn directive_to_wrapper(directive: &Directive) -> DirectiveWrapper {
    match directive {
        Directive::Transaction(txn) => DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: txn.date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(transaction_to_data(txn)),
        },
        Directive::Balance(bal) => DirectiveWrapper {
            directive_type: "balance".to_string(),
            date: bal.date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Balance(balance_to_data(bal)),
        },
        Directive::Open(open) => DirectiveWrapper {
            directive_type: "open".to_string(),
            date: open.date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Open(open_to_data(open)),
        },
        Directive::Close(close) => DirectiveWrapper {
            directive_type: "close".to_string(),
            date: close.date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Close(close_to_data(close)),
        },
        Directive::Commodity(comm) => DirectiveWrapper {
            directive_type: "commodity".to_string(),
            date: comm.date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Commodity(commodity_to_data(comm)),
        },
        Directive::Pad(pad) => DirectiveWrapper {
            directive_type: "pad".to_string(),
            date: pad.date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Pad(pad_to_data(pad)),
        },
        Directive::Event(event) => DirectiveWrapper {
            directive_type: "event".to_string(),
            date: event.date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Event(event_to_data(event)),
        },
        Directive::Note(note) => DirectiveWrapper {
            directive_type: "note".to_string(),
            date: note.date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Note(note_to_data(note)),
        },
        Directive::Document(doc) => DirectiveWrapper {
            directive_type: "document".to_string(),
            date: doc.date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Document(document_to_data(doc)),
        },
        Directive::Price(price) => DirectiveWrapper {
            directive_type: "price".to_string(),
            date: price.date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Price(price_to_data(price)),
        },
        Directive::Query(query) => DirectiveWrapper {
            directive_type: "query".to_string(),
            date: query.date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Query(query_to_data(query)),
        },
        Directive::Custom(custom) => DirectiveWrapper {
            directive_type: "custom".to_string(),
            date: custom.date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Custom(custom_to_data(custom)),
        },
    }
}

/// Convert a list of directives to serializable wrappers.
pub fn directives_to_wrappers(directives: &[Directive]) -> Vec<DirectiveWrapper> {
    directives.iter().map(directive_to_wrapper).collect()
}

/// Convert a serializable wrapper back to a directive.
pub fn wrapper_to_directive(wrapper: &DirectiveWrapper) -> Result<Directive, ConversionError> {
    let date = wrapper
        .date
        .parse::<NaiveDate>()
        .map_err(|_| ConversionError::InvalidDate(wrapper.date.clone()))?;

    match &wrapper.data {
        DirectiveData::Transaction(data) => {
            Ok(Directive::Transaction(data_to_transaction(data, date)?))
        }
        DirectiveData::Balance(data) => Ok(Directive::Balance(data_to_balance(data, date)?)),
        DirectiveData::Open(data) => Ok(Directive::Open(data_to_open(data, date))),
        DirectiveData::Close(data) => Ok(Directive::Close(data_to_close(data, date))),
        DirectiveData::Commodity(data) => Ok(Directive::Commodity(data_to_commodity(data, date))),
        DirectiveData::Pad(data) => Ok(Directive::Pad(data_to_pad(data, date))),
        DirectiveData::Event(data) => Ok(Directive::Event(data_to_event(data, date))),
        DirectiveData::Note(data) => Ok(Directive::Note(data_to_note(data, date))),
        DirectiveData::Document(data) => Ok(Directive::Document(data_to_document(data, date))),
        DirectiveData::Price(data) => Ok(Directive::Price(data_to_price(data, date)?)),
        DirectiveData::Query(data) => Ok(Directive::Query(data_to_query(data, date))),
        DirectiveData::Custom(data) => Ok(Directive::Custom(data_to_custom(data, date))),
    }
}

/// Convert a list of serializable wrappers back to directives.
pub fn wrappers_to_directives(
    wrappers: &[DirectiveWrapper],
) -> Result<Vec<Directive>, ConversionError> {
    wrappers.iter().map(wrapper_to_directive).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_core::{
        Amount, Balance, Close, Commodity, Custom, Decimal, Document, Event, IncompleteAmount,
        MetaValue, Metadata, Note, Open, Pad, Posting, Price, Query, Transaction,
    };
    use std::str::FromStr;

    fn dec(s: &str) -> Decimal {
        Decimal::from_str(s).unwrap()
    }

    #[test]
    fn test_roundtrip_transaction() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let txn = Transaction {
            date,
            flag: '*',
            payee: Some("Grocery Store".into()),
            narration: "Weekly groceries".into(),
            tags: vec!["food".into()],
            links: vec!["grocery-2024".into()],
            meta: Metadata::default(),
            postings: vec![
                rustledger_core::Spanned::synthesized(Posting {
                    account: "Expenses:Food".into(),
                    units: Some(IncompleteAmount::Complete(Amount::new(dec("50.00"), "USD"))),
                    cost: None,
                    price: None,
                    flag: None,
                    meta: Metadata::default(),
                    comments: Vec::new(),
                    trailing_comments: Vec::new(),
                }),
                rustledger_core::Spanned::synthesized(Posting {
                    account: "Assets:Checking".into(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    meta: Metadata::default(),
                    comments: Vec::new(),
                    trailing_comments: Vec::new(),
                }),
            ],
            trailing_comments: Vec::new(),
        };

        let directive = Directive::Transaction(txn);
        let wrapper = directive_to_wrapper(&directive);
        let roundtrip = wrapper_to_directive(&wrapper).unwrap();

        if let (Directive::Transaction(orig), Directive::Transaction(rt)) = (&directive, &roundtrip)
        {
            assert_eq!(orig.date, rt.date);
            assert_eq!(orig.flag, rt.flag);
            assert_eq!(orig.payee, rt.payee);
            assert_eq!(orig.narration, rt.narration);
            assert_eq!(orig.tags, rt.tags);
            assert_eq!(orig.links, rt.links);
            assert_eq!(orig.postings.len(), rt.postings.len());
        } else {
            panic!("Expected Transaction directive");
        }
    }

    #[test]
    fn test_roundtrip_balance() {
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();
        let balance = Balance {
            date,
            account: "Assets:Checking".into(),
            amount: Amount::new(dec("1000.00"), "USD"),
            tolerance: Some(dec("0.01")),
            meta: Metadata::default(),
        };

        let directive = Directive::Balance(balance);
        let wrapper = directive_to_wrapper(&directive);
        let roundtrip = wrapper_to_directive(&wrapper).unwrap();

        if let (Directive::Balance(orig), Directive::Balance(rt)) = (&directive, &roundtrip) {
            assert_eq!(orig.date, rt.date);
            assert_eq!(orig.account, rt.account);
            assert_eq!(orig.amount, rt.amount);
            assert_eq!(orig.tolerance, rt.tolerance);
        } else {
            panic!("Expected Balance directive");
        }
    }

    #[test]
    fn test_roundtrip_open() {
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();
        let open = Open {
            date,
            account: "Assets:Checking".into(),
            currencies: vec!["USD".into(), "EUR".into()],
            booking: Some("FIFO".to_string()),
            meta: Metadata::default(),
        };

        let directive = Directive::Open(open);
        let wrapper = directive_to_wrapper(&directive);
        let roundtrip = wrapper_to_directive(&wrapper).unwrap();

        if let (Directive::Open(orig), Directive::Open(rt)) = (&directive, &roundtrip) {
            assert_eq!(orig.date, rt.date);
            assert_eq!(orig.account, rt.account);
            assert_eq!(orig.currencies, rt.currencies);
            assert_eq!(orig.booking, rt.booking);
        } else {
            panic!("Expected Open directive");
        }
    }

    #[test]
    fn test_roundtrip_price() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let price = Price {
            date,
            currency: "AAPL".into(),
            amount: Amount::new(dec("185.50"), "USD"),
            meta: Metadata::default(),
        };

        let directive = Directive::Price(price);
        let wrapper = directive_to_wrapper(&directive);
        let roundtrip = wrapper_to_directive(&wrapper).unwrap();

        if let (Directive::Price(orig), Directive::Price(rt)) = (&directive, &roundtrip) {
            assert_eq!(orig.date, rt.date);
            assert_eq!(orig.currency, rt.currency);
            assert_eq!(orig.amount, rt.amount);
        } else {
            panic!("Expected Price directive");
        }
    }

    /// Regression for #1214: Document directives must carry tags
    /// and links through both legs of the plugin round-trip. Pre-fix
    /// both `document_to_data` (way out) and `data_to_document` (way
    /// back in) dropped these fields to empty vectors, meaning any
    /// document passing through a plugin lost its tags/links.
    #[test]
    fn test_roundtrip_document_tags_and_links_1214() {
        let date = rustledger_core::naive_date(2024, 1, 15).unwrap();
        let doc = Document {
            date,
            account: "Assets:Bank".into(),
            path: "statements/2024-01.pdf".to_string(),
            tags: vec!["statement".into(), "bank".into()],
            links: vec!["inv-2024-01".into()],
            meta: Metadata::default(),
        };

        let directive = Directive::Document(doc);
        let wrapper = directive_to_wrapper(&directive);
        let roundtrip = wrapper_to_directive(&wrapper).unwrap();

        if let (Directive::Document(orig), Directive::Document(rt)) = (&directive, &roundtrip) {
            assert_eq!(orig.date, rt.date);
            assert_eq!(orig.account, rt.account);
            assert_eq!(orig.path, rt.path);
            assert_eq!(
                orig.tags, rt.tags,
                "Document.tags must survive the plugin round-trip",
            );
            assert_eq!(
                orig.links, rt.links,
                "Document.links must survive the plugin round-trip",
            );
        } else {
            panic!("Expected Document directive");
        }
    }

    #[test]
    fn test_roundtrip_all_directive_types() {
        let date = rustledger_core::naive_date(2024, 1, 1).unwrap();

        let directives = vec![
            Directive::Open(Open {
                date,
                account: "Assets:Test".into(),
                currencies: vec![],
                booking: None,
                meta: Metadata::default(),
            }),
            Directive::Close(Close {
                date,
                account: "Assets:Test".into(),
                meta: Metadata::default(),
            }),
            Directive::Commodity(Commodity {
                date,
                currency: "TEST".into(),
                meta: Metadata::default(),
            }),
            Directive::Pad(Pad {
                date,
                account: "Assets:Checking".into(),
                source_account: "Equity:Opening".into(),
                meta: Metadata::default(),
            }),
            Directive::Event(Event {
                date,
                event_type: "location".to_string(),
                value: "Home".to_string(),
                meta: Metadata::default(),
            }),
            Directive::Note(Note {
                date,
                account: "Assets:Test".into(),
                comment: "Test note".to_string(),
                meta: Metadata::default(),
            }),
            Directive::Document(Document {
                date,
                account: "Assets:Test".into(),
                path: "/path/to/doc.pdf".to_string(),
                tags: vec![],
                links: vec![],
                meta: Metadata::default(),
            }),
            Directive::Query(Query {
                date,
                name: "test_query".to_string(),
                query: "SELECT * FROM transactions".to_string(),
                meta: Metadata::default(),
            }),
            Directive::Custom(Custom {
                date,
                custom_type: "budget".to_string(),
                values: vec![MetaValue::String("monthly".to_string())],
                meta: Metadata::default(),
            }),
        ];

        let wrappers = directives_to_wrappers(&directives);
        let roundtrip = wrappers_to_directives(&wrappers).unwrap();

        assert_eq!(directives.len(), roundtrip.len());
    }
}
