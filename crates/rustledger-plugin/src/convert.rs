//! Conversion between core types and plugin serialization types.

use rustledger_core::{
    Amount, Balance, Close, Commodity, CostSpec, Custom, Decimal, Directive, Document, Event,
    IncompleteAmount, MetaValue, NaiveDate, Note, Open, Pad, Posting, Price, PriceAnnotation,
    Query, Transaction,
};

use crate::types::{DirectiveWrapper, DirectiveData, TransactionData, PostingData, AmountData, CostData, PriceAnnotationData, MetaValueData, BalanceData, OpenData, CloseData, CommodityData, PadData, EventData, NoteData, DocumentData, PriceData, QueryData, CustomData};

/// Convert a directive to its serializable wrapper.
pub fn directive_to_wrapper(directive: &Directive) -> DirectiveWrapper {
    match directive {
        Directive::Transaction(txn) => DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: txn.date.to_string(),
            data: DirectiveData::Transaction(transaction_to_data(txn)),
        },
        Directive::Balance(bal) => DirectiveWrapper {
            directive_type: "balance".to_string(),
            date: bal.date.to_string(),
            data: DirectiveData::Balance(balance_to_data(bal)),
        },
        Directive::Open(open) => DirectiveWrapper {
            directive_type: "open".to_string(),
            date: open.date.to_string(),
            data: DirectiveData::Open(open_to_data(open)),
        },
        Directive::Close(close) => DirectiveWrapper {
            directive_type: "close".to_string(),
            date: close.date.to_string(),
            data: DirectiveData::Close(close_to_data(close)),
        },
        Directive::Commodity(comm) => DirectiveWrapper {
            directive_type: "commodity".to_string(),
            date: comm.date.to_string(),
            data: DirectiveData::Commodity(commodity_to_data(comm)),
        },
        Directive::Pad(pad) => DirectiveWrapper {
            directive_type: "pad".to_string(),
            date: pad.date.to_string(),
            data: DirectiveData::Pad(pad_to_data(pad)),
        },
        Directive::Event(event) => DirectiveWrapper {
            directive_type: "event".to_string(),
            date: event.date.to_string(),
            data: DirectiveData::Event(event_to_data(event)),
        },
        Directive::Note(note) => DirectiveWrapper {
            directive_type: "note".to_string(),
            date: note.date.to_string(),
            data: DirectiveData::Note(note_to_data(note)),
        },
        Directive::Document(doc) => DirectiveWrapper {
            directive_type: "document".to_string(),
            date: doc.date.to_string(),
            data: DirectiveData::Document(document_to_data(doc)),
        },
        Directive::Price(price) => DirectiveWrapper {
            directive_type: "price".to_string(),
            date: price.date.to_string(),
            data: DirectiveData::Price(price_to_data(price)),
        },
        Directive::Query(query) => DirectiveWrapper {
            directive_type: "query".to_string(),
            date: query.date.to_string(),
            data: DirectiveData::Query(query_to_data(query)),
        },
        Directive::Custom(custom) => DirectiveWrapper {
            directive_type: "custom".to_string(),
            date: custom.date.to_string(),
            data: DirectiveData::Custom(custom_to_data(custom)),
        },
    }
}

fn transaction_to_data(txn: &Transaction) -> TransactionData {
    TransactionData {
        flag: txn.flag.to_string(),
        payee: txn.payee.clone(),
        narration: txn.narration.clone(),
        tags: txn.tags.clone(),
        links: txn.links.clone(),
        metadata: txn
            .meta
            .iter()
            .map(|(k, v)| (k.clone(), meta_value_to_data(v)))
            .collect(),
        postings: txn.postings.iter().map(posting_to_data).collect(),
    }
}

fn posting_to_data(posting: &Posting) -> PostingData {
    PostingData {
        account: posting.account.clone(),
        units: posting.units.as_ref().and_then(incomplete_amount_to_data),
        cost: posting.cost.as_ref().map(cost_to_data),
        price: posting.price.as_ref().map(price_annotation_to_data),
        flag: posting.flag.map(|c| c.to_string()),
        metadata: posting
            .meta
            .iter()
            .map(|(k, v)| (k.clone(), meta_value_to_data(v)))
            .collect(),
    }
}

fn incomplete_amount_to_data(incomplete: &IncompleteAmount) -> Option<AmountData> {
    match incomplete {
        IncompleteAmount::Complete(amount) => Some(amount_to_data(amount)),
        IncompleteAmount::CurrencyOnly(currency) => Some(AmountData {
            number: String::new(), // Empty number indicates interpolation needed
            currency: currency.clone(),
        }),
        IncompleteAmount::NumberOnly(number) => Some(AmountData {
            number: number.to_string(),
            currency: String::new(), // Empty currency indicates inference needed
        }),
    }
}

fn amount_to_data(amount: &Amount) -> AmountData {
    AmountData {
        number: amount.number.to_string(),
        currency: amount.currency.clone(),
    }
}

fn cost_to_data(cost: &CostSpec) -> CostData {
    CostData {
        number_per: cost.number_per.map(|n| n.to_string()),
        number_total: cost.number_total.map(|n| n.to_string()),
        currency: cost.currency.clone(),
        date: cost.date.map(|d| d.to_string()),
        label: cost.label.clone(),
        merge: cost.merge,
    }
}

fn price_annotation_to_data(price: &PriceAnnotation) -> PriceAnnotationData {
    match price {
        PriceAnnotation::Unit(amount) => PriceAnnotationData {
            is_total: false,
            amount: Some(amount_to_data(amount)),
            number: None,
            currency: None,
        },
        PriceAnnotation::Total(amount) => PriceAnnotationData {
            is_total: true,
            amount: Some(amount_to_data(amount)),
            number: None,
            currency: None,
        },
        PriceAnnotation::UnitIncomplete(inc) => PriceAnnotationData {
            is_total: false,
            amount: inc.as_amount().map(amount_to_data),
            number: inc.number().map(|n| n.to_string()),
            currency: inc.currency().map(String::from),
        },
        PriceAnnotation::TotalIncomplete(inc) => PriceAnnotationData {
            is_total: true,
            amount: inc.as_amount().map(amount_to_data),
            number: inc.number().map(|n| n.to_string()),
            currency: inc.currency().map(String::from),
        },
        PriceAnnotation::UnitEmpty => PriceAnnotationData {
            is_total: false,
            amount: None,
            number: None,
            currency: None,
        },
        PriceAnnotation::TotalEmpty => PriceAnnotationData {
            is_total: true,
            amount: None,
            number: None,
            currency: None,
        },
    }
}

fn meta_value_to_data(value: &MetaValue) -> MetaValueData {
    match value {
        MetaValue::String(s) => MetaValueData::String(s.clone()),
        MetaValue::Number(n) => MetaValueData::Number(n.to_string()),
        MetaValue::Date(d) => MetaValueData::Date(d.to_string()),
        MetaValue::Account(a) => MetaValueData::Account(a.clone()),
        MetaValue::Currency(c) => MetaValueData::Currency(c.clone()),
        MetaValue::Tag(t) => MetaValueData::Tag(t.clone()),
        MetaValue::Link(l) => MetaValueData::Link(l.clone()),
        MetaValue::Amount(a) => MetaValueData::Amount(amount_to_data(a)),
        MetaValue::Bool(b) => MetaValueData::Bool(*b),
        MetaValue::None => MetaValueData::String(String::new()),
    }
}

fn balance_to_data(bal: &Balance) -> BalanceData {
    BalanceData {
        account: bal.account.clone(),
        amount: amount_to_data(&bal.amount),
        tolerance: bal.tolerance.map(|t| t.to_string()),
    }
}

fn open_to_data(open: &Open) -> OpenData {
    OpenData {
        account: open.account.clone(),
        currencies: open.currencies.clone(),
        booking: open.booking.clone(),
    }
}

fn close_to_data(close: &Close) -> CloseData {
    CloseData {
        account: close.account.clone(),
    }
}

fn commodity_to_data(comm: &Commodity) -> CommodityData {
    CommodityData {
        currency: comm.currency.clone(),
    }
}

fn pad_to_data(pad: &Pad) -> PadData {
    PadData {
        account: pad.account.clone(),
        source_account: pad.source_account.clone(),
    }
}

fn event_to_data(event: &Event) -> EventData {
    EventData {
        event_type: event.event_type.clone(),
        value: event.value.clone(),
    }
}

fn note_to_data(note: &Note) -> NoteData {
    NoteData {
        account: note.account.clone(),
        comment: note.comment.clone(),
    }
}

fn document_to_data(doc: &Document) -> DocumentData {
    DocumentData {
        account: doc.account.clone(),
        path: doc.path.clone(),
    }
}

fn price_to_data(price: &Price) -> PriceData {
    PriceData {
        currency: price.currency.clone(),
        amount: amount_to_data(&price.amount),
    }
}

fn query_to_data(query: &Query) -> QueryData {
    QueryData {
        name: query.name.clone(),
        query: query.query.clone(),
    }
}

fn custom_to_data(custom: &Custom) -> CustomData {
    CustomData {
        custom_type: custom.custom_type.clone(),
        values: custom
            .values
            .iter()
            .map(|v| format!("{v:?}"))
            .collect(),
    }
}

/// Convert a list of directives to serializable wrappers.
pub fn directives_to_wrappers(directives: &[Directive]) -> Vec<DirectiveWrapper> {
    directives.iter().map(directive_to_wrapper).collect()
}

/// Error returned when converting a wrapper back to a directive fails.
#[derive(Debug, Clone, thiserror::Error)]
pub enum ConversionError {
    /// Invalid date format.
    #[error("invalid date format: {0}")]
    InvalidDate(String),
    /// Invalid number format.
    #[error("invalid number format: {0}")]
    InvalidNumber(String),
    /// Invalid flag format.
    #[error("invalid flag: {0}")]
    InvalidFlag(String),
    /// Unknown directive type.
    #[error("unknown directive type: {0}")]
    UnknownDirective(String),
}

/// Convert a serializable wrapper back to a directive.
pub fn wrapper_to_directive(wrapper: &DirectiveWrapper) -> Result<Directive, ConversionError> {
    let date = NaiveDate::parse_from_str(&wrapper.date, "%Y-%m-%d")
        .map_err(|_| ConversionError::InvalidDate(wrapper.date.clone()))?;

    match &wrapper.data {
        DirectiveData::Transaction(data) => Ok(Directive::Transaction(data_to_transaction(data, date)?)),
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

fn data_to_transaction(data: &TransactionData, date: NaiveDate) -> Result<Transaction, ConversionError> {
    let flag = match data.flag.as_str() {
        "*" => '*',
        "!" => '!',
        "P" => 'P',
        other => {
            if let Some(c) = other.chars().next() {
                c
            } else {
                return Err(ConversionError::InvalidFlag(other.to_string()));
            }
        }
    };

    let postings = data
        .postings
        .iter()
        .map(data_to_posting)
        .collect::<Result<Vec<_>, _>>()?;

    let meta = data
        .metadata
        .iter()
        .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
        .collect();

    Ok(Transaction {
        date,
        flag,
        payee: data.payee.clone(),
        narration: data.narration.clone(),
        tags: data.tags.clone(),
        links: data.links.clone(),
        meta,
        postings,
    })
}

fn data_to_posting(data: &PostingData) -> Result<Posting, ConversionError> {
    let units = data.units.as_ref().map(data_to_incomplete_amount).transpose()?;
    let cost = data.cost.as_ref().map(data_to_cost).transpose()?;
    let price = data.price.as_ref().map(data_to_price_annotation).transpose()?;
    let flag = data.flag.as_ref().and_then(|s| s.chars().next());

    let meta = data
        .metadata
        .iter()
        .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
        .collect();

    Ok(Posting {
        account: data.account.clone(),
        units,
        cost,
        price,
        flag,
        meta,
    })
}

fn data_to_incomplete_amount(data: &AmountData) -> Result<IncompleteAmount, ConversionError> {
    if data.number.is_empty() && !data.currency.is_empty() {
        Ok(IncompleteAmount::CurrencyOnly(data.currency.clone()))
    } else if !data.number.is_empty() && data.currency.is_empty() {
        let number = Decimal::from_str_exact(&data.number)
            .map_err(|_| ConversionError::InvalidNumber(data.number.clone()))?;
        Ok(IncompleteAmount::NumberOnly(number))
    } else {
        let amount = data_to_amount(data)?;
        Ok(IncompleteAmount::Complete(amount))
    }
}

fn data_to_amount(data: &AmountData) -> Result<Amount, ConversionError> {
    let number = Decimal::from_str_exact(&data.number)
        .map_err(|_| ConversionError::InvalidNumber(data.number.clone()))?;
    Ok(Amount::new(number, &data.currency))
}

fn data_to_cost(data: &CostData) -> Result<CostSpec, ConversionError> {
    let number_per = data
        .number_per
        .as_ref()
        .map(|s| Decimal::from_str_exact(s))
        .transpose()
        .map_err(|_| ConversionError::InvalidNumber(data.number_per.clone().unwrap_or_default()))?;

    let number_total = data
        .number_total
        .as_ref()
        .map(|s| Decimal::from_str_exact(s))
        .transpose()
        .map_err(|_| ConversionError::InvalidNumber(data.number_total.clone().unwrap_or_default()))?;

    let date = data
        .date
        .as_ref()
        .map(|s| NaiveDate::parse_from_str(s, "%Y-%m-%d"))
        .transpose()
        .map_err(|_| ConversionError::InvalidDate(data.date.clone().unwrap_or_default()))?;

    Ok(CostSpec {
        number_per,
        number_total,
        currency: data.currency.clone(),
        date,
        label: data.label.clone(),
        merge: data.merge,
    })
}

fn data_to_price_annotation(data: &PriceAnnotationData) -> Result<PriceAnnotation, ConversionError> {
    if let Some(amount_data) = &data.amount {
        let amount = data_to_amount(amount_data)?;
        if data.is_total {
            Ok(PriceAnnotation::Total(amount))
        } else {
            Ok(PriceAnnotation::Unit(amount))
        }
    } else if data.number.is_some() || data.currency.is_some() {
        // Incomplete price
        let incomplete = if let (Some(num_str), Some(cur)) = (&data.number, &data.currency) {
            let number = Decimal::from_str_exact(num_str)
                .map_err(|_| ConversionError::InvalidNumber(num_str.clone()))?;
            IncompleteAmount::Complete(Amount::new(number, cur))
        } else if let Some(num_str) = &data.number {
            let number = Decimal::from_str_exact(num_str)
                .map_err(|_| ConversionError::InvalidNumber(num_str.clone()))?;
            IncompleteAmount::NumberOnly(number)
        } else if let Some(cur) = &data.currency {
            IncompleteAmount::CurrencyOnly(cur.clone())
        } else {
            unreachable!()
        };
        if data.is_total {
            Ok(PriceAnnotation::TotalIncomplete(incomplete))
        } else {
            Ok(PriceAnnotation::UnitIncomplete(incomplete))
        }
    } else {
        // Empty price
        if data.is_total {
            Ok(PriceAnnotation::TotalEmpty)
        } else {
            Ok(PriceAnnotation::UnitEmpty)
        }
    }
}

fn data_to_meta_value(data: &MetaValueData) -> MetaValue {
    match data {
        MetaValueData::String(s) => MetaValue::String(s.clone()),
        MetaValueData::Number(s) => {
            if let Ok(n) = Decimal::from_str_exact(s) {
                MetaValue::Number(n)
            } else {
                MetaValue::String(s.clone())
            }
        }
        MetaValueData::Date(s) => {
            if let Ok(d) = NaiveDate::parse_from_str(s, "%Y-%m-%d") {
                MetaValue::Date(d)
            } else {
                MetaValue::String(s.clone())
            }
        }
        MetaValueData::Account(s) => MetaValue::Account(s.clone()),
        MetaValueData::Currency(s) => MetaValue::Currency(s.clone()),
        MetaValueData::Tag(s) => MetaValue::Tag(s.clone()),
        MetaValueData::Link(s) => MetaValue::Link(s.clone()),
        MetaValueData::Amount(a) => {
            if let Ok(amount) = data_to_amount(a) {
                MetaValue::Amount(amount)
            } else {
                MetaValue::String(format!("{} {}", a.number, a.currency))
            }
        }
        MetaValueData::Bool(b) => MetaValue::Bool(*b),
    }
}

fn data_to_balance(data: &BalanceData, date: NaiveDate) -> Result<Balance, ConversionError> {
    let amount = data_to_amount(&data.amount)?;
    let tolerance = data
        .tolerance
        .as_ref()
        .map(|s| Decimal::from_str_exact(s))
        .transpose()
        .map_err(|_| ConversionError::InvalidNumber(data.tolerance.clone().unwrap_or_default()))?;

    Ok(Balance {
        date,
        account: data.account.clone(),
        amount,
        tolerance,
        meta: Default::default(),
    })
}

fn data_to_open(data: &OpenData, date: NaiveDate) -> Open {
    Open {
        date,
        account: data.account.clone(),
        currencies: data.currencies.clone(),
        booking: data.booking.clone(),
        meta: Default::default(),
    }
}

fn data_to_close(data: &CloseData, date: NaiveDate) -> Close {
    Close {
        date,
        account: data.account.clone(),
        meta: Default::default(),
    }
}

fn data_to_commodity(data: &CommodityData, date: NaiveDate) -> Commodity {
    Commodity {
        date,
        currency: data.currency.clone(),
        meta: Default::default(),
    }
}

fn data_to_pad(data: &PadData, date: NaiveDate) -> Pad {
    Pad {
        date,
        account: data.account.clone(),
        source_account: data.source_account.clone(),
        meta: Default::default(),
    }
}

fn data_to_event(data: &EventData, date: NaiveDate) -> Event {
    Event {
        date,
        event_type: data.event_type.clone(),
        value: data.value.clone(),
        meta: Default::default(),
    }
}

fn data_to_note(data: &NoteData, date: NaiveDate) -> Note {
    Note {
        date,
        account: data.account.clone(),
        comment: data.comment.clone(),
        meta: Default::default(),
    }
}

fn data_to_document(data: &DocumentData, date: NaiveDate) -> Document {
    Document {
        date,
        account: data.account.clone(),
        path: data.path.clone(),
        tags: Vec::new(),
        links: Vec::new(),
        meta: Default::default(),
    }
}

fn data_to_price(data: &PriceData, date: NaiveDate) -> Result<Price, ConversionError> {
    let amount = data_to_amount(&data.amount)?;
    Ok(Price {
        date,
        currency: data.currency.clone(),
        amount,
        meta: Default::default(),
    })
}

fn data_to_query(data: &QueryData, date: NaiveDate) -> Query {
    Query {
        date,
        name: data.name.clone(),
        query: data.query.clone(),
        meta: Default::default(),
    }
}

fn data_to_custom(data: &CustomData, date: NaiveDate) -> Custom {
    Custom {
        date,
        custom_type: data.custom_type.clone(),
        values: data.values.iter().map(|s| MetaValue::String(s.clone())).collect(),
        meta: Default::default(),
    }
}

/// Convert a list of serializable wrappers back to directives.
pub fn wrappers_to_directives(wrappers: &[DirectiveWrapper]) -> Result<Vec<Directive>, ConversionError> {
    wrappers.iter().map(wrapper_to_directive).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use std::str::FromStr;

    fn dec(s: &str) -> Decimal {
        Decimal::from_str(s).unwrap()
    }

    #[test]
    fn test_roundtrip_transaction() {
        let date = NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let txn = Transaction {
            date,
            flag: '*',
            payee: Some("Grocery Store".to_string()),
            narration: "Weekly groceries".to_string(),
            tags: vec!["food".to_string()],
            links: vec!["grocery-2024".to_string()],
            meta: HashMap::new(),
            postings: vec![
                Posting {
                    account: "Expenses:Food".to_string(),
                    units: Some(IncompleteAmount::Complete(Amount::new(dec("50.00"), "USD"))),
                    cost: None,
                    price: None,
                    flag: None,
                    meta: HashMap::new(),
                },
                Posting {
                    account: "Assets:Checking".to_string(),
                    units: None,
                    cost: None,
                    price: None,
                    flag: None,
                    meta: HashMap::new(),
                },
            ],
        };

        let directive = Directive::Transaction(txn);
        let wrapper = directive_to_wrapper(&directive);
        let roundtrip = wrapper_to_directive(&wrapper).unwrap();

        if let (Directive::Transaction(orig), Directive::Transaction(rt)) = (&directive, &roundtrip) {
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
        let date = NaiveDate::from_ymd_opt(2024, 1, 1).unwrap();
        let balance = Balance {
            date,
            account: "Assets:Checking".to_string(),
            amount: Amount::new(dec("1000.00"), "USD"),
            tolerance: Some(dec("0.01")),
            meta: HashMap::new(),
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
        let date = NaiveDate::from_ymd_opt(2024, 1, 1).unwrap();
        let open = Open {
            date,
            account: "Assets:Checking".to_string(),
            currencies: vec!["USD".to_string(), "EUR".to_string()],
            booking: Some("FIFO".to_string()),
            meta: HashMap::new(),
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
        let date = NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let price = Price {
            date,
            currency: "AAPL".to_string(),
            amount: Amount::new(dec("185.50"), "USD"),
            meta: HashMap::new(),
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

    #[test]
    fn test_roundtrip_all_directive_types() {
        let date = NaiveDate::from_ymd_opt(2024, 1, 1).unwrap();

        let directives = vec![
            Directive::Open(Open {
                date,
                account: "Assets:Test".to_string(),
                currencies: vec![],
                booking: None,
                meta: HashMap::new(),
            }),
            Directive::Close(Close {
                date,
                account: "Assets:Test".to_string(),
                meta: HashMap::new(),
            }),
            Directive::Commodity(Commodity {
                date,
                currency: "TEST".to_string(),
                meta: HashMap::new(),
            }),
            Directive::Pad(Pad {
                date,
                account: "Assets:Checking".to_string(),
                source_account: "Equity:Opening".to_string(),
                meta: HashMap::new(),
            }),
            Directive::Event(Event {
                date,
                event_type: "location".to_string(),
                value: "Home".to_string(),
                meta: HashMap::new(),
            }),
            Directive::Note(Note {
                date,
                account: "Assets:Test".to_string(),
                comment: "Test note".to_string(),
                meta: HashMap::new(),
            }),
            Directive::Document(Document {
                date,
                account: "Assets:Test".to_string(),
                path: "/path/to/doc.pdf".to_string(),
                tags: vec![],
                links: vec![],
                meta: HashMap::new(),
            }),
            Directive::Query(Query {
                date,
                name: "test_query".to_string(),
                query: "SELECT * FROM transactions".to_string(),
                meta: HashMap::new(),
            }),
            Directive::Custom(Custom {
                date,
                custom_type: "budget".to_string(),
                values: vec![MetaValue::String("monthly".to_string())],
                meta: HashMap::new(),
            }),
        ];

        let wrappers = directives_to_wrappers(&directives);
        let roundtrip = wrappers_to_directives(&wrappers).unwrap();

        assert_eq!(directives.len(), roundtrip.len());
    }
}
