//! Conversion from plugin serialization types to core directives.

use rustledger_core::{
    Amount, Balance, Close, Commodity, CostSpec, Custom, Decimal, Document, Event,
    IncompleteAmount, MetaValue, NaiveDate, Note, Open, Pad, Posting, Price, PriceAnnotation,
    Query, Transaction,
};

use crate::types::{
    AmountData, BalanceData, CloseData, CommodityData, CostData, CustomData, DocumentData,
    EventData, MetaValueData, NoteData, OpenData, PadData, PostingData, PriceAnnotationData,
    PriceData, QueryData, TransactionData,
};

use super::ConversionError;

pub(super) fn data_to_transaction(
    data: &TransactionData,
    date: NaiveDate,
) -> Result<Transaction, ConversionError> {
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
        payee: data.payee.as_ref().map(|p| p.as_str().into()),
        narration: data.narration.as_str().into(),
        tags: data.tags.iter().map(|t| t.as_str().into()).collect(),
        links: data.links.iter().map(|l| l.as_str().into()).collect(),
        meta,
        postings,
        trailing_comments: Vec::new(),
    })
}

pub(super) fn data_to_posting(data: &PostingData) -> Result<Posting, ConversionError> {
    let units = data
        .units
        .as_ref()
        .map(data_to_incomplete_amount)
        .transpose()?;
    let cost = data.cost.as_ref().map(data_to_cost).transpose()?;
    let price = data
        .price
        .as_ref()
        .map(data_to_price_annotation)
        .transpose()?;
    let flag = data.flag.as_ref().and_then(|s| s.chars().next());

    let meta = data
        .metadata
        .iter()
        .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
        .collect();

    Ok(Posting {
        account: data.account.clone().into(),
        units,
        cost,
        price,
        flag,
        meta,
        comments: Vec::new(),
        trailing_comments: Vec::new(),
    })
}

pub(super) fn data_to_incomplete_amount(
    data: &AmountData,
) -> Result<IncompleteAmount, ConversionError> {
    if data.number.is_empty() && !data.currency.is_empty() {
        Ok(IncompleteAmount::CurrencyOnly(data.currency.clone().into()))
    } else if !data.number.is_empty() && data.currency.is_empty() {
        let number = Decimal::from_str_exact(&data.number)
            .map_err(|_| ConversionError::InvalidNumber(data.number.clone()))?;
        Ok(IncompleteAmount::NumberOnly(number))
    } else {
        let amount = data_to_amount(data)?;
        Ok(IncompleteAmount::Complete(amount))
    }
}

pub(super) fn data_to_amount(data: &AmountData) -> Result<Amount, ConversionError> {
    let number = Decimal::from_str_exact(&data.number)
        .map_err(|_| ConversionError::InvalidNumber(data.number.clone()))?;
    Ok(Amount::new(number, &data.currency))
}

pub(super) fn data_to_cost(data: &CostData) -> Result<CostSpec, ConversionError> {
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
        .map_err(|_| {
            ConversionError::InvalidNumber(data.number_total.clone().unwrap_or_default())
        })?;

    let date = data
        .date
        .as_ref()
        .map(|s| NaiveDate::parse_from_str(s, "%Y-%m-%d"))
        .transpose()
        .map_err(|_| ConversionError::InvalidDate(data.date.clone().unwrap_or_default()))?;

    Ok(CostSpec {
        number_per,
        number_total,
        currency: data.currency.as_ref().map(|c| c.clone().into()),
        date,
        label: data.label.clone(),
        merge: data.merge,
    })
}

pub(super) fn data_to_price_annotation(
    data: &PriceAnnotationData,
) -> Result<PriceAnnotation, ConversionError> {
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
            IncompleteAmount::CurrencyOnly(cur.clone().into())
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

pub(super) fn data_to_meta_value(data: &MetaValueData) -> MetaValue {
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

pub(super) fn data_to_balance(
    data: &BalanceData,
    date: NaiveDate,
) -> Result<Balance, ConversionError> {
    let amount = data_to_amount(&data.amount)?;
    let tolerance = data
        .tolerance
        .as_ref()
        .map(|s| Decimal::from_str_exact(s))
        .transpose()
        .map_err(|_| ConversionError::InvalidNumber(data.tolerance.clone().unwrap_or_default()))?;

    Ok(Balance {
        date,
        account: data.account.clone().into(),
        amount,
        tolerance,
        meta: data
            .metadata
            .iter()
            .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
            .collect(),
    })
}

pub(super) fn data_to_open(data: &OpenData, date: NaiveDate) -> Open {
    Open {
        date,
        account: data.account.clone().into(),
        currencies: data.currencies.iter().map(|c| c.clone().into()).collect(),
        booking: data.booking.clone(),
        meta: data
            .metadata
            .iter()
            .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
            .collect(),
    }
}

pub(super) fn data_to_close(data: &CloseData, date: NaiveDate) -> Close {
    Close {
        date,
        account: data.account.clone().into(),
        meta: data
            .metadata
            .iter()
            .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
            .collect(),
    }
}

pub(super) fn data_to_commodity(data: &CommodityData, date: NaiveDate) -> Commodity {
    Commodity {
        date,
        currency: data.currency.clone().into(),
        meta: data
            .metadata
            .iter()
            .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
            .collect(),
    }
}

pub(super) fn data_to_pad(data: &PadData, date: NaiveDate) -> Pad {
    Pad {
        date,
        account: data.account.clone().into(),
        source_account: data.source_account.clone().into(),
        meta: data
            .metadata
            .iter()
            .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
            .collect(),
    }
}

pub(super) fn data_to_event(data: &EventData, date: NaiveDate) -> Event {
    Event {
        date,
        event_type: data.event_type.clone(),
        value: data.value.clone(),
        meta: data
            .metadata
            .iter()
            .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
            .collect(),
    }
}

pub(super) fn data_to_note(data: &NoteData, date: NaiveDate) -> Note {
    Note {
        date,
        account: data.account.clone().into(),
        comment: data.comment.clone(),
        meta: data
            .metadata
            .iter()
            .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
            .collect(),
    }
}

pub(super) fn data_to_document(data: &DocumentData, date: NaiveDate) -> Document {
    Document {
        date,
        account: data.account.clone().into(),
        path: data.path.clone(),
        tags: Vec::new(),
        links: Vec::new(),
        meta: data
            .metadata
            .iter()
            .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
            .collect(),
    }
}

pub(super) fn data_to_price(data: &PriceData, date: NaiveDate) -> Result<Price, ConversionError> {
    let amount = data_to_amount(&data.amount)?;
    Ok(Price {
        date,
        currency: data.currency.clone().into(),
        amount,
        meta: data
            .metadata
            .iter()
            .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
            .collect(),
    })
}

pub(super) fn data_to_query(data: &QueryData, date: NaiveDate) -> Query {
    Query {
        date,
        name: data.name.clone(),
        query: data.query.clone(),
        meta: data
            .metadata
            .iter()
            .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
            .collect(),
    }
}

pub(super) fn data_to_custom(data: &CustomData, date: NaiveDate) -> Custom {
    Custom {
        date,
        custom_type: data.custom_type.clone(),
        values: data.values.iter().map(data_to_meta_value).collect(),
        meta: data
            .metadata
            .iter()
            .map(|(k, v)| (k.clone(), data_to_meta_value(v)))
            .collect(),
    }
}
