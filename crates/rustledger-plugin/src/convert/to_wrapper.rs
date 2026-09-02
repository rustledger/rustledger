//! Conversion from core directives to plugin serialization types.

use rustledger_core::{
    Amount, Balance, Close, Commodity, CostSpec, Custom, Document, Event, IncompleteAmount,
    MetaValue, Note, Open, Pad, Posting, Price, PriceAnnotation, Query, SYNTHESIZED_FILE_ID,
    Spanned, Transaction,
};

use crate::types::{
    AmountData, BalanceData, CloseData, CommodityData, CostData, CustomData, DocumentData,
    EventData, MetaValueData, NoteData, OpenData, PadData, PostingData, PriceAnnotationData,
    PriceData, QueryData, SourceSpan, TransactionData,
};

/// A directive's metadata as the wire's ordered `Vec`, sorted by key.
///
/// [`Metadata`](rustledger_core::Metadata) is an `FxHashMap`, so iterating it
/// yields no particular order -- while the wire type is a `Vec`, whose
/// equality and encoding ARE ordered. Collecting the map directly therefore
/// made the wire representation depend on the order keys happened to be
/// inserted in: two directives with identical metadata could serialize to
/// different bytes and compare unequal.
///
/// Sorting by key costs nothing that could be preserved -- a hash map holds no
/// authored ordering to begin with -- and buys a deterministic encoding, so
/// equal metadata is equal on the wire.
///
/// Keys are unique (map keys), so `sort_by` on the key alone is a total order
/// and the sort is not merely stable-by-luck.
fn meta_to_data(meta: &rustledger_core::Metadata) -> Vec<(String, MetaValueData)> {
    let mut pairs: Vec<(String, MetaValueData)> = meta
        .iter()
        .map(|(k, v)| (k.clone(), meta_value_to_data(v)))
        .collect();
    pairs.sort_by(|(a, _), (b, _)| a.cmp(b));
    pairs
}

pub(super) fn transaction_to_data(txn: &Transaction) -> TransactionData {
    TransactionData {
        flag: txn.flag.to_string(),
        payee: txn.payee.as_ref().map(ToString::to_string),
        narration: txn.narration.to_string(),
        tags: txn.tags.iter().map(ToString::to_string).collect(),
        links: txn.links.iter().map(ToString::to_string).collect(),
        metadata: meta_to_data(&txn.meta),
        postings: txn.postings.iter().map(spanned_posting_to_data).collect(),
    }
}

/// Convert a parser-derived (or synthesized) [`Spanned<Posting>`] to the
/// plugin wire format, preserving its source location so plugins can
/// round-trip the location without writing code that handles it.
pub(super) fn spanned_posting_to_data(spanned: &Spanned<Posting>) -> PostingData {
    let mut data = posting_to_data(&spanned.value);
    if spanned.file_id != SYNTHESIZED_FILE_ID {
        // `usize as u64` is a widening cast on every supported target
        // (32-bit host or wasm32 → u64, 64-bit host → u64) so no
        // saturation or check is required.
        data.span = Some(SourceSpan {
            start: spanned.span.start as u64,
            end: spanned.span.end as u64,
            file_id: spanned.file_id,
        });
    }
    data
}

pub(super) fn posting_to_data(posting: &Posting) -> PostingData {
    PostingData {
        account: posting.account.to_string(),
        units: posting.units.as_ref().and_then(incomplete_amount_to_data),
        cost: posting.cost.as_deref().map(cost_to_data),
        price: posting.price.as_deref().map(price_annotation_to_data),
        flag: posting.flag.map(|c| c.to_string()),
        metadata: meta_to_data(&posting.meta),
        span: None,
    }
}

pub(super) fn incomplete_amount_to_data(incomplete: &IncompleteAmount) -> Option<AmountData> {
    match incomplete {
        IncompleteAmount::Complete(amount) => Some(amount_to_data(amount)),
        IncompleteAmount::CurrencyOnly(currency) => Some(AmountData {
            number: String::new(), // Empty number indicates interpolation needed
            currency: currency.to_string(),
        }),
        IncompleteAmount::NumberOnly(number) => Some(AmountData {
            number: number.to_string(),
            currency: String::new(), // Empty currency indicates inference needed
        }),
    }
}

pub(super) fn amount_to_data(amount: &Amount) -> AmountData {
    AmountData {
        number: amount.number.to_string(),
        currency: amount.currency.to_string(),
    }
}

pub(super) fn cost_to_data(cost: &CostSpec) -> CostData {
    use crate::types::CostNumberData;
    CostData {
        // PerUnitFromTotal preserves both the derived per-unit AND the
        // original `{{ total }}` on the wire. Plugins that want a
        // per-unit value use `CostNumberData::per_unit()`; those that
        // want the precise total (e.g. cost-basis reads matching
        // Python's `beancount.core.convert.get_cost`) use `total()`.
        number: cost.number.map(|n| match n {
            rustledger_core::CostNumber::PerUnit { value: d } => CostNumberData::PerUnit {
                value: d.to_string(),
            },
            rustledger_core::CostNumber::PerUnitFromTotal(b) => CostNumberData::PerUnitFromTotal {
                per_unit: b.per_unit.to_string(),
                total: b.total.to_string(),
            },
            rustledger_core::CostNumber::Total { value: d } => CostNumberData::Total {
                value: d.to_string(),
            },
            rustledger_core::CostNumber::Compound { per_unit, total } => CostNumberData::Compound {
                per_unit: per_unit.to_string(),
                total: total.to_string(),
            },
        }),
        currency: cost.currency.as_ref().map(ToString::to_string),
        date: cost.date.map(|d| d.to_string()),
        label: cost.label.clone(),
        merge: cost.merge,
    }
}

pub(super) fn price_annotation_to_data(price: &PriceAnnotation) -> PriceAnnotationData {
    let is_total = matches!(price.kind, rustledger_core::PriceKind::Total);
    match &price.amount {
        Some(rustledger_core::IncompleteAmount::Complete(amount)) => PriceAnnotationData {
            is_total,
            amount: Some(amount_to_data(amount)),
            number: None,
            currency: None,
        },
        Some(inc) => PriceAnnotationData {
            is_total,
            amount: inc.as_amount().map(amount_to_data),
            number: inc.number().map(|n| n.to_string()),
            currency: inc.currency().map(String::from),
        },
        None => PriceAnnotationData {
            is_total,
            amount: None,
            number: None,
            currency: None,
        },
    }
}

pub(super) fn meta_value_to_data(value: &MetaValue) -> MetaValueData {
    match value {
        MetaValue::String(s) => MetaValueData::String(s.clone()),
        MetaValue::Number(n) => MetaValueData::Number(n.to_string()),
        MetaValue::Date(d) => MetaValueData::Date(d.to_string()),
        MetaValue::Account(a) => MetaValueData::Account(a.to_string()),
        MetaValue::Currency(c) => MetaValueData::Currency(c.to_string()),
        MetaValue::Tag(t) => MetaValueData::Tag(t.to_string()),
        MetaValue::Link(l) => MetaValueData::Link(l.to_string()),
        MetaValue::Amount(a) => MetaValueData::Amount(amount_to_data(a)),
        MetaValue::Bool(b) => MetaValueData::Bool(*b),
        MetaValue::None => MetaValueData::String(String::new()),
        // The plugin wire has no integer case; carry it as a numeric string
        // (plugins already see `Number` the same way).
        MetaValue::Int(i) => MetaValueData::Number(i.to_string()),
    }
}

pub(super) fn balance_to_data(bal: &Balance) -> BalanceData {
    BalanceData {
        account: bal.account.to_string(),
        amount: amount_to_data(&bal.amount),
        tolerance: bal.tolerance.map(|t| t.to_string()),
        metadata: meta_to_data(&bal.meta),
    }
}

pub(super) fn open_to_data(open: &Open) -> OpenData {
    OpenData {
        account: open.account.to_string(),
        currencies: open.currencies.iter().map(ToString::to_string).collect(),
        booking: open.booking.clone(),
        metadata: meta_to_data(&open.meta),
    }
}

pub(super) fn close_to_data(close: &Close) -> CloseData {
    CloseData {
        account: close.account.to_string(),
        metadata: meta_to_data(&close.meta),
    }
}

pub(super) fn commodity_to_data(comm: &Commodity) -> CommodityData {
    CommodityData {
        currency: comm.currency.to_string(),
        metadata: meta_to_data(&comm.meta),
    }
}

pub(super) fn pad_to_data(pad: &Pad) -> PadData {
    PadData {
        account: pad.account.to_string(),
        source_account: pad.source_account.to_string(),
        metadata: meta_to_data(&pad.meta),
    }
}

pub(super) fn event_to_data(event: &Event) -> EventData {
    EventData {
        event_type: event.event_type.clone(),
        value: event.value.clone(),
        metadata: meta_to_data(&event.meta),
    }
}

pub(super) fn note_to_data(note: &Note) -> NoteData {
    NoteData {
        account: note.account.to_string(),
        comment: note.comment.clone(),
        metadata: meta_to_data(&note.meta),
    }
}

pub(super) fn document_to_data(doc: &Document) -> DocumentData {
    DocumentData {
        account: doc.account.to_string(),
        path: doc.path.clone(),
        tags: doc.tags.iter().map(ToString::to_string).collect(),
        links: doc.links.iter().map(ToString::to_string).collect(),
        metadata: meta_to_data(&doc.meta),
    }
}

pub(super) fn price_to_data(price: &Price) -> PriceData {
    PriceData {
        currency: price.currency.to_string(),
        amount: amount_to_data(&price.amount),
        metadata: meta_to_data(&price.meta),
    }
}

pub(super) fn query_to_data(query: &Query) -> QueryData {
    QueryData {
        name: query.name.clone(),
        query: query.query.clone(),
        metadata: meta_to_data(&query.meta),
    }
}

pub(super) fn custom_to_data(custom: &Custom) -> CustomData {
    CustomData {
        custom_type: custom.custom_type.clone(),
        values: custom.values.iter().map(meta_value_to_data).collect(),
        metadata: meta_to_data(&custom.meta),
    }
}
